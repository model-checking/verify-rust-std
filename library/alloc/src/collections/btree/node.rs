// This is an attempt at an implementation following the ideal
//
// ```
// struct BTreeMap<K, V> {
//     height: usize,
//     root: Option<Box<Node<K, V, height>>>
// }
//
// struct Node<K, V, height: usize> {
//     keys: [K; 2 * B - 1],
//     vals: [V; 2 * B - 1],
//     edges: [if height > 0 { Box<Node<K, V, height - 1>> } else { () }; 2 * B],
//     parent: Option<(NonNull<Node<K, V, height + 1>>, u16)>,
//     len: u16,
// }
// ```
//
// Since Rust doesn't actually have dependent types and polymorphic recursion,
// we make do with lots of unsafety.

// A major goal of this module is to avoid complexity by treating the tree as a generic (if
// weirdly shaped) container and avoiding dealing with most of the B-Tree invariants. As such,
// this module doesn't care whether the entries are sorted, which nodes can be underfull, or
// even what underfull means. However, we do rely on a few invariants:
//
// - Trees must have uniform depth/height. This means that every path down to a leaf from a
//   given node has exactly the same length.
// - A node of length `n` has `n` keys, `n` values, and `n + 1` edges.
//   This implies that even an empty node has at least one edge.
//   For a leaf node, "having an edge" only means we can identify a position in the node,
//   since leaf edges are empty and need no data representation. In an internal node,
//   an edge both identifies a position and contains a pointer to a child node.

use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::num::NonZero;
use core::ptr::{self, NonNull};
use core::slice::SliceIndex;

use crate::alloc::{Allocator, Layout};
use crate::boxed::Box;

const B: usize = 6;
pub(super) const CAPACITY: usize = 2 * B - 1;
pub(super) const MIN_LEN_AFTER_SPLIT: usize = B - 1;
const KV_IDX_CENTER: usize = B - 1;
const EDGE_IDX_LEFT_OF_CENTER: usize = B - 1;
const EDGE_IDX_RIGHT_OF_CENTER: usize = B;

/// The underlying representation of leaf nodes and part of the representation of internal nodes.
struct LeafNode<K, V> {
    /// We want to be covariant in `K` and `V`.
    parent: Option<NonNull<InternalNode<K, V>>>,

    /// This node's index into the parent node's `edges` array.
    /// `*node.parent.edges[node.parent_idx]` should be the same thing as `node`.
    /// This is only guaranteed to be initialized when `parent` is non-null.
    parent_idx: MaybeUninit<u16>,

    /// The number of keys and values this node stores.
    len: u16,

    /// The arrays storing the actual data of the node. Only the first `len` elements of each
    /// array are initialized and valid.
    keys: [MaybeUninit<K>; CAPACITY],
    vals: [MaybeUninit<V>; CAPACITY],
}

impl<K, V> LeafNode<K, V> {
    /// Initializes a new `LeafNode` in-place.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `this` points to a (possibly uninitialized) `LeafNode`
    unsafe fn init(this: *mut Self) {
        // As a general policy, we leave fields uninitialized if they can be, as this should
        // be both slightly faster and easier to track in Valgrind.
        unsafe {
            // parent_idx, keys, and vals are all MaybeUninit
            (&raw mut (*this).parent).write(None);
            (&raw mut (*this).len).write(0);
        }
    }

    /// Creates a new boxed `LeafNode`.
    fn new<A: Allocator + Clone>(alloc: A) -> Box<Self, A> {
        let mut leaf = Box::new_uninit_in(alloc);
        unsafe {
            // SAFETY: `leaf` points to a `LeafNode`
            LeafNode::init(leaf.as_mut_ptr());
            // SAFETY: `leaf` was just initialized
            leaf.assume_init()
        }
    }
}

/// The underlying representation of internal nodes. As with `LeafNode`s, these should be hidden
/// behind `BoxedNode`s to prevent dropping uninitialized keys and values. Any pointer to an
/// `InternalNode` can be directly cast to a pointer to the underlying `LeafNode` portion of the
/// node, allowing code to act on leaf and internal nodes generically without having to even check
/// which of the two a pointer is pointing at. This property is enabled by the use of `repr(C)`.
#[repr(C)]
// gdb_providers.py uses this type name for introspection.
struct InternalNode<K, V> {
    data: LeafNode<K, V>,

    /// The pointers to the children of this node. `len + 1` of these are considered
    /// initialized and valid, except that near the end, while the tree is held
    /// through borrow type `Dying`, some of these pointers are dangling.
    edges: [MaybeUninit<BoxedNode<K, V>>; 2 * B],
}

impl<K, V> InternalNode<K, V> {
    /// Creates a new boxed `InternalNode`.
    ///
    /// # Safety
    /// An invariant of internal nodes is that they have at least one
    /// initialized and valid edge. This function does not set up
    /// such an edge.
    unsafe fn new<A: Allocator + Clone>(alloc: A) -> Box<Self, A> {
        let mut node = Box::<Self, _>::new_uninit_in(alloc);
        unsafe {
            // SAFETY: argument points to the `node.data` `LeafNode`
            LeafNode::init(&raw mut (*node.as_mut_ptr()).data);
            // SAFETY: `node.data` was just initialized and `node.edges` is MaybeUninit.
            node.assume_init()
        }
    }
}

/// A managed, non-null pointer to a node. This is either an owned pointer to
/// `LeafNode<K, V>` or an owned pointer to `InternalNode<K, V>`.
///
/// However, `BoxedNode` contains no information as to which of the two types
/// of nodes it actually contains, and, partially due to this lack of information,
/// is not a separate type and has no destructor.
type BoxedNode<K, V> = NonNull<LeafNode<K, V>>;

// N.B. `NodeRef` is always covariant in `K` and `V`, even when the `BorrowType`
// is `Mut`. This is technically wrong, but cannot result in any unsafety due to
// internal use of `NodeRef` because we stay completely generic over `K` and `V`.
// However, whenever a public type wraps `NodeRef`, make sure that it has the
// correct variance.
///
/// A reference to a node.
///
/// This type has a number of parameters that control how it acts:
/// - `BorrowType`: A dummy type that describes the kind of borrow and carries a lifetime.
///    - When this is `Immut<'a>`, the `NodeRef` acts roughly like `&'a Node`.
///    - When this is `ValMut<'a>`, the `NodeRef` acts roughly like `&'a Node`
///      with respect to keys and tree structure, but also allows many
///      mutable references to values throughout the tree to coexist.
///    - When this is `Mut<'a>`, the `NodeRef` acts roughly like `&'a mut Node`,
///      although insert methods allow a mutable pointer to a value to coexist.
///    - When this is `Owned`, the `NodeRef` acts roughly like `Box<Node>`,
///      but does not have a destructor, and must be cleaned up manually.
///    - When this is `Dying`, the `NodeRef` still acts roughly like `Box<Node>`,
///      but has methods to destroy the tree bit by bit, and ordinary methods,
///      while not marked as unsafe to call, can invoke UB if called incorrectly.
///   Since any `NodeRef` allows navigating through the tree, `BorrowType`
///   effectively applies to the entire tree, not just to the node itself.
/// - `K` and `V`: These are the types of keys and values stored in the nodes.
/// - `Type`: This can be `Leaf`, `Internal`, or `LeafOrInternal`. When this is
///   `Leaf`, the `NodeRef` points to a leaf node, when this is `Internal` the
///   `NodeRef` points to an internal node, and when this is `LeafOrInternal` the
///   `NodeRef` could be pointing to either type of node.
///   `Type` is named `NodeType` when used outside `NodeRef`.
///
/// Both `BorrowType` and `NodeType` restrict what methods we implement, to
/// exploit static type safety. There are limitations in the way we can apply
/// such restrictions:
/// - For each type parameter, we can only define a method either generically
///   or for one particular type. For example, we cannot define a method like
///   `into_kv` generically for all `BorrowType`, or once for all types that
///   carry a lifetime, because we want it to return `&'a` references.
///   Therefore, we define it only for the least powerful type `Immut<'a>`.
/// - We cannot get implicit coercion from say `Mut<'a>` to `Immut<'a>`.
///   Therefore, we have to explicitly call `reborrow` on a more powerful
///   `NodeRef` in order to reach a method like `into_kv`.
///
/// All methods on `NodeRef` that return some kind of reference, either:
/// - Take `self` by value, and return the lifetime carried by `BorrowType`.
///   Sometimes, to invoke such a method, we need to call `reborrow_mut`.
/// - Take `self` by reference, and (implicitly) return that reference's
///   lifetime, instead of the lifetime carried by `BorrowType`. That way,
///   the borrow checker guarantees that the `NodeRef` remains borrowed as long
///   as the returned reference is used.
///   The methods supporting insert bend this rule by returning a raw pointer,
///   i.e., a reference without any lifetime.
pub(super) struct NodeRef<BorrowType, K, V, Type> {
    /// The number of levels that the node and the level of leaves are apart, a
    /// constant of the node that cannot be entirely described by `Type`, and that
    /// the node itself does not store. We only need to store the height of the root
    /// node, and derive every other node's height from it.
    /// Must be zero if `Type` is `Leaf` and non-zero if `Type` is `Internal`.
    height: usize,
    /// The pointer to the leaf or internal node. The definition of `InternalNode`
    /// ensures that the pointer is valid either way.
    node: NonNull<LeafNode<K, V>>,
    _marker: PhantomData<(BorrowType, Type)>,
}

/// The root node of an owned tree.
///
/// Note that this does not have a destructor, and must be cleaned up manually.
pub(super) type Root<K, V> = NodeRef<marker::Owned, K, V, marker::LeafOrInternal>;

impl<'a, K: 'a, V: 'a, Type> Copy for NodeRef<marker::Immut<'a>, K, V, Type> {}
impl<'a, K: 'a, V: 'a, Type> Clone for NodeRef<marker::Immut<'a>, K, V, Type> {
    fn clone(&self) -> Self {
        *self
    }
}

unsafe impl<BorrowType, K: Sync, V: Sync, Type> Sync for NodeRef<BorrowType, K, V, Type> {}

unsafe impl<K: Sync, V: Sync, Type> Send for NodeRef<marker::Immut<'_>, K, V, Type> {}
unsafe impl<K: Send, V: Send, Type> Send for NodeRef<marker::Mut<'_>, K, V, Type> {}
unsafe impl<K: Send, V: Send, Type> Send for NodeRef<marker::ValMut<'_>, K, V, Type> {}
unsafe impl<K: Send, V: Send, Type> Send for NodeRef<marker::Owned, K, V, Type> {}
unsafe impl<K: Send, V: Send, Type> Send for NodeRef<marker::Dying, K, V, Type> {}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Leaf> {
    pub(super) fn new_leaf<A: Allocator + Clone>(alloc: A) -> Self {
        Self::from_new_leaf(LeafNode::new(alloc))
    }

    fn from_new_leaf<A: Allocator + Clone>(leaf: Box<LeafNode<K, V>, A>) -> Self {
        // The allocator must be dropped, not leaked.  See also `BTreeMap::alloc`.
        let (node, _alloc) = Box::into_non_null_with_allocator(leaf);
        NodeRef { height: 0, node, _marker: PhantomData }
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Internal> {
    /// Creates a new internal (height > 0) `NodeRef`
    fn new_internal<A: Allocator + Clone>(child: Root<K, V>, alloc: A) -> Self {
        let mut new_node = unsafe { InternalNode::new(alloc) };
        new_node.edges[0].write(child.node);
        NodeRef::from_new_internal(new_node, NonZero::new(child.height + 1).unwrap())
    }

    /// Creates a new internal (height > 0) `NodeRef` from an existing internal node
    fn from_new_internal<A: Allocator + Clone>(
        internal: Box<InternalNode<K, V>, A>,
        height: NonZero<usize>,
    ) -> Self {
        // The allocator must be dropped, not leaked.  See also `BTreeMap::alloc`.
        let (node, _alloc) = Box::into_non_null_with_allocator(internal);
        let mut this = NodeRef { height: height.into(), node: node.cast(), _marker: PhantomData };
        this.borrow_mut().correct_all_childrens_parent_links();
        this
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    /// Unpack a node reference that was packed as `NodeRef::parent`.
    fn from_internal(node: NonNull<InternalNode<K, V>>, height: usize) -> Self {
        debug_assert!(height > 0);
        NodeRef { height, node: node.cast(), _marker: PhantomData }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    /// Exposes the data of an internal node.
    ///
    /// Returns a raw ptr to avoid invalidating other references to this node.
    fn as_internal_ptr(this: &Self) -> *mut InternalNode<K, V> {
        // SAFETY: the static node type is `Internal`.
        this.node.as_ptr() as *mut InternalNode<K, V>
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    /// Borrows exclusive access to the data of an internal node.
    fn as_internal_mut(&mut self) -> &mut InternalNode<K, V> {
        let ptr = Self::as_internal_ptr(self);
        unsafe { &mut *ptr }
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    /// Finds the length of the node. This is the number of keys or values.
    /// The number of edges is `len() + 1`.
    /// Note that, despite being safe, calling this function can have the side effect
    /// of invalidating mutable references that unsafe code has created.
    pub(super) fn len(&self) -> usize {
        // Crucially, we only access the `len` field here. If BorrowType is marker::ValMut,
        // there might be outstanding mutable references to values that we must not invalidate.
        unsafe { usize::from((*Self::as_leaf_ptr(self)).len) }
    }

    /// Returns the number of levels that the node and leaves are apart. Zero
    /// height means the node is a leaf itself. If you picture trees with the
    /// root on top, the number says at which elevation the node appears.
    /// If you picture trees with leaves on top, the number says how high
    /// the tree extends above the node.
    pub(super) fn height(&self) -> usize {
        self.height
    }

    /// Temporarily takes out another, immutable reference to the same node.
    pub(super) fn reborrow(&self) -> NodeRef<marker::Immut<'_>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    /// Exposes the leaf portion of any leaf or internal node.
    ///
    /// Returns a raw ptr to avoid invalidating other references to this node.
    fn as_leaf_ptr(this: &Self) -> *mut LeafNode<K, V> {
        // The node must be valid for at least the LeafNode portion.
        // This is not a reference in the NodeRef type because we don't know if
        // it should be unique or shared.
        this.node.as_ptr()
    }
}

impl<BorrowType: marker::BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    /// Finds the parent of the current node. Returns `Ok(handle)` if the current
    /// node actually has a parent, where `handle` points to the edge of the parent
    /// that points to the current node. Returns `Err(self)` if the current node has
    /// no parent, giving back the original `NodeRef`.
    ///
    /// The method name assumes you picture trees with the root node on top.
    ///
    /// `edge.descend().ascend().unwrap()` and `node.ascend().unwrap().descend()` should
    /// both, upon success, do nothing.
    pub(super) fn ascend(
        self,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge>, Self> {
        const {
            assert!(BorrowType::TRAVERSAL_PERMIT);
        }

        // We need to use raw pointers to nodes because, if BorrowType is marker::ValMut,
        // there might be outstanding mutable references to values that we must not invalidate.
        let leaf_ptr: *const _ = Self::as_leaf_ptr(&self);
        unsafe { (*leaf_ptr).parent }
            .as_ref()
            .map(|parent| Handle {
                node: NodeRef::from_internal(*parent, self.height + 1),
                idx: unsafe { usize::from((*leaf_ptr).parent_idx.assume_init()) },
                _marker: PhantomData,
            })
            .ok_or(self)
    }

    pub(super) fn first_edge(self) -> Handle<Self, marker::Edge> {
        unsafe { Handle::new_edge(self, 0) }
    }

    pub(super) fn last_edge(self) -> Handle<Self, marker::Edge> {
        let len = self.len();
        unsafe { Handle::new_edge(self, len) }
    }

    /// Note that `self` must be nonempty.
    pub(super) fn first_kv(self) -> Handle<Self, marker::KV> {
        let len = self.len();
        assert!(len > 0);
        unsafe { Handle::new_kv(self, 0) }
    }

    /// Note that `self` must be nonempty.
    pub(super) fn last_kv(self) -> Handle<Self, marker::KV> {
        let len = self.len();
        assert!(len > 0);
        unsafe { Handle::new_kv(self, len - 1) }
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    /// Could be a public implementation of PartialEq, but only used in this module.
    fn eq(&self, other: &Self) -> bool {
        let Self { node, height, _marker } = self;
        if node.eq(&other.node) {
            debug_assert_eq!(*height, other.height);
            true
        } else {
            false
        }
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Immut<'a>, K, V, Type> {
    /// Exposes the leaf portion of any leaf or internal node in an immutable tree.
    fn into_leaf(self) -> &'a LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(&self);
        // SAFETY: there can be no mutable references into this tree borrowed as `Immut`.
        unsafe { &*ptr }
    }

    /// Borrows a view into the keys stored in the node.
    pub(super) fn keys(&self) -> &[K] {
        let leaf = self.into_leaf();
        unsafe { leaf.keys.get_unchecked(..usize::from(leaf.len)).assume_init_ref() }
    }
}

impl<K, V> NodeRef<marker::Dying, K, V, marker::LeafOrInternal> {
    /// Similar to `ascend`, gets a reference to a node's parent node, but also
    /// deallocates the current node in the process. This is unsafe because the
    /// current node will still be accessible despite being deallocated.
    pub(super) unsafe fn deallocate_and_ascend<A: Allocator + Clone>(
        self,
        alloc: A,
    ) -> Option<Handle<NodeRef<marker::Dying, K, V, marker::Internal>, marker::Edge>> {
        let height = self.height;
        let node = self.node;
        let ret = self.ascend().ok();
        unsafe {
            alloc.deallocate(
                node.cast(),
                if height > 0 {
                    Layout::new::<InternalNode<K, V>>()
                } else {
                    Layout::new::<LeafNode<K, V>>()
                },
            );
        }
        ret
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    /// Temporarily takes out another mutable reference to the same node. Beware, as
    /// this method is very dangerous, doubly so since it might not immediately appear
    /// dangerous.
    ///
    /// Because mutable pointers can roam anywhere around the tree, the returned
    /// pointer can easily be used to make the original pointer dangling, out of
    /// bounds, or invalid under stacked borrow rules.
    // FIXME(@gereeter) consider adding yet another type parameter to `NodeRef`
    // that restricts the use of navigation methods on reborrowed pointers,
    // preventing this unsafety.
    unsafe fn reborrow_mut(&mut self) -> NodeRef<marker::Mut<'_>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    /// Borrows exclusive access to the leaf portion of a leaf or internal node.
    fn as_leaf_mut(&mut self) -> &mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(self);
        // SAFETY: we have exclusive access to the entire node.
        unsafe { &mut *ptr }
    }

    /// Offers exclusive access to the leaf portion of a leaf or internal node.
    fn into_leaf_mut(mut self) -> &'a mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(&mut self);
        // SAFETY: we have exclusive access to the entire node.
        unsafe { &mut *ptr }
    }

    /// Returns a dormant copy of this node with its lifetime erased which can
    /// be reawakened later.
    pub(super) fn dormant(&self) -> NodeRef<marker::DormantMut, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<K, V, Type> NodeRef<marker::DormantMut, K, V, Type> {
    /// Revert to the unique borrow initially captured.
    ///
    /// # Safety
    ///
    /// The reborrow must have ended, i.e., the reference returned by `new` and
    /// all pointers and references derived from it, must not be used anymore.
    pub(super) unsafe fn awaken<'a>(self) -> NodeRef<marker::Mut<'a>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<K, V, Type> NodeRef<marker::Dying, K, V, Type> {
    /// Borrows exclusive access to the leaf portion of a dying leaf or internal node.
    fn as_leaf_dying(&mut self) -> &mut LeafNode<K, V> {
        let ptr = Self::as_leaf_ptr(self);
        // SAFETY: we have exclusive access to the entire node.
        unsafe { &mut *ptr }
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    /// Borrows exclusive access to an element of the key storage area.
    ///
    /// # Safety
    /// `index` is in bounds of 0..CAPACITY
    unsafe fn key_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<K>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the key slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.as_leaf_mut().keys.as_mut_slice().get_unchecked_mut(index) }
    }

    /// Borrows exclusive access to an element or slice of the node's value storage area.
    ///
    /// # Safety
    /// `index` is in bounds of 0..CAPACITY
    unsafe fn val_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<V>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the value slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.as_leaf_mut().vals.as_mut_slice().get_unchecked_mut(index) }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    /// Borrows exclusive access to an element or slice of the node's storage area for edge contents.
    ///
    /// # Safety
    /// `index` is in bounds of 0..CAPACITY + 1
    unsafe fn edge_area_mut<I, Output: ?Sized>(&mut self, index: I) -> &mut Output
    where
        I: SliceIndex<[MaybeUninit<BoxedNode<K, V>>], Output = Output>,
    {
        // SAFETY: the caller will not be able to call further methods on self
        // until the edge slice reference is dropped, as we have unique access
        // for the lifetime of the borrow.
        unsafe { self.as_internal_mut().edges.as_mut_slice().get_unchecked_mut(index) }
    }
}

impl<'a, K, V, Type> NodeRef<marker::ValMut<'a>, K, V, Type> {
    /// # Safety
    /// - The node has more than `idx` initialized elements.
    unsafe fn into_key_val_mut_at(mut self, idx: usize) -> (&'a K, &'a mut V) {
        // We only create a reference to the one element we are interested in,
        // to avoid aliasing with outstanding references to other elements,
        // in particular, those returned to the caller in earlier iterations.
        let leaf = Self::as_leaf_ptr(&mut self);
        let keys = unsafe { &raw const (*leaf).keys };
        let vals = unsafe { &raw mut (*leaf).vals };
        // We must coerce to unsized array pointers because of Rust issue #74679.
        let keys: *const [_] = keys;
        let vals: *mut [_] = vals;
        let key = unsafe { (&*keys.get_unchecked(idx)).assume_init_ref() };
        let val = unsafe { (&mut *vals.get_unchecked_mut(idx)).assume_init_mut() };
        (key, val)
    }
}

impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    /// Borrows exclusive access to the length of the node.
    pub(super) fn len_mut(&mut self) -> &mut u16 {
        &mut self.as_leaf_mut().len
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    /// # Safety
    /// Every item returned by `range` is a valid edge index for the node.
    unsafe fn correct_childrens_parent_links<R: Iterator<Item = usize>>(&mut self, range: R) {
        for i in range {
            debug_assert!(i <= self.len());
            unsafe { Handle::new_edge(self.reborrow_mut(), i) }.correct_parent_link();
        }
    }

    fn correct_all_childrens_parent_links(&mut self) {
        let len = self.len();
        unsafe { self.correct_childrens_parent_links(0..=len) };
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    /// Sets the node's link to its parent edge,
    /// without invalidating other references to the node.
    fn set_parent_link(&mut self, parent: NonNull<InternalNode<K, V>>, parent_idx: usize) {
        let leaf = Self::as_leaf_ptr(self);
        unsafe { (*leaf).parent = Some(parent) };
        unsafe { (*leaf).parent_idx.write(parent_idx as u16) };
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::LeafOrInternal> {
    /// Clears the root's link to its parent edge.
    fn clear_parent_link(&mut self) {
        let mut root_node = self.borrow_mut();
        let leaf = root_node.as_leaf_mut();
        leaf.parent = None;
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::LeafOrInternal> {
    /// Returns a new owned tree, with its own root node that is initially empty.
    pub(super) fn new<A: Allocator + Clone>(alloc: A) -> Self {
        NodeRef::new_leaf(alloc).forget_type()
    }

    /// Adds a new internal node with a single edge pointing to the previous root node,
    /// make that new node the root node, and return it. This increases the height by 1
    /// and is the opposite of `pop_internal_level`.
    pub(super) fn push_internal_level<A: Allocator + Clone>(
        &mut self,
        alloc: A,
    ) -> NodeRef<marker::Mut<'_>, K, V, marker::Internal> {
        super::mem::take_mut(self, |old_root| NodeRef::new_internal(old_root, alloc).forget_type());

        // `self.borrow_mut()`, except that we just forgot we're internal now:
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    /// Removes the internal root node, using its first child as the new root node.
    /// As it is intended only to be called when the root node has only one child,
    /// no cleanup is done on any of the keys, values and other children.
    /// This decreases the height by 1 and is the opposite of `push_internal_level`.
    ///
    /// Does not invalidate any handles or references pointing into the subtree
    /// rooted at the first child of `self`.
    ///
    /// Panics if there is no internal level, i.e., if the root node is a leaf.
    pub(super) fn pop_internal_level<A: Allocator + Clone>(&mut self, alloc: A) {
        assert!(self.height > 0);

        let top = self.node;

        // SAFETY: we asserted to be internal.
        let mut internal_self = unsafe { self.borrow_mut().cast_to_internal_unchecked() };
        let internal_node = internal_self.as_internal_mut();
        // SAFETY: the first edge is always initialized.
        self.node = unsafe { internal_node.edges[0].assume_init_read() };
        self.height -= 1;
        self.clear_parent_link();

        unsafe {
            alloc.deallocate(top.cast(), Layout::new::<InternalNode<K, V>>());
        }
    }
}

impl<K, V, Type> NodeRef<marker::Owned, K, V, Type> {
    /// Mutably borrows the owned root node. Unlike `reborrow_mut`, this is safe
    /// because the return value cannot be used to destroy the root, and there
    /// cannot be other references to the tree.
    pub(super) fn borrow_mut(&mut self) -> NodeRef<marker::Mut<'_>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    /// Slightly mutably borrows the owned root node.
    pub(super) fn borrow_valmut(&mut self) -> NodeRef<marker::ValMut<'_>, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    /// Irreversibly transitions to a reference that permits traversal and offers
    /// destructive methods and little else.
    pub(super) fn into_dying(self) -> NodeRef<marker::Dying, K, V, Type> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Leaf> {
    /// Adds a key-value pair to the end of the node, and returns
    /// a handle to the inserted value.
    ///
    /// # Safety
    ///
    /// The returned handle has an unbound lifetime.
    pub(super) unsafe fn push_with_handle<'b>(
        &mut self,
        key: K,
        val: V,
    ) -> Handle<NodeRef<marker::Mut<'b>, K, V, marker::Leaf>, marker::KV> {
        let len = self.len_mut();
        let idx = usize::from(*len);
        assert!(idx < CAPACITY);
        *len += 1;
        unsafe {
            self.key_area_mut(idx).write(key);
            self.val_area_mut(idx).write(val);
            Handle::new_kv(
                NodeRef { height: self.height, node: self.node, _marker: PhantomData },
                idx,
            )
        }
    }

    /// Adds a key-value pair to the end of the node, and returns
    /// the mutable reference of the inserted value.
    pub(super) fn push(&mut self, key: K, val: V) -> *mut V {
        // SAFETY: The unbound handle is no longer accessible.
        unsafe { self.push_with_handle(key, val).into_val_mut() }
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    /// Adds a key-value pair, and an edge to go to the right of that pair,
    /// to the end of the node.
    pub(super) fn push(&mut self, key: K, val: V, edge: Root<K, V>) {
        assert!(edge.height == self.height - 1);

        let len = self.len_mut();
        let idx = usize::from(*len);
        assert!(idx < CAPACITY);
        *len += 1;
        unsafe {
            self.key_area_mut(idx).write(key);
            self.val_area_mut(idx).write(val);
            self.edge_area_mut(idx + 1).write(edge.node);
            Handle::new_edge(self.reborrow_mut(), idx + 1).correct_parent_link();
        }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Leaf> {
    /// Removes any static information asserting that this node is a `Leaf` node.
    pub(super) fn forget_type(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    /// Removes any static information asserting that this node is an `Internal` node.
    pub(super) fn forget_type(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
    /// Checks whether a node is an `Internal` node or a `Leaf` node.
    pub(super) fn force(
        self,
    ) -> ForceResult<
        NodeRef<BorrowType, K, V, marker::Leaf>,
        NodeRef<BorrowType, K, V, marker::Internal>,
    > {
        if self.height == 0 {
            ForceResult::Leaf(NodeRef {
                height: self.height,
                node: self.node,
                _marker: PhantomData,
            })
        } else {
            ForceResult::Internal(NodeRef {
                height: self.height,
                node: self.node,
                _marker: PhantomData,
            })
        }
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    /// Unsafely asserts to the compiler the static information that this node is a `Leaf`.
    pub(super) unsafe fn cast_to_leaf_unchecked(
        self,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::Leaf> {
        debug_assert!(self.height == 0);
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }

    /// Unsafely asserts to the compiler the static information that this node is an `Internal`.
    unsafe fn cast_to_internal_unchecked(self) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
        debug_assert!(self.height > 0);
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

/// A reference to a specific key-value pair or edge within a node. The `Node` parameter
/// must be a `NodeRef`, while the `Type` can either be `KV` (signifying a handle on a key-value
/// pair) or `Edge` (signifying a handle on an edge).
///
/// Note that even `Leaf` nodes can have `Edge` handles. Instead of representing a pointer to
/// a child node, these represent the spaces where child pointers would go between the key-value
/// pairs. For example, in a node with length 2, there would be 3 possible edge locations - one
/// to the left of the node, one between the two pairs, and one at the right of the node.
pub(super) struct Handle<Node, Type> {
    node: Node,
    idx: usize,
    _marker: PhantomData<Type>,
}

impl<Node: Copy, Type> Copy for Handle<Node, Type> {}
// We don't need the full generality of `#[derive(Clone)]`, as the only time `Node` will be
// `Clone`able is when it is an immutable reference and therefore `Copy`.
impl<Node: Copy, Type> Clone for Handle<Node, Type> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Node, Type> Handle<Node, Type> {
    /// Retrieves the node that contains the edge or key-value pair this handle points to.
    pub(super) fn into_node(self) -> Node {
        self.node
    }

    /// Returns the position of this handle in the node.
    pub(super) fn idx(&self) -> usize {
        self.idx
    }
}

impl<BorrowType, K, V, NodeType> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV> {
    /// Creates a new handle to a key-value pair in `node`.
    /// Unsafe because the caller must ensure that `idx < node.len()`.
    pub(super) unsafe fn new_kv(node: NodeRef<BorrowType, K, V, NodeType>, idx: usize) -> Self {
        debug_assert!(idx < node.len());

        Handle { node, idx, _marker: PhantomData }
    }

    pub(super) fn left_edge(self) -> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
        unsafe { Handle::new_edge(self.node, self.idx) }
    }

    pub(super) fn right_edge(self) -> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
        unsafe { Handle::new_edge(self.node, self.idx + 1) }
    }
}

impl<BorrowType, K, V, NodeType, HandleType> PartialEq
    for Handle<NodeRef<BorrowType, K, V, NodeType>, HandleType>
{
    fn eq(&self, other: &Self) -> bool {
        let Self { node, idx, _marker } = self;
        node.eq(&other.node) && *idx == other.idx
    }
}

impl<BorrowType, K, V, NodeType, HandleType>
    Handle<NodeRef<BorrowType, K, V, NodeType>, HandleType>
{
    /// Temporarily takes out another immutable handle on the same location.
    pub(super) fn reborrow(
        &self,
    ) -> Handle<NodeRef<marker::Immut<'_>, K, V, NodeType>, HandleType> {
        // We can't use Handle::new_kv or Handle::new_edge because we don't know our type
        Handle { node: self.node.reborrow(), idx: self.idx, _marker: PhantomData }
    }
}

impl<'a, K, V, NodeType, HandleType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, HandleType> {
    /// Temporarily takes out another mutable handle on the same location. Beware, as
    /// this method is very dangerous, doubly so since it might not immediately appear
    /// dangerous.
    ///
    /// For details, see `NodeRef::reborrow_mut`.
    pub(super) unsafe fn reborrow_mut(
        &mut self,
    ) -> Handle<NodeRef<marker::Mut<'_>, K, V, NodeType>, HandleType> {
        // We can't use Handle::new_kv or Handle::new_edge because we don't know our type
        Handle { node: unsafe { self.node.reborrow_mut() }, idx: self.idx, _marker: PhantomData }
    }

    /// Returns a dormant copy of this handle which can be reawakened later.
    ///
    /// See `DormantMutRef` for more details.
    pub(super) fn dormant(
        &self,
    ) -> Handle<NodeRef<marker::DormantMut, K, V, NodeType>, HandleType> {
        Handle { node: self.node.dormant(), idx: self.idx, _marker: PhantomData }
    }
}

impl<K, V, NodeType, HandleType> Handle<NodeRef<marker::DormantMut, K, V, NodeType>, HandleType> {
    /// Revert to the unique borrow initially captured.
    ///
    /// # Safety
    ///
    /// The reborrow must have ended, i.e., the reference returned by `new` and
    /// all pointers and references derived from it, must not be used anymore.
    pub(super) unsafe fn awaken<'a>(
        self,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, HandleType> {
        Handle { node: unsafe { self.node.awaken() }, idx: self.idx, _marker: PhantomData }
    }
}

impl<BorrowType, K, V, NodeType> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
    /// Creates a new handle to an edge in `node`.
    /// Unsafe because the caller must ensure that `idx <= node.len()`.
    pub(super) unsafe fn new_edge(node: NodeRef<BorrowType, K, V, NodeType>, idx: usize) -> Self {
        debug_assert!(idx <= node.len());

        Handle { node, idx, _marker: PhantomData }
    }

    pub(super) fn left_kv(
        self,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV>, Self> {
        if self.idx > 0 {
            Ok(unsafe { Handle::new_kv(self.node, self.idx - 1) })
        } else {
            Err(self)
        }
    }

    pub(super) fn right_kv(
        self,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV>, Self> {
        if self.idx < self.node.len() {
            Ok(unsafe { Handle::new_kv(self.node, self.idx) })
        } else {
            Err(self)
        }
    }
}

pub(super) enum LeftOrRight<T> {
    Left(T),
    Right(T),
}

/// Given an edge index where we want to insert into a node filled to capacity,
/// computes a sensible KV index of a split point and where to perform the insertion.
/// The goal of the split point is for its key and value to end up in a parent node;
/// the keys, values and edges to the left of the split point become the left child;
/// the keys, values and edges to the right of the split point become the right child.
fn splitpoint(edge_idx: usize) -> (usize, LeftOrRight<usize>) {
    debug_assert!(edge_idx <= CAPACITY);
    // Rust issue #74834 tries to explain these symmetric rules.
    match edge_idx {
        0..EDGE_IDX_LEFT_OF_CENTER => (KV_IDX_CENTER - 1, LeftOrRight::Left(edge_idx)),
        EDGE_IDX_LEFT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Left(edge_idx)),
        EDGE_IDX_RIGHT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Right(0)),
        _ => (KV_IDX_CENTER + 1, LeftOrRight::Right(edge_idx - (KV_IDX_CENTER + 1 + 1))),
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    /// Inserts a new key-value pair between the key-value pairs to the right and left of
    /// this edge. This method assumes that there is enough space in the node for the new
    /// pair to fit.
    unsafe fn insert_fit(
        mut self,
        key: K,
        val: V,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV> {
        debug_assert!(self.node.len() < CAPACITY);
        let new_len = self.node.len() + 1;

        unsafe {
            slice_insert(self.node.key_area_mut(..new_len), self.idx, key);
            slice_insert(self.node.val_area_mut(..new_len), self.idx, val);
            *self.node.len_mut() = new_len as u16;

            Handle::new_kv(self.node, self.idx)
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    /// Inserts a new key-value pair between the key-value pairs to the right and left of
    /// this edge. This method splits the node if there isn't enough room.
    ///
    /// Returns a dormant handle to the inserted node which can be reawakened
    /// once splitting is complete.
    fn insert<A: Allocator + Clone>(
        self,
        key: K,
        val: V,
        alloc: A,
    ) -> (
        Option<SplitResult<'a, K, V, marker::Leaf>>,
        Handle<NodeRef<marker::DormantMut, K, V, marker::Leaf>, marker::KV>,
    ) {
        if self.node.len() < CAPACITY {
            // SAFETY: There is enough space in the node for insertion.
            let handle = unsafe { self.insert_fit(key, val) };
            (None, handle.dormant())
        } else {
            let (middle_kv_idx, insertion) = splitpoint(self.idx);
            let middle = unsafe { Handle::new_kv(self.node, middle_kv_idx) };
            let mut result = middle.split(alloc);
            let insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    Handle::new_edge(result.left.reborrow_mut(), insert_idx)
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    Handle::new_edge(result.right.borrow_mut(), insert_idx)
                },
            };
            // SAFETY: We just split the node, so there is enough space for
            // insertion.
            let handle = unsafe { insertion_edge.insert_fit(key, val).dormant() };
            (Some(result), handle)
        }
    }
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    /// Fixes the parent pointer and index in the child node that this edge
    /// links to. This is useful when the ordering of edges has been changed,
    fn correct_parent_link(self) {
        // Create backpointer without invalidating other references to the node.
        let ptr = unsafe { NonNull::new_unchecked(NodeRef::as_internal_ptr(&self.node)) };
        let idx = self.idx;
        let mut child = self.descend();
        child.set_parent_link(ptr, idx);
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    /// Inserts a new key-value pair and an edge that will go to the right of that new pair
    /// between this edge and the key-value pair to the right of this edge. This method assumes
    /// that there is enough space in the node for the new pair to fit.
    fn insert_fit(&mut self, key: K, val: V, edge: Root<K, V>) {
        debug_assert!(self.node.len() < CAPACITY);
        debug_assert!(edge.height == self.node.height - 1);
        let new_len = self.node.len() + 1;

        unsafe {
            slice_insert(self.node.key_area_mut(..new_len), self.idx, key);
            slice_insert(self.node.val_area_mut(..new_len), self.idx, val);
            slice_insert(self.node.edge_area_mut(..new_len + 1), self.idx + 1, edge.node);
            *self.node.len_mut() = new_len as u16;

            self.node.correct_childrens_parent_links(self.idx + 1..new_len + 1);
        }
    }

    /// Inserts a new key-value pair and an edge that will go to the right of that new pair
    /// between this edge and the key-value pair to the right of this edge. This method splits
    /// the node if there isn't enough room.
    fn insert<A: Allocator + Clone>(
        mut self,
        key: K,
        val: V,
        edge: Root<K, V>,
        alloc: A,
    ) -> Option<SplitResult<'a, K, V, marker::Internal>> {
        assert!(edge.height == self.node.height - 1);

        if self.node.len() < CAPACITY {
            self.insert_fit(key, val, edge);
            None
        } else {
            let (middle_kv_idx, insertion) = splitpoint(self.idx);
            let middle = unsafe { Handle::new_kv(self.node, middle_kv_idx) };
            let mut result = middle.split(alloc);
            let mut insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    Handle::new_edge(result.left.reborrow_mut(), insert_idx)
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    Handle::new_edge(result.right.borrow_mut(), insert_idx)
                },
            };
            insertion_edge.insert_fit(key, val, edge);
            Some(result)
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    /// Inserts a new key-value pair between the key-value pairs to the right and left of
    /// this edge. This method splits the node if there isn't enough room, and tries to
    /// insert the split off portion into the parent node recursively, until the root is reached.
    ///
    /// If the returned result is some `SplitResult`, the `left` field will be the root node.
    /// The returned pointer points to the inserted value, which in the case of `SplitResult`
    /// is in the `left` or `right` tree.
    pub(super) fn insert_recursing<A: Allocator + Clone>(
        self,
        key: K,
        value: V,
        alloc: A,
        split_root: impl FnOnce(SplitResult<'a, K, V, marker::LeafOrInternal>),
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV> {
        let (mut split, handle) = match self.insert(key, value, alloc.clone()) {
            // SAFETY: we have finished splitting and can now re-awaken the
            // handle to the inserted element.
            (None, handle) => return unsafe { handle.awaken() },
            (Some(split), handle) => (split.forget_node_type(), handle),
        };

        loop {
            split = match split.left.ascend() {
                Ok(parent) => {
                    match parent.insert(split.kv.0, split.kv.1, split.right, alloc.clone()) {
                        // SAFETY: we have finished splitting and can now re-awaken the
                        // handle to the inserted element.
                        None => return unsafe { handle.awaken() },
                        Some(split) => split.forget_node_type(),
                    }
                }
                Err(root) => {
                    split_root(SplitResult { left: root, ..split });
                    // SAFETY: we have finished splitting and can now re-awaken the
                    // handle to the inserted element.
                    return unsafe { handle.awaken() };
                }
            };
        }
    }
}

impl<BorrowType: marker::BorrowType, K, V>
    Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge>
{
    /// Finds the node pointed to by this edge.
    ///
    /// The method name assumes you picture trees with the root node on top.
    ///
    /// `edge.descend().ascend().unwrap()` and `node.ascend().unwrap().descend()` should
    /// both, upon success, do nothing.
    pub(super) fn descend(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
        const {
            assert!(BorrowType::TRAVERSAL_PERMIT);
        }

        // We need to use raw pointers to nodes because, if BorrowType is
        // marker::ValMut, there might be outstanding mutable references to
        // values that we must not invalidate. There's no worry accessing the
        // height field because that value is copied. Beware that, once the
        // node pointer is dereferenced, we access the edges array with a
        // reference (Rust issue #73987) and invalidate any other references
        // to or inside the array, should any be around.
        let parent_ptr = NodeRef::as_internal_ptr(&self.node);
        let node = unsafe { (*parent_ptr).edges.get_unchecked(self.idx).assume_init_read() };
        NodeRef { node, height: self.node.height - 1, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Immut<'a>, K, V, NodeType>, marker::KV> {
    pub(super) fn into_kv(self) -> (&'a K, &'a V) {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf();
        let k = unsafe { leaf.keys.get_unchecked(self.idx).assume_init_ref() };
        let v = unsafe { leaf.vals.get_unchecked(self.idx).assume_init_ref() };
        (k, v)
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    pub(super) fn key_mut(&mut self) -> &mut K {
        unsafe { self.node.key_area_mut(self.idx).assume_init_mut() }
    }

    pub(super) fn into_val_mut(self) -> &'a mut V {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf_mut();
        unsafe { leaf.vals.get_unchecked_mut(self.idx).assume_init_mut() }
    }

    pub(super) fn into_kv_mut(self) -> (&'a mut K, &'a mut V) {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf_mut();
        let k = unsafe { leaf.keys.get_unchecked_mut(self.idx).assume_init_mut() };
        let v = unsafe { leaf.vals.get_unchecked_mut(self.idx).assume_init_mut() };
        (k, v)
    }
}

impl<'a, K, V, NodeType> Handle<NodeRef<marker::ValMut<'a>, K, V, NodeType>, marker::KV> {
    pub(super) fn into_kv_valmut(self) -> (&'a K, &'a mut V) {
        unsafe { self.node.into_key_val_mut_at(self.idx) }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    pub(super) fn kv_mut(&mut self) -> (&mut K, &mut V) {
        debug_assert!(self.idx < self.node.len());
        // We cannot call separate key and value methods, because calling the second one
        // invalidates the reference returned by the first.
        unsafe {
            let leaf = self.node.as_leaf_mut();
            let key = leaf.keys.get_unchecked_mut(self.idx).assume_init_mut();
            let val = leaf.vals.get_unchecked_mut(self.idx).assume_init_mut();
            (key, val)
        }
    }

    /// Replaces the key and value that the KV handle refers to.
    pub(super) fn replace_kv(&mut self, k: K, v: V) -> (K, V) {
        let (key, val) = self.kv_mut();
        (mem::replace(key, k), mem::replace(val, v))
    }
}

impl<K, V, NodeType> Handle<NodeRef<marker::Dying, K, V, NodeType>, marker::KV> {
    /// Extracts the key and value that the KV handle refers to.
    /// # Safety
    /// The node that the handle refers to must not yet have been deallocated.
    pub(super) unsafe fn into_key_val(mut self) -> (K, V) {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.as_leaf_dying();
        unsafe {
            let key = leaf.keys.get_unchecked_mut(self.idx).assume_init_read();
            let val = leaf.vals.get_unchecked_mut(self.idx).assume_init_read();
            (key, val)
        }
    }

    /// Drops the key and value that the KV handle refers to.
    /// # Safety
    /// The node that the handle refers to must not yet have been deallocated.
    #[inline]
    pub(super) unsafe fn drop_key_val(mut self) {
        // Run the destructor of the value even if the destructor of the key panics.
        struct Dropper<'a, T>(&'a mut MaybeUninit<T>);
        impl<T> Drop for Dropper<'_, T> {
            #[inline]
            fn drop(&mut self) {
                unsafe {
                    self.0.assume_init_drop();
                }
            }
        }

        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.as_leaf_dying();
        unsafe {
            let key = leaf.keys.get_unchecked_mut(self.idx);
            let val = leaf.vals.get_unchecked_mut(self.idx);
            let _guard = Dropper(val);
            key.assume_init_drop();
            // dropping the guard will drop the value
        }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    /// Helps implementations of `split` for a particular `NodeType`,
    /// by taking care of leaf data.
    fn split_leaf_data(&mut self, new_node: &mut LeafNode<K, V>) -> (K, V) {
        debug_assert!(self.idx < self.node.len());
        let old_len = self.node.len();
        let new_len = old_len - self.idx - 1;
        new_node.len = new_len as u16;
        unsafe {
            let k = self.node.key_area_mut(self.idx).assume_init_read();
            let v = self.node.val_area_mut(self.idx).assume_init_read();

            move_to_slice(
                self.node.key_area_mut(self.idx + 1..old_len),
                &mut new_node.keys[..new_len],
            );
            move_to_slice(
                self.node.val_area_mut(self.idx + 1..old_len),
                &mut new_node.vals[..new_len],
            );

            *self.node.len_mut() = self.idx as u16;
            (k, v)
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV> {
    /// Splits the underlying node into three parts:
    ///
    /// - The node is truncated to only contain the key-value pairs to the left of
    ///   this handle.
    /// - The key and value pointed to by this handle are extracted.
    /// - All the key-value pairs to the right of this handle are put into a newly
    ///   allocated node.
    pub(super) fn split<A: Allocator + Clone>(
        mut self,
        alloc: A,
    ) -> SplitResult<'a, K, V, marker::Leaf> {
        let mut new_node = LeafNode::new(alloc);

        let kv = self.split_leaf_data(&mut new_node);

        let right = NodeRef::from_new_leaf(new_node);
        SplitResult { left: self.node, kv, right }
    }

    /// Removes the key-value pair pointed to by this handle and returns it, along with the edge
    /// that the key-value pair collapsed into.
    pub(super) fn remove(
        mut self,
    ) -> ((K, V), Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge>) {
        let old_len = self.node.len();
        unsafe {
            let k = slice_remove(self.node.key_area_mut(..old_len), self.idx);
            let v = slice_remove(self.node.val_area_mut(..old_len), self.idx);
            *self.node.len_mut() = (old_len - 1) as u16;
            ((k, v), self.left_edge())
        }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV> {
    /// Splits the underlying node into three parts:
    ///
    /// - The node is truncated to only contain the edges and key-value pairs to the
    ///   left of this handle.
    /// - The key and value pointed to by this handle are extracted.
    /// - All the edges and key-value pairs to the right of this handle are put into
    ///   a newly allocated node.
    pub(super) fn split<A: Allocator + Clone>(
        mut self,
        alloc: A,
    ) -> SplitResult<'a, K, V, marker::Internal> {
        let old_len = self.node.len();
        unsafe {
            let mut new_node = InternalNode::new(alloc);
            let kv = self.split_leaf_data(&mut new_node.data);
            let new_len = usize::from(new_node.data.len);
            move_to_slice(
                self.node.edge_area_mut(self.idx + 1..old_len + 1),
                &mut new_node.edges[..new_len + 1],
            );

            // SAFETY: self is `marker::Internal`, so `self.node.height` is positive
            let height = NonZero::new_unchecked(self.node.height);
            let right = NodeRef::from_new_internal(new_node, height);

            SplitResult { left: self.node, kv, right }
        }
    }
}

/// Represents a session for evaluating and performing a balancing operation
/// around an internal key-value pair.
pub(super) struct BalancingContext<'a, K, V> {
    parent: Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV>,
    left_child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    right_child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV> {
    pub(super) fn consider_for_balancing(self) -> BalancingContext<'a, K, V> {
        let self1 = unsafe { ptr::read(&self) };
        let self2 = unsafe { ptr::read(&self) };
        BalancingContext {
            parent: self,
            left_child: self1.left_edge().descend(),
            right_child: self2.right_edge().descend(),
        }
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    /// Chooses a balancing context involving the node as a child, thus between
    /// the KV immediately to the left or to the right in the parent node.
    /// Returns an `Err` if there is no parent.
    /// Panics if the parent is empty.
    ///
    /// Prefers the left side, to be optimal if the given node is somehow
    /// underfull, meaning here only that it has fewer elements than its left
    /// sibling and than its right sibling, if they exist. In that case,
    /// merging with the left sibling is faster, since we only need to move
    /// the node's N elements, instead of shifting them to the right and moving
    /// more than N elements in front. Stealing from the left sibling is also
    /// typically faster, since we only need to shift the node's N elements to
    /// the right, instead of shifting at least N of the sibling's elements to
    /// the left.
    pub(super) fn choose_parent_kv(self) -> Result<LeftOrRight<BalancingContext<'a, K, V>>, Self> {
        match unsafe { ptr::read(&self) }.ascend() {
            Ok(parent_edge) => match parent_edge.left_kv() {
                Ok(left_parent_kv) => Ok(LeftOrRight::Left(BalancingContext {
                    parent: unsafe { ptr::read(&left_parent_kv) },
                    left_child: left_parent_kv.left_edge().descend(),
                    right_child: self,
                })),
                Err(parent_edge) => match parent_edge.right_kv() {
                    Ok(right_parent_kv) => Ok(LeftOrRight::Right(BalancingContext {
                        parent: unsafe { ptr::read(&right_parent_kv) },
                        left_child: self,
                        right_child: right_parent_kv.right_edge().descend(),
                    })),
                    Err(_) => unreachable!("empty internal node"),
                },
            },
            Err(root) => Err(root),
        }
    }
}

impl<'a, K, V> BalancingContext<'a, K, V> {
    pub(super) fn left_child_len(&self) -> usize {
        self.left_child.len()
    }

    pub(super) fn right_child_len(&self) -> usize {
        self.right_child.len()
    }

    pub(super) fn into_left_child(self) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.left_child
    }

    pub(super) fn into_right_child(self) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.right_child
    }

    /// Returns whether merging is possible, i.e., whether there is enough room
    /// in a node to combine the central KV with both adjacent child nodes.
    pub(super) fn can_merge(&self) -> bool {
        self.left_child.len() + 1 + self.right_child.len() <= CAPACITY
    }
}

impl<'a, K: 'a, V: 'a> BalancingContext<'a, K, V> {
    /// Performs a merge and lets a closure decide what to return.
    fn do_merge<
        F: FnOnce(
            NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
            NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
        ) -> R,
        R,
        A: Allocator,
    >(
        self,
        result: F,
        alloc: A,
    ) -> R {
        let Handle { node: mut parent_node, idx: parent_idx, _marker } = self.parent;
        let old_parent_len = parent_node.len();
        let mut left_node = self.left_child;
        let old_left_len = left_node.len();
        let mut right_node = self.right_child;
        let right_len = right_node.len();
        let new_left_len = old_left_len + 1 + right_len;

        assert!(new_left_len <= CAPACITY);

        unsafe {
            *left_node.len_mut() = new_left_len as u16;

            let parent_key = slice_remove(parent_node.key_area_mut(..old_parent_len), parent_idx);
            left_node.key_area_mut(old_left_len).write(parent_key);
            move_to_slice(
                right_node.key_area_mut(..right_len),
                left_node.key_area_mut(old_left_len + 1..new_left_len),
            );

            let parent_val = slice_remove(parent_node.val_area_mut(..old_parent_len), parent_idx);
            left_node.val_area_mut(old_left_len).write(parent_val);
            move_to_slice(
                right_node.val_area_mut(..right_len),
                left_node.val_area_mut(old_left_len + 1..new_left_len),
            );

            slice_remove(&mut parent_node.edge_area_mut(..old_parent_len + 1), parent_idx + 1);
            parent_node.correct_childrens_parent_links(parent_idx + 1..old_parent_len);
            *parent_node.len_mut() -= 1;

            if parent_node.height > 1 {
                // SAFETY: the height of the nodes being merged is one below the height
                // of the node of this edge, thus above zero, so they are internal.
                let mut left_node = left_node.reborrow_mut().cast_to_internal_unchecked();
                let mut right_node = right_node.cast_to_internal_unchecked();
                move_to_slice(
                    right_node.edge_area_mut(..right_len + 1),
                    left_node.edge_area_mut(old_left_len + 1..new_left_len + 1),
                );

                left_node.correct_childrens_parent_links(old_left_len + 1..new_left_len + 1);

                alloc.deallocate(right_node.node.cast(), Layout::new::<InternalNode<K, V>>());
            } else {
                alloc.deallocate(right_node.node.cast(), Layout::new::<LeafNode<K, V>>());
            }
        }
        result(parent_node, left_node)
    }

    /// Merges the parent's key-value pair and both adjacent child nodes into
    /// the left child node and returns the shrunk parent node.
    ///
    /// Panics unless we `.can_merge()`.
    pub(super) fn merge_tracking_parent<A: Allocator + Clone>(
        self,
        alloc: A,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
        self.do_merge(|parent, _child| parent, alloc)
    }

    /// Merges the parent's key-value pair and both adjacent child nodes into
    /// the left child node and returns that child node.
    ///
    /// Panics unless we `.can_merge()`.
    pub(super) fn merge_tracking_child<A: Allocator + Clone>(
        self,
        alloc: A,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
        self.do_merge(|_parent, child| child, alloc)
    }

    /// Merges the parent's key-value pair and both adjacent child nodes into
    /// the left child node and returns the edge handle in that child node
    /// where the tracked child edge ended up,
    ///
    /// Panics unless we `.can_merge()`.
    pub(super) fn merge_tracking_child_edge<A: Allocator + Clone>(
        self,
        track_edge_idx: LeftOrRight<usize>,
        alloc: A,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        let old_left_len = self.left_child.len();
        let right_len = self.right_child.len();
        assert!(match track_edge_idx {
            LeftOrRight::Left(idx) => idx <= old_left_len,
            LeftOrRight::Right(idx) => idx <= right_len,
        });
        let child = self.merge_tracking_child(alloc);
        let new_idx = match track_edge_idx {
            LeftOrRight::Left(idx) => idx,
            LeftOrRight::Right(idx) => old_left_len + 1 + idx,
        };
        unsafe { Handle::new_edge(child, new_idx) }
    }

    /// Removes a key-value pair from the left child and places it in the key-value storage
    /// of the parent, while pushing the old parent key-value pair into the right child.
    /// Returns a handle to the edge in the right child corresponding to where the original
    /// edge specified by `track_right_edge_idx` ended up.
    pub(super) fn steal_left(
        mut self,
        track_right_edge_idx: usize,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        self.bulk_steal_left(1);
        unsafe { Handle::new_edge(self.right_child, 1 + track_right_edge_idx) }
    }

    /// Removes a key-value pair from the right child and places it in the key-value storage
    /// of the parent, while pushing the old parent key-value pair onto the left child.
    /// Returns a handle to the edge in the left child specified by `track_left_edge_idx`,
    /// which didn't move.
    pub(super) fn steal_right(
        mut self,
        track_left_edge_idx: usize,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
        self.bulk_steal_right(1);
        unsafe { Handle::new_edge(self.left_child, track_left_edge_idx) }
    }

    /// This does stealing similar to `steal_left` but steals multiple elements at once.
    pub(super) fn bulk_steal_left(&mut self, count: usize) {
        assert!(count > 0);
        unsafe {
            let left_node = &mut self.left_child;
            let old_left_len = left_node.len();
            let right_node = &mut self.right_child;
            let old_right_len = right_node.len();

            // Make sure that we may steal safely.
            assert!(old_right_len + count <= CAPACITY);
            assert!(old_left_len >= count);

            let new_left_len = old_left_len - count;
            let new_right_len = old_right_len + count;
            *left_node.len_mut() = new_left_len as u16;
            *right_node.len_mut() = new_right_len as u16;

            // Move leaf data.
            {
                // Make room for stolen elements in the right child.
                slice_shr(right_node.key_area_mut(..new_right_len), count);
                slice_shr(right_node.val_area_mut(..new_right_len), count);

                // Move elements from the left child to the right one.
                move_to_slice(
                    left_node.key_area_mut(new_left_len + 1..old_left_len),
                    right_node.key_area_mut(..count - 1),
                );
                move_to_slice(
                    left_node.val_area_mut(new_left_len + 1..old_left_len),
                    right_node.val_area_mut(..count - 1),
                );

                // Move the leftmost stolen pair to the parent.
                let k = left_node.key_area_mut(new_left_len).assume_init_read();
                let v = left_node.val_area_mut(new_left_len).assume_init_read();
                let (k, v) = self.parent.replace_kv(k, v);

                // Move parent's key-value pair to the right child.
                right_node.key_area_mut(count - 1).write(k);
                right_node.val_area_mut(count - 1).write(v);
            }

            match (left_node.reborrow_mut().force(), right_node.reborrow_mut().force()) {
                (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                    // Make room for stolen edges.
                    slice_shr(right.edge_area_mut(..new_right_len + 1), count);

                    // Steal edges.
                    move_to_slice(
                        left.edge_area_mut(new_left_len + 1..old_left_len + 1),
                        right.edge_area_mut(..count),
                    );

                    right.correct_childrens_parent_links(0..new_right_len + 1);
                }
                (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                _ => unreachable!(),
            }
        }
    }

    /// The symmetric clone of `bulk_steal_left`.
    pub(super) fn bulk_steal_right(&mut self, count: usize) {
        assert!(count > 0);
        unsafe {
            let left_node = &mut self.left_child;
            let old_left_len = left_node.len();
            let right_node = &mut self.right_child;
            let old_right_len = right_node.len();

            // Make sure that we may steal safely.
            assert!(old_left_len + count <= CAPACITY);
            assert!(old_right_len >= count);

            let new_left_len = old_left_len + count;
            let new_right_len = old_right_len - count;
            *left_node.len_mut() = new_left_len as u16;
            *right_node.len_mut() = new_right_len as u16;

            // Move leaf data.
            {
                // Move the rightmost stolen pair to the parent.
                let k = right_node.key_area_mut(count - 1).assume_init_read();
                let v = right_node.val_area_mut(count - 1).assume_init_read();
                let (k, v) = self.parent.replace_kv(k, v);

                // Move parent's key-value pair to the left child.
                left_node.key_area_mut(old_left_len).write(k);
                left_node.val_area_mut(old_left_len).write(v);

                // Move elements from the right child to the left one.
                move_to_slice(
                    right_node.key_area_mut(..count - 1),
                    left_node.key_area_mut(old_left_len + 1..new_left_len),
                );
                move_to_slice(
                    right_node.val_area_mut(..count - 1),
                    left_node.val_area_mut(old_left_len + 1..new_left_len),
                );

                // Fill gap where stolen elements used to be.
                slice_shl(right_node.key_area_mut(..old_right_len), count);
                slice_shl(right_node.val_area_mut(..old_right_len), count);
            }

            match (left_node.reborrow_mut().force(), right_node.reborrow_mut().force()) {
                (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                    // Steal edges.
                    move_to_slice(
                        right.edge_area_mut(..count),
                        left.edge_area_mut(old_left_len + 1..new_left_len + 1),
                    );

                    // Fill gap where stolen edges used to be.
                    slice_shl(right.edge_area_mut(..old_right_len + 1), count);

                    left.correct_childrens_parent_links(old_left_len + 1..new_left_len + 1);
                    right.correct_childrens_parent_links(0..new_right_len + 1);
                }
                (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                _ => unreachable!(),
            }
        }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge> {
    pub(super) fn forget_node_type(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::Edge> {
        unsafe { Handle::new_edge(self.node.forget_type(), self.idx) }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge> {
    pub(super) fn forget_node_type(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::Edge> {
        unsafe { Handle::new_edge(self.node.forget_type(), self.idx) }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::KV> {
    pub(super) fn forget_node_type(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::KV> {
        unsafe { Handle::new_kv(self.node.forget_type(), self.idx) }
    }
}

impl<BorrowType, K, V, Type> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, Type> {
    /// Checks whether the underlying node is an `Internal` node or a `Leaf` node.
    pub(super) fn force(
        self,
    ) -> ForceResult<
        Handle<NodeRef<BorrowType, K, V, marker::Leaf>, Type>,
        Handle<NodeRef<BorrowType, K, V, marker::Internal>, Type>,
    > {
        match self.node.force() {
            ForceResult::Leaf(node) => {
                ForceResult::Leaf(Handle { node, idx: self.idx, _marker: PhantomData })
            }
            ForceResult::Internal(node) => {
                ForceResult::Internal(Handle { node, idx: self.idx, _marker: PhantomData })
            }
        }
    }
}

impl<'a, K, V, Type> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, Type> {
    /// Unsafely asserts to the compiler the static information that the handle's node is a `Leaf`.
    pub(super) unsafe fn cast_to_leaf_unchecked(
        self,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, Type> {
        let node = unsafe { self.node.cast_to_leaf_unchecked() };
        Handle { node, idx: self.idx, _marker: PhantomData }
    }
}

impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
    /// Move the suffix after `self` from one node to another one. `right` must be empty.
    /// The first edge of `right` remains unchanged.
    pub(super) fn move_suffix(
        &mut self,
        right: &mut NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    ) {
        unsafe {
            let new_left_len = self.idx;
            let mut left_node = self.reborrow_mut().into_node();
            let old_left_len = left_node.len();

            let new_right_len = old_left_len - new_left_len;
            let mut right_node = right.reborrow_mut();

            assert!(right_node.len() == 0);
            assert!(left_node.height == right_node.height);

            if new_right_len > 0 {
                *left_node.len_mut() = new_left_len as u16;
                *right_node.len_mut() = new_right_len as u16;

                move_to_slice(
                    left_node.key_area_mut(new_left_len..old_left_len),
                    right_node.key_area_mut(..new_right_len),
                );
                move_to_slice(
                    left_node.val_area_mut(new_left_len..old_left_len),
                    right_node.val_area_mut(..new_right_len),
                );
                match (left_node.force(), right_node.force()) {
                    (ForceResult::Internal(mut left), ForceResult::Internal(mut right)) => {
                        move_to_slice(
                            left.edge_area_mut(new_left_len + 1..old_left_len + 1),
                            right.edge_area_mut(1..new_right_len + 1),
                        );
                        right.correct_childrens_parent_links(1..new_right_len + 1);
                    }
                    (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                    _ => unreachable!(),
                }
            }
        }
    }
}

pub(super) enum ForceResult<Leaf, Internal> {
    Leaf(Leaf),
    Internal(Internal),
}

/// Result of insertion, when a node needed to expand beyond its capacity.
pub(super) struct SplitResult<'a, K, V, NodeType> {
    // Altered node in existing tree with elements and edges that belong to the left of `kv`.
    pub left: NodeRef<marker::Mut<'a>, K, V, NodeType>,
    // Some key and value that existed before and were split off, to be inserted elsewhere.
    pub kv: (K, V),
    // Owned, unattached, new node with elements and edges that belong to the right of `kv`.
    pub right: NodeRef<marker::Owned, K, V, NodeType>,
}

impl<'a, K, V> SplitResult<'a, K, V, marker::Leaf> {
    pub(super) fn forget_node_type(self) -> SplitResult<'a, K, V, marker::LeafOrInternal> {
        SplitResult { left: self.left.forget_type(), kv: self.kv, right: self.right.forget_type() }
    }
}

impl<'a, K, V> SplitResult<'a, K, V, marker::Internal> {
    pub(super) fn forget_node_type(self) -> SplitResult<'a, K, V, marker::LeafOrInternal> {
        SplitResult { left: self.left.forget_type(), kv: self.kv, right: self.right.forget_type() }
    }
}

pub(super) mod marker {
    use core::marker::PhantomData;

    pub(crate) enum Leaf {}
    pub(crate) enum Internal {}
    pub(crate) enum LeafOrInternal {}

    pub(crate) enum Owned {}
    pub(crate) enum Dying {}
    pub(crate) enum DormantMut {}
    pub(crate) struct Immut<'a>(PhantomData<&'a ()>);
    pub(crate) struct Mut<'a>(PhantomData<&'a mut ()>);
    pub(crate) struct ValMut<'a>(PhantomData<&'a mut ()>);

    pub(crate) trait BorrowType {
        /// If node references of this borrow type allow traversing to other
        /// nodes in the tree, this constant is set to `true`. It can be used
        /// for a compile-time assertion.
        const TRAVERSAL_PERMIT: bool = true;
    }
    impl BorrowType for Owned {
        /// Reject traversal, because it isn't needed. Instead traversal
        /// happens using the result of `borrow_mut`.
        /// By disabling traversal, and only creating new references to roots,
        /// we know that every reference of the `Owned` type is to a root node.
        const TRAVERSAL_PERMIT: bool = false;
    }
    impl BorrowType for Dying {}
    impl<'a> BorrowType for Immut<'a> {}
    impl<'a> BorrowType for Mut<'a> {}
    impl<'a> BorrowType for ValMut<'a> {}
    impl BorrowType for DormantMut {}

    pub(crate) enum KV {}
    pub(crate) enum Edge {}
}

/// Inserts a value into a slice of initialized elements followed by one uninitialized element.
///
/// # Safety
/// The slice has more than `idx` elements.
unsafe fn slice_insert<T>(slice: &mut [MaybeUninit<T>], idx: usize, val: T) {
    unsafe {
        let len = slice.len();
        debug_assert!(len > idx);
        let slice_ptr = slice.as_mut_ptr();
        if len > idx + 1 {
            ptr::copy(slice_ptr.add(idx), slice_ptr.add(idx + 1), len - idx - 1);
        }
        (*slice_ptr.add(idx)).write(val);
    }
}

/// Removes and returns a value from a slice of all initialized elements, leaving behind one
/// trailing uninitialized element.
///
/// # Safety
/// The slice has more than `idx` elements.
unsafe fn slice_remove<T>(slice: &mut [MaybeUninit<T>], idx: usize) -> T {
    unsafe {
        let len = slice.len();
        debug_assert!(idx < len);
        let slice_ptr = slice.as_mut_ptr();
        let ret = (*slice_ptr.add(idx)).assume_init_read();
        ptr::copy(slice_ptr.add(idx + 1), slice_ptr.add(idx), len - idx - 1);
        ret
    }
}

/// Shifts the elements in a slice `distance` positions to the left.
///
/// # Safety
/// The slice has at least `distance` elements.
unsafe fn slice_shl<T>(slice: &mut [MaybeUninit<T>], distance: usize) {
    unsafe {
        let slice_ptr = slice.as_mut_ptr();
        ptr::copy(slice_ptr.add(distance), slice_ptr, slice.len() - distance);
    }
}

/// Shifts the elements in a slice `distance` positions to the right.
///
/// # Safety
/// The slice has at least `distance` elements.
unsafe fn slice_shr<T>(slice: &mut [MaybeUninit<T>], distance: usize) {
    unsafe {
        let slice_ptr = slice.as_mut_ptr();
        ptr::copy(slice_ptr, slice_ptr.add(distance), slice.len() - distance);
    }
}

/// Moves all values from a slice of initialized elements to a slice
/// of uninitialized elements, leaving behind `src` as all uninitialized.
/// Works like `dst.copy_from_slice(src)` but does not require `T` to be `Copy`.
fn move_to_slice<T>(src: &mut [MaybeUninit<T>], dst: &mut [MaybeUninit<T>]) {
    assert!(src.len() == dst.len());
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
}

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    //! Bounded Kani PROBEs on a subset of `btree::node`'s internal helpers: either a
    //! symbolic-trip-count relink loop (`correct_childrens_parent_links` /
    //! `correct_all_childrens_parent_links`, and internal `insert_fit` via its ranged relink), or
    //! a symbolic-length `ptr::copy`/`move_to_slice` bulk shift with no source-level loop of its
    //! own (leaf `insert_fit`, leaf `Handle::remove`, and leaf-height `Handle::move_suffix`).
    //!
    //! **Honest scope: these are PROBEs, not CONTRACTs.** Each harness drives the real, unmodified
    //! function over a bounded fixture (`K = V = i32`, node lengths restricted to a small
    //! representative set such as `{0, 1, CAPACITY}` or `{0, 1, CAPACITY - 1}`) whose lengths,
    //! indices, and ranges are symbolic but whose populated key/value content is deterministic and
    //! position-derived (`(i, 1000 + i)`), not itself symbolic, so a misplaced write after a shift
    //! is observable. Each `#[kani::unwind(n)]` is set above the fixture's own maximum explicit
    //! loop trip count, not pinned equal to it. None of these harnesses claims to discharge
    //! Challenge #4's success criteria in general (arbitrary length, arbitrary height, or the full
    //! recursive insert/remove/balancing call graph) — they are complementary, bounded
    //! safety-and-functional-correctness probes on the specific helpers listed above. Replay-greens
    //! are defeated per harness: parent links are perturbed to a sentinel before the relink
    //! harnesses run; the content harnesses use position-derived values and out-of-range sentinel
    //! inserts so any misplaced write is observable.
    //!
    //! Construction recipe: `NodeRef::new_leaf(Global)` (Owned, empty) then
    //! `root.borrow_mut().push(k, v)` (safe, up to `CAPACITY` times) for leaves;
    //! `NodeRef::new_internal(child, Global)` plus `internal.borrow_mut().push(k, v, child)` for
    //! internal nodes. `Handle::new_kv` / `new_edge` are `pub(super) unsafe` and used directly
    //! in-crate with a chosen valid idx once a node is populated. Content and parent-link
    //! post-state reads go through already-verified-safe API paths (`into_kv`, `descend`/
    //! `ascend`); length checks use `NodeRef::len()`, the established-safe idiom for this
    //! readback, not a raw field read on a freshly-written node.

    use core::kani;

    use super::*;
    use crate::alloc::Global;

    const CAP: usize = CAPACITY; // 11 (B=6)

    /// Builds an Owned leaf `NodeRef` with `len` (0..=CAP) (k, v) = (i32, i32) pairs pushed via the
    /// safe `push` recipe; when `len > 0` the pushed keys/values are unconstrained symbolic i32
    /// (no ordering invariant is relied upon by any fn under test here). In THIS module, every
    /// call site passes `len == 0` — it is used only to build empty height-0 leaf children for
    /// `symbolic_internal`, so the symbolic-content code path (the `for` loop body) never actually
    /// executes with nonzero content anywhere in this harness set; the harnesses that need
    /// populated leaf content build it inline with deterministic, position-derived values instead.
    fn symbolic_leaf(len: usize) -> NodeRef<marker::Owned, i32, i32, marker::Leaf> {
        let mut root: NodeRef<marker::Owned, i32, i32, marker::Leaf> = NodeRef::new_leaf(Global);
        for _ in 0..len {
            let k: i32 = kani::any();
            let v: i32 = kani::any();
            root.borrow_mut().push(k, v);
        }
        root
    }

    /// Builds an Owned internal `NodeRef` with `len` (0..=CAP) symbolic i32 keys/values and
    /// `len + 1` height-0 empty-leaf children, correctly parent-linked by construction (each safe
    /// `push` call maintains its own child's parent link).
    fn symbolic_internal(len: usize) -> NodeRef<marker::Owned, i32, i32, marker::Internal> {
        let first_child = symbolic_leaf(0);
        let mut internal: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(first_child.forget_type(), Global);
        for i in 0..len {
            let child = symbolic_leaf(0);
            internal.borrow_mut().push(i as i32, 1000 + i as i32, child.forget_type());
        }
        internal
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: len in {0, 1, CAPACITY} (1/2/12 edges); every child is an empty (len-0)
    // height-0 leaf; all parent links are PERTURBED to a garbage-but-valid `NonNull` before the
    // call, so the post-call check is a genuine fix, not a replay of already-correct state; only
    // ONE symbolic child index (`check_i`) is read back per run. Proves: after
    // `correct_all_childrens_parent_links()`, the checked child's (parent ptr, parent_idx)
    // round-trips correctly via `ascend()`. Does NOT prove the property for ALL children
    // simultaneously in one run (no all-quantified assertion) — the covers below establish that
    // different runs reach check_i == 0, check_i > 0 (multi-iteration witness), and check_i ==
    // last edge of a maximal node.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_correct_all_childrens_parent_links_no_ub() {
        let len: usize = kani::any();
        kani::assume(len == 0 || len == 1 || len == CAP);

        let mut internal = symbolic_internal(len);
        let internal_addr = internal.reborrow().node.as_ptr() as usize;

        // Perturb every child's parent link to a garbage-but-valid (never dereferenced)
        // NonNull, so the fix below is genuine, not a no-op on already-correct state.
        let garbage = NonNull::<InternalNode<i32, i32>>::dangling();
        for i in 0..=len {
            let mut_ref = internal.borrow_mut();
            let edge = unsafe { Handle::new_edge(mut_ref, i) };
            let mut child = edge.descend();
            child.set_parent_link(garbage, 9999);
        }

        let check_i: usize = kani::any();
        kani::assume(check_i <= len);

        internal.borrow_mut().correct_all_childrens_parent_links();

        let mut_ref = internal.borrow_mut();
        let edge = unsafe { Handle::new_edge(mut_ref, check_i) };
        let descended = edge.descend();
        let ascended = descended.ascend();
        assert!(
            ascended.is_ok(),
            "correct_all_childrens_parent_links: child at check_i lost its parent link"
        );
        let parent_edge = ascended.ok().unwrap();
        assert_eq!(
            parent_edge.idx(),
            check_i,
            "correct_all_childrens_parent_links: wrong parent_idx"
        );
        let parent_addr = NodeRef::as_internal_ptr(&parent_edge.into_node()) as usize;
        assert_eq!(
            parent_addr, internal_addr,
            "correct_all_childrens_parent_links: wrong parent pointer"
        );

        kani::cover(check_i == 0, "checked edge 0 after the fix");
        kani::cover(
            check_i > 0 && len > 0,
            "checked an edge > 0 after the fix -- genuine multi-iteration loop witness",
        );
        kani::cover(
            check_i == len && len == CAP,
            "checked the LAST edge of a maximal (CAPACITY+1-edge) internal node",
        );
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: old_len in {0, 1, CAPACITY - 1} (leaf, must be < CAPACITY per
    // insert_fit's own debug_assert); idx symbolic in 0..=old_len (unconstrained within that
    // bound). Proves ONLY structural/metadata safety: new_len == old_len + 1 (read via
    // `NodeRef::len()`, the proven-safe raw-pointer path), and the returned KV handle's own idx
    // == the insertion idx. Does NOT check content placement or the shift itself — see
    // `check_leaf_insert_fit_content` for that, kept as a separate, strongly-asserting companion
    // harness below.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_leaf_insert_fit_no_ub() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP - 1);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let mut root: NodeRef<marker::Owned, i32, i32, marker::Leaf> = NodeRef::new_leaf(Global);
        for i in 0..old_len {
            root.borrow_mut().push(i as i32, 1000 + i as i32);
        }

        let node_mut = root.borrow_mut();
        let edge = unsafe { Handle::new_edge(node_mut, idx) };
        // SAFETY: old_len < CAPACITY (this harness's own kani::assume), matching insert_fit's
        // debug_assert precondition -- there is room for one more element.
        let kv_handle = unsafe { edge.insert_fit(9000_i32, 9500_i32) };
        let inserted_idx = kv_handle.idx();
        drop(kv_handle);

        let new_len = root.borrow_mut().len();
        assert_eq!(new_len, old_len + 1, "insert_fit: len did not grow by exactly 1");
        assert_eq!(inserted_idx, idx, "insert_fit: returned KV handle idx != insertion idx");

        kani::cover(idx < old_len, "insert_fit: interior insertion (shift branch)");
        kani::cover(idx == old_len, "insert_fit: append insertion (no-shift branch)");
    }

    /// Every post-state quantity `check_leaf_insert_fit_content` needs, computed once by a shared,
    /// byte-identical construction (fixture -> insert_fit call -> readback). `old_len` pushes are
    /// position-derived ((i, 1000 + i)) so a misplacement after the shift is observable; the
    /// inserted (key, val) is a sentinel pair (9000, 9500) chosen far outside the pushed content's
    /// range (the push loop runs `0..old_len`, so the max pushed key/val at
    /// old_len <= CAPACITY - 1 == 10 is (9, 1009), not (10, 1010)).
    struct LeafInsertFitResult {
        /// Readback at `idx` — must be the inserted sentinel.
        at_idx: (i32, i32),
        /// `Some(readback at 0)` when `idx > 0` — head untouched by the shift.
        head0: Option<(i32, i32)>,
        /// `Some(readback at idx + 1)` when `idx < old_len` — the element originally AT `idx`
        /// must now sit one position to the right (the shift's direct witness).
        shifted_from_idx: Option<(i32, i32)>,
        /// `Some(readback at old_len)` when `idx < old_len` (interior insert; on append, `idx ==
        /// old_len`, the original last element never moves) — the original LAST element must
        /// have shifted all the way to the new last position.
        shifted_last: Option<(i32, i32)>,
    }

    fn leaf_insert_fit_content_setup(old_len: usize, idx: usize) -> LeafInsertFitResult {
        let mut root: NodeRef<marker::Owned, i32, i32, marker::Leaf> = NodeRef::new_leaf(Global);
        for i in 0..old_len {
            root.borrow_mut().push(i as i32, 1000 + i as i32);
        }

        let node_mut = root.borrow_mut();
        let edge = unsafe { Handle::new_edge(node_mut, idx) };
        let kv_handle = unsafe { edge.insert_fit(9000_i32, 9500_i32) };
        drop(kv_handle);

        let at_idx = {
            let readback = unsafe { Handle::new_kv(root.reborrow(), idx) };
            let (k, v) = readback.into_kv();
            (*k, *v)
        };
        let head0 = if idx > 0 {
            let readback = unsafe { Handle::new_kv(root.reborrow(), 0) };
            let (k, v) = readback.into_kv();
            Some((*k, *v))
        } else {
            None
        };
        let shifted_from_idx = if idx < old_len {
            let readback = unsafe { Handle::new_kv(root.reborrow(), idx + 1) };
            let (k, v) = readback.into_kv();
            Some((*k, *v))
        } else {
            None
        };
        let shifted_last = if idx < old_len {
            let readback = unsafe { Handle::new_kv(root.reborrow(), old_len) };
            let (k, v) = readback.into_kv();
            Some((*k, *v))
        } else {
            None
        };

        LeafInsertFitResult { at_idx, head0, shifted_from_idx, shifted_last }
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: SEPARATE, functional-content companion to `check_leaf_insert_fit_no_ub`
    // (strong post-state content equalities isolated in their own harness). Same old_len/idx
    // domain. All 4 checks read back via fresh `Handle::new_kv(root.reborrow(), pos).into_kv()`
    // calls — the same proven-safe Immut-readback path used throughout this module, never a raw
    // new-node field read. Proves the shift-by-one moved the right elements to the right places
    // and left the head alone; does not prove it for every element simultaneously (spot-checks
    // only: idx, 0, idx + 1, old_len).
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_leaf_insert_fit_content() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP - 1);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let r = leaf_insert_fit_content_setup(old_len, idx);

        assert!(r.at_idx == (9000, 9500), "inserted sentinel not found at idx");
        if let Some(h0) = r.head0 {
            assert!(h0 == (0, 1000), "head (position 0) mutated by the shift");
        }
        if let Some(sfi) = r.shifted_from_idx {
            assert!(
                sfi == (idx as i32, 1000 + idx as i32),
                "element originally at idx did not shift to idx + 1"
            );
        }
        if let Some(sl) = r.shifted_last {
            assert!(
                sl == ((old_len - 1) as i32, 1000 + (old_len - 1) as i32),
                "original last element did not shift to the new last position"
            );
        }

        kani::cover(
            idx < old_len,
            "leaf insert_fit content: genuine interior shift verified end-to-end",
        );
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: old_len in {0, 1, CAPACITY - 1} (internal, must be < CAPACITY per
    // insert_fit's own debug_assert); idx symbolic in 0..=old_len. Fixture:
    // `symbolic_internal(old_len)` (already fully, correctly parent-linked). Proves ONLY
    // structural safety: new_len == old_len + 1, read via `NodeRef::len()` (proven-safe
    // raw-pointer path). Does NOT check content placement, the new edge's identity/link, or the
    // shift of existing edges — see `check_internal_insert_fit_content` for those, kept as a
    // separate, strongly-asserting companion harness below.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_internal_insert_fit_no_ub() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP - 1);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let mut internal = symbolic_internal(old_len);
        let new_child = symbolic_leaf(0);
        let new_edge_root: Root<i32, i32> = new_child.forget_type();

        let mut_ref = internal.borrow_mut();
        let mut handle = unsafe { Handle::new_edge(mut_ref, idx) };
        handle.insert_fit(9000_i32, 9500_i32, new_edge_root);
        drop(handle);

        let new_len = internal.borrow_mut().len();
        assert_eq!(new_len, old_len + 1, "internal insert_fit: len did not grow by exactly 1");

        kani::cover(idx < old_len, "internal insert_fit: interior insertion (shift branch)");
        kani::cover(idx == old_len, "internal insert_fit: append insertion (no-shift branch)");
    }

    /// Every post-state quantity `check_internal_insert_fit_content` needs, computed once.
    /// `old_len` KV pairs (position-derived, (i, 1000 + i)) and `old_len + 1` height-0 children,
    /// all already correctly parent-linked (via `symbolic_internal`); the inserted KV is the
    /// sentinel pair (9000, 9500); the inserted edge's child is a fresh, distinguishable (by
    /// pointer) empty leaf.
    struct InternalInsertFitResult {
        /// Readback at `idx` — must be the inserted sentinel.
        at_idx: (i32, i32),
        /// The new edge's child (at idx + 1, post-insert) is the EXACT child NodeRef we passed
        /// in (pointer-identity, not just "some" child).
        new_edge_child_addr_matches: bool,
        /// The new edge's (idx + 1) parent link round-trips (ascend -> idx == idx + 1, parent
        /// ptr == this internal node) — the direct witness that the ranged relink fixed the
        /// newly-inserted edge.
        new_edge_parent_link_ok: bool,
        /// `Some(...)` when `idx < old_len` (interior insert): the edge that was originally at
        /// `idx + 1` (now at `idx + 2`, since the new edge itself landed at `idx + 1` and
        /// `slice_insert` shifts everything from `idx + 1` rightward) ALSO has its parent link
        /// correctly updated (ascend -> idx == idx + 2) — a second-iteration witness that the
        /// ranged relink loop did more than fix just the one new edge.
        shifted_edge_parent_link_ok: Option<bool>,
    }

    fn internal_insert_fit_content_setup(old_len: usize, idx: usize) -> InternalInsertFitResult {
        let mut internal = symbolic_internal(old_len);
        let internal_addr = internal.reborrow().node.as_ptr() as usize;

        let new_child = symbolic_leaf(0);
        let new_child_addr = new_child.reborrow().node.as_ptr() as usize;
        let new_edge_root: Root<i32, i32> = new_child.forget_type();

        let mut_ref = internal.borrow_mut();
        let mut handle = unsafe { Handle::new_edge(mut_ref, idx) };
        handle.insert_fit(9000_i32, 9500_i32, new_edge_root);
        drop(handle);

        let at_idx = {
            let readback = unsafe { Handle::new_kv(internal.reborrow(), idx) };
            let (k, v) = readback.into_kv();
            (*k, *v)
        };

        let new_edge_child_addr_matches = {
            let mut_ref2 = internal.borrow_mut();
            let edge2 = unsafe { Handle::new_edge(mut_ref2, idx + 1) };
            let descended = edge2.descend();
            descended.reborrow().node.as_ptr() as usize == new_child_addr
        };

        let new_edge_parent_link_ok = {
            let mut_ref3 = internal.borrow_mut();
            let edge3 = unsafe { Handle::new_edge(mut_ref3, idx + 1) };
            let descended = edge3.descend();
            match descended.ascend() {
                Ok(parent_edge) => {
                    let idx_ok = parent_edge.idx() == idx + 1;
                    let addr_ok = NodeRef::as_internal_ptr(&parent_edge.into_node()) as usize
                        == internal_addr;
                    idx_ok && addr_ok
                }
                Err(_) => false,
            }
        };

        let shifted_edge_parent_link_ok = if idx < old_len {
            let mut_ref4 = internal.borrow_mut();
            let edge4 = unsafe { Handle::new_edge(mut_ref4, idx + 2) };
            let descended = edge4.descend();
            match descended.ascend() {
                Ok(parent_edge) => {
                    let idx_ok = parent_edge.idx() == idx + 2;
                    let addr_ok = NodeRef::as_internal_ptr(&parent_edge.into_node()) as usize
                        == internal_addr;
                    Some(idx_ok && addr_ok)
                }
                Err(_) => Some(false),
            }
        } else {
            None
        };

        InternalInsertFitResult {
            at_idx,
            new_edge_child_addr_matches,
            new_edge_parent_link_ok,
            shifted_edge_parent_link_ok,
        }
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: SEPARATE, functional-content companion to
    // `check_internal_insert_fit_no_ub`. Same old_len/idx domain. Proves the sentinel KV landed
    // at idx, the new edge's child landed at idx + 1 by POINTER IDENTITY, its parent link was
    // corrected, AND (on interior inserts) the immediately-following pre-existing edge's parent
    // link was ALSO corrected — a genuine multi-iteration witness for the ranged relink AS
    // CALLED FROM insert_fit (distinct from, and in addition to, the standalone full-range
    // coverage in `check_correct_all_childrens_parent_links_no_ub`). This harness descends three
    // times and ascends twice against a node that was just mutated by a 3-way shift plus a
    // ranged relink — the highest-risk pointer-aliasing shape in this file's fixture family.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_internal_insert_fit_content() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP - 1);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let r = internal_insert_fit_content_setup(old_len, idx);

        assert!(r.at_idx == (9000, 9500), "inserted sentinel KV not found at idx");
        assert!(r.new_edge_child_addr_matches, "new edge's child != the child we passed in");
        assert!(r.new_edge_parent_link_ok, "new edge's parent link not corrected");
        if let Some(ok) = r.shifted_edge_parent_link_ok {
            assert!(ok, "pre-existing edge just past the new one has a stale parent link");
        }

        kani::cover(
            idx < old_len,
            "internal insert_fit content: interior insertion, multi-edge relink witnessed",
        );
        kani::cover(
            idx == old_len,
            "internal insert_fit content: append insertion (single relink)",
        );
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: old_len in {1, CAPACITY} (leaf; remove's own implicit precondition is
    // old_len >= 1); idx symbolic in 0..old_len (unconstrained within that bound). Proves ONLY
    // structural/metadata safety: new_len == old_len - 1 (read via `NodeRef::len()`, the
    // proven-safe raw-pointer path), and the returned edge handle's own idx == the removal idx
    // (the edge the KV pair "collapsed into", per the fn's own doc comment). Does NOT check the
    // extracted (k, v) value or the shift itself — see `check_leaf_remove_content` for those,
    // kept as a separate, strongly-asserting companion harness below.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_leaf_remove_no_ub() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx < old_len);

        let mut root: NodeRef<marker::Owned, i32, i32, marker::Leaf> = NodeRef::new_leaf(Global);
        for i in 0..old_len {
            root.borrow_mut().push(i as i32, 1000 + i as i32);
        }

        let node_mut = root.borrow_mut();
        let kv_handle = unsafe { Handle::new_kv(node_mut, idx) };
        let (_removed, edge_handle) = kv_handle.remove();
        let returned_idx = edge_handle.idx();
        drop(edge_handle);

        let new_len = root.borrow_mut().len();
        assert_eq!(new_len, old_len - 1, "remove: len did not shrink by exactly 1");
        assert_eq!(returned_idx, idx, "remove: returned edge idx != removal idx");

        kani::cover(idx + 1 < old_len, "remove: interior removal (shift branch)");
        kani::cover(idx + 1 == old_len, "remove: tail removal (no-shift branch)");
        kani::cover(old_len == 1, "remove: last-element removal (leaf becomes empty)");
    }

    /// Every post-state quantity `check_leaf_remove_content` needs, computed once by a shared,
    /// byte-identical construction (fixture -> remove call -> readback). `old_len` pushes are
    /// position-derived ((i, 1000 + i)) so a misplacement after the shift-left is observable.
    struct LeafRemoveContentResult {
        /// The (k, v) `remove` returned -- must be the original element at `idx`.
        removed: (i32, i32),
        /// `Some(readback at 0)` when `idx > 0` -- head untouched by the shift.
        head0: Option<(i32, i32)>,
        /// `Some(readback at idx)` when `idx < new_len` (new_len = old_len - 1) -- the element
        /// originally at `idx + 1` must now sit at `idx` (the shift's direct witness).
        shifted_first: Option<(i32, i32)>,
        /// `Some(readback at new_len - 1)` when `idx < new_len` -- the original LAST element must
        /// have shifted all the way down to the new last position.
        shifted_last: Option<(i32, i32)>,
    }

    fn leaf_remove_content_setup(old_len: usize, idx: usize) -> LeafRemoveContentResult {
        let mut root: NodeRef<marker::Owned, i32, i32, marker::Leaf> = NodeRef::new_leaf(Global);
        for i in 0..old_len {
            root.borrow_mut().push(i as i32, 1000 + i as i32);
        }

        let node_mut = root.borrow_mut();
        let kv_handle = unsafe { Handle::new_kv(node_mut, idx) };
        let ((k, v), edge_handle) = kv_handle.remove();
        drop(edge_handle);

        let new_len = old_len - 1;

        let head0 = if idx > 0 {
            let readback = unsafe { Handle::new_kv(root.reborrow(), 0) };
            let (k2, v2) = readback.into_kv();
            Some((*k2, *v2))
        } else {
            None
        };
        let shifted_first = if idx < new_len {
            let readback = unsafe { Handle::new_kv(root.reborrow(), idx) };
            let (k2, v2) = readback.into_kv();
            Some((*k2, *v2))
        } else {
            None
        };
        let shifted_last = if idx < new_len {
            let readback = unsafe { Handle::new_kv(root.reborrow(), new_len - 1) };
            let (k2, v2) = readback.into_kv();
            Some((*k2, *v2))
        } else {
            None
        };

        LeafRemoveContentResult { removed: (k, v), head0, shifted_first, shifted_last }
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: SEPARATE, functional-content companion to `check_leaf_remove_no_ub`.
    // Same old_len/idx domain. All reads back via fresh `Handle::new_kv(root.reborrow(),
    // pos).into_kv()` calls -- the same proven-safe Immut-readback path used throughout this
    // module, never a raw new-node field read. Proves the extracted (k, v) matches what was at
    // idx, the head (position 0) is untouched when idx > 0, and the shift-left moved the right
    // elements to the right places (spot-checks at the shift's first and last landing positions
    // only); does not prove it for every element simultaneously.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_leaf_remove_content() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx < old_len);

        let r = leaf_remove_content_setup(old_len, idx);

        assert!(
            r.removed == (idx as i32, 1000 + idx as i32),
            "removed (k, v) != original (k, v) at idx"
        );
        if let Some(h0) = r.head0 {
            assert!(h0 == (0, 1000), "head (position 0) mutated by the shift");
        }
        if let Some(sf) = r.shifted_first {
            assert!(
                sf == ((idx + 1) as i32, 1000 + (idx + 1) as i32),
                "element originally at idx + 1 did not shift to idx"
            );
        }
        if let Some(sl) = r.shifted_last {
            assert!(
                sl == ((old_len - 1) as i32, 1000 + (old_len - 1) as i32),
                "original last element did not shift to the new last position"
            );
        }

        kani::cover(
            idx + 1 < old_len,
            "leaf remove content: genuine interior shift verified end-to-end",
        );
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: old_len in {0, 1, CAPACITY} (source leaf); idx symbolic in 0..=old_len
    // (the split point). Fixture: a populated source Leaf NodeRef (position-derived content, same
    // push recipe as every harness above) plus a FRESH, EMPTY sibling Leaf NodeRef of the same
    // height (0) -- `move_suffix`'s own asserted preconditions (`right_node.len() == 0`,
    // `left_node.height == right_node.height`) are met by construction, so no panic branch is
    // exercised. This harness asserts memory safety only (no post-state `len`/content equality —
    // that is a disclosed residual for this contribution, not shipped here). It drives the real,
    // unmodified `move_suffix` over the fixture above and covers three structurally distinct split
    // shapes: a genuine interior split, the no-op split (right stays empty), and the
    // everything-moves split (left becomes empty). This is the highest-risk harness in this file's
    // fixture family: a bounded-copy shape spanning two live leaf nodes instead of one, a
    // `forget_type`/`forget_node_type` type-erasure round-trip through `marker::LeafOrInternal`,
    // and a `&mut` passed across two separately-owned nodes.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_move_suffix_leaf_no_ub() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let mut left_root: NodeRef<marker::Owned, i32, i32, marker::Leaf> =
            NodeRef::new_leaf(Global);
        for i in 0..old_len {
            left_root.borrow_mut().push(i as i32, 1000 + i as i32);
        }
        let mut right_root: NodeRef<marker::Owned, i32, i32, marker::Leaf> =
            NodeRef::new_leaf(Global);

        let left_mut = left_root.borrow_mut();
        let edge = unsafe { Handle::new_edge(left_mut, idx) };
        let mut split_edge = edge.forget_node_type();

        let mut right_lofi: NodeRef<marker::Mut<'_>, i32, i32, marker::LeafOrInternal> =
            right_root.borrow_mut().forget_type();
        split_edge.move_suffix(&mut right_lofi);
        drop(split_edge);
        drop(right_lofi);

        // No post-state assertions here -- see the label comment above: this harness proves
        // memory safety of `move_suffix` itself; a functional length/content companion is not
        // part of this submission.

        kani::cover(
            idx > 0 && idx < old_len,
            "move_suffix: genuine interior split (both sides non-empty)",
        );
        kani::cover(idx == old_len, "move_suffix: no-op split (right stays empty)");
        kani::cover(
            idx == 0 && old_len > 0,
            "move_suffix: everything moves to the right (left becomes empty)",
        );
    }

    // ---------------------------------------------------------------------
    // PROBE — residual: len in {1, CAPACITY}; `lo..hi` is constructed so it is ALWAYS a valid
    // edge-index range per the fn's own safety contract ("every item returned by range is a
    // valid edge index"). Calls `correct_childrens_parent_links` DIRECTLY (not via the
    // `correct_all_...` wrapper) with this arbitrary sub-range, then reads back ONE symbolic
    // `check_i` edge via the same proven-safe `descend().ascend()` round-trip the full-range
    // harness above uses. Two branches, both asserted, both covered: `check_i` INSIDE `[lo, hi)`
    // must be genuinely relinked (`idx == check_i`, parent pointer == this node, via the
    // deref-free `as_internal_ptr` projection); `check_i` OUTSIDE `[lo, hi)` must be UNTOUCHED
    // (`idx` still reads back as the 9999 sentinel — proves the fn is genuinely range-SCOPED, not
    // a disguised full pass). The out-of-range branch never dereferences the dangling parent
    // pointer itself (only `Handle::idx()`, a plain field read, and — for the in-range branch
    // only — `NodeRef::as_internal_ptr`, a pointer cast with no deref). Does NOT assert the
    // property for every edge simultaneously (no all-quantified check) — the cover set below
    // witnesses both branches plus the empty-range and full-range-via-direct-call corners across
    // a genuine multi-edge node. It also covers a proper subrange that may start at 0 (not only a
    // strictly-interior sub-range), and a single in-range `check_i` check on a maximal-occupancy
    // node (`hi - lo` may be 1, so this does not by itself witness more than one relink iteration).
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_correct_childrens_parent_links_subrange_no_ub() {
        let len: usize = kani::any();
        kani::assume(len == 1 || len == CAP);

        let mut internal = symbolic_internal(len);
        let internal_addr = internal.reborrow().node.as_ptr() as usize;

        // Perturb every child's parent link to a garbage-but-valid (never dereferenced)
        // NonNull with a sentinel parent_idx no genuine relink could ever produce.
        let garbage = NonNull::<InternalNode<i32, i32>>::dangling();
        for i in 0..=len {
            let mut_ref = internal.borrow_mut();
            let edge = unsafe { Handle::new_edge(mut_ref, i) };
            let mut child = edge.descend();
            child.set_parent_link(garbage, 9999);
        }

        let lo: usize = kani::any();
        let hi: usize = kani::any();
        kani::assume(lo <= hi && hi <= len + 1);

        let check_i: usize = kani::any();
        kani::assume(check_i <= len);

        unsafe { internal.borrow_mut().correct_childrens_parent_links(lo..hi) };

        let mut_ref = internal.borrow_mut();
        let edge = unsafe { Handle::new_edge(mut_ref, check_i) };
        let descended = edge.descend();
        let ascended = descended.ascend();
        assert!(
            ascended.is_ok(),
            "correct_childrens_parent_links: child lost its parent link entirely"
        );
        let parent_edge = ascended.ok().unwrap();

        if check_i >= lo && check_i < hi {
            assert_eq!(
                parent_edge.idx(),
                check_i,
                "in-range child: wrong parent_idx after sub-range relink"
            );
            let parent_addr = NodeRef::as_internal_ptr(&parent_edge.into_node()) as usize;
            assert_eq!(
                parent_addr, internal_addr,
                "in-range child: wrong parent pointer after sub-range relink"
            );
        } else {
            assert_eq!(
                parent_edge.idx(),
                9999,
                "out-of-range child: parent link was touched but the sub-range should not have covered it"
            );
        }

        kani::cover(
            check_i >= lo && check_i < hi,
            "checked an edge INSIDE the sub-range (expect fixed)",
        );
        kani::cover(
            check_i < lo || check_i >= hi,
            "checked an edge OUTSIDE the sub-range (expect untouched)",
        );
        kani::cover(
            lo < hi && hi < len + 1,
            "a proper subrange not extending to the end (may start at 0)",
        );
        kani::cover(lo == hi, "empty range: zero-iteration call, nothing relinked");
        kani::cover(
            lo == 0 && hi == len + 1,
            "full range via DIRECT call (mirrors correct_all_... behavior)",
        );
        kani::cover(
            check_i >= lo && check_i < hi && len == CAP,
            "an in-range index is checked on a maximal-occupancy node",
        );
    }

    // =======================================================================
    // BALANCING-OPERATION TIER
    //
    // The helpers named in the challenge's second success-criteria list -- `NodeRef::new_internal`,
    // `BalancingContext::{do_merge, merge_tracking_child_edge, steal_left, steal_right,
    // bulk_steal_left, bulk_steal_right}` -- plus `Handle::split` and the functional-content
    // companions for `Handle::move_suffix`.
    //
    // These carry the same PROBE framing as the block above: bounded fixtures, `K = V = i32`, and
    // every residual named. Where a node's occupancy is left symbolic over `0..=CAPACITY`, note
    // that `CAPACITY` is a compile-time constant and a `LeafNode` stores
    // `[MaybeUninit<K>; CAPACITY]`, so that range is the node type's COMPLETE occupancy domain
    // rather than a harness-chosen bound; the bounds that ARE harness-chosen are called out
    // individually below.
    // =======================================================================
    /// Reads a `(key, value)` pair out of a mutable node by index. Both are `i32` (`Copy`), so
    /// nothing is moved out of the node and the node stays fully initialized.
    ///
    /// # Safety-relevant precondition
    /// `idx < node.len()` — every call site below guards on the node's length.
    fn kv_at(
        node: NodeRef<marker::Mut<'_>, i32, i32, marker::LeafOrInternal>,
        idx: usize,
    ) -> (i32, i32) {
        let mut h = unsafe { Handle::new_kv(node, idx) };
        let (k, v) = h.kv_mut();
        (*k, *v)
    }
    /// Builds the standard balancing fixture: a height-1 internal parent of length 1 whose edge 0
    /// is a leaf of `left_len` symbolic pairs and whose edge 1 is a leaf of `right_len` symbolic
    /// pairs, with the parent's own separating pair `(pk, pv)`. Returns the raw node pointers so
    /// post-state reads on a COPY DESTINATION can go through the raw projection rather than
    /// `Handle::new_kv` (whose `debug_assert!(idx < node.len())` consults a field that may itself
    /// be the quantity under test).
    #[allow(dead_code)]
    struct BalanceFixture {
        parent: NodeRef<marker::Owned, i32, i32, marker::Internal>,
        parent_nn: NonNull<LeafNode<i32, i32>>,
        left_nn: NonNull<LeafNode<i32, i32>>,
        right_nn: NonNull<LeafNode<i32, i32>>,
        pk: i32,
        pv: i32,
    }
    fn balance_fixture(left_len: usize, right_len: usize) -> BalanceFixture {
        let left = symbolic_leaf(left_len);
        let left_nn = left.reborrow().node;
        let right = symbolic_leaf(right_len);
        let right_nn = right.reborrow().node;

        let mut parent: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(left.forget_type(), Global);
        let parent_nn = parent.reborrow().node;
        let pk: i32 = kani::any();
        let pv: i32 = kani::any();
        parent.borrow_mut().push(pk, pv, right.forget_type());

        BalanceFixture { parent, parent_nn, left_nn, right_nn, pk, pv }
    }
    /// Frees the three leaf/internal allocations a `BalanceFixture` owns. No drop glue (i32 K/V).
    unsafe fn balance_teardown(f: &BalanceFixture) {
        unsafe {
            Global.deallocate(f.parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(f.left_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(f.right_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
        }
    }
    /// Builds a height-1 internal node with `len` symbolic pairs and `len + 1` empty leaf children,
    /// choosing from `IB + 1` pre-built leaves. Returns the node plus the raw pointers of every
    /// leaf allocated, so the caller can free exactly what it made.
    #[allow(dead_code)]
    struct InternalSide {
        node: NodeRef<marker::Owned, i32, i32, marker::Internal>,
        node_nn: NonNull<LeafNode<i32, i32>>,
        leaves: [NonNull<LeafNode<i32, i32>>; 3],
    }
    /// `IB == 2`: three grandchild leaves per side, so occupancy 0..=2.
    fn internal_side_ib2(len: usize) -> InternalSide {
        let g0 = symbolic_leaf(0);
        let g0_nn = g0.reborrow().node;
        let g1 = symbolic_leaf(0);
        let g1_nn = g1.reborrow().node;
        let g2 = symbolic_leaf(0);
        let g2_nn = g2.reborrow().node;

        let mut node: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(g0.forget_type(), Global);
        let node_nn = node.reborrow().node;
        let k0: i32 = kani::any();
        let v0: i32 = kani::any();
        let k1: i32 = kani::any();
        let v1: i32 = kani::any();
        if len >= 1 {
            node.borrow_mut().push(k0, v0, g1.forget_type());
        }
        if len >= 2 {
            node.borrow_mut().push(k1, v1, g2.forget_type());
        }

        InternalSide { node, node_nn, leaves: [g0_nn, g1_nn, g2_nn] }
    }
    /// Frees one side's internal node and its three grandchild leaves. Takes the raw pointers by
    /// value rather than a `&InternalSide`, because the caller moves the struct's `node` field out
    /// (via `forget_type()`) to build the parent, which partially moves the struct and would make
    /// any later borrow of it ill-formed.
    unsafe fn free_internal_side(
        node_nn: NonNull<LeafNode<i32, i32>>,
        leaves: [NonNull<LeafNode<i32, i32>>; 3],
    ) {
        unsafe {
            Global.deallocate(node_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            let mut i = 0;
            while i < 3 {
                Global.deallocate(leaves[i].cast(), Layout::new::<LeafNode<i32, i32>>());
                i += 1;
            }
        }
    }
    /// Builds a height-1 internal node with `len` symbolic pairs, drawing children from exactly
    /// `N` freshly allocated empty leaves. Every leaf is allocated regardless of `len` so the
    /// caller's teardown is a constant shape; unpushed leaves are simply never linked.
    fn internal_side_n<const N: usize>(
        len: usize,
    ) -> (
        NodeRef<marker::Owned, i32, i32, marker::Internal>,
        NonNull<LeafNode<i32, i32>>,
        [NonNull<LeafNode<i32, i32>>; N],
    ) {
        let first = symbolic_leaf(0);
        let mut leaves = [NonNull::<LeafNode<i32, i32>>::dangling(); N];
        leaves[0] = first.reborrow().node;

        let mut node: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(first.forget_type(), Global);
        let node_nn = node.reborrow().node;

        let mut i = 0;
        while i + 1 < N {
            let child = symbolic_leaf(0);
            leaves[i + 1] = child.reborrow().node;
            if len >= i + 1 {
                let k: i32 = kani::any();
                let v: i32 = kani::any();
                node.borrow_mut().push(k, v, child.forget_type());
            }
            i += 1;
        }

        (node, node_nn, leaves)
    }
    unsafe fn free_side_n<const N: usize>(
        node_nn: NonNull<LeafNode<i32, i32>>,
        leaves: [NonNull<LeafNode<i32, i32>>; N],
    ) {
        unsafe {
            Global.deallocate(node_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            let mut i = 0;
            while i < N {
                Global.deallocate(leaves[i].cast(), Layout::new::<LeafNode<i32, i32>>());
                i += 1;
            }
        }
    }
    /// `N` = `IB + 1` grandchildren per side; `IB` bounds each internal child's occupancy.
    fn do_merge_internal_occupancy_body<const N: usize>() {
        let ib: usize = N - 1;
        let old_left_len: usize = kani::any();
        let right_len: usize = kani::any();
        kani::assume(old_left_len <= ib);
        kani::assume(right_len <= ib);
        kani::assume(old_left_len + 1 + right_len <= CAP);

        let (left, left_nn, left_leaves) = internal_side_n::<N>(old_left_len);
        let (right, right_nn, right_leaves) = internal_side_n::<N>(right_len);
        let spare = symbolic_leaf(0);
        let spare_nn = spare.reborrow().node;
        let third: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(spare.forget_type(), Global);
        let third_nn = third.reborrow().node;

        let mut parent: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(left.forget_type(), Global);
        let parent_nn = parent.reborrow().node;
        let k0: i32 = kani::any();
        let v0: i32 = kani::any();
        let k1: i32 = kani::any();
        let v1: i32 = kani::any();
        parent.borrow_mut().push(k0, v0, right.forget_type());
        parent.borrow_mut().push(k1, v1, third.forget_type());
        assert!(parent.height() == 2, "IS0: the fixture is a height-2 tree");

        {
            let kv = unsafe { Handle::new_kv(parent.borrow_mut(), 0) };
            let bc = kv.consider_for_balancing();
            let _shrunk = bc.merge_tracking_parent(Global);
        }

        kani::cover(right_len == 0, "NV1: an EMPTY right child is merged in");
        kani::cover(right_len == ib && ib > 0, "NV2: a maximal right child for this bound");
        kani::cover(old_left_len == ib && ib > 0, "NV3: a maximal left prefix for this bound");
        kani::cover(
            old_left_len + 1 + right_len == CAP,
            "NV4: the merge fills the surviving child to CAPACITY",
        );

        // `do_merge` frees the RIGHT internal node itself; freeing it here would be a double free.
        // Its grandchild leaves are NOT freed by it and remain ours.
        unsafe {
            Global.deallocate(parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            free_side_n::<N>(left_nn, left_leaves);
            Global.deallocate(third_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(spare_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            let mut i = 0;
            while i < N {
                Global.deallocate(right_leaves[i].cast(), Layout::new::<LeafNode<i32, i32>>());
                i += 1;
            }
        }
    }
    /// Every post-state quantity `check_move_suffix_leaf_content` needs, computed once by a
    /// shared, byte-identical construction (fixture -> move_suffix call -> readback), mirroring
    /// `LeafRemoveContentResult` / `leaf_remove_content_setup`'s shape (the removal-side twin of
    /// this same fixture idiom). `old_len` pushes are position-derived ((i, 1000 + i)) so a
    /// misplacement across the split is observable. All reads happen via fresh, freestanding
    /// `Handle::new_kv(root.reborrow(), pos).into_kv()` calls -- the same proven-safe Immut
    /// readback path used throughout this file (`check_handle_into_kv_no_ub`,
    /// `check_leaf_remove_content`) -- never a raw `NodeRef::len()` or field read on the
    /// freshly-written `right_root` sibling.
    struct MoveSuffixLeafContentResult {
        /// `Some(readback at 0)` when `idx > 0` -- left's head, untouched by the move.
        left_head0: Option<(i32, i32)>,
        /// `Some(readback at idx - 1)` when `idx > 0` -- left's new last element, the original
        /// element that stayed at position `idx - 1` (the boundary just before the split).
        left_last: Option<(i32, i32)>,
        /// `Some(readback at 0)` when `idx < old_len` -- the first moved element, originally at
        /// `idx` in `left`, must now sit at position 0 in `right`.
        right_head0: Option<(i32, i32)>,
        /// `Some(readback at old_len - idx - 1)` when `idx < old_len` -- the last moved element,
        /// originally the LAST element of `left`, must now sit at the new last position of
        /// `right`.
        right_last: Option<(i32, i32)>,
    }
    fn move_suffix_leaf_content_setup(old_len: usize, idx: usize) -> MoveSuffixLeafContentResult {
        let mut left_root: NodeRef<marker::Owned, i32, i32, marker::Leaf> =
            NodeRef::new_leaf(Global);
        for i in 0..old_len {
            left_root.borrow_mut().push(i as i32, 1000 + i as i32);
        }
        let mut right_root: NodeRef<marker::Owned, i32, i32, marker::Leaf> =
            NodeRef::new_leaf(Global);

        let left_mut = left_root.borrow_mut();
        let edge = unsafe { Handle::new_edge(left_mut, idx) };
        let mut split_edge = edge.forget_node_type();

        let mut right_lofi: NodeRef<marker::Mut<'_>, i32, i32, marker::LeafOrInternal> =
            right_root.borrow_mut().forget_type();
        split_edge.move_suffix(&mut right_lofi);
        drop(split_edge);
        drop(right_lofi);

        let new_right_len = old_len - idx;

        let left_head0 = if idx > 0 {
            let readback = unsafe { Handle::new_kv(left_root.reborrow(), 0) };
            let (k, v) = readback.into_kv();
            Some((*k, *v))
        } else {
            None
        };
        let left_last = if idx > 0 {
            let readback = unsafe { Handle::new_kv(left_root.reborrow(), idx - 1) };
            let (k, v) = readback.into_kv();
            Some((*k, *v))
        } else {
            None
        };
        let right_head0 = if new_right_len > 0 {
            let readback = unsafe { Handle::new_kv(right_root.reborrow(), 0) };
            let (k, v) = readback.into_kv();
            Some((*k, *v))
        } else {
            None
        };
        let right_last = if new_right_len > 0 {
            let readback = unsafe { Handle::new_kv(right_root.reborrow(), new_right_len - 1) };
            let (k, v) = readback.into_kv();
            Some((*k, *v))
        } else {
            None
        };

        MoveSuffixLeafContentResult { left_head0, left_last, right_head0, right_last }
    }
    // ---------------------------------------------------------------------
    // DIAGNOSTIC — `move_suffix`, raw post-state stored lengths on BOTH nodes.
    //
    // `check_move_suffix_leaf_no_ub` (shipped) deliberately carries no post-state length
    // assertion. This
    // harness re-measures that exact dropped claim at the current pin, in isolation, through the
    // raw `LeafNode` projection (not `NodeRef::len()`, not `Handle::new_kv`), so a RED cannot be
    // blamed on the readback wrapper.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_move_suffix_leaf_raw_len() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let mut left_root: NodeRef<marker::Owned, i32, i32, marker::Leaf> =
            NodeRef::new_leaf(Global);
        for i in 0..old_len {
            left_root.borrow_mut().push(i as i32, 1000 + i as i32);
        }
        let left_ptr = left_root.reborrow().node.as_ptr();
        let mut right_root: NodeRef<marker::Owned, i32, i32, marker::Leaf> =
            NodeRef::new_leaf(Global);
        let right_ptr = right_root.reborrow().node.as_ptr();

        let left_mut = left_root.borrow_mut();
        let edge = unsafe { Handle::new_edge(left_mut, idx) };
        let mut split_edge = edge.forget_node_type();

        let mut right_lofi: NodeRef<marker::Mut<'_>, i32, i32, marker::LeafOrInternal> =
            right_root.borrow_mut().forget_type();
        split_edge.move_suffix(&mut right_lofi);
        drop(split_edge);
        drop(right_lofi);

        // `move_suffix` writes both lengths only when `new_right_len > 0`; when idx == old_len it
        // returns without touching either, so the expected values below are the fixture's own.
        let expect_left = idx;
        let expect_right = old_len - idx;

        assert!(
            unsafe { usize::from((*left_ptr).len) } == expect_left,
            "ML1: left's stored len == idx after the split"
        );
        assert!(
            unsafe { usize::from((*right_ptr).len) } == expect_right,
            "ML2: right's stored len == old_len - idx after the split"
        );

        kani::cover(idx > 0 && idx < old_len, "NV1: genuine interior split");
        kani::cover(idx == old_len, "NV2: no-op split (right stays empty)");
        kani::cover(idx == 0 && old_len > 0, "NV3: everything moves right");
    }
    // ---------------------------------------------------------------------
    // LABEL: PROBE — residual: SEPARATE, functional-content companion to
    // `check_move_suffix_leaf_no_ub` (per the split_leaf_data / leaf_remove lesson: strong
    // post-state content equalities isolated in their own harness, read back exclusively
    // through the proven-safe Immut `Handle::new_kv(...).into_kv()` path -- never the raw
    // `NodeRef::len()`/field read on the fresh sibling that failed in the no_ub harness's
    // earlier revision). Same old_len/idx domain. Proves: left's head and new-last elements are
    // untouched/correctly bounded when idx > 0, and the first and last moved elements land at
    // the expected positions in `right` when idx < old_len (spot-checks at the split's boundary
    // positions only, the move_suffix-side mirror of `check_leaf_remove_content`'s checks);
    // does not prove it for every element simultaneously, and does not re-derive `len` itself
    // (that quantity is exactly the one the no_ub harness dropped).
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_move_suffix_leaf_content_all() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let r = move_suffix_leaf_content_setup(old_len, idx);

        if let Some(h0) = r.left_head0 {
            assert!(h0 == (0, 1000), "CHECK_A: left head (position 0) mutated by the move");
        }
        if let Some(ll) = r.left_last {
            assert!(
                ll == ((idx - 1) as i32, 1000 + (idx - 1) as i32),
                "CHECK_B: left's new-last element != original element at idx - 1"
            );
        }
        if let Some(rh0) = r.right_head0 {
            assert!(
                rh0 == (idx as i32, 1000 + idx as i32),
                "CHECK_C: right's first element != original element at idx"
            );
        }
        if let Some(rl) = r.right_last {
            assert!(
                rl == ((old_len - 1) as i32, 1000 + (old_len - 1) as i32),
                "CHECK_D: right's new-last element != original last element of left"
            );
        }

        kani::cover(
            idx > 0 && idx < old_len,
            "move_suffix content: genuine interior split verified end-to-end",
        );
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_move_suffix_leaf_content_check_a() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let r = move_suffix_leaf_content_setup(old_len, idx);

        if let Some(h0) = r.left_head0 {
            assert!(h0 == (0, 1000), "CHECK_A: left head (position 0) mutated by the move");
        }

        kani::cover(
            idx > 0 && idx < old_len,
            "move_suffix CHECK_A: genuine interior split (both sides non-empty)",
        );
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_move_suffix_leaf_content_check_b() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let r = move_suffix_leaf_content_setup(old_len, idx);

        if let Some(ll) = r.left_last {
            assert!(
                ll == ((idx - 1) as i32, 1000 + (idx - 1) as i32),
                "CHECK_B: left's new-last element != original element at idx - 1"
            );
        }

        kani::cover(
            idx > 0 && idx < old_len,
            "move_suffix CHECK_B: genuine interior split (both sides non-empty)",
        );
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_move_suffix_leaf_content_check_c() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let r = move_suffix_leaf_content_setup(old_len, idx);

        if let Some(rh0) = r.right_head0 {
            assert!(
                rh0 == (idx as i32, 1000 + idx as i32),
                "CHECK_C: right's first element != original element at idx"
            );
        }

        kani::cover(
            idx > 0 && idx < old_len,
            "move_suffix CHECK_C: genuine interior split (both sides non-empty)",
        );
    }
    #[kani::proof]
    #[kani::unwind(12)]
    fn check_move_suffix_leaf_content_check_d() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 0 || old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx <= old_len);

        let r = move_suffix_leaf_content_setup(old_len, idx);

        if let Some(rl) = r.right_last {
            assert!(
                rl == ((old_len - 1) as i32, 1000 + (old_len - 1) as i32),
                "CHECK_D: right's new-last element != original last element of left"
            );
        }

        kani::cover(
            idx > 0 && idx < old_len,
            "move_suffix CHECK_D: genuine interior split (both sides non-empty)",
        );
    }
    // ---------------------------------------------------------------------
    // CONTRACT CANDIDATE — `Handle::<_, KV>::split` on a LEAF, the whole public function.
    //
    // Drives the whole public function, which allocates the new right node itself and returns a
    // `SplitResult`, rather than only its private helper `split_leaf_data`. This drives the real `split`, which allocates the new right node
    // itself and returns a `SplitResult`, and checks the returned kv plus both sides' stored
    // lengths and their boundary content.
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_leaf_split_no_ub() {
        let old_len: usize = kani::any();
        kani::assume(old_len == 1 || old_len == CAP);
        let idx: usize = kani::any();
        kani::assume(idx < old_len);

        let mut root: NodeRef<marker::Owned, i32, i32, marker::Leaf> = NodeRef::new_leaf(Global);
        for i in 0..old_len {
            root.borrow_mut().push(i as i32, 1000 + i as i32);
        }
        let left_ptr = root.reborrow().node.as_ptr();

        // Destructure the `SplitResult` immediately and drop its `left` field: that field is a
        // `Mut` borrow of `root`, and holding it would keep `root` mutably borrowed past the
        // `into_dying()` teardown below. Every post-state read on either node goes through the
        // raw `LeafNode` projection instead, so nothing here depends on that borrow surviving.
        let (split_kv, mut right_owned) = {
            let handle = unsafe { Handle::new_kv(root.borrow_mut(), idx) };
            let SplitResult { left: _left, kv, right } = handle.split(Global);
            (kv, right)
        };

        let new_right_len = old_len - idx - 1;
        let right_ptr = right_owned.reborrow().node.as_ptr();

        assert!(
            split_kv == (idx as i32, 1000 + idx as i32),
            "SP1: the split-off kv is the pair at idx"
        );
        assert!(
            unsafe { usize::from((*left_ptr).len) } == idx,
            "SP2: the source node's stored len == idx"
        );
        assert!(
            unsafe { usize::from((*right_ptr).len) } == new_right_len,
            "SP3: the new node's stored len == old_len - idx - 1"
        );
        if new_right_len > 0 {
            assert!(
                unsafe { (*right_ptr).keys[0].assume_init_read() } == (idx + 1) as i32,
                "SP4: the new node's first key is the source key at idx + 1"
            );
            assert!(
                unsafe { (*right_ptr).vals[0].assume_init_read() } == 1000 + (idx + 1) as i32,
                "SP5: the new node's first val is the source val at idx + 1"
            );
            assert!(
                unsafe { (*right_ptr).keys[new_right_len - 1].assume_init_read() }
                    == (old_len - 1) as i32,
                "SP6: the new node's last key is the source's original last key"
            );
        }
        if idx > 0 {
            assert!(
                unsafe { (*left_ptr).keys[0].assume_init_read() } == 0,
                "SP7: the source node's head is untouched by the split"
            );
        }

        kani::cover(
            old_len == CAP && idx == MIN_LEN_AFTER_SPLIT,
            "NV1: the real call site's shape (full node, split at B - 1)",
        );
        kani::cover(new_right_len == 0, "NV2: the split produced an empty right node");
        kani::cover(idx == 0, "NV3: the split point is the very first pair");

        let mut dying_left: NodeRef<marker::Dying, i32, i32, marker::Leaf> = root.into_dying();
        let dying_left_ptr = dying_left.node;
        unsafe {
            dying_left.as_leaf_dying();
            Global.deallocate(dying_left_ptr.cast(), Layout::new::<LeafNode<i32, i32>>());
        }
        let mut dying_right: NodeRef<marker::Dying, i32, i32, marker::Leaf> =
            right_owned.into_dying();
        let dying_right_ptr = dying_right.node;
        unsafe {
            dying_right.as_leaf_dying();
            Global.deallocate(dying_right_ptr.cast(), Layout::new::<LeafNode<i32, i32>>());
        }
    }
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_new_internal_no_ub() {
        // Two shapes: a height-0 leaf child (producing a height-1 internal node) and a height-1
        // internal child (producing a height-2 node), which is the shape `push_internal_level`
        // and the split path actually build.
        let deep: bool = kani::any();

        let (built_nn, child_nn, expected_height) = if deep {
            let grandchild = symbolic_leaf(0);
            let grandchild_nn = grandchild.reborrow().node;
            let child: NodeRef<marker::Owned, i32, i32, marker::Internal> =
                NodeRef::new_internal(grandchild.forget_type(), Global);
            let child_nn = child.reborrow().node;
            let built: NodeRef<marker::Owned, i32, i32, marker::Internal> =
                NodeRef::new_internal(child.forget_type(), Global);
            let built_nn = built.reborrow().node;
            assert!(built.height() == 2, "NI1: an internal child yields a height-2 node");
            unsafe {
                Global.deallocate(grandchild_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            }
            (built_nn, child_nn, 2usize)
        } else {
            let child = symbolic_leaf(0);
            let child_nn = child.reborrow().node;
            let built: NodeRef<marker::Owned, i32, i32, marker::Internal> =
                NodeRef::new_internal(child.forget_type(), Global);
            let built_nn = built.reborrow().node;
            assert!(built.height() == 1, "NI2: a leaf child yields a height-1 node");
            (built_nn, child_nn, 1usize)
        };

        // The child's parent link must have been written by the constructor's own relink.
        assert!(
            unsafe { usize::from((*child_nn.as_ptr()).parent_idx.assume_init_read()) } == 0,
            "NI3: the child was linked at edge 0"
        );
        assert!(
            unsafe { (*child_nn.as_ptr()).parent }
                == Some(built_nn.cast::<InternalNode<i32, i32>>()),
            "NI4: the child points back at the node just built"
        );

        kani::cover(expected_height == 1, "NV1: built over a leaf child");
        kani::cover(expected_height == 2, "NV2: built over an internal child");

        unsafe {
            Global.deallocate(built_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            if deep {
                Global.deallocate(child_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            } else {
                Global.deallocate(child_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            }
        }
    }
    // ---------------------------------------------------------------------
    // `correct_all_childrens_parent_links` over the COMPLETE occupancy domain.
    //
    // The counterpart harness in the shipped probe set samples `len` at {0, 1, CAPACITY}. This one
    // leaves `len` fully symbolic in `0..=CAPACITY`, which for this node type is every reachable
    // occupancy — so a green here is a genuinely domain-complete memory-safety result for the
    // relink loop, not a three-point sample. Same perturb-then-fix design, same single symbolic
    // read-back index (the functional claim stays per-index; the MEMORY-SAFETY checks Kani emits
    // are all-paths regardless, which is what the challenge's criterion actually asks for).
    // ---------------------------------------------------------------------
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_correct_all_childrens_parent_links_full_domain() {
        let len: usize = kani::any();
        kani::assume(len <= CAP);

        let mut internal = symbolic_internal(len);

        let garbage = NonNull::<InternalNode<i32, i32>>::dangling();
        for i in 0..=len {
            let mut_ref = internal.borrow_mut();
            let edge = unsafe { Handle::new_edge(mut_ref, i) };
            let mut child = edge.descend();
            child.set_parent_link(garbage, 9999);
        }

        let check_i: usize = kani::any();
        kani::assume(check_i <= len);

        internal.borrow_mut().correct_all_childrens_parent_links();

        let mut_ref = internal.borrow_mut();
        let edge = unsafe { Handle::new_edge(mut_ref, check_i) };
        let descended = edge.descend();
        let ascended = descended.ascend();
        assert!(ascended.is_ok(), "CA2: a relinked child failed to ascend to its parent");
        let parent_edge = ascended.ok().unwrap();
        assert!(parent_edge.idx() == check_i, "CA1: the child ascends to its own edge index");

        kani::cover(len == 0, "NV1: a childless (single-edge) node");
        kani::cover(len > 1 && len < CAP, "NV2: a strictly intermediate occupancy");
        kani::cover(len == CAP, "NV3: a maximal-occupancy node");
        kani::cover(check_i == len && len > 0, "NV4: the last edge is the one checked");
    }
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_steal_left_leaf_no_ub() {
        let old_left_len: usize = kani::any();
        let old_right_len: usize = kani::any();
        kani::assume(old_left_len <= CAP);
        kani::assume(old_right_len <= CAP);
        // `bulk_steal_left(1)`'s own preconditions, specialised to count == 1.
        kani::assume(old_left_len >= 1);
        kani::assume(old_right_len + 1 <= CAP);
        // The caller contract `steal_left` documents for its tracked edge.
        let track: usize = kani::any();
        kani::assume(track <= old_right_len);

        let mut f = balance_fixture(old_left_len, old_right_len);
        {
            let kv = unsafe { Handle::new_kv(f.parent.borrow_mut(), 0) };
            let bc = kv.consider_for_balancing();
            let edge = bc.steal_left(track);
            assert!(edge.idx == 1 + track, "SL1: the tracked right edge shifted up by exactly one");
        }

        kani::cover(track == 0, "NV1: the tracked edge was the first one");
        kani::cover(
            track == old_right_len && old_right_len > 0,
            "NV2: the tracked edge was the last one on a non-empty right child",
        );
        kani::cover(old_right_len + 1 == CAP, "NV3: the steal filled the right child to CAPACITY");

        unsafe { balance_teardown(&f) };
    }
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_steal_right_leaf_no_ub() {
        let old_left_len: usize = kani::any();
        let old_right_len: usize = kani::any();
        kani::assume(old_left_len <= CAP);
        kani::assume(old_right_len <= CAP);
        // `bulk_steal_right(1)`'s own preconditions, specialised to count == 1.
        kani::assume(old_right_len >= 1);
        kani::assume(old_left_len + 1 <= CAP);
        // The caller contract `steal_right` documents: the tracked edge lives in the LEFT child,
        // which has grown by one, so the admissible range is `..= old_left_len + 1`.
        let track: usize = kani::any();
        kani::assume(track <= old_left_len + 1);

        let mut f = balance_fixture(old_left_len, old_right_len);
        {
            let kv = unsafe { Handle::new_kv(f.parent.borrow_mut(), 0) };
            let bc = kv.consider_for_balancing();
            let edge = bc.steal_right(track);
            assert!(edge.idx == track, "SR1: the tracked left edge did not move");
        }

        kani::cover(track == 0, "NV1: the tracked edge was the first one");
        kani::cover(track == old_left_len + 1, "NV2: the tracked edge was the new last one");
        kani::cover(old_left_len + 1 == CAP, "NV3: the steal filled the left child to CAPACITY");

        unsafe { balance_teardown(&f) };
    }
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_merge_tracking_child_edge_leaf_no_ub() {
        let old_left_len: usize = kani::any();
        let right_len: usize = kani::any();
        kani::assume(old_left_len <= CAP);
        kani::assume(right_len <= CAP);
        // `do_merge`'s own precondition (it asserts, and a violating caller is specified to panic).
        kani::assume(old_left_len + 1 + right_len <= CAP);

        // Track an edge on either side. The fn asserts this bound itself; assuming it keeps the
        // harness on the no-panic path, which is the one whose memory safety is in question.
        let side: bool = kani::any();
        let raw: usize = kani::any();
        let track = if side {
            kani::assume(raw <= old_left_len);
            LeftOrRight::Left(raw)
        } else {
            kani::assume(raw <= right_len);
            LeftOrRight::Right(raw)
        };
        let expected = if side { raw } else { old_left_len + 1 + raw };

        let mut f = balance_fixture(old_left_len, right_len);
        // `merge_tracking_child_edge` frees the RIGHT child itself, so the teardown below must
        // not touch it — this harness therefore does its own two-allocation teardown rather than
        // calling `balance_teardown`.
        {
            let kv = unsafe { Handle::new_kv(f.parent.borrow_mut(), 0) };
            let bc = kv.consider_for_balancing();
            let edge = bc.merge_tracking_child_edge(track, Global);
            assert!(edge.idx == expected, "MT1: the tracked edge landed at its documented index");
        }

        kani::cover(side, "NV1: an edge in the LEFT child was tracked");
        kani::cover(!side, "NV2: an edge in the RIGHT child was tracked");
        kani::cover(
            old_left_len + 1 + right_len == CAP,
            "NV3: the merge filled the surviving child to CAPACITY",
        );

        unsafe {
            Global.deallocate(f.parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(f.left_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
        }
    }
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_do_merge_leaf_no_ub() {
        let old_left_len: usize = kani::any();
        let right_len: usize = kani::any();
        kani::assume(old_left_len <= CAP);
        kani::assume(right_len <= CAP);
        // The fn's own precondition (node.rs:1419), ASSUMED rather than asserted: a caller that
        // violates it is specified to panic, which is not UB and is not this harness's subject.
        kani::assume(old_left_len + 1 + right_len <= CAP);
        let new_left_len = old_left_len + 1 + right_len;

        let left = symbolic_leaf(old_left_len);
        let left_nn = left.reborrow().node;
        let left_ptr = left_nn.as_ptr();
        let right = symbolic_leaf(right_len);
        let right_nn = right.reborrow().node;
        let right_ptr = right_nn.as_ptr();
        let third = symbolic_leaf(1);
        let third_nn = third.reborrow().node;
        let third_ptr = third_nn.as_ptr();

        let mut parent: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(left.forget_type(), Global);
        let parent_nn = parent.reborrow().node;
        let parent_ptr = parent_nn.as_ptr();
        let parent_int_nn = parent_nn.cast::<InternalNode<i32, i32>>();
        let parent_int_ptr = parent_int_nn.as_ptr();
        let k0: i32 = kani::any();
        let v0: i32 = kani::any();
        let k1: i32 = kani::any();
        let v1: i32 = kani::any();
        parent.borrow_mut().push(k0, v0, right.forget_type());
        parent.borrow_mut().push(k1, v1, third.forget_type());

        // Pre-state snapshot. The right child is read HERE and nowhere else — the call frees it.
        let mut left_k_before = [0i32; CAP];
        let mut left_v_before = [0i32; CAP];
        let mut right_k_before = [0i32; CAP];
        let mut right_v_before = [0i32; CAP];
        for i in 0..CAP {
            if i < old_left_len {
                left_k_before[i] = unsafe { (*left_ptr).keys[i].assume_init_read() };
                left_v_before[i] = unsafe { (*left_ptr).vals[i].assume_init_read() };
            }
            if i < right_len {
                right_k_before[i] = unsafe { (*right_ptr).keys[i].assume_init_read() };
                right_v_before[i] = unsafe { (*right_ptr).vals[i].assume_init_read() };
            }
        }
        assert!(
            unsafe { usize::from((*left_ptr).len) } == old_left_len,
            "G0: fixture — left's stored len before the call"
        );
        assert!(
            unsafe { usize::from((*right_ptr).len) } == right_len,
            "G1: fixture — right's stored len before the call"
        );
        assert!(
            unsafe { usize::from((*parent_ptr).len) } == 2,
            "G2: fixture — the parent holds two pairs and three edges before the call"
        );
        assert!(
            unsafe { usize::from((*third_ptr).parent_idx.assume_init_read()) } == 2,
            "G3: fixture — the spare child sits at edge 2 before the call"
        );

        // ---------------- THE TARGET CALL ----------------
        {
            let kv = unsafe { Handle::new_kv(parent.borrow_mut(), 0) };
            let bc = kv.consider_for_balancing();
            let _shrunk = bc.merge_tracking_parent(Global);
        }

        // -------- CLAIM 1: the merged child's new length. --------
        // ⚠ This is the exact fact `bulk_steal_left`'s proof could NOT make about ITS destination
        // child, on an object written by the same helper at a symbolic offset.
        assert!(
            unsafe { usize::from((*left_ptr).len) } == new_left_len,
            "S1: left's stored len == old_left_len + 1 + right_len"
        );

        // -------- CLAIM 2: the merged child's pre-existing prefix is untouched. -------- (M2/M2v)
        for i in 0..CAP {
            if i < old_left_len {
                assert!(
                    unsafe { (*left_ptr).keys[i].assume_init_read() } == left_k_before[i],
                    "S2: left's pre-existing key prefix is untouched"
                );
                assert!(
                    unsafe { (*left_ptr).vals[i].assume_init_read() } == left_v_before[i],
                    "S3: left's pre-existing val prefix is untouched"
                );
            }
        }

        // -------- CLAIM 3: the parent's pair was pulled down into the gap. -------- (M3/M3v)
        assert!(
            unsafe { (*left_ptr).keys[old_left_len].assume_init_read() } == k0,
            "D1: left[old_left_len] key := the parent's separating key"
        );
        assert!(
            unsafe { (*left_ptr).vals[old_left_len].assume_init_read() } == v0,
            "D2: left[old_left_len] val := the parent's separating val"
        );

        // -------- CLAIM 4: the whole right child landed after it. -------- (M4/M4v)
        // `move_to_slice(right[..right_len], left[old_left_len+1..new_left_len])`, both arrays.
        for i in 0..CAP {
            if i < right_len {
                assert!(
                    unsafe { (*left_ptr).keys[old_left_len + 1 + i].assume_init_read() }
                        == right_k_before[i],
                    "D3: left[old_left_len+1..] keys := the whole right child"
                );
                assert!(
                    unsafe { (*left_ptr).vals[old_left_len + 1 + i].assume_init_read() }
                        == right_v_before[i],
                    "D4: left[old_left_len+1..] vals := the whole right child"
                );
            }
        }

        // -------- CLAIM 5: the parent shrank correctly. -------- (Q1/Q2/Q2v)
        // The parent is a copy DESTINATION here (three `slice_remove`s) — the first time in this
        // family that a copy destination's own fields are claimed rather than covered.
        assert!(
            unsafe { usize::from((*parent_ptr).len) } == 1,
            "D5: the parent's stored len dropped to 1"
        );
        assert!(
            unsafe { (*parent_ptr).keys[0].assume_init_read() } == k1,
            "D6: the parent's surviving key shifted down into slot 0"
        );
        assert!(
            unsafe { (*parent_ptr).vals[0].assume_init_read() } == v1,
            "D7: the parent's surviving val shifted down into slot 0"
        );

        // -------- CLAIM 6: the edge array closed the gap and the links were repaired. --------
        // (Q3/Q4/Q5) `slice_remove(edge_area(..3), 1)` then
        // `correct_childrens_parent_links(1..2)` — the repair runs, at a constant trip count.
        assert!(
            unsafe { (*parent_int_ptr).edges[1].assume_init_read() } == third_nn,
            "D8: the parent's edge 1 is now the spare child"
        );
        assert!(
            unsafe { usize::from((*third_ptr).parent_idx.assume_init_read()) } == 1,
            "D9: the spare child's parent_idx was corrected 2 -> 1"
        );
        assert!(
            unsafe { (*third_ptr).parent } == Some(parent_int_nn),
            "D10: the spare child still points at the parent"
        );

        // ---------------- Non-vacuity. ----------------
        kani::cover(right_len == 0, "NV1: an EMPTY right child is merged in");
        kani::cover(right_len > 1, "NV2: a multi-pair right child is merged in");
        kani::cover(old_left_len == 0, "NV3: the left child was empty before the merge");
        kani::cover(old_left_len > 0, "NV4: a non-empty left prefix is preserved across the merge");
        kani::cover(new_left_len == CAP, "NV5: the merge fills the left child to CAPACITY");
        kani::cover(
            old_left_len > 0 && right_len > 1,
            "NV6: a non-empty prefix and a multi-pair move happen together",
        );

        // Teardown: THREE live allocations, not four — `do_merge` freed the right child itself
        // (node.rs:1456), and this harness proves that free is not UB. Freeing it again here
        // would be a double free.
        unsafe {
            Global.deallocate(parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(left_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(third_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
        }
    }
    #[kani::proof]
    #[kani::unwind(5)]
    fn check_do_merge_internal_no_ub() {
        const IB: usize = 2;

        let old_left_len: usize = kani::any();
        let right_len: usize = kani::any();
        kani::assume(old_left_len <= IB);
        kani::assume(right_len <= IB);
        let new_left_len = old_left_len + 1 + right_len;

        let lg0 = symbolic_leaf(0);
        let lg0_nn = lg0.reborrow().node;
        let lg1 = symbolic_leaf(0);
        let lg1_nn = lg1.reborrow().node;
        let lg2 = symbolic_leaf(0);
        let lg2_nn = lg2.reborrow().node;
        let rg0 = symbolic_leaf(0);
        let rg0_nn = rg0.reborrow().node;
        let rg1 = symbolic_leaf(0);
        let rg1_nn = rg1.reborrow().node;
        let rg2 = symbolic_leaf(0);
        let rg2_nn = rg2.reborrow().node;
        let tg = symbolic_leaf(0);
        let tg_nn = tg.reborrow().node;
        let lg = [lg0_nn, lg1_nn, lg2_nn];
        let rg = [rg0_nn, rg1_nn, rg2_nn];

        let mut left: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(lg0.forget_type(), Global);
        let left_nn = left.reborrow().node;
        let left_ptr = left_nn.as_ptr();
        let left_int_nn = left_nn.cast::<InternalNode<i32, i32>>();
        let left_int_ptr = left_int_nn.as_ptr();
        let lk0: i32 = kani::any();
        let lv0: i32 = kani::any();
        let lk1: i32 = kani::any();
        let lv1: i32 = kani::any();
        if old_left_len >= 1 {
            left.borrow_mut().push(lk0, lv0, lg1.forget_type());
        }
        if old_left_len >= 2 {
            left.borrow_mut().push(lk1, lv1, lg2.forget_type());
        }

        let mut right: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(rg0.forget_type(), Global);
        let right_nn = right.reborrow().node;
        let right_ptr = right_nn.as_ptr();
        let right_int_nn = right_nn.cast::<InternalNode<i32, i32>>();
        let rk0: i32 = kani::any();
        let rv0: i32 = kani::any();
        let rk1: i32 = kani::any();
        let rv1: i32 = kani::any();
        if right_len >= 1 {
            right.borrow_mut().push(rk0, rv0, rg1.forget_type());
        }
        if right_len >= 2 {
            right.borrow_mut().push(rk1, rv1, rg2.forget_type());
        }

        let third: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(tg.forget_type(), Global);
        let third_nn = third.reborrow().node;
        let third_ptr = third_nn.as_ptr();

        let mut parent: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(left.forget_type(), Global);
        let parent_nn = parent.reborrow().node;
        let parent_ptr = parent_nn.as_ptr();
        let parent_int_nn = parent_nn.cast::<InternalNode<i32, i32>>();
        let parent_int_ptr = parent_int_nn.as_ptr();
        let k0: i32 = kani::any();
        let v0: i32 = kani::any();
        let k1: i32 = kani::any();
        let v1: i32 = kani::any();
        parent.borrow_mut().push(k0, v0, right.forget_type());
        parent.borrow_mut().push(k1, v1, third.forget_type());

        let mut left_k_before = [0i32; IB + 1];
        let mut left_v_before = [0i32; IB + 1];
        let mut right_k_before = [0i32; IB + 1];
        let mut right_v_before = [0i32; IB + 1];
        for i in 0..=IB {
            if i < old_left_len {
                left_k_before[i] = unsafe { (*left_ptr).keys[i].assume_init_read() };
                left_v_before[i] = unsafe { (*left_ptr).vals[i].assume_init_read() };
            }
            if i < right_len {
                right_k_before[i] = unsafe { (*right_ptr).keys[i].assume_init_read() };
                right_v_before[i] = unsafe { (*right_ptr).vals[i].assume_init_read() };
            }
        }

        // ---- the fixture, ASSERTED (17a measured every one of these UNSATISFIABLE) ----
        assert!(unsafe { usize::from((*left_ptr).len) } == old_left_len);
        assert!(unsafe { usize::from((*right_ptr).len) } == right_len);
        assert!(unsafe { usize::from((*parent_ptr).len) } == 2);
        let mut g_rlink = true;
        for i in 0..=IB {
            if i <= right_len {
                let g = rg[i].as_ptr();
                if usize::from(unsafe { (*g).parent_idx.assume_init_read() }) != i {
                    g_rlink = false;
                }
                if unsafe { (*g).parent } != Some(right_int_nn) {
                    g_rlink = false;
                }
            }
        }
        assert!(g_rlink);
        assert!(unsafe { usize::from((*third_ptr).parent_idx.assume_init_read()) } == 2);

        // ---------------- THE TARGET CALL ----------------
        {
            let kv = unsafe { Handle::new_kv(parent.borrow_mut(), 0) };
            let bc = kv.consider_for_balancing();
            let _shrunk = bc.merge_tracking_parent(Global);
        }

        // ---- the merged child's leaf-prefix fields ----
        assert!(unsafe { usize::from((*left_ptr).len) } == new_left_len);
        let mut m_prefix = true;
        let mut m_moved = true;
        for i in 0..=IB {
            if i < old_left_len {
                if unsafe { (*left_ptr).keys[i].assume_init_read() } != left_k_before[i] {
                    m_prefix = false;
                }
                if unsafe { (*left_ptr).vals[i].assume_init_read() } != left_v_before[i] {
                    m_prefix = false;
                }
            }
            if i < right_len {
                if unsafe { (*left_ptr).keys[old_left_len + 1 + i].assume_init_read() }
                    != right_k_before[i]
                {
                    m_moved = false;
                }
                if unsafe { (*left_ptr).vals[old_left_len + 1 + i].assume_init_read() }
                    != right_v_before[i]
                {
                    m_moved = false;
                }
            }
        }
        assert!(m_prefix);
        assert!(unsafe { (*left_ptr).keys[old_left_len].assume_init_read() } == k0);
        assert!(unsafe { (*left_ptr).vals[old_left_len].assume_init_read() } == v0);
        assert!(m_moved);

        // ---- the merged child's EDGE array: the copy this arm alone performs ----
        let mut e_prefix = true;
        let mut e_moved = true;
        for i in 0..=IB {
            if i <= old_left_len {
                if unsafe { (*left_int_ptr).edges[i].assume_init_read() } != lg[i] {
                    e_prefix = false;
                }
            }
            if i <= right_len {
                if unsafe { (*left_int_ptr).edges[old_left_len + 1 + i].assume_init_read() }
                    != rg[i]
                {
                    e_moved = false;
                }
            }
        }
        assert!(e_prefix);
        assert!(e_moved);

        // ---- the SYMBOLIC-TRIP-COUNT parent-link repair, and its non-effect on the rest ----
        let mut e_links = true;
        let mut e_own = true;
        for i in 0..=IB {
            if i <= right_len {
                let g = rg[i].as_ptr();
                if usize::from(unsafe { (*g).parent_idx.assume_init_read() })
                    != old_left_len + 1 + i
                {
                    e_links = false;
                }
                if unsafe { (*g).parent } != Some(left_int_nn) {
                    e_links = false;
                }
            }
            if i <= old_left_len {
                let g = lg[i].as_ptr();
                if usize::from(unsafe { (*g).parent_idx.assume_init_read() }) != i {
                    e_own = false;
                }
                if unsafe { (*g).parent } != Some(left_int_nn) {
                    e_own = false;
                }
            }
        }
        assert!(e_links);
        assert!(e_own);

        // ---- the shrunk parent, and its own repair ----
        assert!(unsafe { usize::from((*parent_ptr).len) } == 1);
        assert!(unsafe { (*parent_ptr).keys[0].assume_init_read() } == k1);
        assert!(unsafe { (*parent_ptr).vals[0].assume_init_read() } == v1);
        assert!(unsafe { (*parent_int_ptr).edges[1].assume_init_read() } == third_nn);
        assert!(unsafe { usize::from((*third_ptr).parent_idx.assume_init_read()) } == 1);
        assert!(unsafe { (*third_ptr).parent } == Some(parent_int_nn));

        // ---- non-vacuity: the admitted space is not a single degenerate shape ----
        kani::cover(right_len == 0, "NV1: a length-0 right child is merged");
        kani::cover(right_len == IB, "NV2: a multi-edge move happens");
        kani::cover(old_left_len > 0, "NV3: a non-empty left prefix survives the merge");
        kani::cover(
            old_left_len > 0 && right_len > 1,
            "NV4: a non-empty prefix and a multi-edge move happen together",
        );
        kani::cover(new_left_len == 2 * IB + 1, "NV5: the widest admitted merge is reached");

        unsafe {
            Global.deallocate(parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(left_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(third_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(lg0_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(lg1_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(lg2_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(rg0_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(rg1_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(rg2_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(tg_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
        }
    }
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_bulk_steal_left_leaf_scoped_no_ub() {
        let old_left_len: usize = kani::any();
        let old_right_len: usize = kani::any();
        let count: usize = kani::any();
        kani::assume(old_left_len <= CAP);
        kani::assume(old_right_len <= CAP);
        // The fn's own three preconditions, ASSUMED rather than asserted: a caller that violates
        // them is specified to panic, which is not UB and is not this harness's subject.
        kani::assume(count > 0);
        kani::assume(old_left_len >= count);
        kani::assume(old_right_len + count <= CAP);

        let new_left_len = old_left_len - count;
        let new_right_len = old_right_len + count;

        let left = symbolic_leaf(old_left_len);
        let left_nn = left.reborrow().node;
        let left_ptr = left_nn.as_ptr();
        let right = symbolic_leaf(old_right_len);
        let right_nn = right.reborrow().node;
        let right_ptr = right_nn.as_ptr();

        let mut parent: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(left.forget_type(), Global);
        let parent_nn = parent.reborrow().node;
        let pk: i32 = kani::any();
        let pv: i32 = kani::any();
        parent.borrow_mut().push(pk, pv, right.forget_type());

        // Pre-state snapshot, taken through the SAME raw path used after the call, so a difference
        // between the two cannot be an artifact of two different read routes.
        let mut left_k_before = [0i32; CAP];
        let mut left_v_before = [0i32; CAP];
        let mut right_k_before = [0i32; CAP];
        for i in 0..CAP {
            if i < old_left_len {
                left_k_before[i] = unsafe { (*left_ptr).keys[i].assume_init_read() };
                left_v_before[i] = unsafe { (*left_ptr).vals[i].assume_init_read() };
            }
            if i < old_right_len {
                right_k_before[i] = unsafe { (*right_ptr).keys[i].assume_init_read() };
            }
        }
        // The fixture is sound before the call. These are ASSERTIONS, not covers: if either fails
        // the harness is measuring against a pre-state that was already wrong.
        assert!(
            unsafe { usize::from((*left_ptr).len) } == old_left_len,
            "G0: fixture — left stored len before the call"
        );
        assert!(
            unsafe { usize::from((*right_ptr).len) } == old_right_len,
            "G1: fixture — right stored len before the call"
        );

        // ---------------- THE TARGET CALL ----------------
        {
            let kv = unsafe { Handle::new_kv(parent.borrow_mut(), 0) };
            let mut bc = kv.consider_for_balancing();
            bc.bulk_steal_left(count);
        }

        // ---------------- CLAIM 1: the copy SOURCE side is intact. ----------------
        // The left child is only ever read out of, never written into, so nothing here is
        // exposed to the destination-offset imprecision.
        assert!(
            unsafe { usize::from((*left_ptr).len) } == new_left_len,
            "S1: left stored len == old_left_len - count"
        );
        for i in 0..CAP {
            if i < new_left_len {
                assert!(
                    unsafe { (*left_ptr).keys[i].assume_init_read() } == left_k_before[i],
                    "S2: left's retained key prefix is untouched"
                );
                assert!(
                    unsafe { (*left_ptr).vals[i].assume_init_read() } == left_v_before[i],
                    "S3: left's retained val prefix is untouched"
                );
            }
        }

        // ---------------- CLAIM 2: the stolen block landed at the front of `right`. ----------
        // `move_to_slice(left[new_left_len+1..old_left_len], right[..count-1])`, both arrays.
        for i in 0..CAP {
            if i + 1 < count {
                assert!(
                    unsafe { (*right_ptr).keys[i].assume_init_read() }
                        == left_k_before[new_left_len + 1 + i],
                    "D1: right[..count-1] keys := the stolen left block"
                );
                assert!(
                    unsafe { (*right_ptr).vals[i].assume_init_read() }
                        == left_v_before[new_left_len + 1 + i],
                    "D2: right[..count-1] vals := the stolen left block"
                );
            }
        }

        // ---------------- CLAIM 3: the pair rotation through the parent. ----------------
        // The parent's OLD kv is written into `right[count-1]` by two single-element `.write()`s,
        // and the parent takes `left[new_left_len]` via `replace_kv`.
        assert!(
            unsafe { (*right_ptr).keys[count - 1].assume_init_read() } == pk,
            "D3: right[count-1] key := the parent's OLD key"
        );
        assert!(
            unsafe { (*right_ptr).vals[count - 1].assume_init_read() } == pv,
            "D4: right[count-1] val := the parent's OLD val"
        );
        let parent_after = kv_at(parent.borrow_mut().forget_type(), 0);
        assert!(
            parent_after == (left_k_before[new_left_len], left_v_before[new_left_len]),
            "D5: the parent now holds left[new_left_len]"
        );

        // -------- CLAIM 4: the destination child's own state. --------
        // Asserted, not covered: the destination's stored length after the steal, and the shift-up
        // of its pre-existing pairs in BOTH the key and the value array.
        assert!(
            unsafe { usize::from((*right_ptr).len) } == new_right_len,
            "D6: right's stored len == old_right_len + count"
        );
        for i in 0..CAP {
            if i < old_right_len {
                assert!(
                    unsafe { (*right_ptr).keys[count + i].assume_init_read() } == right_k_before[i],
                    "D7: right's own keys are shifted up by count"
                );
                assert!(
                    unsafe { (*right_ptr).vals[count + i].assume_init_read() } == right_v_before[i],
                    "D8: right's own vals are shifted up by count"
                );
            }
        }

        // ---------------- Non-vacuity. ----------------
        kani::cover(count == 1, "NV1: count == 1 — the `steal_left` specialization");
        kani::cover(count > 1, "NV2: count > 1 — a genuine bulk steal of several pairs");
        kani::cover(new_left_len == 0, "NV3: the left child was emptied by the steal");
        kani::cover(new_right_len == CAP, "NV4: the right child was filled to CAPACITY");
        kani::cover(
            old_right_len > 0 && count > 1,
            "NV5: shift-up and a multi-pair move happen together",
        );

        // Teardown: three live allocations, no drop glue (i32 K/V).
        unsafe {
            Global.deallocate(parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(left_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(right_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
        }
    }
    #[kani::proof]
    #[kani::unwind(13)]
    fn check_bulk_steal_right_leaf_scoped_no_ub() {
        let old_left_len: usize = kani::any();
        let old_right_len: usize = kani::any();
        let count: usize = kani::any();
        kani::assume(old_left_len <= CAP);
        kani::assume(old_right_len <= CAP);
        // The fn's own three preconditions, ASSUMED rather than asserted: a caller that violates
        // them is specified to panic, which is not UB and is not this harness's subject.
        kani::assume(count > 0);
        kani::assume(old_right_len >= count);
        kani::assume(old_left_len + count <= CAP);

        let new_left_len = old_left_len + count;
        let new_right_len = old_right_len - count;

        let left = symbolic_leaf(old_left_len);
        let left_nn = left.reborrow().node;
        let left_ptr = left_nn.as_ptr();
        let right = symbolic_leaf(old_right_len);
        let right_nn = right.reborrow().node;
        let right_ptr = right_nn.as_ptr();

        let mut parent: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(left.forget_type(), Global);
        let parent_nn = parent.reborrow().node;
        let pk: i32 = kani::any();
        let pv: i32 = kani::any();
        parent.borrow_mut().push(pk, pv, right.forget_type());

        // Pre-state snapshot through the SAME raw path used after the call.
        let mut left_k_before = [0i32; CAP];
        let mut left_v_before = [0i32; CAP];
        let mut right_k_before = [0i32; CAP];
        let mut right_v_before = [0i32; CAP];
        for i in 0..CAP {
            if i < old_left_len {
                left_k_before[i] = unsafe { (*left_ptr).keys[i].assume_init_read() };
                left_v_before[i] = unsafe { (*left_ptr).vals[i].assume_init_read() };
            }
            if i < old_right_len {
                right_k_before[i] = unsafe { (*right_ptr).keys[i].assume_init_read() };
                right_v_before[i] = unsafe { (*right_ptr).vals[i].assume_init_read() };
            }
        }
        assert!(
            unsafe { usize::from((*left_ptr).len) } == old_left_len,
            "G0: fixture — left stored len before the call"
        );
        assert!(
            unsafe { usize::from((*right_ptr).len) } == old_right_len,
            "G1: fixture — right stored len before the call"
        );

        // ---------------- THE TARGET CALL ----------------
        {
            let kv = unsafe { Handle::new_kv(parent.borrow_mut(), 0) };
            let mut bc = kv.consider_for_balancing();
            bc.bulk_steal_right(count);
        }

        // -------- CLAIM 1: the DESTINATION child (left) is fully provable. --------
        // The destination child's own pre-existing prefix is untouched by the steal.
        assert!(
            unsafe { usize::from((*left_ptr).len) } == new_left_len,
            "S1: left stored len == old_left_len + count"
        );
        for i in 0..CAP {
            if i < old_left_len {
                assert!(
                    unsafe { (*left_ptr).keys[i].assume_init_read() } == left_k_before[i],
                    "S2: left's pre-existing key prefix is untouched"
                );
                assert!(
                    unsafe { (*left_ptr).vals[i].assume_init_read() } == left_v_before[i],
                    "S3: left's pre-existing val prefix is untouched"
                );
            }
        }

        // -------- CLAIM 2: the parent's OLD kv landed at left[old_left_len]. --------
        assert!(
            unsafe { (*left_ptr).keys[old_left_len].assume_init_read() } == pk,
            "D1: left[old_left_len] key := the parent's OLD key"
        );
        assert!(
            unsafe { (*left_ptr).vals[old_left_len].assume_init_read() } == pv,
            "D2: left[old_left_len] val := the parent's OLD val"
        );

        // -------- CLAIM 3: the stolen block landed after it. --------
        // `move_to_slice(right[..count-1], left[old_left_len+1..new_left_len])`, both arrays.
        for i in 0..CAP {
            if i + 1 < count {
                assert!(
                    unsafe { (*left_ptr).keys[old_left_len + 1 + i].assume_init_read() }
                        == right_k_before[i],
                    "D3: left[old_left_len+1..] keys := the stolen right block"
                );
                assert!(
                    unsafe { (*left_ptr).vals[old_left_len + 1 + i].assume_init_read() }
                        == right_v_before[i],
                    "D4: left[old_left_len+1..] vals := the stolen right block"
                );
            }
        }

        // -------- CLAIM 4: right's KEYS closed the gap. --------
        // `slice_shl(right.key_area_mut(..old_right_len), count)`. The value analogue is asserted
        // separately in CLAIM 6 below rather than folded in here, because the two arrays sit at
        // different object offsets and are worth stating as distinct claims.
        for i in 0..CAP {
            if i < new_right_len {
                assert!(
                    unsafe { (*right_ptr).keys[i].assume_init_read() } == right_k_before[count + i],
                    "D5: right's keys are shifted DOWN by count"
                );
            }
        }

        // -------- CLAIM 5: the pair rotation through the parent. --------
        let parent_after = kv_at(parent.borrow_mut().forget_type(), 0);
        assert!(
            parent_after == (right_k_before[count - 1], right_v_before[count - 1]),
            "D6: the parent now holds right's OLD [count-1] pair"
        );

        // -------- CLAIM 6: the source child's own state. --------
        // Asserted, not covered: the source's stored length after the steal, and the shift-DOWN of
        // its surviving pairs in the value array (the key side is CLAIM 4 above).
        assert!(
            unsafe { usize::from((*right_ptr).len) } == new_right_len,
            "D7: right's stored len == old_right_len - count"
        );
        for i in 0..CAP {
            if i < new_right_len {
                assert!(
                    unsafe { (*right_ptr).vals[i].assume_init_read() } == right_v_before[count + i],
                    "D8: right's vals are shifted DOWN by count"
                );
            }
        }

        // ---------------- Non-vacuity. ----------------
        kani::cover(count == 1, "NV1: count == 1 — the `steal_right` specialization");
        kani::cover(count > 1, "NV2: count > 1 — a genuine bulk steal of several pairs");
        kani::cover(new_right_len == 0, "NV3: the right child was emptied by the steal");
        kani::cover(new_left_len == CAP, "NV4: the left child was filled to CAPACITY");
        kani::cover(
            new_right_len > 0 && count > 1,
            "NV5: a non-empty shift-down and a multi-pair move happen together",
        );
        kani::cover(old_left_len > 0, "NV6: a non-empty pre-existing left prefix is exercised");

        // Teardown: three live allocations, no drop glue (i32 K/V).
        unsafe {
            Global.deallocate(parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            Global.deallocate(left_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
            Global.deallocate(right_nn.cast(), Layout::new::<LeafNode<i32, i32>>());
        }
    }
    #[kani::proof]
    #[kani::unwind(6)]
    fn check_bulk_steal_left_internal_no_ub() {
        const IB: usize = 2;

        let old_left_len: usize = kani::any();
        let old_right_len: usize = kani::any();
        let count: usize = kani::any();
        kani::assume(old_left_len <= IB);
        kani::assume(old_right_len <= IB);
        // The function's own three preconditions, ASSUMED: a caller that violates them is
        // specified to panic, which is not UB and is not this harness's subject.
        kani::assume(count > 0);
        kani::assume(old_left_len >= count);
        kani::assume(old_right_len + count <= CAP);

        let left = internal_side_ib2(old_left_len);
        let right = internal_side_ib2(old_right_len);
        // Capture the (Copy) raw pointers BEFORE moving each side's `node` field into the parent.
        let left_nn = left.node_nn;
        let left_leaves = left.leaves;
        let right_nn = right.node_nn;
        let right_leaves = right.leaves;

        let mut parent: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(left.node.forget_type(), Global);
        let parent_nn = parent.reborrow().node;
        let pk: i32 = kani::any();
        let pv: i32 = kani::any();
        parent.borrow_mut().push(pk, pv, right.node.forget_type());
        assert!(parent.height() == 2, "BSLI0: the fixture is a height-2 tree");

        {
            let kv = unsafe { Handle::new_kv(parent.borrow_mut(), 0) };
            let mut bc = kv.consider_for_balancing();
            bc.bulk_steal_left(count);
        }

        kani::cover(count == 1, "NV1: count == 1 — the `steal_left` specialization, internal arm");
        kani::cover(count > 1, "NV2: count > 1 — a genuine bulk steal of several edges");
        kani::cover(old_left_len - count == 0, "NV3: the left child was emptied of pairs");
        kani::cover(
            old_right_len > 0 && count > 0,
            "NV4: a non-empty edge shift-up and an edge move happen together",
        );

        unsafe {
            Global.deallocate(parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            free_internal_side(left_nn, left_leaves);
            free_internal_side(right_nn, right_leaves);
        }
    }
    #[kani::proof]
    #[kani::unwind(6)]
    fn check_bulk_steal_right_internal_no_ub() {
        const IB: usize = 2;

        let old_left_len: usize = kani::any();
        let old_right_len: usize = kani::any();
        let count: usize = kani::any();
        kani::assume(old_left_len <= IB);
        kani::assume(old_right_len <= IB);
        kani::assume(count > 0);
        kani::assume(old_right_len >= count);
        kani::assume(old_left_len + count <= CAP);

        let left = internal_side_ib2(old_left_len);
        let right = internal_side_ib2(old_right_len);
        // Capture the (Copy) raw pointers BEFORE moving each side's `node` field into the parent.
        let left_nn = left.node_nn;
        let left_leaves = left.leaves;
        let right_nn = right.node_nn;
        let right_leaves = right.leaves;

        let mut parent: NodeRef<marker::Owned, i32, i32, marker::Internal> =
            NodeRef::new_internal(left.node.forget_type(), Global);
        let parent_nn = parent.reborrow().node;
        let pk: i32 = kani::any();
        let pv: i32 = kani::any();
        parent.borrow_mut().push(pk, pv, right.node.forget_type());
        assert!(parent.height() == 2, "BSRI0: the fixture is a height-2 tree");

        {
            let kv = unsafe { Handle::new_kv(parent.borrow_mut(), 0) };
            let mut bc = kv.consider_for_balancing();
            bc.bulk_steal_right(count);
        }

        kani::cover(count == 1, "NV1: count == 1 — the `steal_right` specialization, internal arm");
        kani::cover(count > 1, "NV2: count > 1 — a genuine bulk steal of several edges");
        kani::cover(old_right_len - count == 0, "NV3: the right child was emptied of pairs");
        kani::cover(
            old_left_len > 0 && count > 0,
            "NV4: a non-empty left prefix and an edge move happen together",
        );

        unsafe {
            Global.deallocate(parent_nn.cast(), Layout::new::<InternalNode<i32, i32>>());
            free_internal_side(left_nn, left_leaves);
            free_internal_side(right_nn, right_leaves);
        }
    }
    #[kani::proof]
    #[kani::unwind(15)]
    fn check_do_merge_internal_full_occupancy_no_ub() {
        do_merge_internal_occupancy_body::<12>();
    }
}

#[cfg(test)]
mod tests;
