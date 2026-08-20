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

#[cfg(kani)]
use core::kani;
use core::marker::PhantomData;
use core::mem::{self, MaybeUninit};
use core::num::NonZero;
use core::ptr::{self, NonNull};
use core::slice::SliceIndex;

use safety::requires;

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
    #[requires(core::ub_checks::can_write(this))]
    #[cfg_attr(kani, kani::modifies(this))]
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
    #[requires(idx < self.len())]
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
    #[requires(idx < node.len())]
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
    #[requires(idx <= node.len())]
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

        // Each iteration is one parent hop (fit, split-root, or parent-insert).
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
#[requires(idx < slice.len())]
#[cfg_attr(kani, kani::modifies(slice))]
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
#[requires(idx < slice.len())]
#[cfg_attr(kani, kani::modifies(slice))]
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
#[requires(distance <= slice.len())]
#[cfg_attr(kani, kani::modifies(slice))]
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
#[requires(distance <= slice.len())]
#[cfg_attr(kani, kani::modifies(slice))]
unsafe fn slice_shr<T>(slice: &mut [MaybeUninit<T>], distance: usize) {
    unsafe {
        let slice_ptr = slice.as_mut_ptr();
        ptr::copy(slice_ptr, slice_ptr.add(distance), slice.len() - distance);
    }
}

/// Moves all values from a slice of initialized elements to a slice
/// of uninitialized elements, leaving behind `src` as all uninitialized.
/// Works like `dst.copy_from_slice(src)` but does not require `T` to be `Copy`.
#[requires(src.len() == dst.len())]
#[cfg_attr(kani, kani::modifies(dst))]
fn move_to_slice<T>(src: &mut [MaybeUninit<T>], dst: &mut [MaybeUninit<T>]) {
    assert!(src.len() == dst.len());
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    //! Memory-safety proofs for `btree::node` (Challenge 4 / issue #77).
    //!
    //! Occupancy is quantified over the full `0..=CAPACITY` space of a node.
    //! `CAPACITY` is a type-level constant (`2 * B - 1`), not a harness bound:
    //! a node cannot store more pairs. Tree height is the remaining unbounded
    //! parameter and is handled by the loop contract on `insert_recursing`.
    use core::kani;
    use core::mem::MaybeUninit;

    use super::*;
    use crate::alloc::Global;
    use crate::boxed::Box;

    type Leaf = NodeRef<marker::Owned, u8, u8, marker::Leaf>;
    type Internal = NodeRef<marker::Owned, u8, u8, marker::Internal>;

    fn any_len() -> usize {
        kani::any_where(|&n: &usize| n <= CAPACITY)
    }

    fn any_nonempty_len() -> usize {
        kani::any_where(|&n: &usize| n > 0 && n <= CAPACITY)
    }

    /// Initialize `n` slots by writing the key/value arrays directly.
    /// Avoids `push`/`Handle::new_kv` so contract proofs can call those once at top level.
    /// Uses `ptr::copy` (no Rust loop) so insert_recursing proofs can keep a low unwind.
    fn leaf_with_len(n: usize) -> Leaf {
        kani::assume(n <= CAPACITY);
        let mut node = NodeRef::new_leaf(Global);
        let keys: [u8; CAPACITY] = kani::any();
        let vals: [u8; CAPACITY] = kani::any();
        {
            let mut borrow = node.borrow_mut();
            unsafe {
                ptr::copy_nonoverlapping(
                    keys.as_ptr().cast::<MaybeUninit<u8>>(),
                    borrow.key_area_mut(..n).as_mut_ptr(),
                    n,
                );
                ptr::copy_nonoverlapping(
                    vals.as_ptr().cast::<MaybeUninit<u8>>(),
                    borrow.val_area_mut(..n).as_mut_ptr(),
                    n,
                );
            }
            *borrow.len_mut() = n as u16;
        }
        node
    }

    fn any_leaf() -> Leaf {
        leaf_with_len(any_len())
    }

    fn any_nonempty_leaf() -> Leaf {
        leaf_with_len(any_nonempty_len())
    }

    fn parent_with_leaves(left_n: usize, right_n: usize) -> Internal {
        let left = leaf_with_len(left_n).forget_type();
        let mut parent = NodeRef::new_internal(left, Global);
        parent.borrow_mut().push(kani::any(), kani::any(), leaf_with_len(right_n).forget_type());
        parent
    }

    fn init_buf<const N: usize>(buf: &mut [MaybeUninit<u8>; N], len: usize) {
        kani::assume(len <= N);
        let src: [u8; N] = kani::any();
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr().cast::<MaybeUninit<u8>>(), buf.as_mut_ptr(), len);
        }
    }

    // --- Contracts on unsafe constructors and slice primitives ---

    #[kani::proof_for_contract(LeafNode::init)]
    #[kani::unwind(13)]
    fn check_leaf_node_init() {
        let mut leaf = Box::<LeafNode<u8, u8>, _>::new_uninit_in(Global);
        unsafe {
            LeafNode::init(leaf.as_mut_ptr());
            let leaf = leaf.assume_init();
            assert!(leaf.len == 0);
            assert!(leaf.parent.is_none());
        }
    }

    #[kani::proof_for_contract(Handle::new_kv)]
    #[kani::unwind(13)]
    fn check_handle_new_kv() {
        let mut node = any_nonempty_leaf();
        let idx = kani::any_where(|&i: &usize| i < node.len());
        let handle = unsafe { Handle::new_kv(node.borrow_mut(), idx) };
        assert!(handle.idx() == idx);
    }

    #[kani::proof_for_contract(Handle::new_edge)]
    #[kani::unwind(13)]
    fn check_handle_new_edge() {
        let node = any_leaf();
        let idx = kani::any_where(|&i: &usize| i <= node.len());
        let handle = unsafe { Handle::new_edge(node.reborrow(), idx) };
        assert!(handle.idx() == idx);
    }

    #[kani::proof_for_contract(NodeRef::into_key_val_mut_at)]
    #[kani::unwind(13)]
    fn check_into_key_val_mut_at() {
        let mut node = any_nonempty_leaf();
        let idx = kani::any_where(|&i: &usize| i < node.len());
        let (k, v) = unsafe { node.borrow_valmut().into_key_val_mut_at(idx) };
        let _ = *k;
        *v = kani::any();
    }

    #[kani::proof_for_contract(slice_insert)]
    #[kani::unwind(13)]
    fn check_slice_insert() {
        const N: usize = CAPACITY + 1;
        let mut buf = [const { MaybeUninit::<u8>::uninit() }; N];
        let len = kani::any_where(|&l: &usize| l > 0 && l <= N);
        let idx = kani::any_where(|&i: &usize| i < len);
        init_buf(&mut buf, len.saturating_sub(1));
        unsafe {
            slice_insert(&mut buf[..len], idx, kani::any());
        }
    }

    #[kani::proof_for_contract(slice_remove)]
    #[kani::unwind(13)]
    fn check_slice_remove() {
        const N: usize = CAPACITY + 1;
        let mut buf = [const { MaybeUninit::<u8>::uninit() }; N];
        let len = kani::any_where(|&l: &usize| l > 0 && l <= N);
        let idx = kani::any_where(|&i: &usize| i < len);
        init_buf(&mut buf, len);
        let _ = unsafe { slice_remove(&mut buf[..len], idx) };
    }

    #[kani::proof_for_contract(slice_shl)]
    #[kani::unwind(13)]
    fn check_slice_shl() {
        const N: usize = CAPACITY + 1;
        let mut buf = [const { MaybeUninit::<u8>::uninit() }; N];
        let len = kani::any_where(|&l: &usize| l <= N);
        let distance = kani::any_where(|&d: &usize| d <= len);
        init_buf(&mut buf, len);
        unsafe {
            slice_shl(&mut buf[..len], distance);
        }
    }

    #[kani::proof_for_contract(slice_shr)]
    #[kani::unwind(13)]
    fn check_slice_shr() {
        const N: usize = CAPACITY + 1;
        let mut buf = [const { MaybeUninit::<u8>::uninit() }; N];
        let len = kani::any_where(|&l: &usize| l <= N);
        let distance = kani::any_where(|&d: &usize| d <= len);
        init_buf(&mut buf, len);
        unsafe {
            slice_shr(&mut buf[..len], distance);
        }
    }

    #[kani::proof_for_contract(move_to_slice)]
    #[kani::unwind(13)]
    fn check_move_to_slice() {
        const N: usize = CAPACITY + 1;
        let mut src = [const { MaybeUninit::<u8>::uninit() }; N];
        let mut dst = [const { MaybeUninit::<u8>::uninit() }; N];
        let len = kani::any_where(|&l: &usize| l <= N);
        init_buf(&mut src, len);
        move_to_slice(&mut src[..len], &mut dst[..len]);
    }

    // --- Safe APIs that contain unsafe, symbolic occupancy ---

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_leaf_node_new() {
        let leaf = LeafNode::<u8, u8>::new(Global);
        assert!(leaf.len == 0);
        assert!(leaf.parent.is_none());
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_len() {
        let n = any_len();
        let node = leaf_with_len(n);
        assert!(node.len() == n);
        assert!(node.height() == 0);
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_first_last_edge() {
        let node = any_leaf();
        let first = node.reborrow().first_edge();
        assert!(first.idx() == 0);
        let last = node.reborrow().last_edge();
        assert!(last.idx() == node.len());
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_first_last_kv() {
        let node = any_nonempty_leaf();
        let first = node.reborrow().first_kv();
        assert!(first.idx() == 0);
        let last = node.reborrow().last_kv();
        assert!(last.idx() == node.len() - 1);
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_keys_and_into_leaf() {
        let node = any_leaf();
        let borrow = node.reborrow();
        let keys = borrow.keys();
        assert!(keys.len() == node.len());
        if !keys.is_empty() {
            let i = kani::any_where(|&i: &usize| i < keys.len());
            let _ = keys[i];
        }
        let leaf = borrow.into_leaf();
        assert!(usize::from(leaf.len) == node.len());
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_as_leaf_mut_and_into_leaf_mut() {
        let mut node = any_leaf();
        {
            let mut borrow = node.borrow_mut();
            let leaf = borrow.as_leaf_mut();
            let _ = leaf.len;
        }
        let leaf = node.borrow_mut().into_leaf_mut();
        let _ = leaf.len;
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_as_leaf_dying() {
        let node = any_leaf();
        let mut dying = node.into_dying();
        let leaf = dying.as_leaf_dying();
        let _ = leaf.len;
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_ascend_root_leaf() {
        let node = any_leaf();
        assert!(node.reborrow().ascend().is_err());
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_push_leaf() {
        let n = kani::any_where(|&n: &usize| n < CAPACITY);
        let mut node = leaf_with_len(n);
        let val = kani::any();
        let slot = node.borrow_mut().push(kani::any(), val);
        assert!(node.len() == n + 1);
        unsafe {
            assert!(*slot == val);
        }
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_left_right_edge() {
        let node = any_nonempty_leaf();
        let kv = node.reborrow().first_kv();
        let left = kv.left_edge();
        assert!(left.idx() == 0);
        let kv = node.reborrow().first_kv();
        let right = kv.right_edge();
        assert!(right.idx() == 1);
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_left_right_kv() {
        let node = any_nonempty_leaf();
        let last = node.reborrow().last_edge();
        assert!(last.left_kv().is_ok());
        let first = node.reborrow().first_edge();
        assert!(first.right_kv().is_ok());
        let first = node.reborrow().first_edge();
        assert!(first.left_kv().is_err());
        let last = node.reborrow().last_edge();
        assert!(last.right_kv().is_err());
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_into_kv() {
        let node = any_nonempty_leaf();
        let idx = kani::any_where(|&i: &usize| i < node.len());
        let handle = unsafe { Handle::new_kv(node.reborrow(), idx) };
        let (k, v) = handle.into_kv();
        let _ = (*k, *v);
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_key_mut() {
        let mut node = any_nonempty_leaf();
        let idx = kani::any_where(|&i: &usize| i < node.len());
        let mut handle = unsafe { Handle::new_kv(node.borrow_mut(), idx) };
        *handle.key_mut() = kani::any();
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_into_val_mut() {
        let mut node = any_nonempty_leaf();
        let idx = kani::any_where(|&i: &usize| i < node.len());
        let handle = unsafe { Handle::new_kv(node.borrow_mut(), idx) };
        let val = handle.into_val_mut();
        *val = kani::any();
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_into_kv_mut() {
        let mut node = any_nonempty_leaf();
        let idx = kani::any_where(|&i: &usize| i < node.len());
        let handle = unsafe { Handle::new_kv(node.borrow_mut(), idx) };
        let (k, v) = handle.into_kv_mut();
        *k = kani::any();
        *v = kani::any();
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_into_kv_valmut() {
        let mut node = any_nonempty_leaf();
        let idx = kani::any_where(|&i: &usize| i < node.len());
        let handle = unsafe { Handle::new_kv(node.borrow_valmut(), idx) };
        let (k, v) = handle.into_kv_valmut();
        let _ = *k;
        *v = kani::any();
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_kv_mut() {
        let mut node = any_nonempty_leaf();
        let idx = kani::any_where(|&i: &usize| i < node.len());
        let mut handle = unsafe { Handle::new_kv(node.borrow_mut(), idx) };
        let (k, v) = handle.kv_mut();
        *k = kani::any();
        *v = kani::any();
    }

    // --- Internal nodes ---

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_new_internal_and_as_internal_mut() {
        let child = any_leaf().forget_type();
        let mut internal = NodeRef::new_internal(child, Global);
        assert!(internal.height() == 1);
        assert!(internal.len() == 0);
        let mut borrow = internal.borrow_mut();
        let node = borrow.as_internal_mut();
        let _ = node.data.len;
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_descend_and_ascend() {
        let child_n = any_len();
        let internal = NodeRef::new_internal(leaf_with_len(child_n).forget_type(), Global);
        let edge = internal.reborrow().first_edge();
        let descended = edge.descend();
        assert!(descended.len() == child_n);
        assert!(descended.height() == 0);
        assert!(descended.ascend().is_ok());
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_pop_internal_level() {
        let mut root = NodeRef::new_internal(any_leaf().forget_type(), Global).forget_type();
        assert!(root.height() == 1);
        root.pop_internal_level(Global);
        assert!(root.height() == 0);
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_push_internal() {
        let mut parent = NodeRef::new_internal(any_leaf().forget_type(), Global);
        let old = parent.len();
        parent.borrow_mut().push(kani::any(), kani::any(), any_leaf().forget_type());
        assert!(parent.len() == old + 1);
    }

    // --- Recursion / loops ---

    #[kani::proof]
    #[kani::unwind(3)]
    fn check_insert_recursing_fit() {
        let n = kani::any_where(|&n: &usize| n < CAPACITY);
        let mut node = leaf_with_len(n);
        let idx = kani::any_where(|&i: &usize| i <= n);
        let edge = unsafe { Handle::new_edge(node.borrow_mut(), idx) };
        let handle = edge.insert_recursing(kani::any(), kani::any(), Global, |_| {});
        assert!(handle.into_node().len() == n + 1);
    }

    /// Full root leaf: the loop takes the `Err(root)` / `split_root` arm.
    /// Concrete idx/key so autoharness stays under the 10m CBMC cap.
    #[kani::proof]
    #[kani::unwind(3)]
    fn check_insert_recursing_split_root() {
        let mut node = leaf_with_len(CAPACITY);
        let edge = unsafe { Handle::new_edge(node.borrow_mut(), 0) };
        let _ = edge.insert_recursing(0u8, 0u8, Global, |_split| {});
    }

    /// Full child under a parent: the loop takes the `Ok(parent)` arm once.
    /// Unwind is 3 (not 13): a loop contract on `insert_recursing` would havoc
    /// `SplitResult` node pointers and OOM the autoharness job.
    /// Concrete idx/key so autoharness stays under the 10m CBMC cap.
    #[kani::proof]
    #[kani::unwind(3)]
    fn check_insert_recursing_into_parent() {
        let mut parent = NodeRef::new_internal(leaf_with_len(CAPACITY).forget_type(), Global);
        let child = parent.borrow_mut().first_edge().descend();
        let leaf = unsafe { child.cast_to_leaf_unchecked() };
        let edge = unsafe { Handle::new_edge(leaf, 0) };
        let _ = edge.insert_recursing(0u8, 0u8, Global, |_| {});
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_do_merge_via_merge_tracking_child_edge() {
        let left_n = any_len();
        let right_n = any_len();
        kani::assume(left_n.saturating_add(1).saturating_add(right_n) <= CAPACITY);
        let mut parent = parent_with_leaves(left_n, right_n);
        let ctx = parent.borrow_mut().first_kv().consider_for_balancing();
        let track = kani::any_where(|&i: &usize| i <= left_n);
        let edge = ctx.merge_tracking_child_edge(LeftOrRight::Left(track), Global);
        assert!(edge.idx() == track);
        assert!(edge.into_node().len() == left_n.saturating_add(1).saturating_add(right_n));
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_steal_left() {
        let left_n = kani::any_where(|&n: &usize| n >= 1 && n <= CAPACITY);
        let right_n = kani::any_where(|&n: &usize| n < CAPACITY);
        let track = kani::any_where(|&i: &usize| i <= right_n);
        let mut parent = parent_with_leaves(left_n, right_n);
        let ctx = parent.borrow_mut().first_kv().consider_for_balancing();
        let edge = ctx.steal_left(track);
        assert!(edge.idx() == 1 + track);
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_steal_right() {
        let left_n = kani::any_where(|&n: &usize| n < CAPACITY);
        let right_n = kani::any_where(|&n: &usize| n >= 1 && n <= CAPACITY);
        let track = kani::any_where(|&i: &usize| i <= left_n);
        let mut parent = parent_with_leaves(left_n, right_n);
        let ctx = parent.borrow_mut().first_kv().consider_for_balancing();
        let edge = ctx.steal_right(track);
        assert!(edge.idx() == track);
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_bulk_steal_left() {
        let count = kani::any_where(|&c: &usize| c > 0 && c <= CAPACITY);
        let left_n = kani::any_where(|&n: &usize| n >= count && n <= CAPACITY);
        let right_n = kani::any_where(|&n: &usize| n <= CAPACITY.saturating_sub(count));
        let mut parent = parent_with_leaves(left_n, right_n);
        let mut ctx = parent.borrow_mut().first_kv().consider_for_balancing();
        ctx.bulk_steal_left(count);
        assert!(ctx.left_child_len() == left_n.saturating_sub(count));
        assert!(ctx.right_child_len() == right_n.saturating_add(count));
    }

    #[kani::proof]
    #[kani::unwind(13)]
    fn check_bulk_steal_right() {
        let count = kani::any_where(|&c: &usize| c > 0 && c <= CAPACITY);
        let left_n = kani::any_where(|&n: &usize| n <= CAPACITY.saturating_sub(count));
        let right_n = kani::any_where(|&n: &usize| n >= count && n <= CAPACITY);
        let mut parent = parent_with_leaves(left_n, right_n);
        let mut ctx = parent.borrow_mut().first_kv().consider_for_balancing();
        ctx.bulk_steal_right(count);
        assert!(ctx.left_child_len() == left_n.saturating_add(count));
        assert!(ctx.right_child_len() == right_n.saturating_sub(count));
    }
}
