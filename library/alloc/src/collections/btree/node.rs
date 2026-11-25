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

use safety::{ensures, requires};

use crate::alloc::{Allocator, AllocatorClone, Layout};
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
    #[ensures(|_| unsafe { (*this).parent.is_none() })]
    #[ensures(|_| unsafe { (*this).len == 0 })]
    #[cfg_attr(kani, kani::modifies(this))]
    unsafe fn init(this: *mut Self) {
        // As a general policy, we leave fields uninitialized if they can be, as this should
        // be both slightly faster and easier to track in Valgrind.
        // ignore-tidy-undocumented-unsafe
        unsafe {
            // parent_idx, keys, and vals are all MaybeUninit
            (&raw mut (*this).parent).write(None);
            (&raw mut (*this).len).write(0);
        }
    }

    /// Creates a new boxed `LeafNode`.
    fn new<A: AllocatorClone>(alloc: A) -> Box<Self, A> {
        let mut leaf = Box::new_uninit_in(alloc);

        // SAFETY: `leaf` points to a `LeafNode`.
        unsafe { LeafNode::init(leaf.as_mut_ptr()) };
        // SAFETY: `leaf` was just initialized.
        unsafe { leaf.assume_init() }
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
    unsafe fn new<A: AllocatorClone>(alloc: A) -> Box<Self, A> {
        let mut node = Box::<Self, _>::new_uninit_in(alloc);

        // SAFETY: argument points to the `node.data` `LeafNode`.
        unsafe { LeafNode::init(&raw mut (*node.as_mut_ptr()).data) };
        // SAFETY: `node.data` was just initialized and `node.edges` is MaybeUninit.
        unsafe { node.assume_init() }
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
    pub(super) fn new_leaf<A: AllocatorClone>(alloc: A) -> Self {
        Self::from_new_leaf(LeafNode::new(alloc))
    }

    fn from_new_leaf<A: AllocatorClone>(leaf: Box<LeafNode<K, V>, A>) -> Self {
        // The allocator must be dropped, not leaked.  See also `BTreeMap::alloc`.
        let (node, _alloc) = Box::into_non_null_with_allocator(leaf);
        NodeRef { height: 0, node, _marker: PhantomData }
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Internal> {
    /// Creates a new internal (height > 0) `NodeRef`
    fn new_internal<A: AllocatorClone>(child: Root<K, V>, alloc: A) -> Self {
        // ignore-tidy-undocumented-unsafe
        let mut new_node = unsafe { InternalNode::new(alloc) };
        new_node.edges[0].write(child.node);
        NodeRef::from_new_internal(new_node, NonZero::new(child.height + 1).unwrap())
    }

    /// Creates a new internal (height > 0) `NodeRef` from an existing internal node
    fn from_new_internal<A: AllocatorClone>(
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
        // ignore-tidy-undocumented-unsafe
        unsafe { &mut *ptr }
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    /// Finds the length of the node. This is the number of keys or values.
    /// The number of edges is `len() + 1`.
    /// Note that, despite being safe, calling this function can have the side effect
    /// of invalidating mutable references that unsafe code has created.
    pub(super) fn len(&self) -> usize {
        // SAFETY: We only access the `len` field here. If BorrowType is marker::ValMut,
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
    #[requires(verify::can_ascend(&self))]
    #[ensures(|result| {
        let original_node = old(self.node);
        let original_height = old(self.height);
        match (old(verify::ascend_link(&self)), result) {
            (Some((parent, idx)), Ok(edge)) => {
                edge.node.node == parent.cast()
                    && edge.node.height == original_height + 1
                    && edge.idx == idx
            }
            (None, Err(root)) => root.node == original_node && root.height == original_height,
            _ => false,
        }
    })]
    pub(super) fn ascend(
        self,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge>, Self> {
        const {
            assert!(BorrowType::TRAVERSAL_PERMIT);
        }

        // We need to use raw pointers to nodes because, if BorrowType is marker::ValMut,
        // there might be outstanding mutable references to values that we must not invalidate.
        let leaf_ptr: *const _ = Self::as_leaf_ptr(&self);
        // ignore-tidy-undocumented-unsafe
        unsafe { (*leaf_ptr).parent }
            .as_ref()
            .map(|parent| Handle {
                node: NodeRef::from_internal(*parent, self.height + 1),
                // ignore-tidy-undocumented-unsafe
                idx: unsafe { usize::from((*leaf_ptr).parent_idx.assume_init()) },
                _marker: PhantomData,
            })
            .ok_or(self)
    }

    pub(super) fn first_edge(self) -> Handle<Self, marker::Edge> {
        // ignore-tidy-undocumented-unsafe
        unsafe { Handle::new_edge(self, 0) }
    }

    pub(super) fn last_edge(self) -> Handle<Self, marker::Edge> {
        let len = self.len();
        // ignore-tidy-undocumented-unsafe
        unsafe { Handle::new_edge(self, len) }
    }

    /// Note that `self` must be nonempty.
    pub(super) fn first_kv(self) -> Handle<Self, marker::KV> {
        let len = self.len();
        assert!(len > 0);
        // ignore-tidy-undocumented-unsafe
        unsafe { Handle::new_kv(self, 0) }
    }

    /// Note that `self` must be nonempty.
    pub(super) fn last_kv(self) -> Handle<Self, marker::KV> {
        let len = self.len();
        assert!(len > 0);
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
        unsafe { leaf.keys.get_unchecked(..usize::from(leaf.len)).assume_init_ref() }
    }
}

impl<K, V> NodeRef<marker::Dying, K, V, marker::LeafOrInternal> {
    /// Similar to `ascend`, gets a reference to a node's parent node, but also
    /// deallocates the current node in the process. This is unsafe because the
    /// current node will still be accessible despite being deallocated.
    pub(super) unsafe fn deallocate_and_ascend<A: AllocatorClone>(
        self,
        alloc: A,
    ) -> Option<Handle<NodeRef<marker::Dying, K, V, marker::Internal>, marker::Edge>> {
        let height = self.height;
        let node = self.node;
        let ret = self.ascend().ok();
        // ignore-tidy-undocumented-unsafe
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
    /// Drops all kvs in this node without deallocating the node itself
    ///
    /// # Safety
    ///
    /// - kvs in the node must be initialized and must not be accessed after this call.
    /// - No kvs in the node can be accessed through any other path while this function is running.
    pub(super) unsafe fn drop_kvs(&mut self) {
        struct DropGuard<'a, K, V> {
            node: &'a NodeRef<marker::Dying, K, V, marker::LeafOrInternal>,
            idx: usize,
        }
        impl<'a, K, V> Drop for DropGuard<'a, K, V> {
            fn drop(&mut self) {
                let len = self.node.len();
                for i in self.idx..len {
                    // SAFETY: i < len and the kv has been initialized and
                    // it won't use the i-th kv more than once.
                    unsafe {
                        let kv = Handle::new_kv(ptr::read(self.node), i);
                        kv.drop_key_val();
                    }
                }
            }
        }
        let len = self.len();
        for idx in 0..len {
            // If `kv.drop_key_val()` panics, the guard would drop
            // the rest and skip the panicked kv.
            let guard = DropGuard { node: self, idx: idx + 1 };
            // SAFETY: idx < len and the kv has been initialized and
            // it won't touch the idx-th more than once
            unsafe {
                let kv = Handle::new_kv(ptr::read(self), idx);
                kv.drop_key_val();
            }

            core::mem::forget(guard);
        }
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
        // ignore-tidy-undocumented-unsafe
        let keys = unsafe { &raw const (*leaf).keys };
        // ignore-tidy-undocumented-unsafe
        let vals = unsafe { &raw mut (*leaf).vals };
        // We must coerce to unsized array pointers because of Rust issue #74679.
        let keys: *const [_] = keys;
        let vals: *mut [_] = vals;
        // ignore-tidy-undocumented-unsafe
        let key = unsafe { (&*keys.get_unchecked(idx)).assume_init_ref() };
        // ignore-tidy-undocumented-unsafe
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
            // ignore-tidy-undocumented-unsafe
            unsafe { Handle::new_edge(self.reborrow_mut(), i) }.correct_parent_link();
        }
    }

    fn correct_all_childrens_parent_links(&mut self) {
        let len = self.len();
        // ignore-tidy-undocumented-unsafe
        unsafe { self.correct_childrens_parent_links(0..=len) };
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    /// Sets the node's link to its parent edge,
    /// without invalidating other references to the node.
    fn set_parent_link(&mut self, parent: NonNull<InternalNode<K, V>>, parent_idx: usize) {
        let leaf = Self::as_leaf_ptr(self);
        // ignore-tidy-undocumented-unsafe
        unsafe { (*leaf).parent = Some(parent) };
        // ignore-tidy-undocumented-unsafe
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
    pub(super) fn new<A: AllocatorClone>(alloc: A) -> Self {
        NodeRef::new_leaf(alloc).forget_type()
    }

    /// Adds a new internal node with a single edge pointing to the previous root node,
    /// make that new node the root node, and return it. This increases the height by 1
    /// and is the opposite of `pop_internal_level`.
    pub(super) fn push_internal_level<A: AllocatorClone>(
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
    pub(super) fn pop_internal_level<A: AllocatorClone>(&mut self, alloc: A) {
        assert!(self.height > 0);

        let top = self.node;

        // SAFETY: we asserted to be internal.
        let mut internal_self = unsafe { self.borrow_mut().cast_to_internal_unchecked() };
        let internal_node = internal_self.as_internal_mut();
        // SAFETY: the first edge is always initialized.
        self.node = unsafe { internal_node.edges[0].assume_init_read() };
        self.height -= 1;
        self.clear_parent_link();

        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
        unsafe { Handle::new_edge(self.node, self.idx) }
    }

    pub(super) fn right_edge(self) -> Handle<NodeRef<BorrowType, K, V, NodeType>, marker::Edge> {
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
            // ignore-tidy-undocumented-unsafe
            Ok(unsafe { Handle::new_kv(self.node, self.idx - 1) })
        } else {
            Err(self)
        }
    }

    pub(super) fn right_kv(
        self,
    ) -> Result<Handle<NodeRef<BorrowType, K, V, NodeType>, marker::KV>, Self> {
        if self.idx < self.node.len() {
            // ignore-tidy-undocumented-unsafe
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

        // ignore-tidy-undocumented-unsafe
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
    fn insert<A: AllocatorClone>(
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
            // ignore-tidy-undocumented-unsafe
            let middle = unsafe { Handle::new_kv(self.node, middle_kv_idx) };
            let mut result = middle.split(alloc);
            let insertion_edge = match insertion {
                // ignore-tidy-undocumented-unsafe
                LeftOrRight::Left(insert_idx) => unsafe {
                    Handle::new_edge(result.left.reborrow_mut(), insert_idx)
                },
                // ignore-tidy-undocumented-unsafe
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
    #[requires(verify::can_relink(&self.node, self.idx))]
    #[ensures(|_| verify::has_parent_link(
        old(verify::relink_child(&self.node, self.idx)), old(self.node.node.cast()), old(self.idx),
    ))]
    #[cfg_attr(kani, kani::modifies(
        unsafe { &raw mut (*verify::relink_child(&self.node, self.idx)).parent },
        unsafe { &raw mut (*verify::relink_child(&self.node, self.idx)).parent_idx },
    ))]
    fn correct_parent_link(self) {
        // Create backpointer without invalidating other references to the node.
        // ignore-tidy-undocumented-unsafe
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

        // ignore-tidy-undocumented-unsafe
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
    fn insert<A: AllocatorClone>(
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
            // ignore-tidy-undocumented-unsafe
            let middle = unsafe { Handle::new_kv(self.node, middle_kv_idx) };
            let mut result = middle.split(alloc);
            let mut insertion_edge = match insertion {
                // ignore-tidy-undocumented-unsafe
                LeftOrRight::Left(insert_idx) => unsafe {
                    Handle::new_edge(result.left.reborrow_mut(), insert_idx)
                },
                // ignore-tidy-undocumented-unsafe
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
    pub(super) fn insert_recursing<A: AllocatorClone>(
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
        // ignore-tidy-undocumented-unsafe
        let node = unsafe { (*parent_ptr).edges.get_unchecked(self.idx).assume_init_read() };
        NodeRef { node, height: self.node.height - 1, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Immut<'a>, K, V, NodeType>, marker::KV> {
    pub(super) fn into_kv(self) -> (&'a K, &'a V) {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf();
        // ignore-tidy-undocumented-unsafe
        let k = unsafe { leaf.keys.get_unchecked(self.idx).assume_init_ref() };
        // ignore-tidy-undocumented-unsafe
        let v = unsafe { leaf.vals.get_unchecked(self.idx).assume_init_ref() };
        (k, v)
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    pub(super) fn key_mut(&mut self) -> &mut K {
        // ignore-tidy-undocumented-unsafe
        unsafe { self.node.key_area_mut(self.idx).assume_init_mut() }
    }

    pub(super) fn into_val_mut(self) -> &'a mut V {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf_mut();
        // ignore-tidy-undocumented-unsafe
        unsafe { leaf.vals.get_unchecked_mut(self.idx).assume_init_mut() }
    }

    pub(super) fn into_kv_mut(self) -> (&'a mut K, &'a mut V) {
        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.into_leaf_mut();
        // ignore-tidy-undocumented-unsafe
        let k = unsafe { leaf.keys.get_unchecked_mut(self.idx).assume_init_mut() };
        // ignore-tidy-undocumented-unsafe
        let v = unsafe { leaf.vals.get_unchecked_mut(self.idx).assume_init_mut() };
        (k, v)
    }
}

impl<'a, K, V, NodeType> Handle<NodeRef<marker::ValMut<'a>, K, V, NodeType>, marker::KV> {
    pub(super) fn into_kv_valmut(self) -> (&'a K, &'a mut V) {
        // ignore-tidy-undocumented-unsafe
        unsafe { self.node.into_key_val_mut_at(self.idx) }
    }
}

impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    pub(super) fn kv_mut(&mut self) -> (&mut K, &mut V) {
        debug_assert!(self.idx < self.node.len());
        // We cannot call separate key and value methods, because calling the second one
        // invalidates the reference returned by the first.
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
                // ignore-tidy-undocumented-unsafe
                unsafe {
                    self.0.assume_init_drop();
                }
            }
        }

        debug_assert!(self.idx < self.node.len());
        let leaf = self.node.as_leaf_dying();
        // ignore-tidy-undocumented-unsafe
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
    #[requires(verify::can_split_leaf_data(&self.node, self.idx, new_node))]
    #[ensures(|_| {
        self.node.len() == old(self.idx)
            && usize::from(new_node.len) == old(self.node.len() - self.idx - 1)
    })]
    #[cfg_attr(kani, kani::modifies(
        unsafe { &raw mut (*NodeRef::as_leaf_ptr(&self.node)).len },
        &raw mut new_node.len,
        &raw mut new_node.keys,
        &raw mut new_node.vals,
    ))]
    fn split_leaf_data(&mut self, new_node: &mut LeafNode<K, V>) -> (K, V) {
        debug_assert!(self.idx < self.node.len());
        let old_len = self.node.len();
        let new_len = old_len - self.idx - 1;
        new_node.len = new_len as u16;
        // ignore-tidy-undocumented-unsafe
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
    pub(super) fn split<A: AllocatorClone>(
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
        // ignore-tidy-undocumented-unsafe
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
    pub(super) fn split<A: AllocatorClone>(
        mut self,
        alloc: A,
    ) -> SplitResult<'a, K, V, marker::Internal> {
        let old_len = self.node.len();
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
        let self1 = unsafe { ptr::read(&self) };
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
        match unsafe { ptr::read(&self) }.ascend() {
            Ok(parent_edge) => match parent_edge.left_kv() {
                Ok(left_parent_kv) => Ok(LeftOrRight::Left(BalancingContext {
                    // ignore-tidy-undocumented-unsafe
                    parent: unsafe { ptr::read(&left_parent_kv) },
                    left_child: left_parent_kv.left_edge().descend(),
                    right_child: self,
                })),
                Err(parent_edge) => match parent_edge.right_kv() {
                    Ok(right_parent_kv) => Ok(LeftOrRight::Right(BalancingContext {
                        // ignore-tidy-undocumented-unsafe
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

        // ignore-tidy-undocumented-unsafe
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

            slice_remove(parent_node.edge_area_mut(..old_parent_len + 1), parent_idx + 1);
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
    pub(super) fn merge_tracking_parent<A: AllocatorClone>(
        self,
        alloc: A,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
        self.do_merge(|parent, _child| parent, alloc)
    }

    /// Merges the parent's key-value pair and both adjacent child nodes into
    /// the left child node and returns that child node.
    ///
    /// Panics unless we `.can_merge()`.
    pub(super) fn merge_tracking_child<A: AllocatorClone>(
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
    pub(super) fn merge_tracking_child_edge<A: AllocatorClone>(
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
        unsafe { Handle::new_edge(self.left_child, track_left_edge_idx) }
    }

    /// This does stealing similar to `steal_left` but steals multiple elements at once.
    pub(super) fn bulk_steal_left(&mut self, count: usize) {
        assert!(count > 0);
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
        unsafe { Handle::new_edge(self.node.forget_type(), self.idx) }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge> {
    pub(super) fn forget_node_type(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::Edge> {
        // ignore-tidy-undocumented-unsafe
        unsafe { Handle::new_edge(self.node.forget_type(), self.idx) }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::KV> {
    pub(super) fn forget_node_type(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::KV> {
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
        // ignore-tidy-undocumented-unsafe
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
#[cfg_attr(kani, kani::modifies(ptr::slice_from_raw_parts_mut(
    unsafe { slice.as_mut_ptr().add(idx) },
    slice.len() - idx,
)))]
unsafe fn slice_insert<T>(slice: &mut [MaybeUninit<T>], idx: usize, val: T) {
    let len = slice.len();
    debug_assert!(len > idx);
    let slice_ptr = slice.as_mut_ptr();
    // ignore-tidy-undocumented-unsafe
    unsafe {
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
    let len = slice.len();
    debug_assert!(idx < len);
    let slice_ptr = slice.as_mut_ptr();
    // ignore-tidy-undocumented-unsafe
    unsafe {
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
    let slice_ptr = slice.as_mut_ptr();
    // ignore-tidy-undocumented-unsafe
    unsafe {
        ptr::copy(slice_ptr.add(distance), slice_ptr, slice.len() - distance);
    }
}

/// Shifts the elements in a slice `distance` positions to the right.
///
/// # Safety
/// The slice has at least `distance` elements.
unsafe fn slice_shr<T>(slice: &mut [MaybeUninit<T>], distance: usize) {
    let slice_ptr = slice.as_mut_ptr();
    // ignore-tidy-undocumented-unsafe
    unsafe {
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
    // ignore-tidy-undocumented-unsafe
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
#[unstable(feature = "kani", issue = "none")]
mod verify {
    use core::cell::Cell;

    use super::*;
    use crate::alloc::{AllocError, Global};

    type OwnedLeaf = NodeRef<marker::Owned, u8, u8, marker::Leaf>;
    type OwnedInternal = NodeRef<marker::Owned, u8, u8, marker::Internal>;

    const fn empty_leaf<K, V>() -> LeafNode<K, V> {
        LeafNode {
            parent: None,
            parent_idx: MaybeUninit::uninit(),
            len: 0,
            keys: [const { MaybeUninit::uninit() }; CAPACITY],
            vals: [const { MaybeUninit::uninit() }; CAPACITY],
        }
    }

    const fn empty_internal<K, V>() -> InternalNode<K, V> {
        InternalNode { data: empty_leaf(), edges: [const { MaybeUninit::uninit() }; CAPACITY + 1] }
    }

    fn borrow_leaf<K, V>(
        leaf: &mut LeafNode<K, V>,
    ) -> NodeRef<marker::Mut<'_>, K, V, marker::Leaf> {
        NodeRef { height: 0, node: NonNull::from_mut(leaf), _marker: PhantomData }
    }

    #[derive(Default)]
    struct TrackingAllocator {
        freed: Cell<Option<(NonNull<u8>, Layout)>>,
    }

    // SAFETY: Global handles allocation and deallocation. Bookkeeping does not affect live allocations.
    unsafe impl Allocator for TrackingAllocator {
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            Global.allocate(layout)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            // SAFETY: The caller provides a live allocation and its layout.
            unsafe { Global.deallocate(ptr, layout) };
            self.freed.set(Some((ptr, layout)));
        }
    }

    fn leaf_with_len(len: usize) -> OwnedLeaf {
        OwnedLeaf::from_new_leaf(Box::new(leaf_for_insertion(len)))
    }

    // Initialize exactly the live prefix in bulk, including when len is symbolic.
    fn leaf_for_insertion(len: usize) -> LeafNode<u8, u8> {
        assert!(len <= CAPACITY);
        let mut leaf = empty_leaf();
        let keys = kani::any::<[u8; CAPACITY]>();
        let vals = kani::any::<[u8; CAPACITY]>();
        // SAFETY: The arrays have the same capacity. The source bytes are initialized and the
        // destination prefixes are separate storage.
        unsafe {
            ptr::copy_nonoverlapping(keys.as_ptr(), leaf.keys.as_mut_ptr().cast(), len);
            ptr::copy_nonoverlapping(vals.as_ptr(), leaf.vals.as_mut_ptr().cast(), len);
        }
        leaf.len = len as u16;
        leaf
    }

    /// Constructs a leaf with a Kani-selected length in the complete legal range
    /// `0..=CAPACITY`. The owned node has a live allocation, a detached header,
    /// and exactly len initialized key/value slots.
    /// Key/value contents are symbolic; this helper is used for structural and memory-safety
    /// properties rather than position-sensitive content checks.
    fn verifier_leaf() -> (OwnedLeaf, usize) {
        let len = kani::any_where(|len: &usize| *len <= CAPACITY);
        (leaf_with_len(len), len)
    }

    /// Constructs a non-empty leaf with a Kani-selected length in `1..=CAPACITY`.
    /// A non-empty fixture is required by APIs such as `first_kv` and `last_kv`,
    /// whose precondition is that at least one key/value is initialized.
    fn verifier_nonempty_leaf() -> (OwnedLeaf, usize) {
        let len = kani::any_where(|len: &usize| *len > 0 && *len <= CAPACITY);
        (leaf_with_len(len), len)
    }

    fn internal_root_with_child<K, V, A: AllocatorClone>(
        child: Root<K, V>,
        alloc: A,
    ) -> NodeRef<marker::Owned, K, V, marker::Internal> {
        let height = child.height + 1;
        // SAFETY: The fixture initializes the first edge before using the internal node.
        let mut parent = unsafe { InternalNode::new(alloc) };
        parent.edges[0].write(child.node);
        let (parent, _alloc) = Box::into_non_null_with_allocator(parent);
        let mut parent = NodeRef::from_internal(parent, height);
        parent.borrow_mut().first_edge().correct_parent_link();
        parent
    }

    // Use disjoint leaf subobjects for proofs that only relink the existing children. They live
    // through the whole call. Operations that deallocate a child must first give that edge a
    // separately allocated node.
    fn internal_with_borrowed_children<'a, K: kani::Arbitrary + Copy, V: kani::Arbitrary + Copy>(
        parent: &'a mut InternalNode<K, V>,
        children: &'a mut [LeafNode<K, V>; CAPACITY + 1],
        len: usize,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
        assert!(len <= CAPACITY);
        const { assert!(CAPACITY == 11) };
        let keys = kani::any::<[K; CAPACITY]>();
        let vals = kani::any::<[V; CAPACITY]>();
        let parent = NonNull::from_mut(parent);
        let parent_ptr = parent.as_ptr();
        let child_ptr = children.as_mut_ptr();
        let link_child = move |i: usize| {
            // SAFETY: Each call initializes a distinct live child and a distinct edge in the
            // separately borrowed parent.
            unsafe {
                let child = &mut *child_ptr.add(i);
                child.parent = Some(parent);
                child.parent_idx.write(i as u16);
                (*parent_ptr).edges[i].write(NonNull::from_mut(child));
            }
        };
        link_child(0);
        macro_rules! initialize_entries {
            ($($i:literal),*) => {
                $(if $i < len {
                    // SAFETY: The parent is live and exclusively borrowed by the fixture.
                    let data = unsafe { &mut (*parent_ptr).data };
                    data.keys[$i].write(keys[$i]);
                    data.vals[$i].write(vals[$i]);
                    link_child($i + 1);
                })*
            };
        }
        initialize_entries!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
        // SAFETY: All live key, value, and edge slots of the owned parent storage are initialized.
        unsafe { (*parent_ptr).data.len = len as u16 };
        NodeRef::from_internal(parent, 1)
    }

    pub(super) fn ascend_link<BorrowType, K, V, Type>(
        node: &NodeRef<BorrowType, K, V, Type>,
    ) -> Option<(NonNull<InternalNode<K, V>>, usize)> {
        let child = NodeRef::as_leaf_ptr(node);
        // SAFETY: The precondition checks the child and, if attached, the backlink index.
        unsafe { (*child).parent.map(|parent| (parent, (*child).parent_idx.assume_init().into())) }
    }

    pub(super) fn can_ascend<BorrowType, K, V, Type>(
        node: &NodeRef<BorrowType, K, V, Type>,
    ) -> bool {
        let child = NodeRef::as_leaf_ptr(node);
        // SAFETY: The raw field addresses are formed within the live child prefix. The index
        // is only read when a parent is present and its value can be read as a u16.
        unsafe {
            core::ub_checks::can_dereference(child)
                && ((*child).parent.is_none()
                    || (node.height < usize::MAX
                        && core::ub_checks::can_dereference((*child).parent_idx.as_ptr())))
        }
    }

    pub(super) fn can_split_leaf_data<K, V, Type>(
        node: &NodeRef<marker::Mut<'_>, K, V, Type>,
        pivot: usize,
        destination: &LeafNode<K, V>,
    ) -> bool {
        let source = NodeRef::as_leaf_ptr(node);
        // Both split callers allocate a fresh node for the destination.
        // SAFETY: Once the leaf prefix is accessible and the pivot is in range, its key and
        // value slot addresses can be checked as pointers to initialized K and V.
        unsafe {
            core::ub_checks::can_write(source)
                && core::ub_checks::can_dereference(source)
                && !core::ub_checks::same_allocation(source, ptr::from_ref(destination))
                && pivot < node.len()
                && node.len() <= CAPACITY
                && core::ub_checks::can_dereference((*source).keys[pivot].as_ptr())
                && core::ub_checks::can_dereference((*source).vals[pivot].as_ptr())
        }
    }

    // Relinking uses only the initialized edge and the child's LeafNode prefix. The child can
    // be a leaf or an internal node, and its old backlink is allowed to be stale.
    pub(super) fn can_relink<K, V>(
        node: &NodeRef<marker::Mut<'_>, K, V, marker::Internal>,
        idx: usize,
    ) -> bool {
        let ptr = NodeRef::as_internal_ptr(node);
        node.height() > 0
            && core::ub_checks::can_dereference(ptr)
            && idx <= node.len()
            && node.len() <= CAPACITY
            // SAFETY: The parent is accessible and idx is within its edge array.
            && core::ub_checks::can_dereference(unsafe { (*ptr).edges[idx].as_ptr() })
            && core::ub_checks::can_write(relink_child(node, idx))
    }

    pub(super) fn relink_child<K, V>(
        node: &NodeRef<marker::Mut<'_>, K, V, marker::Internal>,
        idx: usize,
    ) -> *mut LeafNode<K, V> {
        let ptr = NodeRef::as_internal_ptr(node);
        // SAFETY: The contract checks that the internal node and the selected edge are valid.
        unsafe { (*ptr).edges[idx].assume_init_read().as_ptr() }
    }

    pub(super) fn has_parent_link<K, V>(
        child: *const LeafNode<K, V>,
        parent: NonNull<InternalNode<K, V>>,
        idx: usize,
    ) -> bool {
        core::ub_checks::can_dereference(child)
            // SAFETY: The child is live, and a present backlink includes an initialized index.
            && unsafe {
                (*child).parent == Some(parent)
                    && usize::from((*child).parent_idx.assume_init()) == idx
            }
    }

    #[kani::proof_for_contract(
        Handle::<NodeRef<marker::Mut<'_>, u8, u8, marker::Internal>, marker::Edge>::correct_parent_link
    )]
    fn harness_correct_parent_link() {
        check_parent_link_contract::<u8, u8>();
    }

    #[kani::proof_for_contract(
        Handle::<NodeRef<marker::Mut<'_>, (), (), marker::Internal>, marker::Edge>::correct_parent_link
    )]
    fn harness_correct_parent_link_unit() {
        check_parent_link_contract::<(), ()>();
    }

    fn check_parent_link_contract<K, V>() {
        let len = kani::any_where(|len: &usize| *len <= CAPACITY);
        let idx = kani::any_where(|idx: &usize| *idx <= len);
        let height = kani::any_where(|h: &usize| *h > 0);
        let child = NodeRef::<marker::Owned, K, V, marker::Leaf>::new_leaf(Global);
        // SAFETY: Only the selected edge is required by the single-edge repair contract.
        let mut parent = unsafe { InternalNode::new(Global) };
        parent.data.len = len as u16;
        parent.edges[idx].write(child.node);
        let parent_ptr = NonNull::from_mut(&mut *parent);
        let parent = NodeRef::from_internal(parent_ptr, height);
        // SAFETY: The chosen index is in the initialized edge prefix.
        unsafe { Handle::new_edge(parent, idx) }.correct_parent_link();
        assert!(has_parent_link(child.node.as_ptr(), parent_ptr, idx));
        kani::cover(idx == CAPACITY && height > 1, "relink the last edge above the leaf level");
    }

    // Checks the usize instance of the conversions used by the VeriFast root proof.
    #[kani::proof]
    fn harness_new_internal_height_conversion() {
        let height: usize = kani::any();
        match NonZero::new(height) {
            None => {
                assert_eq!(height, 0);
                kani::cover(true, "zero has no NonZero representation");
            }
            Some(nonzero) => {
                assert_ne!(height, 0);
                let converted: usize = nonzero.into();
                assert_eq!(converted, height);
                // SAFETY: This branch establishes that height is nonzero.
                let unchecked = unsafe { NonZero::new_unchecked(height) };
                assert_eq!(usize::from(unchecked), height);
                kani::cover(height == usize::MAX, "round-trip the largest representable height");
            }
        }
    }

    // The shared loop proof also uses the production inclusive iterator. Its specification
    // covers ranges whose end is below usize::MAX, including the empty state after returning
    // the last item.
    #[kani::proof]
    fn harness_relink_inclusive_range_next() {
        let start = kani::any::<usize>();
        let end = kani::any_where(|end: &usize| *end < usize::MAX);
        let range = start..=end;
        let mut iter = IntoIterator::into_iter(range.clone());
        assert_eq!(iter, range);
        if start <= end {
            assert_eq!(iter.next(), Some(start));
            assert_eq!(iter, start + 1..=end);
        } else {
            assert_eq!(iter.next(), None);
            assert_eq!(iter, range);
        }
        kani::cover(start == end && end == CAPACITY, "yield the last valid child edge");
        kani::cover(start > end, "an empty range leaves the iterator unchanged");
    }

    fn assert_edge_child(
        parent: NodeRef<marker::Immut<'_>, u8, u8, marker::Internal>,
        idx: usize,
        expected: BoxedNode<u8, u8>,
    ) {
        assert!(idx <= parent.len());
        // SAFETY: The assertions in the caller establish the initialized edge prefix.
        let child = unsafe { Handle::new_edge(parent, idx) }.descend();
        assert_eq!(child.node, expected);
        assert_eq!(child.height(), parent.height() - 1);
        let backlink = child.ascend().ok().unwrap();
        assert_eq!(backlink.idx(), idx);
        assert_eq!(backlink.into_node().node, parent.node);
    }

    // Harness for `LeafNode::init`.
    #[kani::proof_for_contract(LeafNode::init)]
    fn harness_leaf_node_init() {
        let mut leaf = Box::<LeafNode<u8, u8>, _>::new_uninit_in(Global);
        unsafe {
            LeafNode::init(leaf.as_mut_ptr());
            kani::cover(true, "LeafNode::init was called");
        }
    }

    // Harness for `LeafNode::new`.
    #[kani::proof]
    fn harness_leaf_node_new() {
        let leaf = LeafNode::<u8, u8>::new(Global);
        assert!(leaf.parent.is_none());
        assert_eq!(leaf.len, 0);
        kani::cover(true, "LeafNode::new returned an initialized empty leaf");
    }

    // Harness for `InternalNode::new`.
    //
    // `InternalNode::new` initializes only the embedded `LeafNode` portion. The
    // edge array intentionally remains `MaybeUninit`; this harness therefore
    // checks the initialized metadata and does not read any edge slot.
    #[kani::proof]
    fn harness_internal_node_new() {
        let node = unsafe { InternalNode::<u8, u8>::new(Global) };

        assert!(node.data.parent.is_none());
        assert_eq!(node.data.len, 0);
        kani::cover(true, "InternalNode::new returned initialized metadata");
    }

    // Harness for `NodeRef::as_internal_mut`.
    #[kani::proof]
    fn harness_node_ref_as_internal_mut() {
        let len = kani::any_where(|n: &usize| *n <= CAPACITY);
        let mut parent = empty_internal::<u8, u8>();
        let mut children = [const { empty_leaf() }; CAPACITY + 1];
        let mut internal_view = internal_with_borrowed_children(&mut parent, &mut children, len);
        let node = internal_view.as_internal_mut();
        assert_eq!(node.data.len, len as u16);
        kani::cover(len == 0, "as_internal_mut checked an empty internal node");
        kani::cover(len == CAPACITY, "as_internal_mut checked a full internal node");
    }

    // Harness for `NodeRef::len`.
    #[kani::proof]
    fn harness_node_ref_len() {
        let (root, len) = verifier_leaf();
        assert_eq!(root.len(), len);
        kani::cover(len == 0, "len checked an empty leaf");
        kani::cover(len == CAPACITY, "len checked a full leaf");

        let mut parent = empty_internal::<u8, u8>();
        let mut children = [const { empty_leaf() }; CAPACITY + 1];
        let root = internal_with_borrowed_children(&mut parent, &mut children, len);
        assert_eq!(root.len(), len);
        kani::cover(len == 0, "len checked the prefix of an empty internal node");
        kani::cover(len == CAPACITY, "len checked the prefix of a full internal node");
    }

    // Harness for `NodeRef::first_edge`.
    #[kani::proof]
    fn harness_node_ref_first_edge() {
        let (root, len) = verifier_leaf();
        let edge = root.first_edge();
        assert_eq!(edge.idx(), 0);
        kani::cover(len == 0, "first_edge checked an empty leaf");
        kani::cover(len == CAPACITY, "first_edge checked a full leaf");
    }

    // Harness for `NodeRef::last_edge`.
    #[kani::proof]
    fn harness_node_ref_last_edge() {
        let (root, len) = verifier_leaf();
        let edge = root.last_edge();
        assert_eq!(edge.idx(), len);
        kani::cover(len == 0, "last_edge checked an empty leaf");
        kani::cover(len == CAPACITY, "last_edge checked a full leaf");
    }

    // Harness for `NodeRef::first_kv`.
    #[kani::proof]
    fn harness_node_ref_first_kv() {
        let (root, len) = verifier_nonempty_leaf();
        let kv = root.first_kv();
        assert_eq!(kv.idx(), 0);
        kani::cover(len == 1, "first_kv checked a one-element leaf");
        kani::cover(len == CAPACITY, "first_kv checked a full leaf");
    }

    // Harness for `NodeRef::last_kv`.
    #[kani::proof]
    fn harness_node_ref_last_kv() {
        let (root, len) = verifier_nonempty_leaf();
        let kv = root.last_kv();
        assert_eq!(kv.idx(), len - 1);
        kani::cover(len == 1, "last_kv checked a one-element leaf");
        kani::cover(len == CAPACITY, "last_kv checked a full leaf");
    }

    // The empty modifies set checks that following either kind of backlink leaves the tree alone.
    #[kani::proof_for_contract(NodeRef::<marker::Mut<'_>, u8, u8, marker::LeafOrInternal>::ascend)]
    fn harness_node_ref_ascend_contract() {
        let attached = kani::any::<bool>();
        let height = kani::any_where(|h: &usize| !attached || *h < usize::MAX);
        let len = kani::any_where(|n: &u16| usize::from(*n) <= CAPACITY);
        let idx = kani::any_where(|i: &u16| *i <= len);
        let mut leaf = empty_leaf();
        let mut internal = empty_internal();
        let data = if height == 0 { &mut leaf } else { &mut internal.data };
        let mut parent = empty_internal();
        let parent_ptr = NonNull::from_mut(&mut parent);
        if attached {
            parent.data.len = len;
            parent.edges[usize::from(idx)].write(NonNull::from_mut(data));
            data.parent = Some(parent_ptr);
            data.parent_idx.write(idx);
        }
        let mut child = borrow_leaf::<u8, u8>(data).forget_type();
        child.height = height;
        let result = child.ascend();
        kani::cover(!attached && result.is_err(), "ascend from a detached root");
        kani::cover(
            attached && height > 0 && usize::from(idx) == CAPACITY && result.is_ok(),
            "ascend from the last internal child of a full node",
        );
    }

    // Harness for `NodeRef::into_leaf`.
    #[kani::proof]
    fn harness_node_ref_into_leaf() {
        let (root, len) = verifier_leaf();
        let leaf = root.reborrow().into_leaf();
        assert_eq!(leaf.len as usize, len);
        kani::cover(len == 0, "into_leaf checked an empty leaf");
        kani::cover(len == CAPACITY, "into_leaf checked a full leaf");
    }

    // Harness for `NodeRef::keys`.
    #[kani::proof]
    fn harness_node_ref_keys() {
        let (root, len) = verifier_leaf();
        let view = root.reborrow();
        let keys = view.keys();
        assert_eq!(keys.len(), len);
        if len > 0 {
            let idx = kani::any_where(|i: &usize| *i < len);
            assert!(ptr::eq(&keys[idx], view.into_leaf().keys[idx].as_ptr()));
        }
        kani::cover(len == 0, "keys checked an empty leaf");
        kani::cover(len == CAPACITY, "keys checked a full leaf");
    }

    // Harness for `NodeRef::as_leaf_mut`.
    #[kani::proof]
    fn harness_node_ref_as_leaf_mut() {
        let (mut root, len) = verifier_leaf();
        let mut view = root.borrow_mut();
        let leaf = view.as_leaf_mut();
        assert_eq!(leaf.len as usize, len);
        kani::cover(len == 0, "as_leaf_mut checked an empty leaf");
        kani::cover(len == CAPACITY, "as_leaf_mut checked a full leaf");
    }

    // Harness for `NodeRef::into_leaf_mut`.
    #[kani::proof]
    fn harness_node_ref_into_leaf_mut() {
        let (mut root, len) = verifier_leaf();
        let view = root.borrow_mut();
        let leaf = view.into_leaf_mut();
        assert_eq!(leaf.len as usize, len);
        kani::cover(len == 0, "into_leaf_mut checked an empty leaf");
        kani::cover(len == CAPACITY, "into_leaf_mut checked a full leaf");
    }

    // Harness for `NodeRef::as_leaf_dying`.
    #[kani::proof]
    fn harness_node_ref_as_leaf_dying() {
        let (mut root, len) = verifier_leaf();
        let mut dying = root.into_dying();
        let leaf = dying.as_leaf_dying();
        assert_eq!(leaf.len as usize, len);
        kani::cover(len == 0, "as_leaf_dying checked an empty leaf");
        kani::cover(len == CAPACITY, "as_leaf_dying checked a full leaf");
    }

    // Harness for `NodeRef::pop_internal_level`.
    #[kani::proof]
    fn harness_node_ref_pop_internal_level() {
        let height = kani::any_where(|height: &usize| *height > 0);
        let (leaf, _) = verifier_leaf();
        let leaf = leaf.forget_type();
        let mut child =
            if height == 1 { leaf } else { internal_root_with_child(leaf, Global).forget_type() };
        // Pop reads the first edge and clears the retained child's backlink.
        child.height = height - 1;
        let child_ptr = child.node;
        let child_len = child.len();
        let mut root = internal_root_with_child(child, Global).forget_type();
        root.pop_internal_level(Global);
        assert_eq!(root.node, child_ptr);
        assert_eq!(root.height(), height - 1);
        assert_eq!(root.len(), child_len);
        assert!(root.reborrow().ascend().is_err());
        kani::cover(height == 1, "pop an internal root above a leaf");
        kani::cover(height == usize::MAX, "pop an internal root above an internal child");
    }

    // Harness for `NodeRef::push`.
    #[kani::proof]
    fn harness_node_ref_push() {
        let (mut root, _) = verifier_leaf();
        let before = root.len();
        if before < CAPACITY {
            let (key, val) = kani::any::<(u8, u8)>();
            let inserted = root.borrow_mut().push(key, val);
            assert_eq!(root.len(), before + 1);
            let (stored_key, stored_val) = root.reborrow().last_kv().into_kv();
            assert!(ptr::eq(inserted, stored_val));
            assert_eq!((*stored_key, *stored_val), (key, val));
            kani::cover(before == 0, "push checked insertion into an empty leaf");
            kani::cover(before == CAPACITY - 1, "push checked insertion into a nearly full leaf");
        }
    }

    #[kani::proof]
    fn harness_node_ref_push_internal() {
        let len = kani::any_where(|n: &usize| *n < CAPACITY);
        let height = kani::any_where(|h: &usize| *h > 0);
        let leaf = OwnedLeaf::new_leaf(Global).forget_type();
        let mut incoming =
            if height == 1 { leaf } else { internal_root_with_child(leaf, Global).forget_type() };
        // Push reads only the incoming root and writes its backlink.
        incoming.height = height - 1;
        let child = incoming.node;
        let mut storage = empty_internal();
        let mut children = [const { empty_leaf() }; CAPACITY + 1];
        let mut parent = internal_with_borrowed_children(&mut storage, &mut children, len);
        parent.height = height;
        let (key, val) = kani::any();
        parent.push(key, val, incoming);

        let parent = parent.reborrow();
        assert_eq!(parent.len(), len + 1);
        assert_eq!(parent.last_kv().into_kv(), (&key, &val));
        assert_edge_child(parent, len + 1, child);
        kani::cover(len + 1 == CAPACITY, "push into the last available internal slot");
        kani::cover(height > 1, "push a subtree into an internal node");
    }

    // Harness for `Handle::left_edge`.
    #[kani::proof]
    fn harness_handle_left_edge() {
        let (root, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        // SAFETY: idx identifies an initialized KV.
        let edge = unsafe { Handle::new_kv(root.reborrow(), idx) }.left_edge();
        assert_eq!(edge.idx(), idx);
        assert_eq!(edge.into_node().node, root.node);
        kani::cover(idx + 1 == CAPACITY, "left_edge from the last KV of a full node");
    }

    // Harness for `Handle::right_edge`.
    #[kani::proof]
    fn harness_handle_right_edge() {
        let (root, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        // SAFETY: idx identifies an initialized KV.
        let edge = unsafe { Handle::new_kv(root.reborrow(), idx) }.right_edge();
        assert_eq!(edge.idx(), idx + 1);
        assert_eq!(edge.into_node().node, root.node);
        kani::cover(idx + 1 == CAPACITY, "right_edge from the last KV of a full node");
    }

    // Harness for `Handle::left_kv`.
    #[kani::proof]
    fn harness_handle_left_kv() {
        let (root, len) = verifier_leaf();
        let idx = kani::any_where(|i: &usize| *i <= len);
        // SAFETY: Leaves have an edge at every position from 0 through len.
        match unsafe { Handle::new_edge(root.reborrow(), idx) }.left_kv() {
            Ok(kv) => {
                assert!(idx > 0);
                assert_eq!(kv.idx(), idx - 1);
                assert_eq!(kv.into_node().node, root.node);
                kani::cover(idx == len, "left_kv succeeds at the last edge");
            }
            Err(edge) => {
                assert_eq!(idx, 0);
                assert_eq!(edge.idx(), idx);
                assert_eq!(edge.into_node().node, root.node);
                kani::cover(len == 0, "left_kv returns the edge of an empty node");
            }
        }
    }

    // Harness for `Handle::right_kv`.
    #[kani::proof]
    fn harness_handle_right_kv() {
        let (root, len) = verifier_leaf();
        let idx = kani::any_where(|i: &usize| *i <= len);
        // SAFETY: Leaves have an edge at every position from 0 through len.
        match unsafe { Handle::new_edge(root.reborrow(), idx) }.right_kv() {
            Ok(kv) => {
                assert!(idx < len);
                assert_eq!(kv.idx(), idx);
                assert_eq!(kv.into_node().node, root.node);
                kani::cover(idx == 0, "right_kv succeeds at the first edge");
            }
            Err(edge) => {
                assert_eq!(idx, len);
                assert_eq!(edge.idx(), idx);
                assert_eq!(edge.into_node().node, root.node);
                kani::cover(len == CAPACITY, "right_kv returns the last edge of a full node");
            }
        }
    }

    // Harness for `Handle::descend`.
    #[kani::proof]
    fn harness_handle_descend() {
        let len = kani::any_where(|n: &usize| *n <= CAPACITY);
        let mut parent = empty_internal::<u8, u8>();
        let mut children = [const { empty_leaf() }; CAPACITY + 1];
        let internal = internal_with_borrowed_children(&mut parent, &mut children, len);
        let idx = kani::any_where(|i: &usize| *i <= len);
        let child_ptr = relink_child(&internal, idx);
        // SAFETY: The fixture initializes each edge up to and including len.
        let edge = unsafe { Handle::new_edge(internal.reborrow(), idx) }.forget_node_type();
        let ForceResult::Internal(edge) = edge.force() else {
            panic!("the edge belongs to an internal node");
        };
        assert_eq!(edge.idx(), idx);
        let descended = edge.descend();
        assert_eq!(descended.height(), 0);
        assert_eq!(descended.node.as_ptr(), child_ptr);
        kani::cover(idx == CAPACITY, "descend through the last edge of a full node");
    }

    #[kani::proof]
    fn harness_consider_for_balancing() {
        let len = kani::any_where(|n: &usize| 0 < *n && *n <= CAPACITY);
        let idx = kani::any_where(|i: &usize| *i < len);
        let mut storage = empty_internal::<u8, u8>();
        let mut children = [const { empty_leaf() }; CAPACITY + 1];
        let parent = internal_with_borrowed_children(&mut storage, &mut children, len);
        let parent_ptr = parent.node;
        let left = relink_child(&parent, idx);
        let right = relink_child(&parent, idx + 1);

        // SAFETY: The separator and both adjacent edges belong to the active prefix.
        let context = unsafe { Handle::new_kv(parent, idx) }.consider_for_balancing();
        assert_eq!((context.parent.node.node, context.parent.idx()), (parent_ptr, idx));
        assert_eq!(context.left_child.node.as_ptr(), left);
        assert_eq!(context.right_child.node.as_ptr(), right);
        kani::cover(idx == 0, "balance around the first separator");
        kani::cover(idx + 1 == CAPACITY, "balance around the last separator of a full node");
    }

    #[kani::proof]
    fn harness_choose_parent_kv() {
        let len = kani::any_where(|n: &usize| 0 < *n && *n <= CAPACITY);
        let idx = kani::any_where(|i: &usize| *i <= len);
        let attached = kani::any::<bool>();
        let mut detached = empty_leaf::<u8, u8>();
        let mut parent = empty_internal();
        let mut children = [const { empty_leaf() }; CAPACITY + 1];
        let parent = internal_with_borrowed_children(&mut parent, &mut children, len);
        let parent_ptr = parent.node;
        let separator = idx.saturating_sub(1);
        // SAFETY: The separator and both adjacent edges belong to the active prefix.
        let (left, right) = unsafe {
            let kv = Handle::new_kv(parent.reborrow(), separator);
            (kv.left_edge().descend().node, kv.right_edge().descend().node)
        };
        let child = if attached {
            // SAFETY: idx selects an initialized edge, and no shared view remains live.
            unsafe { Handle::new_edge(parent, idx) }.descend()
        } else {
            borrow_leaf(&mut detached).forget_type()
        };
        let original = child.node;

        let context = match child.choose_parent_kv() {
            Ok(LeftOrRight::Left(context)) => {
                assert!(attached && idx > 0);
                context
            }
            Ok(LeftOrRight::Right(context)) => {
                assert!(attached && idx == 0);
                context
            }
            Err(root) => {
                assert!(!attached && root.node == original);
                kani::cover(!attached, "a detached root has no parent separator");
                return;
            }
        };
        assert_eq!((context.parent.node.node, context.parent.idx()), (parent_ptr, separator));
        assert_eq!((context.left_child.node, context.right_child.node), (left, right));
        kani::cover(idx == 0, "choose the separator to the right of the first child");
        kani::cover(idx == CAPACITY, "choose the separator to the left of the last child");
    }

    // Harness for `Handle::into_kv`.
    #[kani::proof]
    fn harness_handle_into_kv() {
        let (root, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        let leaf = root.reborrow().into_leaf();
        // SAFETY: idx is in the initialized prefix of both arrays.
        let (key, value) = unsafe { Handle::new_kv(root.reborrow(), idx) }.into_kv();
        assert!(ptr::eq(key, leaf.keys[idx].as_ptr()));
        assert!(ptr::eq(value, leaf.vals[idx].as_ptr()));
        kani::cover(idx + 1 == CAPACITY, "into_kv reads the last pair of a full node");
    }

    // Harness for `Handle::key_mut`.
    #[kani::proof]
    fn harness_handle_key_mut() {
        let (mut root, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        let key = kani::any();
        // SAFETY: idx is in the initialized prefix.
        *unsafe { Handle::new_kv(root.borrow_mut(), idx) }.key_mut() = key;
        assert_eq!(root.reborrow().keys()[idx], key);
        kani::cover(idx + 1 == CAPACITY, "key_mut writes the last key of a full node");
    }

    // Harness for `Handle::into_val_mut`.
    #[kani::proof]
    fn harness_handle_into_val_mut() {
        let (mut root, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        let val = kani::any();
        // SAFETY: idx is in the initialized prefix.
        *unsafe { Handle::new_kv(root.borrow_mut(), idx) }.into_val_mut() = val;
        // SAFETY: The same slot remains initialized after writing a value through it.
        assert_eq!(unsafe { root.reborrow().into_leaf().vals[idx].assume_init() }, val);
        kani::cover(idx + 1 == CAPACITY, "into_val_mut writes the last value of a full node");
    }

    // Harness for `Handle::into_kv_mut`.
    #[kani::proof]
    fn harness_handle_into_kv_mut() {
        let (mut root, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        // SAFETY: Both slots at idx are initialized and uniquely borrowed.
        let (key, value) = unsafe { Handle::new_kv(root.borrow_mut(), idx) }.into_kv_mut();
        *key = 1;
        *value = 2;
        assert_eq!((*key, *value), (1, 2));
        kani::cover(idx + 1 == CAPACITY, "into_kv_mut writes both fields of the last pair");
    }

    // Harness for `Handle::into_kv_valmut`.
    #[kani::proof]
    fn harness_handle_into_kv_valmut() {
        let len = kani::any_where(|n: &usize| (2..=CAPACITY).contains(n));
        let mut root = leaf_with_len(len);
        let first = kani::any_where(|i: &usize| *i < len);
        let second = kani::any_where(|i: &usize| *i < len && *i != first);
        let first_key = root.reborrow().keys()[first];
        let second_key = root.reborrow().keys()[second];
        let view = root.borrow_valmut();
        // SAFETY: As in IterMut, duplicate the view only to visit two distinct initialized slots.
        let (key1, val1) = unsafe { Handle::new_kv(ptr::read(&view), first) }.into_kv_valmut();
        // SAFETY: second is initialized and distinct from the outstanding value reference.
        let (key2, val2) = unsafe { Handle::new_kv(view, second) }.into_kv_valmut();
        *val1 = 1;
        *val2 = 2;
        assert_eq!((*key1, *key2), (first_key, second_key));
        assert_eq!((*val1, *val2), (1, 2));
        kani::cover(first + 1 == CAPACITY && second == 0, "two value references coexist");
    }

    // Harness for `Handle::kv_mut`.
    #[kani::proof]
    fn harness_handle_kv_mut() {
        let (mut root, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        // SAFETY: idx is in the initialized prefix.
        let mut handle = unsafe { Handle::new_kv(root.borrow_mut(), idx) };
        let (key, value) = handle.kv_mut();
        *key = 1;
        *value = 2;
        assert_eq!((*key, *value), (1, 2));
        let (key, value) = handle.reborrow().into_kv();
        assert_eq!((*key, *value), (1, 2));
        kani::cover(idx + 1 == CAPACITY, "kv_mut writes both fields of the last pair");
    }

    #[kani::proof]
    fn harness_handle_into_key_val() {
        let (leaf, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        // SAFETY: idx selects an initialized pair in both views. The shared view ends before
        // moving the pair, and the dying node is never accessed again.
        let (key, value) = unsafe { Handle::new_kv(leaf.reborrow(), idx) }.into_kv();
        let expected = (*key, *value);
        let dying = leaf.into_dying();
        let actual = unsafe { Handle::new_kv(dying, idx).into_key_val() };
        assert_eq!(actual, expected);
        kani::cover(len == CAPACITY && idx == len - 1, "extract the final pair of a full node");
    }

    #[kani::proof]
    fn harness_handle_remove_leaf() {
        let (mut leaf, len) = verifier_nonempty_leaf();
        let idx = kani::any_where(|i: &usize| *i < len);
        // SAFETY: Both handles selected below refer to initialized pairs.
        let (expected, next) = unsafe {
            let view = leaf.reborrow();
            let (key, val) = Handle::new_kv(view, idx).forget_node_type().into_kv();
            let next = (idx + 1 < len).then(|| {
                let (key, val) = Handle::new_kv(view, idx + 1).into_kv();
                (*key, *val)
            });
            ((*key, *val), next)
        };

        let leaf_ptr = leaf.node;
        // SAFETY: The removed KV was initialized by the fixture.
        let (removed, edge) = unsafe { Handle::new_kv(leaf.borrow_mut(), idx) }.remove();
        let edge = edge.forget_node_type();
        // SAFETY: The edge returned by leaf removal still points into the leaf.
        let edge = unsafe { edge.cast_to_leaf_unchecked() };
        assert_eq!(removed, expected);
        assert_eq!(edge.idx(), idx);
        assert_eq!(edge.node.node, leaf_ptr);
        assert_eq!(edge.reborrow().into_node().len(), len - 1);
        if let Some(next) = next {
            let (key, val) = edge.reborrow().right_kv().ok().unwrap().into_kv();
            assert_eq!((*key, *val), next);
        }
        kani::cover(idx == 0 && len == CAPACITY, "remove shifts the longest leaf suffix");
        kani::cover(idx + 1 == len, "remove returns the last edge");
    }

    #[kani::proof]
    fn harness_deallocate_leaf_root() {
        let alloc = TrackingAllocator::default();
        let root = OwnedLeaf::new_leaf(&alloc).forget_type().into_dying();
        let ptr = root.node;
        // SAFETY: The empty node was allocated by alloc and has no live handles.
        let parent = unsafe { root.deallocate_and_ascend(&alloc) };
        assert!(parent.is_none());
        assert_eq!(alloc.freed.get(), Some((ptr.cast(), Layout::new::<LeafNode<u8, u8>>())));
        kani::cover(parent.is_none(), "deallocate a leaf root without a parent");
    }

    #[kani::proof]
    fn harness_deallocate_attached_child() {
        let internal = kani::any::<bool>();
        let alloc = TrackingAllocator::default();
        let leaf = OwnedLeaf::new_leaf(&alloc).forget_type();
        let child =
            if internal { internal_root_with_child(leaf, &alloc).forget_type() } else { leaf };
        let child_ptr = child.node;
        let parent = internal_root_with_child(child, &alloc).into_dying();
        let parent_ptr = parent.node;
        let child = parent.first_edge().descend();
        // SAFETY: The child came from alloc, and the proof uses only the parent after freeing it.
        let edge = unsafe { child.deallocate_and_ascend(&alloc) }.unwrap();
        assert_eq!((edge.node.node, edge.idx()), (parent_ptr, 0));
        let layout = if internal {
            Layout::new::<InternalNode<u8, u8>>()
        } else {
            Layout::new::<LeafNode<u8, u8>>()
        };
        assert_eq!(alloc.freed.get(), Some((child_ptr.cast(), layout)));
        kani::cover(internal, "deallocate an internal node and recover the parent edge");
        kani::cover(!internal, "deallocate a leaf and recover the parent edge");
    }

    #[kani::proof]
    fn harness_move_suffix_projections() {
        let len = kani::any_where(|n: &usize| *n <= CAPACITY);
        let cut = kani::any_where(|i: &usize| *i <= len);
        let height = kani::any_where(|h: &usize| *h > 0);
        let mut storage = empty_internal::<u8, u8>();
        let mut children = [const { empty_leaf() }; CAPACITY + 1];
        let mut source = internal_with_borrowed_children(&mut storage, &mut children, len);
        source.height = height;
        let base = NodeRef::as_internal_ptr(&source);
        // SAFETY: The internal allocation is live and all these addresses lie in its storage.
        let (key_base, val_base, edge_base, length) = unsafe {
            (
                (&raw const (*base).data.keys).cast::<MaybeUninit<u8>>(),
                (&raw const (*base).data.vals).cast::<MaybeUninit<u8>>(),
                (&raw const (*base).edges).cast::<MaybeUninit<BoxedNode<u8, u8>>>(),
                &raw const (*base).data.len,
            )
        };
        let moved = len - cut;

        // SAFETY: The handle selects an initialized edge and the borrowed node is used exclusively.
        let mut edge = unsafe { Handle::new_edge(source.forget_type(), cut) };
        // SAFETY: There is no other active borrow of this handle.
        let mut node = unsafe { edge.reborrow_mut() }.into_node();
        assert_eq!(node.height(), height);
        assert_eq!(node.len(), len);
        assert!(ptr::addr_eq(node.len_mut(), length));

        // SAFETY: All the ranges are within the respective node arrays, including when empty.
        let keys = unsafe { node.key_area_mut(cut..len) };
        assert_eq!(keys.len(), moved);
        assert!(ptr::addr_eq(keys.as_ptr(), key_base.wrapping_add(cut)));
        // SAFETY: The moved prefix is at most CAPACITY elements long.
        let vals = unsafe { node.val_area_mut(..moved) };
        assert_eq!(vals.len(), moved);
        assert!(ptr::addr_eq(vals.as_ptr(), val_base));
        let ForceResult::Internal(mut node) = node.force() else {
            panic!("positive height selects the internal layout");
        };
        // SAFETY: Both endpoints are in 0..=CAPACITY + 1 and cut <= len.
        let edges = unsafe { node.edge_area_mut(cut + 1..len + 1) };
        assert_eq!(edges.len(), moved);
        assert!(ptr::addr_eq(edges.as_ptr(), edge_base.wrapping_add(cut + 1)));
        kani::cover(
            cut == 0 && len == CAPACITY && height > 1,
            "project the full suffix at an internal level",
        );
        kani::cover(cut == CAPACITY && len == CAPACITY, "project the empty suffix at the end");
    }

    #[kani::proof]
    fn harness_insert_leaf_step_fit() {
        let len = kani::any_where(|n: &usize| *n < CAPACITY);
        let idx = kani::any_where(|i: &usize| *i <= len);
        let mut leaf = leaf_for_insertion(len);
        let (key, val) = kani::any::<(u8, u8)>();
        // SAFETY: idx is a valid insertion edge in this leaf.
        let edge = unsafe { Handle::new_edge(borrow_leaf(&mut leaf), idx) };
        let (split, dormant) = edge.insert(key, val, Global);
        assert!(split.is_none());
        // SAFETY: Insertion is complete and the leaf is exclusively borrowed by the handle.
        let handle = unsafe { dormant.awaken() };
        assert_eq!(handle.idx(), idx);
        let (stored_key, stored_val) = handle.reborrow().into_kv();
        assert_eq!((*stored_key, *stored_val), (key, val));
        assert_eq!(usize::from(leaf.len), len + 1);
        kani::cover(len == 0, "insert into an empty leaf");
        kani::cover(len + 1 == CAPACITY && idx < len, "insert by shifting an occupied leaf suffix");
    }

    #[kani::proof]
    fn harness_splitpoint_bounds() {
        let edge = kani::any_where(|i: &usize| *i <= CAPACITY);
        let (middle, insertion) = splitpoint(edge);
        assert!((KV_IDX_CENTER - 1..=KV_IDX_CENTER + 1).contains(&middle));
        assert!(middle < CAPACITY);
        let left_len = middle;
        let right_len = CAPACITY - middle - 1;
        assert!(left_len < CAPACITY && right_len < CAPACITY);
        assert!(right_len + 1 <= 7);
        match insertion {
            LeftOrRight::Left(idx) => {
                assert!(idx <= left_len);
                assert_eq!(idx, edge);
                assert!(left_len + 1 - idx <= 7);
            }
            LeftOrRight::Right(idx) => {
                assert!(idx <= right_len);
                assert_eq!(middle + 1 + idx, edge);
                assert!(right_len + 1 - idx <= 7);
            }
        }
        kani::cover(edge == 0, "a full node can split at the first insertion edge");
        kani::cover(edge == CAPACITY, "a full node can split at the last insertion edge");
    }

    #[kani::proof_for_contract(slice_insert::<u8>)]
    fn harness_slice_insert_frame() {
        // A node has at most CAPACITY KV slots and CAPACITY + 1 edge slots.
        let len = usize::from(kani::any_where(|n: &u8| *n > 0 && usize::from(*n) <= CAPACITY + 1));
        let idx = usize::from(kani::any_where(|i: &u8| usize::from(*i) < len));
        let observed = usize::from(kani::any_where(|i: &u8| usize::from(*i) < len));
        let mut slots = MaybeUninit::new(kani::any::<[u8; CAPACITY + 1]>()).transpose();
        let value = kani::any();
        // SAFETY: The observed prefix element is initialized. Elements after idx move right.
        let expected = if observed == idx {
            value
        } else {
            unsafe { slots[observed - usize::from(observed > idx)].assume_init() }
        };
        slots[len - 1] = MaybeUninit::uninit();
        // SAFETY: The prefix to be shifted is initialized, and idx is in bounds.
        unsafe { slice_insert(&mut slots[..len], idx, value) };
        // SAFETY: Insertion initializes the entire active prefix.
        assert_eq!(unsafe { slots[observed].assume_init() }, expected);
        kani::cover(idx == 0 && len == CAPACITY + 1, "shift a full edge array's live prefix");
    }

    #[kani::proof_for_contract(slice_insert::<NonNull<LeafNode<u8, u8>>>)]
    fn harness_slice_insert_edge_frame() {
        let len = usize::from(kani::any_where(|n: &u8| *n > 0 && usize::from(*n) <= CAPACITY + 1));
        let idx = usize::from(kani::any_where(|i: &u8| usize::from(*i) < len));
        let mut child = empty_leaf::<u8, u8>();
        let mut incoming = empty_leaf();
        let mut slots = [MaybeUninit::new(NonNull::from_mut(&mut child)); CAPACITY + 1];
        slots[len - 1] = MaybeUninit::uninit();
        // SAFETY: The active range has an initialized prefix with an open last slot, and idx
        // selects a position in the range.
        unsafe { slice_insert(&mut slots[..len], idx, NonNull::from_mut(&mut incoming)) };
        kani::cover(idx == 0 && len == CAPACITY + 1, "shift the largest pointer suffix");
    }

    #[kani::proof_for_contract(move_to_slice::<NonNull<LeafNode<u8, u8>>>)]
    fn harness_move_edge_slice_frame() {
        let len = usize::from(kani::any_where(|n: &u8| usize::from(*n) <= CAPACITY + 1));
        let from = usize::from(kani::any_where(|i: &u8| usize::from(*i) <= CAPACITY + 1 - len));
        let to = usize::from(kani::any_where(|i: &u8| usize::from(*i) <= CAPACITY + 1 - len));
        let mut child = empty_leaf::<u8, u8>();
        let mut src = [MaybeUninit::new(NonNull::from_mut(&mut child)); CAPACITY + 1];
        let mut dst = [MaybeUninit::uninit(); CAPACITY + 1];
        move_to_slice(&mut src[from..from + len], &mut dst[to..to + len]);
        kani::cover(from == 1 && to == 0 && len == CAPACITY, "copy an internal edge suffix");
    }

    // Check the payload movement separately from child-edge relinking. The write set preserves
    // both backlinks and any payload in a descendant.
    #[kani::proof_for_contract(
        Handle::<NodeRef<marker::Mut<'_>, u8, u8, marker::Internal>, marker::KV>::split_leaf_data
    )]
    #[kani::solver(minisat)]
    fn harness_split_leaf_data_frame() {
        let len = usize::from(kani::any_where(|n: &u8| *n > 0 && usize::from(*n) <= CAPACITY));
        let pivot = usize::from(kani::any_where(|i: &u8| usize::from(*i) < len));
        let observed = usize::from(kani::any_where(|i: &u8| usize::from(*i) < len));
        let height = kani::any_where(|h: &usize| *h > 0);
        let mut source = InternalNode { data: leaf_for_insertion(len), ..empty_internal() };
        let mut right = empty_internal();
        // SAFETY: observed lies in the initialized prefix of source.
        let expected = unsafe {
            (source.data.keys[observed].assume_init(), source.data.vals[observed].assume_init())
        };
        let node = NodeRef::from_internal(NonNull::from_mut(&mut source), height);
        // SAFETY: pivot identifies an initialized KV slot.
        let mut pivot_handle = unsafe { Handle::new_kv(node, pivot) };
        let promoted = pivot_handle.split_leaf_data(&mut right.data);

        let stored = if observed == pivot {
            promoted
        } else {
            let (data, slot) = if observed < pivot {
                (&source.data, observed)
            } else {
                (&right.data, observed - pivot - 1)
            };
            assert!(slot < usize::from(data.len));
            // SAFETY: The retained slot is in the live prefix of the corresponding half.
            unsafe { (data.keys[slot].assume_init(), data.vals[slot].assume_init()) }
        };
        assert_eq!(stored, expected);
        kani::cover(
            len == CAPACITY && pivot == 0 && observed == CAPACITY - 1,
            "move the last pair of the maximum length KV suffix",
        );
    }

    #[kani::proof]
    fn harness_insert_leaf_step_split() {
        let idx = usize::from(kani::any_where(|i: &u8| usize::from(*i) <= CAPACITY));
        let ancestor_idx = kani::any_where(|i: &u16| usize::from(*i) <= CAPACITY);
        let attached = kani::any::<bool>();
        let mut leaf = leaf_for_insertion(CAPACITY);
        let mut ancestor = empty_internal();
        let ancestor_ptr = NonNull::from_mut(&mut ancestor);
        if attached {
            leaf.parent = Some(ancestor_ptr);
            leaf.parent_idx.write(ancestor_idx);
            ancestor.data.len = ancestor_idx;
            ancestor.edges[usize::from(ancestor_idx)].write(NonNull::from_mut(&mut leaf));
        }
        let (pivot, insertion) = splitpoint(idx);
        // SAFETY: The full leaf initializes every pair, including the selected pivot.
        let promoted = unsafe { (leaf.keys[pivot].assume_init(), leaf.vals[pivot].assume_init()) };
        let leaf = borrow_leaf(&mut leaf);
        let original = leaf.node;
        let (key, val) = kani::any::<(u8, u8)>();
        // SAFETY: Every edge of the full leaf is available for insertion.
        let edge = unsafe { Handle::new_edge(leaf, idx) };
        let (split, dormant) = edge.insert(key, val, Global);
        let split = split.expect("a full leaf splits");
        assert_eq!(split.left.node, original);
        assert_ne!(split.right.node, original);
        assert_eq!(split.left.height(), 0);
        assert_eq!(split.right.height(), 0);
        assert_eq!(split.left.len() + split.right.len(), CAPACITY);
        assert_eq!(split.kv, promoted);
        match split.left.reborrow().ascend() {
            Ok(edge) => {
                assert!(attached);
                assert_eq!(edge.node.node, ancestor_ptr.cast());
                assert_eq!(edge.idx(), usize::from(ancestor_idx));
                assert_eq!(edge.descend().node, original);
            }
            Err(root) => {
                assert!(!attached);
                assert_eq!(root.node, original);
            }
        }
        assert!(split.right.reborrow().ascend().is_err());
        let (destination, slot) = match insertion {
            LeftOrRight::Left(slot) => (split.left.node, slot),
            LeftOrRight::Right(slot) => (split.right.node, slot),
        };
        assert_eq!((dormant.node.node, dormant.idx()), (destination, slot));
        drop(split);
        // SAFETY: No split handle or reference into either result node is used again.
        let inserted = unsafe { dormant.awaken() };
        let (stored_key, stored_val) = inserted.reborrow().into_kv();
        assert_eq!((*stored_key, *stored_val), (key, val));
        kani::cover(
            attached && idx == EDGE_IDX_LEFT_OF_CENTER,
            "split an attached leaf to the left",
        );
        kani::cover(
            !attached && idx == EDGE_IDX_RIGHT_OF_CENTER,
            "split the leaf root to the right",
        );
    }

    // The parent shifts in do_merge depend only on its occupancy and separator index.
    // Exercise every such pair on the actual slice_remove helper, independently of the
    // child-occupancy proofs and the relink-range proof.
    #[kani::proof]
    fn harness_merge_parent_shift_ranges() {
        let len = kani::any_where(|n: &usize| *n > 0 && *n <= CAPACITY);
        let idx = kani::any_where(|i: &usize| *i < len);
        let original_keys = kani::any::<[u8; CAPACITY]>();
        let mut keys = MaybeUninit::new(original_keys).transpose();
        // Use pointer-sized words to check the edge ranges. VeriFast checks the pointer moves
        // and repairs in the production merge.
        let original_edges = kani::any::<[usize; CAPACITY + 1]>();
        let mut edges = MaybeUninit::new(original_edges).transpose();

        // SAFETY: The source slices contain only initialized slots, and len and idx
        // specify an existing separator and its right edge.
        let (key, removed) = unsafe {
            (slice_remove(&mut keys[..len], idx), slice_remove(&mut edges[..=len], idx + 1))
        };
        assert!(key == original_keys[idx], "remove the parent separator");
        assert!(removed == original_edges[idx + 1], "remove the edge right of the separator");
        kani::cover(len == CAPACITY && idx == 0, "shift the longest parent suffix");
        kani::cover(idx + 1 == len, "remove the final separator with no trailing shift");
    }
}
