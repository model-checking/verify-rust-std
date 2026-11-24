//! Ancestor ownership and the key, value, and child moves used during splitting.
//! Refinement checks the production `as_leaf_ptr` and `set_parent_link`.

#![allow(dead_code)]

use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ptr::NonNull;

//@ use std::mem::{MaybeUninit, open_MaybeUninit, close_MaybeUninit};
//@ use std::option::Option;
//@ use std::ptr::NonNull;

const B: usize = 6;

const CAPACITY: usize = 2 * B - 1;

//@ fix B() -> usize { 6 }

//@ fix CAPACITY() -> usize { 2 * B - 1 }

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

#[repr(C)]
struct InternalNode<K, V> {
    data: LeafNode<K, V>,

    /// The pointers to the children of this node. `len + 1` of these are considered
    /// initialized and valid, except that near the end, while the tree is held
    /// through borrow type `Dying`, some of these pointers are dangling.
    edges: [MaybeUninit<BoxedNode<K, V>>; 2 * B],
}

type BoxedNode<K, V> = NonNull<LeafNode<K, V>>;

struct NodeRef<BorrowType, K, V, Type> {
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

mod marker {
    use super::PhantomData;
    pub(crate) struct Mut<'a>(PhantomData<&'a mut ()>);
    pub(crate) enum LeafOrInternal {}
    pub(crate) enum DormantMut {}
    pub(crate) enum Owned {}
    pub(crate) enum Leaf {}
    pub(crate) enum Internal {}
    pub(crate) enum KV {}
    pub(crate) enum Edge {}
}

// BEGIN_ANCESTOR_PROOF
/*@
// Keep exact ancestor storage, including inactive slots that must stay unchanged.
inductive ParentPayload<K,V> = ParentPayload(
    list<MaybeUninit<K>>, list<MaybeUninit<V>>, list<MaybeUninit<NonNull<LeafNode<K,V>>>>
);
inductive ParentStep<K,V> = ParentStep(*InternalNode<K,V>, u16, u16, ParentPayload<K,V>);

pred link<K,V>(child: *LeafNode<K,V>, parent: Option<NonNull<InternalNode<K,V>>>, index: u16;) =
    (*child).parent |-> parent &*&
    if parent == Option::None {
        index == 0
    } else {
        (*child).parent_idx |-> MaybeUninit::new(index)
    };

pred parent_payload<K,V>(
    child: *LeafNode<K,V>, parent: *InternalNode<K,V>, index: u16, len: u16, payload: ParentPayload<K,V>;
) =
    parent != 0 &*& pointer_within_limits(parent) == true &*& pointer_within_limits(&(*parent).data) == true &*&
    0 <= index &*& index <= len &*& len <= CAPACITY &*&
    match payload {
        ParentPayload(keys, vals, edges) =>
            (*parent).data.len |-> len &*&
            (*parent).data.keys[..CAPACITY] |-> keys &*&
            (*parent).data.vals[..CAPACITY] |-> vals &*&
            (*parent).edges[..CAPACITY + 1] |-> edges &*&
            nth(index, edges) == MaybeUninit::new(NonNull::new(child))
    };

pred ancestors<K,V>(child: *LeafNode<K,V>, path: list<ParentStep<K,V>>, root: *LeafNode<K,V>;) =
    match path {
        nil => child == root &*& link(child, Option::None, 0),
        cons(step, rest) =>
            match step {
                ParentStep(parent, idx, len, payload) =>
                    link(child, Option::Some(NonNull::new(parent)), idx) &*&
                    parent_payload(child, parent, idx, len, payload) &*&
                    ancestors(&(*parent).data, rest, root)
            }
    };

@*/

// The raw-pointer form uses the exact two stores extracted from the NodeRef method.
unsafe fn write_child_backlink<K, V>(
    leaf: *mut LeafNode<K, V>,
    parent: NonNull<InternalNode<K, V>>,
    parent_idx: usize,
)
//@ req thread_token(?t) &*& (*leaf).parent |-> _ &*& (*leaf).parent_idx |-> _ &*& parent_idx <= CAPACITY;
//@ ens thread_token(t) &*& (*leaf).parent |-> Option::Some(parent) &*& (*leaf).parent_idx |-> MaybeUninit::new(parent_idx as u16);
//@ on_unwind_ens false;
{
    unsafe { (*leaf).parent = Some(parent) };
    //@ open LeafNode_parent_idx_(leaf, _);
    //@ points_to__limits(&(*leaf).parent_idx);
    unsafe { (*leaf).parent_idx.write(parent_idx as u16) };
}

/*@
pred child_headers<K,V>(children: list<NonNull<LeafNode<K,V>>>;) =
    match children {
        nil => true,
        cons(child, rest) =>
            (*child.as_ptr()).parent |-> _ &*& (*child.as_ptr()).parent_idx |-> _ &*& child_headers(rest)
    };

pred linked_headers<K,V>(children: list<NonNull<LeafNode<K,V>>>, parent: NonNull<InternalNode<K,V>>, index: usize;) =
    match children {
        nil => true,
        cons(child, rest) =>
            (*child.as_ptr()).parent |-> Option::Some(parent) &*&
            (*child.as_ptr()).parent_idx |-> MaybeUninit::new(index as u16) &*&
            linked_headers(rest, parent, index + 1)
    };

lem append_linked_header<K,V>(prefix: list<NonNull<LeafNode<K,V>>>, child: NonNull<LeafNode<K,V>>, parent: NonNull<InternalNode<K,V>>, first: usize)
    req linked_headers(prefix, parent, first) &*&
        (*child.as_ptr()).parent |-> Option::Some(parent) &*&
        (*child.as_ptr()).parent_idx |-> MaybeUninit::new((first + length(prefix)) as u16);
    ens linked_headers(append(prefix, [child]), parent, first);
{
    open linked_headers(prefix, parent, first);
    match prefix {
        nil => { close linked_headers([], parent, first + 1); }
        cons(old, rest) => { append_linked_header(rest, child, parent, first + 1); }
    }
    close linked_headers(append(prefix, [child]), parent, first);
}

fix initialized_edges<K,V>(children: list<NonNull<LeafNode<K,V>>>) -> list<MaybeUninit<NonNull<LeafNode<K,V>>>> {
    match children {
        nil => nil,
        cons(child, rest) => cons(MaybeUninit::new(child), initialized_edges(rest))
    }
}

lem initialized_edges_append<K,V>(a: list<NonNull<LeafNode<K,V>>>, b: list<NonNull<LeafNode<K,V>>>)
    req true;
    ens initialized_edges(append(a, b)) == append(initialized_edges(a), initialized_edges(b));
{
    match a {
        nil => {}
        cons(child, rest) => { initialized_edges_append(rest, b); }
    }
}

lem initialized_edge_count<K,V>(children: list<NonNull<LeafNode<K,V>>>)
    req true;
    ens length(initialized_edges(children)) == length(children);
{
    match children {
        nil => {}
        cons(child, rest) => { initialized_edge_count(rest); }
    }
}

lem empty_list_if_zero<T>(items: list<T>)
    req length(items) == 0;
    ens items == [];
{
    match items {
        nil => {}
        cons(item, more) => {}
    }
}

lem unpack_nonempty<T>(items: list<T>)
    req length(items) > 0;
    ens items == cons(?item, ?more);
{
    match items { nil => {} cons(item, more) => {} }
}
@*/

unsafe fn repair_edges<K, V>(parent: NonNull<InternalNode<K, V>>, start: usize, end: usize)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    start <= end &*& end <= CAPACITY + 1 &*&
    pointer_within_limits(&(*parent.as_ptr()).edges) == true &*&
    (*parent.as_ptr()).edges[start..end] |-> ?bits &*& child_headers(?children) &*&
    bits == initialized_edges(children) &*& length(children) == end - start;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    (*parent.as_ptr()).edges[start..end] |-> initialized_edges(children) &*&
    linked_headers(children, parent, start);
@*/
//@ on_unwind_ens false;
{
    let parent_ptr = parent.as_ptr();
    let base = unsafe { (&raw const (*parent_ptr).edges) as *const MaybeUninit<BoxedNode<K, V>> };
    let mut i = start;
    //@ close array(base + start, 0, []);
    //@ close linked_headers([], parent, start);
    loop {
        /*@
        inv thread_token(t) &*& lifetime_token(func_lft) &*& type_interp::<K>() &*& type_interp::<V>() &*&
            start <= i &*& i <= end &*& end <= CAPACITY + 1 &*&
            (*parent_ptr).edges[start..i] |-> ?prefix_bits &*&
            (*parent_ptr).edges[i..end] |-> ?rest_bits &*&
            linked_headers(?prefix, parent, start) &*& child_headers(?rest) &*&
            prefix_bits == initialized_edges(prefix) &*& rest_bits == initialized_edges(rest) &*&
            children == append(prefix, rest) &*& length(prefix) == i - start &*& length(rest) == end - i;
        @*/
        if i == end {
            break;
        }
        //@ unpack_nonempty(rest);
        //@ assert rest == cons(?child, ?remaining);
        //@ open array(base + i, end - i, initialized_edges(rest));
        //@ open_MaybeUninit(base + i);
        let edge = unsafe { *(base.add(i) as *const NonNull<LeafNode<K, V>>) };
        //@ close_MaybeUninit(base + i);
        //@ close array(base + i + 1, 0, []);
        //@ close array(base + i, 1, initialized_edges([child]));
        //@ open child_headers(rest);
        unsafe { write_child_backlink(edge.as_ptr(), parent, i) };
        //@ append_linked_header(prefix, child, parent, start);
        //@ array_join(base + start);
        //@ initialized_edges_append(prefix, [child]);
        //@ append_assoc(prefix, [child], remaining);
        i += 1;
    }
    //@ assert child_headers(?unrepaired);
    //@ assert linked_headers(?repaired, parent, start);
    //@ empty_list_if_zero(unrepaired);
    //@ append_nil(repaired);
    //@ open child_headers(unrepaired);
    //@ array_join(base + start);
}

unsafe fn move_split_edges<K, V>(
    left: NonNull<InternalNode<K, V>>,
    right: NonNull<InternalNode<K, V>>,
    pivot: usize,
    old_len: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& pivot < old_len &*& old_len <= CAPACITY &*&
    pointer_within_limits(&(*left.as_ptr()).edges) == true &*&
    pointer_within_limits(&(*right.as_ptr()).edges) == true &*&
    (*left.as_ptr()).edges[pivot + 1..old_len + 1] |-> ?edges &*&
    (*right.as_ptr()).edges[..old_len - pivot] |-> _ &*&
    child_headers(?children) &*& edges == initialized_edges(children) &*& length(children) == old_len - pivot;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    (*left.as_ptr()).edges[pivot + 1..old_len + 1] |-> edges &*&
    (*right.as_ptr()).edges[..old_len - pivot] |-> edges &*& linked_headers(children, right, 0);
@*/
//@ on_unwind_ens false;
{
    let src = unsafe { (&raw const (*left.as_ptr()).edges) as *const MaybeUninit<BoxedNode<K, V>> };
    let dst = unsafe { (&raw mut (*right.as_ptr()).edges) as *mut MaybeUninit<BoxedNode<K, V>> };
    unsafe { std::ptr::copy_nonoverlapping(src.add(pivot + 1), dst, old_len - pivot) };
    unsafe { repair_edges(right, 0, old_len - pivot) };
}

// Match the storage effects of moving the key, value, and edge suffixes. A
// separate Kani contract checks the pivot read in the native split_leaf_data.
unsafe fn split_preserves_ancestors<K, V>(
    left: NonNull<InternalNode<K, V>>,
    right: NonNull<InternalNode<K, V>>,
    pivot: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    ancestors(&(*left.as_ptr()).data, ?path, ?root) &*& link(&(*right.as_ptr()).data, Option::None, 0) &*&
    (*left.as_ptr()).data.len |-> ?old_len &*& (*right.as_ptr()).data.len |-> 0 &*& pivot < old_len &*& old_len <= CAPACITY &*&
    pointer_within_limits(&(*left.as_ptr()).edges) == true &*&
    pointer_within_limits(&(*right.as_ptr()).edges) == true &*&
    (*left.as_ptr()).edges[pivot + 1..old_len + 1] |-> ?edges &*&
    (*right.as_ptr()).edges[..old_len - pivot] |-> _ &*&
    child_headers(?children) &*& edges == initialized_edges(children) &*& length(children) == old_len - pivot &*&
    pointer_within_limits(&(*left.as_ptr()).data.keys) == true &*&
    pointer_within_limits(&(*left.as_ptr()).data.vals) == true &*&
    pointer_within_limits(&(*right.as_ptr()).data.keys) == true &*&
    pointer_within_limits(&(*right.as_ptr()).data.vals) == true &*&
    (*left.as_ptr()).data.keys[pivot + 1..old_len] |-> ?keys &*&
    (*left.as_ptr()).data.vals[pivot + 1..old_len] |-> ?vals &*&
    (*right.as_ptr()).data.keys[..old_len - pivot - 1] |-> _ &*&
    (*right.as_ptr()).data.vals[..old_len - pivot - 1] |-> _;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    ancestors(&(*left.as_ptr()).data, path, root) &*& link(&(*right.as_ptr()).data, Option::None, 0) &*&
    (*left.as_ptr()).data.len |-> (pivot as u16) &*& (*right.as_ptr()).data.len |-> ((old_len - pivot - 1) as u16) &*&
    (*left.as_ptr()).edges[pivot + 1..old_len + 1] |-> edges &*&
    (*right.as_ptr()).edges[..old_len - pivot] |-> edges &*& linked_headers(children, right, 0) &*&
    (*left.as_ptr()).data.keys[pivot + 1..old_len] |-> keys &*&
    (*left.as_ptr()).data.vals[pivot + 1..old_len] |-> vals &*&
    (*right.as_ptr()).data.keys[..old_len - pivot - 1] |-> keys &*&
    (*right.as_ptr()).data.vals[..old_len - pivot - 1] |-> vals;
@*/
//@ on_unwind_ens false;
{
    let src = left.as_ptr();
    let dst = right.as_ptr();
    let len = unsafe { (*src).data.len } as usize;
    let new_len = len - pivot - 1;
    unsafe {
        (*dst).data.len = new_len as u16;
        let src_keys = ((&raw const (*src).data.keys) as *const MaybeUninit<K>);
        let src_vals = ((&raw const (*src).data.vals) as *const MaybeUninit<V>);
        let dst_keys = ((&raw mut (*dst).data.keys) as *mut MaybeUninit<K>);
        let dst_vals = ((&raw mut (*dst).data.vals) as *mut MaybeUninit<V>);
        std::ptr::copy_nonoverlapping(src_keys.add(pivot + 1), dst_keys, new_len);
        std::ptr::copy_nonoverlapping(src_vals.add(pivot + 1), dst_vals, new_len);
        (*src).data.len = pivot as u16;
        move_split_edges(left, right, pivot, len);
    }
}

// BEGIN_BACKLINK_METHODS
impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    unsafe fn as_leaf_ptr(this: &Self) -> *mut LeafNode<K, V>
/*@
    req [?f](*this |-> ?node_ref);
    @*/
    /*@
    ens [f](*this |-> node_ref) &*& result == node_ref.node.as_ptr();
    @*/
    //@ on_unwind_ens false;
    {
        //@ open_points_to(this);
        let ptr = this.node.as_ptr();
        //@ close_points_to(this, f);
        ptr
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    unsafe fn set_parent_link(&mut self, parent: NonNull<InternalNode<K, V>>, parent_idx: usize)
    //@ req *self |-> ?node_ref &*& (*node_ref.node.as_ptr()).parent |-> _ &*& (*node_ref.node.as_ptr()).parent_idx |-> _ &*& parent_idx <= CAPACITY;
    //@ ens *self |-> node_ref &*& (*node_ref.node.as_ptr()).parent |-> Option::Some(parent) &*& (*node_ref.node.as_ptr()).parent_idx |-> MaybeUninit::new(parent_idx as u16);
    //@ on_unwind_ens false;
    {
        //@ let view = precreate_ref(self);
        //@ init_ref_readonly(view, 1/2);
        let leaf = unsafe { Self::as_leaf_ptr(self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(self, _);
        unsafe { (*leaf).parent = Some(parent) };
        //@ open LeafNode_parent_idx_(leaf, _);
        //@ points_to__limits(&(*leaf).parent_idx);
        unsafe { (*leaf).parent_idx.write(parent_idx as u16) };
    }
}

// END_BACKLINK_METHODS

struct Handle<Node, Type> {
    node: Node,
    idx: usize,
    _marker: PhantomData<Type>,
}

// The production iterator is specialized to the two range types used by its
// callers. The invariant preserves the edge slots and separates the repaired
// prefix from the pending suffix.

// BEGIN_NODE_LEN
impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    unsafe fn len(&self) -> usize
    //@ req [?f](*self |-> ?node) &*& [?ql]((*node.node.as_ptr()).len |-> ?len);
    //@ ens [f](*self |-> node) &*& [ql]((*node.node.as_ptr()).len |-> len) &*& result == len;
    //@ on_unwind_ens false;
    {
        //@ open_points_to(self);
        let ptr = self.node.as_ptr();
        //@ close_points_to(self, f);
        unsafe { (*ptr).len as usize }
    }
}
// END_NODE_LEN

// BEGIN_NODE_REBORROW
impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    unsafe fn reborrow_mut<'b>(&'b mut self) -> NodeRef<marker::Mut<'b>, K, V, Type>
    //@ req *self |-> ?node;
    //@ ens *self |-> node &*& result.node == node.node &*& result.height == node.height;
    //@ on_unwind_ens false;
    {
        //@ open_points_to(self);
        let borrowed = NodeRef { height: self.height, node: self.node, _marker: PhantomData };
        //@ close_points_to(self);
        borrowed
    }
}
// END_NODE_REBORROW

// BEGIN_NEW_EDGE
impl<BorrowType, K, V, Type> Handle<NodeRef<BorrowType, K, V, Type>, marker::Edge> {
    unsafe fn new_edge(node: NodeRef<BorrowType, K, V, Type>, idx: usize) -> Self
    //@ req (*node.node.as_ptr()).len |-> ?len &*& idx <= len;
    //@ ens result.node == node &*& result.idx == idx &*& (*node.node.as_ptr()).len |-> len;
    //@ on_unwind_ens false;
    {
        unsafe { debug_assert!(idx <= node.len()) };
        let edge = Handle { node, idx, _marker: PhantomData };
        //@ close_points_to(&node, 1/2);
        edge
    }
}
// END_NEW_EDGE

// The generator binds the read and the two stores to descend and set_parent_link.
impl<'a, K, V> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    unsafe fn correct_parent_link(self)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        0 < self.node.height &*& self.node.height <= usize::MAX &*& 0 <= self.idx &*& self.idx <= CAPACITY &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& self.node.node.as_ptr() as *InternalNode<K,V> == parent.as_ptr() &*&
        pointer_within_limits(&(*parent.as_ptr()).edges) == true &*&
        exists::<BoxedNode<K,V>>(?child) &*& (*parent.as_ptr()).edges[..CAPACITY + 1] |-> ?edges &*&
        nth(self.idx, edges) == MaybeUninit::new(child) &*&
        (*child.as_ptr()).parent |-> _ &*& (*child.as_ptr()).parent_idx |-> _;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        (*parent.as_ptr()).edges[..CAPACITY + 1] |-> edges &*&
        (*child.as_ptr()).parent |-> Option::Some(parent) &*&
        (*child.as_ptr()).parent_idx |-> MaybeUninit::new(self.idx as u16);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(parent);
        //@ open exists(child);
        //@ std::ptr::NonNull_new_as_ptr(parent);
        let parent_ptr = self.node.node.as_ptr() as *mut InternalNode<K, V>;
        let parent_link = unsafe { NonNull::new_unchecked(parent_ptr) };
        //@ std::ptr::NonNull_new_as_ptr(parent_link);
        // BEGIN_RAW_EDGE_READ
        //@ let array = &(*parent_ptr).edges;
        //@ close_points_to(array);
        //@ let view = precreate_ref(array);
        //@ init_ref_readonly(view, 1/2);
        //@ open_points_to(view);
        //@ let base = view as *MaybeUninit<BoxedNode<K,V>>;
        //@ array_inv::<MaybeUninit<BoxedNode<K,V>>>();
        //@ array_split(base, self.idx);
        //@ array_split(base + self.idx, 1);
        //@ nth_drop(0, self.idx, edges);
        //@ open [1/2]array(base + self.idx, 1, _);
        //@ open [1/2]array(base + self.idx + 1, 0, _);
        //@ let slot = precreate_ref(base + self.idx);
        //@ init_ref_readonly(slot, 1/2);
        let edge = unsafe { (*parent_ptr).edges.get_unchecked(self.idx).assume_init_read() };
        //@ end_ref_readonly(slot);
        //@ merge_fractions points_to(base + self.idx, _);
        //@ close [1/2]array(base + self.idx, 1, [MaybeUninit::new(child)]);
        //@ array_join(base + self.idx);
        //@ array_join(base);
        //@ close_points_to(view, 1/2);
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(array, _);
        //@ open_points_to(array);
        // END_RAW_EDGE_READ
        let _child_height = self.node.height - 1;
        unsafe { write_child_backlink(edge.as_ptr(), parent_link, self.idx) };
    }
}

// BEGIN_RELINK_STEP
unsafe fn repair_one__VeriFast_wrapper<'a, 'b, K, V>(
    node: &'b mut NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
    i: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *node |-> ?original &*& 0 < original.height &*& original.height <= usize::MAX &*&
    (*original.node.as_ptr()).len |-> ?len &*& 0 <= i &*& i <= len &*& len <= CAPACITY &*&
    exists::<NonNull<InternalNode<K,V>>>(?parent) &*& original.node.as_ptr() as *InternalNode<K,V> == parent.as_ptr() &*&
    pointer_within_limits(&(*parent.as_ptr()).edges) == true &*& exists::<BoxedNode<K,V>>(?child) &*&
    (*parent.as_ptr()).edges[..CAPACITY + 1] |-> ?edges &*& nth(i, edges) == MaybeUninit::new(child) &*&
    (*child.as_ptr()).parent |-> _ &*& (*child.as_ptr()).parent_idx |-> _;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *node |-> original &*& (*original.node.as_ptr()).len |-> len &*&
    (*parent.as_ptr()).edges[..CAPACITY + 1] |-> edges &*&
    (*child.as_ptr()).parent |-> Option::Some(parent) &*&
    (*child.as_ptr()).parent_idx |-> MaybeUninit::new(i as u16);
@*/
//@ on_unwind_ens false;
{
    //@ open exists(parent);
    //@ open exists(child);
    //@ close exists(parent);
    //@ close exists(child);
    unsafe { Handle::new_edge/*@::<marker::Mut<'b>,K,V,marker::Internal>@*/(
        node.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::Internal,'b>@*/(), i
    ).correct_parent_link/*@::<'b,K,V>@*/() };
}

// END_RELINK_STEP



impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn relink_range<'b>(&'b mut self, range: std::ops::Range<usize>)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> ?node &*& 0 < node.height &*& node.height <= usize::MAX &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& node.node.as_ptr() as *InternalNode<K,V> == parent.as_ptr() &*&
        (*node.node.as_ptr()).len |-> ?len &*& len <= CAPACITY &*&
        0 <= range.start &*& range.start <= range.end &*& range.end <= len + 1 &*&
        pointer_within_limits(&(*parent.as_ptr()).edges) == true &*&
        child_headers(?children) &*& (*parent.as_ptr()).edges[..CAPACITY + 1] |-> ?edges &*&
        exists::<pair<list<MaybeUninit<BoxedNode<K,V>>>, list<MaybeUninit<BoxedNode<K,V>>>>>(pair(?before, ?after)) &*&
        length(before) == range.start &*&
        edges == append(before, append(initialized_edges(children), after)) &*&
        length(children) == range.end - range.start;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> node &*& (*node.node.as_ptr()).len |-> len &*&
        (*parent.as_ptr()).edges[..CAPACITY + 1] |-> edges &*&
        linked_headers(children, parent, range.start);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(parent);
        //@ open exists(pair(before, after));
        let mut iter = range.into_iter();
        //@ let first = range.start;
        //@ let end = range.end;
        //@ close linked_headers([], parent, first);
        loop {
            /*@
            inv iter |-> ?state &*& state.end == end &*&
                thread_token(t) &*& lifetime_token(func_lft) &*& type_interp::<K>() &*& type_interp::<V>() &*&
                *self |-> node &*& (*node.node.as_ptr()).len |-> len &*&
                first <= state.start &*& state.start <= end &*&
                linked_headers(?prefix, parent, first) &*& child_headers(?rest) &*&
                (*parent.as_ptr()).edges[..CAPACITY + 1] |-> edges &*&
                children == append(prefix, rest) &*& length(prefix) == state.start - first &*& length(rest) == end - state.start;
            @*/
            let iter_ref = &mut iter;
            let next = iter_ref.next();
            match next {
                None => break,
                Some(i) => {
                    //@ unpack_nonempty(rest);
                    //@ assert rest == cons(?child, ?remaining);
                    //@ initialized_edge_count(prefix);
                    //@ initialized_edge_count(rest);
                    //@ initialized_edges_append(prefix, rest);
                    //@ length_append(initialized_edges(prefix), initialized_edges(rest));
                    //@ length_append(initialized_edges(children), after);
                    //@ nth_append_r(before, append(initialized_edges(children), after), i - first);
                    //@ nth_append(initialized_edges(children), after, i - first);
                    //@ nth_append_r(initialized_edges(prefix), initialized_edges(rest), 0);
                    //@ open child_headers(rest);
                    //@ let view = precreate_ref(self);
                    //@ init_ref_readonly(view, 1/2);
                    unsafe { debug_assert!(i <= self.len()) };
                    //@ end_ref_readonly(view);
                    //@ merge_fractions points_to(self,_);
                    //@ close exists(parent);
                    //@ close exists(child);
                    unsafe { repair_one__VeriFast_wrapper/*@::<K,V,'a,'b>@*/(self, i) };
                    //@ append_linked_header(prefix, child, parent, first);
                    //@ append_assoc(prefix, [child], remaining);
                }
            }
        }
        //@ assert child_headers(?unrepaired);
        //@ assert linked_headers(?repaired, parent, first);
        //@ empty_list_if_zero(unrepaired);
        //@ append_nil(repaired);
        //@ open child_headers(unrepaired);
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn relink_inclusive<'b>(&'b mut self, range: std::ops::RangeInclusive<usize>)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> ?node &*& 0 < node.height &*& node.height <= usize::MAX &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& node.node.as_ptr() as *InternalNode<K,V> == parent.as_ptr() &*&
        (*node.node.as_ptr()).len |-> ?len &*& len <= CAPACITY &*&
        range.exhausted == false &*& 0 <= range.start &*& range.start <= (range.end + 1) &*& (range.end + 1) <= len + 1 &*&
        pointer_within_limits(&(*parent.as_ptr()).edges) == true &*&
        child_headers(?children) &*& (*parent.as_ptr()).edges[..CAPACITY + 1] |-> ?edges &*&
        exists::<pair<list<MaybeUninit<BoxedNode<K,V>>>, list<MaybeUninit<BoxedNode<K,V>>>>>(pair(?before, ?after)) &*&
        length(before) == range.start &*&
        edges == append(before, append(initialized_edges(children), after)) &*&
        length(children) == (range.end + 1) - range.start;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> node &*& (*node.node.as_ptr()).len |-> len &*&
        (*parent.as_ptr()).edges[..CAPACITY + 1] |-> edges &*&
        linked_headers(children, parent, range.start);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(parent);
        //@ open exists(pair(before, after));
        let mut iter = range.into_iter();
        //@ let first = range.start;
        //@ let end = (range.end + 1);
        //@ close linked_headers([], parent, first);
        loop {
            /*@
            inv iter |-> ?state &*& state.end + 1 == end &*& state.exhausted == false &*&
                thread_token(t) &*& lifetime_token(func_lft) &*& type_interp::<K>() &*& type_interp::<V>() &*&
                *self |-> node &*& (*node.node.as_ptr()).len |-> len &*&
                first <= state.start &*& state.start <= end &*&
                linked_headers(?prefix, parent, first) &*& child_headers(?rest) &*&
                (*parent.as_ptr()).edges[..CAPACITY + 1] |-> edges &*&
                children == append(prefix, rest) &*& length(prefix) == state.start - first &*& length(rest) == end - state.start;
            @*/
            let iter_ref = &mut iter;
            let next = iter_ref.next();
            match next {
                None => break,
                Some(i) => {
                    //@ unpack_nonempty(rest);
                    //@ assert rest == cons(?child, ?remaining);
                    //@ initialized_edge_count(prefix);
                    //@ initialized_edge_count(rest);
                    //@ initialized_edges_append(prefix, rest);
                    //@ length_append(initialized_edges(prefix), initialized_edges(rest));
                    //@ length_append(initialized_edges(children), after);
                    //@ nth_append_r(before, append(initialized_edges(children), after), i - first);
                    //@ nth_append(initialized_edges(children), after, i - first);
                    //@ nth_append_r(initialized_edges(prefix), initialized_edges(rest), 0);
                    //@ open child_headers(rest);
                    //@ let view = precreate_ref(self);
                    //@ init_ref_readonly(view, 1/2);
                    unsafe { debug_assert!(i <= self.len()) };
                    //@ end_ref_readonly(view);
                    //@ merge_fractions points_to(self,_);
                    //@ close exists(parent);
                    //@ close exists(child);
                    unsafe { repair_one__VeriFast_wrapper/*@::<K,V,'a,'b>@*/(self, i) };
                    //@ append_linked_header(prefix, child, parent, first);
                    //@ append_assoc(prefix, [child], remaining);
                }
            }
        }
        //@ assert child_headers(?unrepaired);
        //@ assert linked_headers(?repaired, parent, first);
        //@ empty_list_if_zero(unrepaired);
        //@ append_nil(repaired);
        //@ open child_headers(unrepaired);
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn relink_all<'b>(&'b mut self)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> ?node &*& 0 < node.height &*& node.height <= usize::MAX &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& node.node.as_ptr() as *InternalNode<K,V> == parent.as_ptr() &*&
        (*node.node.as_ptr()).len |-> ?occupancy &*& occupancy <= CAPACITY &*&
        pointer_within_limits(&(*parent.as_ptr()).edges) == true &*&
        child_headers(?children) &*& (*parent.as_ptr()).edges[..CAPACITY + 1] |-> ?edges &*&
        exists::<list<MaybeUninit<BoxedNode<K,V>>>>(?tail) &*&
        edges == append(initialized_edges(children), tail) &*& length(children) == occupancy + 1;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> node &*& (*node.node.as_ptr()).len |-> occupancy &*&
        (*parent.as_ptr()).edges[..CAPACITY + 1] |-> edges &*& linked_headers(children, parent, 0);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(parent);
        //@ open exists(tail);
        //@ let view = precreate_ref(self);
        //@ init_ref_readonly(view, 1/2);
        let len = unsafe { self.len() };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(self, _);
        //@ close exists(parent);
        //@ let prefix = nil::<MaybeUninit<BoxedNode<K,V>>>;
        //@ close exists(pair(prefix, tail));
        unsafe { self.relink_inclusive/*@::<'a,K,V,'b>@*/(0..=len) };
    }
}

fn main() {}
