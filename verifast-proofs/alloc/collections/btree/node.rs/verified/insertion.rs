#![feature(allocator_ext)]
#![feature(slice_ptr_get)]
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
    pub(crate) struct Immut<'a>(PhantomData<&'a ()>);
    pub(crate) struct Mut<'a>(PhantomData<&'a mut ()>);
    pub(crate) struct ValMut<'a>(PhantomData<&'a mut ()>);
    pub(crate) enum LeafOrInternal {}
    pub(crate) enum DormantMut {}
    pub(crate) enum Owned {}
    pub(crate) enum Dying {}
    pub(crate) enum Leaf {}
    pub(crate) enum Internal {}
    pub(crate) enum KV {}
    pub(crate) enum Edge {}
    pub(crate) trait BorrowType {
        const TRAVERSAL_PERMIT: bool = true;
    }
    impl BorrowType for Owned {
        const TRAVERSAL_PERMIT: bool = false;
    }
    impl BorrowType for Dying {}
    impl BorrowType for DormantMut {}
    impl BorrowType for Immut<'_> {}
    impl BorrowType for Mut<'_> {}
    impl BorrowType for ValMut<'_> {}
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

use std::num::NonZero;
use std::ptr;

// Ownership proof of insertion using the library's node layout and
// AllocatorClone bound. It covers both leaf insertion paths, propagation
// through an arbitrary ancestor chain, and installation of a new root
// before awakening the inserted handle.
// Where a proof needs non-unwinding allocator destruction, its contract
// records the safety guarantee of the Rust A: Allocator bound. Ordinary
// ownership of A does not imply that guarantee.

use std::alloc::AllocatorClone;

//@ use std::alloc::{Allocator, Allocator_full_borrow_content_};
//@ use std::boxed::Box_in;
//@ use std::clone::allocator_clone_bound;

// The shared borrow ends before any allocation or allocator drop.
// BEGIN_ALLOCATOR_CLONE
unsafe fn clone_allocator<A: AllocatorClone>(alloc: &mut A) -> A
/*@
req thread_token(?t) &*& type_interp::<A>() &*& [_]allocator_clone_bound::<A>() &*&
    *alloc |-> ?original &*& Allocator(t, original, ?id);
@*/
/*@
ens thread_token(t) &*& type_interp::<A>() &*&
    *alloc |-> ?after &*& Allocator(t, after, id) &*& Allocator(t, result, id);
@*/
//@ on_unwind_ens false;
{
    //@ std::alloc::close_Allocator_full_borrow_content_(t, alloc);
    //@ let k = begin_lifetime();
    //@ borrow(k, Allocator_full_borrow_content_(t, alloc, id));
    //@ std::alloc::share_Allocator_full_borrow_content_(k, t, alloc, id);
    //@ let view = precreate_ref(alloc);
    //@ std::alloc::init_ref_Allocator_share(k, t, view);
    //@ let f = open_frac_borrow(k, ref_initialized_(view), 1/2);
    //@ open [f]ref_initialized_::<A>(view)();
    let clone = (*alloc).clone();
    //@ close [f]ref_initialized_::<A>(view)();
    //@ close_frac_borrow(f, ref_initialized_(view));
    //@ merge_fractions lifetime_token(k);
    //@ end_lifetime(k);
    //@ borrow_end(k, Allocator_full_borrow_content_(t, alloc, id));
    //@ std::alloc::open_Allocator_full_borrow_content_(t, alloc, id);
    clone
}
// END_ALLOCATOR_CLONE

// Verify the drop using the generic drop contract, including its unwind case.
unsafe fn drop_allocator<A: AllocatorClone>(allocator: A)
//@ req thread_token(?t) &*& Allocator::<A>(t, allocator, _);
//@ ens thread_token(t);
//@ on_unwind_ens thread_token(t);
{
    //@ std::alloc::Allocator_to_own(allocator);
    drop(allocator);
}
impl<K, V> LeafNode<K, V> {
    unsafe fn init(this: *mut Self)
    //@ req (*this).parent |-?-> _ &*& (*this).len |-?-> _;
    //@ ens (*this).parent |-> Option::None &*& (*this).len |-> 0;
    //@ on_unwind_ens false;
    {
        // As a general policy, we leave fields uninitialized if they can be, as this should
        // be both slightly faster and easier to track in Valgrind.
        // ignore-tidy-undocumented-unsafe
        unsafe {
            // parent_idx, keys, and vals are all MaybeUninit
            (&raw mut (*this).parent).write(None);
            (&raw mut (*this).len).write(0);
        }
    }

    // Expose the boxed storage contract for the array fields in VeriFast.
    unsafe fn new<A: AllocatorClone>(alloc: A) -> Box<Self, A>
    //@ req thread_token(?t) &*& Allocator(t, alloc, ?alloc_id);
    //@ ens thread_token(t) &*& Box_in(t, result, alloc_id, ?node) &*& node.parent == Option::None &*& node.len == 0;
    //@ on_unwind_ens thread_token(t);
    {
        //@ let allocator = alloc;
        //@ std::alloc::Allocator_inv::<A>();
        //@ assert Allocator(t, allocator, alloc_id);
        let mut leaf = Box::new_uninit_in(alloc);
        //@ let contents = std::boxed::Box_separate_contents(&mut leaf);
        // Open storage only for the allocator lifetime available in this call.
        // The traded token is returned before rebuilding the Box.
        //@ assert [?q]lifetime_token(?k);
        //@ assert lifetime_inclusion(k, lft_of_type::<A>()) == true;
        //@ lifetime_inclusion_trans(k, lft_of_type::<A>(), alloc_id.lft);
        //@ let q_alloc = lifetime_token_trade(k, q, alloc_id.lft);
        //@ open_points_to_at_lft(contents, q_alloc);
        //@ points_to_limits(contents);
        let storage = &mut *leaf;
        //@ points_to_limits(storage);
        //@ std::mem::open_MaybeUninit(storage);
        //@ let data = storage as *LeafNode<K, V>;

        // SAFETY: `leaf` points to a `LeafNode`.
        unsafe { LeafNode::init(storage.as_mut_ptr()) };
        // SAFETY: `leaf` was just initialized.
        //@ std::mem::MaybeUninit__to_MaybeUninit(&(*data).parent_idx);
        //@ open LeafNode_keys_(data, _);
        //@ std::mem::Array__MaybeUninit_to_Array_MaybeUninit(&(*data).keys);
        //@ open LeafNode_vals_(data, _);
        //@ std::mem::Array__MaybeUninit_to_Array_MaybeUninit(&(*data).vals);
        //@ std::mem::close_MaybeUninit(storage);
        //@ close_points_to_at_lft(contents);
        //@ lifetime_token_trade_back(q_alloc, alloc_id.lft);
        //@ std::boxed::Box_unseparate_contents(&mut leaf);
        unsafe { leaf.assume_init() }
    }
}

impl<K, V> InternalNode<K, V> {
    unsafe fn new<A: AllocatorClone>(alloc: A) -> Box<Self, A>
    //@ req thread_token(?t) &*& Allocator(t, alloc, ?alloc_id);
    //@ ens thread_token(t) &*& Box_in(t, result, alloc_id, ?value) &*& value.data.parent == Option::None &*& value.data.len == 0;
    //@ on_unwind_ens thread_token(t);
    {
        //@ let allocator = alloc;
        //@ std::alloc::Allocator_inv::<A>();
        //@ assert Allocator(t, allocator, alloc_id);
        let mut node = Box::<Self, _>::new_uninit_in(alloc);
        //@ let contents = std::boxed::Box_separate_contents(&mut node);
        // Open storage only for the allocator lifetime available in this call.
        // The traded token is returned before rebuilding the Box.
        //@ assert [?q]lifetime_token(?k);
        //@ assert lifetime_inclusion(k, lft_of_type::<A>()) == true;
        //@ lifetime_inclusion_trans(k, lft_of_type::<A>(), alloc_id.lft);
        //@ let q_alloc = lifetime_token_trade(k, q, alloc_id.lft);
        //@ open_points_to_at_lft(contents, q_alloc);
        //@ points_to_limits(contents);
        let storage = &mut *node;
        //@ points_to_limits(storage);
        //@ std::mem::open_MaybeUninit(storage);
        //@ let data = storage as *InternalNode<K, V>;
        //@ open InternalNode_data_(data, _);

        // SAFETY: argument points to the `node.data` `LeafNode`.
        unsafe { LeafNode::init(&raw mut (*storage.as_mut_ptr()).data) };
        // SAFETY: `node.data` was just initialized and `node.edges` is MaybeUninit.
        //@ std::mem::MaybeUninit__to_MaybeUninit(&(*data).data.parent_idx);
        //@ open LeafNode_keys_(&(*data).data, _);
        //@ std::mem::Array__MaybeUninit_to_Array_MaybeUninit(&(*data).data.keys);
        //@ open LeafNode_vals_(&(*data).data, _);
        //@ std::mem::Array__MaybeUninit_to_Array_MaybeUninit(&(*data).data.vals);
        //@ close LeafNode_keys(&(*data).data, _);
        //@ close LeafNode_vals(&(*data).data, _);
        //@ close InternalNode_data(data, _);
        //@ open InternalNode_edges_(data, _);
        //@ std::mem::Array__MaybeUninit_to_Array_MaybeUninit(&(*data).edges);
        //@ std::mem::close_MaybeUninit(storage);
        //@ close_points_to_at_lft(contents);
        //@ lifetime_token_trade_back(q_alloc, alloc_id.lft);
        //@ std::boxed::Box_unseparate_contents(&mut node);
        unsafe { node.assume_init() }
    }
}

struct Handle<Node, Type> {
    node: Node,
    idx: usize,
    _marker: PhantomData<Type>,
}

// BEGIN_ROOT_REBORROW
struct DormantMutRef<'a, T> {
    ptr: NonNull<T>,
    _marker: PhantomData<&'a mut T>,
}

impl<'a, T> DormantMutRef<'a, T> {
    unsafe fn reborrow(&mut self) -> &'a mut T
    //@ req *self |-> ?dormant &*& *dormant.ptr.as_ptr() |-> ?value;
    //@ ens *self |-> dormant &*& *result |-> value &*& result == dormant.ptr.as_ptr();
    //@ on_unwind_ens false;
    {
        // SAFETY: our own safety conditions imply this reference is again unique.
        //@ open_points_to(self);
        let result = unsafe { &mut *self.ptr.as_ptr() };
        //@ close_points_to(self);
        result
    }
}
// END_ROOT_REBORROW

// BEGIN_WAKE_HANDLES
impl<K, V, Type> NodeRef<marker::DormantMut, K, V, Type> {
    unsafe fn awaken<'a>(self) -> NodeRef<marker::Mut<'a>, K, V, Type>
    //@ req true;
    //@ ens result.node == self.node &*& result.height == self.height;
    //@ on_unwind_ens false;
    {
        NodeRef {
            height: self.height,
            node: self.node,
            _marker: PhantomData,
        }
    }
}

impl<K, V, NodeType, HandleType> Handle<NodeRef<marker::DormantMut, K, V, NodeType>, HandleType> {
    unsafe fn awaken<'a>(self) -> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, HandleType>
    //@ req true;
    /*@
    ens result.node.node == self.node.node &*& result.node.height == self.node.height &*& result.idx == self.idx;
    @*/
    //@ on_unwind_ens false;
    {
        Handle {
            node: unsafe { self.node.awaken() },
            idx: self.idx,
            _marker: PhantomData,
        }
    }
}
// END_WAKE_HANDLES

// BEGIN_DORMANCY
impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn dormant<'b>(&'b self) -> NodeRef<marker::DormantMut, K, V, Type>
    //@ req [?f](*self |-> ?node);
    //@ ens [f](*self |-> node) &*& result.height == node.height &*& result.node == node.node;
    //@ on_unwind_ens false;
    {
        //@ open_points_to(self);
        let result = NodeRef { height: self.height, node: self.node, _marker: PhantomData };
        //@ close_points_to(self, f);
        result
    }
}

impl<'a, K, V, NodeType, HandleType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, HandleType> {
    unsafe fn dormant<'b>(&'b self) -> Handle<NodeRef<marker::DormantMut, K, V, NodeType>, HandleType>
    //@ req [?f](*self |-> ?origin);
    /*@
    ens [f](*self |-> origin) &*& result.node.node == origin.node.node &*&
        result.node.height == origin.node.height &*& result.idx == origin.idx;
    @*/
    //@ on_unwind_ens false;
    {
        //@ open_points_to(self);
        //@ let node_view = precreate_ref(&(*self).node);
        //@ init_ref_readonly(node_view, 1/2);
        let result = Handle {
            node: unsafe { self.node.dormant/*@::<'a,K,V,NodeType,'b>@*/() },
            idx: self.idx,
            _marker: PhantomData,
        };
        //@ end_ref_readonly(node_view);
        //@ merge_fractions points_to(&(*self).node, _);
        //@ close_points_to(self, f);
        result
    }
}
// END_DORMANCY

// The NodeRef in this proof carries pointer and height metadata. The
// contracts for node operations separately require the relevant storage.
/*@
pred<BorrowType,K,V,NodeType> <NodeRef<BorrowType,K,V,NodeType>>.own(t, node) =
    node.node.as_ptr() as usize != 0;

lem NodeRef_own_mono<BorrowType0,BorrowType1,K0,K1,V0,V1,Type0,Type1>()
    req type_interp::<BorrowType0>() &*& type_interp::<BorrowType1>() &*& type_interp::<K0>() &*& type_interp::<K1>() &*&
        type_interp::<V0>() &*& type_interp::<V1>() &*& type_interp::<Type0>() &*& type_interp::<Type1>() &*&
        NodeRef_own::<BorrowType0,K0,V0,Type0>(?t,?node) &*&
        is_subtype_of::<BorrowType0,BorrowType1>() == true &*& is_subtype_of::<K0,K1>() == true &*&
        is_subtype_of::<V0,V1>() == true &*& is_subtype_of::<Type0,Type1>() == true;
    ens type_interp::<BorrowType0>() &*& type_interp::<BorrowType1>() &*& type_interp::<K0>() &*& type_interp::<K1>() &*&
        type_interp::<V0>() &*& type_interp::<V1>() &*& type_interp::<Type0>() &*& type_interp::<Type1>() &*&
        NodeRef_own::<BorrowType1,K1,V1,Type1>(t,NodeRef::<BorrowType1,K1,V1,Type1> { height: upcast::<usize,usize>(node.height), node: upcast(node.node) });
{
    open NodeRef_own::<BorrowType0,K0,V0,Type0>(t,node);
    std::ptr::NonNull_upcast::<LeafNode<K0,V0>,LeafNode<K1,V1>>(node.node);
    let n1 = upcast::<NonNull<LeafNode<K0,V0>>,NonNull<LeafNode<K1,V1>>>(node.node);
    close NodeRef_own::<BorrowType1,K1,V1,Type1>(t,NodeRef::<BorrowType1,K1,V1,Type1> { height: upcast::<usize,usize>(node.height), node: n1 });
}

lem NodeRef_drop<BorrowType,K,V,Type>()
    req NodeRef_own::<BorrowType,K,V,Type>(?t,?node);
    ens <usize>.own(t,node.height) &*& <NonNull<LeafNode<K,V>>>.own(t,node.node);
{
    open NodeRef_own::<BorrowType,K,V,Type>(t,node);
    close usize_own(t,node.height);
    std::ptr::close_NonNull_own(t,node.node);
}
@*/

/*@
fix btree_product(x: i32, y: i32) -> i32 { x * y }
lem btree_distribute(x: i32, y: i32, z: i32)
    req true;
    ens btree_product(x, y + z) == x * y + x * z;
{}
fix btree_nat_value(n: nat) -> i32 {
    match n { zero => 0, succ(n0) => btree_nat_value(n0) + 1 }
}
lem btree_nat_for_usize(n: usize) -> nat
    req 0 <= n;
    ens btree_nat_value(result) == n;
{
    let i = 0;
    let value = zero;
    while i < n
        inv 0 <= i &*& i <= n &*& btree_nat_value(value) == i;
        decreases n - i;
    {
        value = succ(value);
        i = i + 1;
    }
    return value;
}
lem btree_associate(n: nat, b: i32, c: i32)
    req true;
    ens (btree_nat_value(n) * b) * c == btree_nat_value(n) * (b * c);
{
    match n {
        zero => {}
        succ(n0) => {
            btree_associate(n0, b, c);
            btree_distribute(b, btree_nat_value(n0), 1);
            btree_distribute(c, btree_nat_value(n0) * b, b);
            btree_distribute(b * c, btree_nat_value(n0), 1);
        }
    }
}

// Pointer arithmetic preserves alignment when the element stride is aligned.
lem btree_aligned_offset<T>(base: *T, count: usize)
    req 0 <= count &*& (base as usize) % std::mem::align_of::<T>() == 0 &*&
        pointer_within_limits(base) == true &*& pointer_within_limits(base + count) == true;
    ens ((base + count) as usize) % std::mem::align_of::<T>() == 0;
{
    std::alloc::is_valid_layout_size_of_align_of::<T>();
    is_power_of_2_pos(std::mem::align_of::<T>());
    assert ((base + count) as usize) == (base as usize) + count * std::mem::size_of::<T>();
    size_align::<T>();
    div_rem_nonneg(base as usize, std::mem::align_of::<T>());
    div_rem_nonneg(std::mem::size_of::<T>(), std::mem::align_of::<T>());
    let n = btree_nat_for_usize(count);
    btree_associate(n, std::mem::size_of::<T>() / std::mem::align_of::<T>(), std::mem::align_of::<T>());
    btree_distribute(std::mem::align_of::<T>(), (base as usize) / std::mem::align_of::<T>(),
        count * (std::mem::size_of::<T>() / std::mem::align_of::<T>()));
    div_rem_nonneg_unique((base + count) as usize, std::mem::align_of::<T>(),
        (base as usize) / std::mem::align_of::<T>() + count * (std::mem::size_of::<T>() / std::mem::align_of::<T>()), 0);
}


fix btree_encoded<T>(values: list<T>, bytes: list<option<u8>>) -> bool {
    match values {
        nil => bytes == nil,
        cons(v, rest) =>
            length(bytes) == length(values) * std::mem::size_of::<T>() &&
            of_u8s_::<T>(take(std::mem::size_of::<T>(), bytes)) == some(v) &&
            btree_encoded(rest, drop(std::mem::size_of::<T>(), bytes))
    }
}

lem btree_drop_append_left<T>(n: i32, xs: list<T>, ys: list<T>)
    req 0 <= n &*& n <= length(xs);
    ens drop(n, append(xs, ys)) == append(drop(n, xs), ys);
{
    match xs {
        nil => {}
        cons(x, rest) => {
            if n != 0 { btree_drop_append_left(n - 1, rest, ys); }
        }
    }
}

lem btree_encoded_length<T>(values: list<T>, bytes: list<option<u8>>)
    req btree_encoded(values, bytes) == true;
    ens length(bytes) == length(values) * std::mem::size_of::<T>();
{
    match values { nil => {} cons(v, rest) => {} }
}

lem btree_encoded_append<T>(xs: list<T>, xb: list<option<u8>>, ys: list<T>, yb: list<option<u8>>)
    req btree_encoded(xs, xb) == true &*& btree_encoded(ys, yb) == true;
    ens btree_encoded(append(xs, ys), append(xb, yb)) == true;
{
    match xs {
        nil => { assert xb == nil; }
        cons(x, rest) => {
            std::alloc::is_valid_layout_size_of_align_of::<T>();
            btree_encoded_length(xs, xb);
            btree_encoded_length(ys, yb);
            btree_distribute(std::mem::size_of::<T>(), length(xs), length(ys));
            mul_mono_l(1, length(xs), std::mem::size_of::<T>());
            take_append_l(std::mem::size_of::<T>(), xb, yb);
            btree_drop_append_left(std::mem::size_of::<T>(), xb, yb);
            btree_encoded_append(rest, drop(std::mem::size_of::<T>(), xb), ys, yb);
            assert length(append(xb, yb)) == length(append(xs, ys)) * std::mem::size_of::<T>();
            assert of_u8s_::<T>(take(std::mem::size_of::<T>(), append(xb, yb))) == some(x);
            assert btree_encoded(append(rest, ys), drop(std::mem::size_of::<T>(), append(xb, yb))) == true;
        }
    }
}

lem btree_encoded_split<T>(values: list<T>, bytes: list<option<u8>>, count: i32)
    req btree_encoded(values, bytes) == true &*& 0 <= count &*& count <= length(values);
    ens btree_encoded(take(count, values), take(count * std::mem::size_of::<T>(), bytes)) == true &*&
        btree_encoded(drop(count, values), drop(count * std::mem::size_of::<T>(), bytes)) == true;
{
    match values {
        nil => {}
        cons(v, rest) => {
            std::alloc::is_valid_layout_size_of_align_of::<T>();
            btree_encoded_length(values, bytes);
            if count != 0 {
                mul_mono_l(1, length(values), std::mem::size_of::<T>());
                mul_mono_l(1, count, std::mem::size_of::<T>());
                let first = take(std::mem::size_of::<T>(), bytes);
                let tail = drop(std::mem::size_of::<T>(), bytes);
                btree_encoded_split(rest, tail, count - 1);
                append_take_drop_n(bytes, std::mem::size_of::<T>());
                take_append(count * std::mem::size_of::<T>(), first, tail);
                drop_append(count * std::mem::size_of::<T>(), first, tail);
                btree_encoded_append(cons(v, nil), first,
                    take(count - 1, rest), take((count - 1) * std::mem::size_of::<T>(), tail));
            }
        }
    }
}

lem btree_values_to_bytes<T>(p: *T, n: i32)
    req p[..n] |-> ?values &*& p as usize % std::mem::align_of::<T>() == 0;
    ens (p as *u8)[..n * std::mem::size_of::<T>()] |-?-> ?bytes &*& btree_encoded(values, bytes) == true;
{
    std::alloc::is_valid_layout_size_of_align_of::<T>();
    open array(p, n, values);
    if n == 0 {
        close array_::<u8>(p as *u8, 0, nil);
    } else {
        to_u8s_(p);
        array__inv::<u8>();
        assert (p as *u8)[..std::mem::size_of::<T>()] |-?-> ?first;
        btree_aligned_offset(p, 1);
        btree_values_to_bytes(p + 1, n - 1);
        assert ((p + 1) as *u8)[..(n - 1) * std::mem::size_of::<T>()] |-?-> ?tail_bytes;
        btree_encoded_append(cons(head(values), nil), first, tail(values), tail_bytes);
        array__join(p as *u8);
    }
}

lem btree_bytes_to_values<T>(p: *T, values: list<T>)
    req (p as *u8)[..length(values) * std::mem::size_of::<T>()] |-?-> ?bytes &*&
        btree_encoded(values, bytes) == true &*& p as usize % std::mem::align_of::<T>() == 0;
    ens p[..length(values)] |-> values;
{
    match values {
        nil => {
            open array_::<u8>(p as *u8, 0, bytes);
            close array(p, 0, nil);
        }
        cons(v, rest) => {
            std::alloc::is_valid_layout_size_of_align_of::<T>();
            mul_mono_l(1, length(values), std::mem::size_of::<T>());
            btree_distribute(std::mem::size_of::<T>(), 1, length(rest));
            array__split(p as *u8, std::mem::size_of::<T>());
            from_u8s_(p);
            btree_aligned_offset(p, 1);
            btree_bytes_to_values(p + 1, rest);
            close array(p, length(values), values);
        }
    }
}

lem btree_restore_shr<T>(p: *T, n: i32, distance: i32, values: list<T>, bytes: list<option<u8>>)
    req 0 <= distance &*& distance <= n &*& length(values) == n &*&
        btree_encoded(values, bytes) == true &*&
        (p as *u8)[..n * std::mem::size_of::<T>()] |-?-> append(take(distance * std::mem::size_of::<T>(), bytes), take((n - distance) * std::mem::size_of::<T>(), bytes)) &*&
        p as usize % std::mem::align_of::<T>() == 0;
    ens p[..n] |-> append(take(distance, values), take(n - distance, values));
{
    btree_encoded_split(values, bytes, distance);
    btree_encoded_split(values, bytes, n - distance);
    btree_encoded_append(take(distance, values), take(distance * std::mem::size_of::<T>(), bytes), take(n - distance, values), take((n - distance) * std::mem::size_of::<T>(), bytes));
    btree_bytes_to_values(p, append(take(distance, values), take(n - distance, values)));
}

@*/

// The slice-to-pointer cast is the body of [T]::as_mut_ptr. The proof
// generator checks that body and the remaining operations against the library.
// BEGIN_SLICE_INSERT
unsafe fn slice_insert<T>(slice: &mut [MaybeUninit<T>], idx: usize, val: T)
/*@
req thread_token(?t) &*& type_interp::<T>() &*& <T>.own(t,val) &*&
    0 <= idx &*& idx < slice.len() &*& slice.len() <= CAPACITY + 1 &*&
    (slice as *MaybeUninit<T>)[..slice.len()] |-> ?slots;
@*/
/*@
ens thread_token(t) &*& type_interp::<T>() &*& <T>.own(t,val) &*&
    (slice as *MaybeUninit<T>)[..slice.len()] |->
        append(take(idx,slots),cons(MaybeUninit::new(val),take(slice.len() - idx - 1, drop(idx,slots))));
@*/
//@ on_unwind_ens false;
{
    let len = slice.len();
    debug_assert!(len > idx);
    let slice_ptr = slice.as_mut_ptr();
    //@ array_split(slice_ptr,idx);
    //@ let base = slice_ptr + idx;
    //@ let suffix = drop(idx, slots);
    //@ length_drop(idx,slots);
    //@ insertion_slot_limits(base);
    //@ let shifted = append(take(1,suffix),take(len - idx - 1,suffix));
    unsafe {
        if len > idx + 1 {
            //@ btree_values_to_bytes(base, len - idx);
            //@ assert (base as *u8)[..(len - idx) * std::mem::size_of::<MaybeUninit<T>>()] |-?-> ?bytes;
            //@ btree_aligned_offset(base, 1);
            //@ close exists::<bool>(true);
            //@ close exists::<usize>(1);
            ptr::copy(slice_ptr.add(idx), slice_ptr.add(idx + 1), len - idx - 1);
            //@ btree_restore_shr(base,len - idx,1,suffix,bytes);
        } else {
            //@ take_length(suffix);
            //@ take_0(suffix);
            //@ append_nil(suffix);
        }
        //@ length_take(1,suffix);
        //@ drop_append(1,take(1,suffix),take(len - idx - 1,suffix));
        //@ array_split(base,1);
        //@ open array(base,1,take(1,shifted));
        (*slice_ptr.add(idx)).write(val);
        //@ close array(base,1,[MaybeUninit::new(val)]);
        //@ array_join(base);
        //@ array_join(slice_ptr);
    }
}

// END_SLICE_INSERT

/*@
lem insertion_slot_limits<T>(p: *MaybeUninit<T>)
    req p[..?n] |-> ?values &*& n > 0;
    ens p[..n] |-> values &*& p != 0 &*& p as usize != 0 &*& pointer_within_limits(p + 1) == true &*&
        p as usize % std::mem::align_of::<MaybeUninit<T>>() == 0;
{
    array_split(p, 1);
    open array(p, 1, take(1, values));
    points_to_limits(p);
    to_u8s_(p);
    from_u8s_(p);
    std::mem::MaybeUninit__to_MaybeUninit(p);
    close array(p, 1, take(1, values));
    array_join(p);
}
@*/

const KV_IDX_CENTER: usize = B - 1;
//@ fix KV_IDX_CENTER() -> usize { B - 1 }
const EDGE_IDX_LEFT_OF_CENTER: usize = B - 1;
//@ fix EDGE_IDX_LEFT_OF_CENTER() -> usize { B - 1 }
const EDGE_IDX_RIGHT_OF_CENTER: usize = B;
//@ fix EDGE_IDX_RIGHT_OF_CENTER() -> usize { B }

enum LeftOrRight<T> {
    Left(T),
    Right(T),
}

struct SplitResult<'a, K, V, NodeType> {
    // Altered node in existing tree with elements and edges that belong to the left of `kv`.
    pub left: NodeRef<marker::Mut<'a>, K, V, NodeType>,
    // Some key and value that existed before and were split off, to be inserted elsewhere.
    pub kv: (K, V),
    // Owned, unattached, new node with elements and edges that belong to the right of `kv`.
    pub right: NodeRef<marker::Owned, K, V, NodeType>,
}

type Root<K, V> = NodeRef<marker::Owned, K, V, marker::LeafOrInternal>;

/*@
fix insertion_pivot(index: usize) -> usize {
    if index < EDGE_IDX_LEFT_OF_CENTER { KV_IDX_CENTER - 1 } else if index <= EDGE_IDX_RIGHT_OF_CENTER { KV_IDX_CENTER } else { KV_IDX_CENTER + 1 }
}
@*/
unsafe fn splitpoint(edge_idx: usize) -> (usize, LeftOrRight<usize>)
//@ req 0 <= edge_idx &*& edge_idx <= CAPACITY;
/*@
ens 0 <= result.0 &*& result.0 < CAPACITY &*& result.0 == insertion_pivot(edge_idx) &*&
    match result.1 {
        LeftOrRight::Left(index) => 0 <= index &*& index == edge_idx &*& index <= result.0,
        LeftOrRight::Right(index) => 0 <= index &*& edge_idx == result.0 + 1 + index &*& index <= CAPACITY - result.0 - 1
    };
@*/
//@ on_unwind_ens false;
{
    debug_assert!(edge_idx <= CAPACITY);
    // Rust issue #74834 tries to explain these symmetric rules.
    match edge_idx {
        0..EDGE_IDX_LEFT_OF_CENTER => (KV_IDX_CENTER - 1, LeftOrRight::Left(edge_idx)),
        EDGE_IDX_LEFT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Left(edge_idx)),
        EDGE_IDX_RIGHT_OF_CENTER => (KV_IDX_CENTER, LeftOrRight::Right(0)),
        _ => {
            /*@
            if edge_idx < EDGE_IDX_LEFT_OF_CENTER + 1 {
                assert edge_idx == EDGE_IDX_LEFT_OF_CENTER;
            } else if edge_idx < EDGE_IDX_RIGHT_OF_CENTER + 1 {
                assert edge_idx == EDGE_IDX_RIGHT_OF_CENTER;
            }
            @*/
            (KV_IDX_CENTER + 1, LeftOrRight::Right(edge_idx - (KV_IDX_CENTER + 1 + 1)))
        }
    }
}

/*@
// Separating the active child headers is valid even if each child is itself
// internal. Its payload and descendants can stay with the caller.
lem split_linked_headers<K,V>(children: list<NonNull<LeafNode<K,V>>>, parent: NonNull<InternalNode<K,V>>, start: usize, count: usize)
    req linked_headers(children, parent, start) &*& 0 <= count &*& count <= length(children);
    ens linked_headers(take(count,children), parent, start) &*& linked_headers(drop(count,children), parent, start + count);
{
    if count == 0 {
        close linked_headers([], parent, start);
    } else {
        unpack_nonempty(children);
        assert children == cons(?child, ?rest);
        open linked_headers(children, parent, start);
        split_linked_headers(rest, parent, start + 1, count - 1);
        close linked_headers(take(count,children), parent, start);
    }
}

lem join_linked_headers<K,V>(a: list<NonNull<LeafNode<K,V>>>, b: list<NonNull<LeafNode<K,V>>>, parent: NonNull<InternalNode<K,V>>, start: usize)
    req linked_headers(a, parent, start) &*& linked_headers(b, parent, start + length(a));
    ens linked_headers(append(a,b), parent, start);
{
    open linked_headers(a, parent, start);
    match a {
        nil => {}
        cons(child, rest) => {
            join_linked_headers(rest, b, parent, start + 1);
            close linked_headers(append(a,b), parent, start);
        }
    }
}

lem forget_link_indices<K,V>(children: list<NonNull<LeafNode<K,V>>>, parent: NonNull<InternalNode<K,V>>, start: usize)
    req linked_headers(children, parent, start);
    ens child_headers(children);
{
    open linked_headers(children, parent, start);
    match children {
        nil => {}
        cons(child, rest) => { forget_link_indices(rest, parent, start + 1); }
    }
    close child_headers(children);
}

lem take_after_drop<T>(xs: list<T>, first: usize, count: usize)
    req 0 <= first &*& 0 <= count &*& first + count <= length(xs);
    ens take(count, drop(first,xs)) == drop(first,take(first + count,xs));
{
    match xs {
        nil => {}
        cons(x, rest) => {
            if first > 0 { take_after_drop(rest, first - 1, count); }
        }
    }
}

lem take_twice<T>(xs: list<T>, short: usize, long: usize)
    req 0 <= short &*& short <= long &*& long <= length(xs);
    ens take(short,take(long,xs)) == take(short,xs);
{
    match xs {
        nil => {}
        cons(x, rest) => { if short > 0 { take_twice(rest, short - 1, long - 1); } }
    }
}

lem initialized_edge_split<K,V>(children: list<NonNull<LeafNode<K,V>>>, first: usize)
    req 0 <= first &*& first <= length(children);
    ens take(first,initialized_edges(children)) == initialized_edges(take(first,children)) &*&
        drop(first,initialized_edges(children)) == initialized_edges(drop(first,children));
{
    match children {
        nil => {}
        cons(child, rest) => {
            if first > 0 { initialized_edge_split(rest, first - 1); }
        }
    }
}

lem join_segments<T>(base: *T, first: usize, second: usize, prefix: list<T>, suffix: list<T>)
    req (base + first)[..second] |-> suffix &*& base[..first] |-> prefix;
    ens base[..first + second] |-> append(prefix,suffix);
{
    array_join(base);
}

pred node_arrays<K,V>(node: *InternalNode<K,V>; keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>, edges: list<MaybeUninit<NonNull<LeafNode<K,V>>>>) =
    pointer_within_limits(&(*node).data) == true &*& pointer_within_limits(&(*node).data.keys) == true &*&
    pointer_within_limits(&(*node).data.vals) == true &*& pointer_within_limits(&(*node).edges) == true &*&
    (*node).data.keys[..CAPACITY] |-> keys &*& (*node).data.vals[..CAPACITY] |-> vals &*&
    (*node).edges[..CAPACITY + 1] |-> edges;

pred internal_slots<K,V>(node: NonNull<InternalNode<K,V>>, len: usize, children: list<NonNull<LeafNode<K,V>>>; keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>) =
    node_arrays(node.as_ptr(), keys, vals, ?edges) &*& (*node.as_ptr()).data.len |-> (len as u16) &*&
    0 <= len &*& len <= CAPACITY &*& length(children) == len + 1 &*&
    take(len + 1, edges) == initialized_edges(children) &*& linked_headers(children, node, 0);
@*/

unsafe fn fit_node<K, V>(
    parent: NonNull<InternalNode<K, V>>,
    index: usize,
    key: K,
    value: V,
    right: NonNull<LeafNode<K, V>>,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,value) &*&
    ancestors(&(*parent.as_ptr()).data, ?path, ?root) &*& internal_slots(parent, ?len, ?children, ?original_keys, ?original_vals) &*&
    0 <= index &*& index <= len &*& len < CAPACITY &*& (*right.as_ptr()).parent |-> Option::None &*& (*right.as_ptr()).parent_idx |-> _;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,value) &*&
    ancestors(&(*parent.as_ptr()).data, path, root) &*& internal_slots(parent, len + 1, append(take(index + 1,children),cons(right,drop(index + 1,children))), ?fitted_keys, ?fitted_vals);
@*/
//@ on_unwind_ens false;
{
    //@ open internal_slots(parent, len, children, original_keys, original_vals);
    //@ assert node_arrays(parent.as_ptr(), original_keys, original_vals, ?original_edges);
    //@ open node_arrays(parent.as_ptr(), original_keys, original_vals, original_edges);
    let parent_ptr = parent.as_ptr();
    let new_len = unsafe { (*parent_ptr).data.len } as usize + 1;
    let key_base = unsafe { (&raw mut (*parent_ptr).data.keys) as *mut MaybeUninit<K> };
    let val_base = unsafe { (&raw mut (*parent_ptr).data.vals) as *mut MaybeUninit<V> };
    let edge_base = unsafe { (&raw mut (*parent_ptr).edges) as *mut MaybeUninit<BoxedNode<K, V>> };
    //@ array_split(key_base,new_len);
    //@ array_split(val_base,new_len);
    //@ array_split(edge_base,new_len + 1);
    //@ insertion_slot_limits(key_base);
    //@ insertion_slot_limits(val_base);
    //@ insertion_slot_limits(edge_base);
    //@ split_linked_headers(children, parent, 0, index + 1);
    //@ let before = take(index + 1, children);
    //@ let after = drop(index + 1, children);
    //@ length_take(index + 1,children);
    //@ length_drop(index + 1,children);
    //@ forget_link_indices(after, parent, index + 1);
    //@ initialized_edge_split(children,index + 1);
    //@ take_after_drop(original_edges,index + 1,len - index);
    //@ take_after_drop(original_edges,index + 1,len + 1 - index);
    //@ take_twice(drop(index + 1,original_edges),len - index,len + 1 - index);
    //@ take_twice(original_edges,index + 1,len + 2);
    //@ take_twice(original_edges,index + 1,len + 1);

    unsafe {
        slice_insert(std::slice::from_raw_parts_mut(key_base, new_len), index, key);
        slice_insert(std::slice::from_raw_parts_mut(val_base, new_len), index, value);
        //@ std::ptr::close_NonNull_own(t,right);
        //@ produce_type_interp::<NonNull<LeafNode<K,V>>>();
        slice_insert(std::slice::from_raw_parts_mut(edge_base, new_len + 1), index + 1, right);
        //@ leak <NonNull<LeafNode<K,V>>>.own(t,right);
        //@ std::ptr::open_NonNull_own(t,right);
        //@ leak type_interp::<NonNull<LeafNode<K,V>>>();
        (*parent_ptr).data.len = new_len as u16;

        //@ let inserted = cons(right, after);
        //@ assert edge_base[..len + 2] |-> ?filled;
        //@ assert filled == append(initialized_edges(before), initialized_edges(inserted));
        //@ array_split(edge_base,index + 1);
        //@ initialized_edge_count(before);
        //@ initialized_edge_count(inserted);
        //@ take_append_l(index + 1,initialized_edges(before),initialized_edges(inserted));
        //@ take_length(initialized_edges(before));
        //@ drop_append(index + 1,initialized_edges(before),initialized_edges(inserted));
        //@ close child_headers(inserted);
        repair_edges(parent, index + 1, new_len + 1);
        //@ join_linked_headers(before,inserted,parent,0);
        //@ let inactive = drop(len + 2,original_edges);
        //@ join_segments(edge_base + index + 1,len + 1 - index,CAPACITY - len - 1,initialized_edges(inserted),inactive);
        //@ join_segments(edge_base,index + 1,CAPACITY - index,initialized_edges(before),append(initialized_edges(inserted),inactive));
        //@ append_assoc(initialized_edges(before),initialized_edges(inserted),inactive);
        //@ array_join(key_base);
        //@ array_join(val_base);
        //@ assert edge_base[..CAPACITY + 1] |-> ?new_edges;
        //@ assert key_base[..CAPACITY] |-> ?new_keys;
        //@ assert val_base[..CAPACITY] |-> ?new_vals;
        //@ let active = append(initialized_edges(before), initialized_edges(inserted));
        //@ assert new_edges == append(active,inactive);
        //@ initialized_edges_append(before,inserted);
        //@ take_append_l(len + 2, active, inactive);
        //@ take_length(active);
        //@ close node_arrays(parent_ptr, new_keys, new_vals, new_edges);
        //@ close internal_slots(parent, len + 1, append(before,inserted), new_keys, new_vals);
    }
}

// BEGIN_READ_SLOT
unsafe fn read_promoted<T>(slot: *const MaybeUninit<T>) -> T
//@ req thread_token(?t) &*& type_interp::<T>() &*& *slot |-> ?bits &*& bits.inner() == some(?value) &*& <T>.own(t,value);
//@ ens thread_token(t) &*& type_interp::<T>() &*& *slot |-> MaybeUninit::new(value) &*& result == value &*& <T>.own(t,value);
//@ on_unwind_ens false;
{
    //@ open_MaybeUninit(slot);
    //@ points_to_limits(slot as *T);
    let promoted = unsafe { std::ptr::read(slot as *const T) };
    //@ close_MaybeUninit(slot);
    promoted
}
// END_READ_SLOT

unsafe fn split_full_node<K, V>(
    left: NonNull<InternalNode<K, V>>,
    right: NonNull<InternalNode<K, V>>,
    pivot: usize,
) -> (K, V)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    ancestors(&(*left.as_ptr()).data, ?path, ?root) &*&
    ancestors(&(*right.as_ptr()).data, [], &(*right.as_ptr()).data) &*&
    internal_slots(left, CAPACITY, ?children, ?keys, ?vals) &*&
    node_arrays(right.as_ptr(), ?right_keys, ?right_vals, ?right_edges) &*&
    (*right.as_ptr()).data.len |-> 0 &*& 0 <= pivot &*& pivot < CAPACITY &*&
    nth(pivot, keys).inner() == some(?promoted_key) &*& nth(pivot, vals).inner() == some(?promoted_value) &*&
    <K>.own(t, promoted_key) &*& <V>.own(t, promoted_value);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    ancestors(&(*left.as_ptr()).data, path, root) &*&
    ancestors(&(*right.as_ptr()).data, [], &(*right.as_ptr()).data) &*&
    internal_slots(left, pivot, take(pivot + 1, children), ?left_key_bits, ?left_val_bits) &*&
    internal_slots(right, CAPACITY - pivot - 1, drop(pivot + 1, children), ?new_key_bits, ?new_val_bits) &*&
    result.0 == promoted_key &*& result.1 == promoted_value &*& <K>.own(t, promoted_key) &*& <V>.own(t, promoted_value);
@*/
//@ on_unwind_ens false;
{
    //@ open internal_slots(left, CAPACITY, children, keys, vals);
    //@ assert node_arrays(left.as_ptr(), keys, vals, ?edges);
    //@ open node_arrays(left.as_ptr(), keys, vals, edges);
    //@ open node_arrays(right.as_ptr(), right_keys, right_vals, right_edges);
    //@ let left_edge_base = &(*left.as_ptr()).edges as *MaybeUninit<NonNull<LeafNode<K,V>>>;
    //@ let right_edge_base = &(*right.as_ptr()).edges as *MaybeUninit<NonNull<LeafNode<K,V>>>;
    //@ let right_key_base = &(*right.as_ptr()).data.keys as *MaybeUninit<K>;
    //@ let right_val_base = &(*right.as_ptr()).data.vals as *MaybeUninit<V>;
    let key_base = unsafe { (&raw const (*left.as_ptr()).data.keys) as *const MaybeUninit<K> };
    let val_base = unsafe { (&raw const (*left.as_ptr()).data.vals) as *const MaybeUninit<V> };
    //@ array_split(key_base, pivot);
    //@ array_split(key_base + pivot, 1);
    //@ array_split(val_base, pivot);
    //@ array_split(val_base + pivot, 1);
    //@ drop_n_plus_one(pivot, keys);
    //@ drop_n_plus_one(pivot, vals);
    //@ open array(key_base + pivot, 1, take(1, drop(pivot, keys)));
    //@ open array(val_base + pivot, 1, take(1, drop(pivot, vals)));
    let key = unsafe { read_promoted(key_base.add(pivot)) };
    let value = unsafe { read_promoted(val_base.add(pivot)) };
    //@ close array(key_base + pivot, 1, [MaybeUninit::new(promoted_key)]);
    //@ close array(val_base + pivot, 1, [MaybeUninit::new(promoted_value)]);

    //@ let left_children = take(pivot + 1, children);
    //@ let right_children = drop(pivot + 1, children);
    //@ array_split(left_edge_base, pivot + 1);
    //@ array_split(right_edge_base, CAPACITY - pivot);
    //@ array_split(right_key_base, CAPACITY - pivot - 1);
    //@ array_split(right_val_base, CAPACITY - pivot - 1);
    //@ take_length(edges);
    //@ initialized_edge_split(children, pivot + 1);
    //@ length_take(pivot + 1, children);
    //@ length_drop(pivot + 1, children);
    //@ split_linked_headers(children, left, 0, pivot + 1);
    //@ forget_link_indices(right_children, left, pivot + 1);
    //@ open ancestors(&(*right.as_ptr()).data, [], &(*right.as_ptr()).data);
    //@ array_to_array_(right_edge_base);
    //@ array_to_array_(right_key_base);
    //@ array_to_array_(right_val_base);
    unsafe { split_preserves_ancestors(left, right, pivot) };
    //@ close ancestors(&(*right.as_ptr()).data, [], &(*right.as_ptr()).data);

    //@ array_join(key_base + pivot);
    //@ array_join(key_base);
    //@ array_join(val_base + pivot);
    //@ array_join(val_base);
    //@ array_join(left_edge_base);
    //@ array_join(right_key_base);
    //@ array_join(right_val_base);
    //@ array_join(right_edge_base);
    //@ assert left_edge_base[..CAPACITY + 1] |-> ?new_left_edges;
    //@ assert right_edge_base[..CAPACITY + 1] |-> ?new_right_edges;
    //@ assert key_base[..CAPACITY] |-> ?new_left_keys;
    //@ assert val_base[..CAPACITY] |-> ?new_left_vals;
    //@ assert right_key_base[..CAPACITY] |-> ?new_right_keys;
    //@ assert right_val_base[..CAPACITY] |-> ?new_right_vals;
    //@ append_take_drop_n(edges, pivot + 1);
    //@ assert new_left_edges == edges;
    //@ initialized_edge_count(right_children);
    //@ take_append_l(CAPACITY - pivot, initialized_edges(right_children), drop(CAPACITY - pivot, right_edges));
    //@ take_length(initialized_edges(right_children));
    //@ close node_arrays(left.as_ptr(), new_left_keys, new_left_vals, new_left_edges);
    //@ close node_arrays(right.as_ptr(), new_right_keys, new_right_vals, new_right_edges);
    //@ close internal_slots(left, pivot, left_children, new_left_keys, new_left_vals);
    //@ close internal_slots(right, CAPACITY - pivot - 1, right_children, new_right_keys, new_right_vals);
    (key, value)
}

/*@
pred dormant_pair<K,V>(leaf: *LeafNode<K,V>, index: usize; key: MaybeUninit<K>, value: MaybeUninit<V>) =
    (*leaf).len |-> ?len &*& 0 <= index &*& index < len &*& len <= CAPACITY &*&
    *((&(*leaf).keys as *MaybeUninit<K>) + index) |-> key &*&
    *((&(*leaf).vals as *MaybeUninit<V>) + index) |-> value &*&
    key.inner() != none &*& value.inner() != none;
@*/

/*@
pred reserve_allocation(k: lifetime_t, q: real) = [q]lifetime_token(k);

pred allocated_internal<K,V>(node: *InternalNode<K,V>, alloc_id: std::alloc::alloc_id_t, lifetime: lifetime_t, fraction: real) =
    std::alloc::alloc_block_in(alloc_id, node as *u8, std::alloc::Layout::new::<InternalNode<K,V>>()) &*&
    close_points_to_at_lft_token(1, alloc_id.lft, node, ?alloc_fraction) &*&
    close_lifetime_trade_token(alloc_fraction, alloc_id.lft, fraction, lifetime) &*&
    struct_InternalNode_padding(node) &*& struct_LeafNode_padding(&(*node).data);
@*/

unsafe fn fresh_internal<K, V, A: AllocatorClone>(alloc: A) -> (NonNull<InternalNode<K, V>>, A)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<A>(t, alloc, ?alloc_id) &*& exists::<lifetime_t>(?k) &*& [?q]lifetime_token(k) &*& lifetime_inclusion(k, alloc_id.lft) == true;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<A>(t,result.1,alloc_id) &*& [q/2]lifetime_token(k) &*& allocated_internal(result.0.as_ptr(), alloc_id, k, q/2) &*& node_arrays(result.0.as_ptr(), _, _, _) &*&
    ancestors(&(*result.0.as_ptr()).data, [], &(*result.0.as_ptr()).data) &*&
    (*result.0.as_ptr()).data.len |-> 0 &*& (*result.0.as_ptr()).data.parent_idx |-> _;
@*/
//@ on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& [q]lifetime_token(k);
{
    let internal = unsafe { InternalNode::<K,V>::new(alloc) };
    let (node, retained_allocator) = Box::into_non_null_with_allocator(internal);
    //@ let pointer = node.as_ptr();
    // Keep a positive share for the next iteration. The other share can
    // be recovered by closing the freshly opened node storage.
    //@ close reserve_allocation(k,q/2);
    //@ let q_alloc = lifetime_token_trade(k, q/2, alloc_id.lft);
    //@ open_points_to_at_lft(pointer, q_alloc);
    //@ points_to_limits(pointer);
    //@ open_points_to(pointer);
    //@ close node_arrays(pointer, _, _, _);
    //@ close allocated_internal(pointer, alloc_id, k, q/2);
    //@ close link(&(*pointer).data, Option::None, 0);
    //@ close ancestors(&(*pointer).data, [], &(*pointer).data);
    //@ open reserve_allocation(k,q/2);
    (node, retained_allocator)
}

/*@
pred pivot_owner<K,V>(t: thread_id_t, len: usize, index: usize, keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>) =
    if len == CAPACITY {
        nth(insertion_pivot(index), keys).inner() == some(?key) &*&
        nth(insertion_pivot(index), vals).inner() == some(?value) &*&
        <K>.own(t, key) &*& <V>.own(t, value)
    } else { true };

pred route_frames<K,V>(t: thread_id_t, path: list<ParentStep<K,V>>) =
    match path {
        nil => true,
        cons(step, rest) =>
            match step {
                ParentStep(parent, index, len, payload) =>
                    match payload {
                        ParentPayload(keys, vals, edges) =>
                            exists::<list<NonNull<LeafNode<K,V>>>>(?children) &*&
                            length(children) == len + 1 &*& take(len + 1, edges) == initialized_edges(children) &*&
                            linked_headers(take(index, children), NonNull::new(parent), 0) &*&
                            linked_headers(drop(index + 1, children), NonNull::new(parent), index + 1) &*&
                            pivot_owner(t, len, index, keys, vals) &*& struct_LeafNode_padding(&(*parent).data) &*& struct_InternalNode_padding(parent) &*& route_frames(t, rest)
                    }
            }
    };

lem nth_initialized_edge<K,V>(children: list<NonNull<LeafNode<K,V>>>, index: i32)
    req 0 <= index &*& index < length(children);
    ens nth(index, initialized_edges(children)) == MaybeUninit::new(nth(index, children));
{
    match children {
        nil => {}
        cons(child, rest) => { if index > 0 { nth_initialized_edge(rest, index - 1); } }
    }
}

lem nth_take_range<T>(items: list<T>, len: i32, index: i32)
    req 0 <= index &*& index < len &*& len <= length(items);
    ens nth(index, take(len, items)) == nth(index, items);
{
    match items {
        nil => {}
        cons(item, rest) => { if index > 0 { nth_take_range(rest, len - 1, index - 1); } }
    }
}

lem nth_at_partition<T>(items: list<T>, index: i32)
    req 0 <= index &*& index < length(items);
    ens append(take(index, items),cons(nth(index,items), drop(index + 1,items))) == items;
{
    drop_n_plus_one(index, items);
    append_take_drop_n(items, index);
}

lem expose_receiving_node<K,V>(
    t: thread_id_t, child: *LeafNode<K,V>, parent: NonNull<InternalNode<K,V>>, index: u16,
    len: u16, keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>, edges: list<MaybeUninit<NonNull<LeafNode<K,V>>>>,
    higher: list<ParentStep<K,V>>
)
    req child != 0 &*& pointer_within_limits(child) == true &*&
        link(child, Option::Some(parent), index) &*& parent_payload(child, parent.as_ptr(), index, len, ParentPayload(keys,vals,edges)) &*&
        route_frames(t, cons(ParentStep(parent.as_ptr(), index, len, ParentPayload(keys,vals,edges)), higher));
    ens internal_slots(parent, len, ?children, keys, vals) &*& 0 <= index &*& index <= len &*&
        nth(index, children) == NonNull::new(child) &*& pivot_owner(t, len, index, keys, vals) &*& route_frames(t, higher) &*& struct_LeafNode_padding(&(*parent.as_ptr()).data) &*& struct_InternalNode_padding(parent.as_ptr());
{
    open link(child, Option::Some(parent), index);
    open parent_payload(child, parent.as_ptr(), index, len, ParentPayload(keys,vals,edges));
    open route_frames(t, cons(ParentStep(parent.as_ptr(), index, len, ParentPayload(keys,vals,edges)), higher));
    assert exists::<list<NonNull<LeafNode<K,V>>>>(?all_children);
    open exists::<list<NonNull<LeafNode<K,V>>>>(all_children);
    std::ptr::NonNull_new_as_ptr(parent);
    assert 0 <= index;
    nth_take_range(edges, len + 1, index);
    nth_initialized_edge(all_children, index);
    assert (nth(index, edges)).inner() == some(nth(index, all_children));
    assert (nth(index, edges)).inner() == some(NonNull::new(child));
    let focus = nth(index, all_children);
    assert focus == NonNull::new(child);
    points_to_limits(&(*child).parent);
    assert child != 0 &*& pointer_within_limits(child) == true;
    close linked_headers([], parent, index + 1);
    close linked_headers([focus], parent, index);
    join_linked_headers([focus], drop(index + 1,all_children), parent, index);
    length_take(index, all_children);
    join_linked_headers(take(index,all_children), cons(focus,drop(index + 1,all_children)), parent, 0);
    nth_at_partition(all_children, index);
    close node_arrays(parent.as_ptr(), keys, vals, edges);
    close internal_slots(parent, len, all_children, keys, vals);
}
@*/

unsafe fn open_next_parent<K, V>(
    child: *const LeafNode<K, V>,
) -> Option<(NonNull<InternalNode<K, V>>, u16)>
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    child != 0 &*& pointer_within_limits(child) == true &*&
    ancestors(child, ?path, ?root) &*& route_frames(t, path);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    match result {
        Option::None => path == [] &*& ancestors(child, path, root) &*& route_frames(t, path),
        Option::Some(step) =>
            path == cons(ParentStep(step.0.as_ptr(), step.1, ?len, ParentPayload(?keys, ?vals, ?edges)), ?higher) &*&
            ancestors(&(*step.0.as_ptr()).data, higher, root) &*& route_frames(t, higher) &*&
            internal_slots(step.0, len, ?children, keys, vals) &*& 0 <= step.1 &*& step.1 <= len &*& len <= CAPACITY &*&
            nth(step.1,children) == NonNull::new(child) &*&
            pivot_owner(t, len, step.1, keys, vals) &*& struct_LeafNode_padding(&(*step.0.as_ptr()).data) &*& struct_InternalNode_padding(step.0.as_ptr())
    };
@*/
//@ on_unwind_ens false;
{
    //@ open ancestors(child, path, root);
    //@ open link(child, _, _);
    let backlink = unsafe { (*child).parent };
    match backlink {
        None => {
            //@ assert path == [];
            //@ close link(child, Option::None, 0);
            //@ close ancestors(child, [], root);
            None
        }
        Some(parent) => {
            //@ assert path == cons(ParentStep(?parent_ptr, ?index, ?len, ParentPayload(?keys, ?vals, ?edges)), ?higher);
            //@ std::ptr::NonNull_new_as_ptr(parent);
            //@ open_MaybeUninit(&(*child).parent_idx);
            //@ points_to_limits(&(*child).parent_idx as *u16);
            let observed_index = unsafe { *((&raw const (*child).parent_idx) as *const u16) };
            //@ close_MaybeUninit(&(*child).parent_idx);
            //@ open parent_payload(child, parent_ptr, index, len, ParentPayload(keys,vals,edges));
            //@ assert parent == NonNull::new(parent_ptr);
            //@ std::ptr::NonNull_as_ptr_new(parent_ptr);
            //@ close parent_payload(child, parent_ptr, index, len, ParentPayload(keys,vals,edges));
            //@ close link(child, Option::Some(parent), index);
            //@ expose_receiving_node(t, child, parent, index, len, keys, vals, edges, higher);
            Some((parent, observed_index))
        }
    }
}

impl<'tree,K,V> NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal> {
    unsafe fn ascend(mut self) -> Result<Handle<NodeRef<marker::Mut<'tree>, K, V, marker::Internal>, marker::Edge>, Self>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        ancestors(self.node.as_ptr(), ?path, ?root) &*& route_frames(t, path) &*&
        0 <= self.height &*& self.height + length(path) < usize::MAX;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        match result {
            Result::Err(detached) => detached == self &*& path == [] &*& ancestors(self.node.as_ptr(), path, root) &*& route_frames(t, path),
            Result::Ok(edge) =>
                exists::<NonNull<InternalNode<K,V>>>(?parent) &*& edge.node.node.as_ptr() == parent.as_ptr() as *LeafNode<K,V> &*&
                path == cons(ParentStep(parent.as_ptr(), ?idx, ?len, ParentPayload(?keys, ?vals, ?edges)), ?higher) &*&
                edge.idx == idx &*& edge.node.height == self.height + 1 &*& edge.idx <= len &*& len <= CAPACITY &*&
                ancestors(&(*parent.as_ptr()).data, higher, root) &*& route_frames(t, higher) &*&
                ready_parent(t,parent,len,idx,?children,keys,vals) &*& nth(idx,children) == self.node &*&
                struct_LeafNode_padding(&(*parent.as_ptr()).data) &*& struct_InternalNode_padding(parent.as_ptr())
        };
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert [?q]points_to(&self, ?original);
        //@ let view = precreate_ref(&self);
        //@ init_ref_readonly(view, 1/2);
        let leaf_ptr: *const _ = unsafe { Self::as_leaf_ptr(&self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self, _);
        //@ open_points_to(&self);
        let height = self.height;
        let node = self.node;
        //@ close_points_to(&self, q);
        //@ std::ptr::NonNull_as_ptr_nonnull(original.node);
        //@ std::ptr::NonNull_new_as_ptr(original.node);
        let successor = unsafe { open_next_parent(leaf_ptr) };
        let result = match successor {
            None => None,
            Some((parent, observed_index)) => {
                //@ assert path == cons(ParentStep(parent.as_ptr(), observed_index, ?len, ParentPayload(?keys, ?vals, ?edges)), ?higher);
                //@ close ready_parent(t,parent,len,observed_index,_,keys,vals);
                //@ close exists(parent);
                let parent_height = height + 1;
                Some(Handle {
                    node: unsafe { NodeRef::from_internal(parent, parent_height) },
                    idx: observed_index as usize,
                    _marker: PhantomData,
                })
            }
        };
        result.ok_or(NodeRef { height, node, _marker: PhantomData })
    }
}

impl<BorrowType,K,V> NodeRef<BorrowType,K,V,marker::Internal> {
    unsafe fn from_internal(node: NonNull<InternalNode<K, V>>, height: usize) -> Self
    //@ req height > 0;
    //@ ens result.node.as_ptr() == node.as_ptr() as *LeafNode<K,V> &*& result.height == height;
    //@ on_unwind_ens false;
    {
        debug_assert!(height > 0);
        //@ std::ptr::NonNull_as_ptr_as_usize_nonzero(node);
        let leaf = unsafe { NonNull::new_unchecked(node.as_ptr() as *mut LeafNode<K, V>) };
        NodeRef { height, node: leaf, _marker: PhantomData }
    }
}

/*@
pred failed_full_parent<K,V>(
    t: thread_id_t, id: std::alloc::alloc_id_t, k: lifetime_t,
    parent: NonNull<InternalNode<K,V>>, index: usize,
    children: list<NonNull<LeafNode<K,V>>>,
    keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>, sibling: Option<NonNull<InternalNode<K,V>>>
) =
    match sibling {
        Option::None =>
            internal_slots(parent,CAPACITY,children,keys,vals) &*& pivot_owner(t,CAPACITY,index,keys,vals),
        Option::Some(fresh) =>
            internal_slots(parent,insertion_pivot(index),take(insertion_pivot(index)+1,children),_,_) &*&
            internal_slots(fresh,CAPACITY-insertion_pivot(index)-1,drop(insertion_pivot(index)+1,children),_,_) &*&
            ancestors(&(*fresh.as_ptr()).data,[],&(*fresh.as_ptr()).data) &*& (*fresh.as_ptr()).data.parent_idx |-> _ &*&
            allocated_internal(fresh.as_ptr(),id,k,_)
    };
@*/

/*@
pred ready_parent<K,V>(
    t: thread_id_t,
    parent: NonNull<InternalNode<K,V>>, len: usize, index: usize,
    children: list<NonNull<LeafNode<K,V>>>, slots_k: list<MaybeUninit<K>>, slots_v: list<MaybeUninit<V>>
) = internal_slots(parent,len,children,slots_k,slots_v) &*& pivot_owner(t,len,index,slots_k,slots_v);
@*/

// Check the dispatch and result ownership for both library insert methods.
// Allocation and array updates use the verified storage operations in insertion.rs.

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

impl<K, V, Type> NodeRef<marker::Owned, K, V, Type> {
    unsafe fn borrow_mut<'b>(&'b mut self) -> NodeRef<marker::Mut<'b>, K, V, Type>
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

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Leaf> {
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

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge> {
    unsafe fn new_edge(node: NodeRef<BorrowType, K, V, marker::Leaf>, idx: usize) -> Self
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

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::KV> {
    unsafe fn new_kv(node: NodeRef<BorrowType, K, V, marker::Leaf>, idx: usize) -> Self
    //@ req (*node.node.as_ptr()).len |-> ?len &*& idx < len;
    //@ ens result.node == node &*& result.idx == idx &*& (*node.node.as_ptr()).len |-> len;
    //@ on_unwind_ens false;
    {
        unsafe { debug_assert!(idx < node.len()) };
        let edge = Handle { node, idx, _marker: PhantomData };
        //@ close_points_to(&node, 1/2);
        edge
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    unsafe fn len(&self) -> usize
    //@ req [?f](*self |-> ?node) &*& [?ql]((*(node.node.as_ptr() as *InternalNode<K,V>)).data.len |-> ?len);
    //@ ens [f](*self |-> node) &*& [ql]((*(node.node.as_ptr() as *InternalNode<K,V>)).data.len |-> len) &*& result == len;
    //@ on_unwind_ens false;
    {
        //@ open_points_to(self);
        let ptr = self.node.as_ptr() as *mut InternalNode<K,V>;
        //@ close_points_to(self, f);
        unsafe { (*ptr).data.len as usize }
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge> {
    unsafe fn new_edge(node: NodeRef<BorrowType, K, V, marker::Internal>, idx: usize) -> Self
    //@ req (*(node.node.as_ptr() as *InternalNode<K,V>)).data.len |-> ?len &*& idx <= len;
    //@ ens result.node == node &*& result.idx == idx &*& (*(node.node.as_ptr() as *InternalNode<K,V>)).data.len |-> len;
    //@ on_unwind_ens false;
    {
        unsafe { debug_assert!(idx <= node.len()) };
        let edge = Handle { node, idx, _marker: PhantomData };
        //@ close_points_to(&node, 1/2);
        edge
    }
}

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::KV> {
    unsafe fn new_kv(node: NodeRef<BorrowType, K, V, marker::Internal>, idx: usize) -> Self
    //@ req (*(node.node.as_ptr() as *InternalNode<K,V>)).data.len |-> ?len &*& idx < len;
    //@ ens result.node == node &*& result.idx == idx &*& (*(node.node.as_ptr() as *InternalNode<K,V>)).data.len |-> len;
    //@ on_unwind_ens false;
    {
        unsafe { debug_assert!(idx < node.len()) };
        let edge = Handle { node, idx, _marker: PhantomData };
        //@ close_points_to(&node, 1/2);
        edge
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
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

impl<BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::Edge> {
    unsafe fn new_edge(node: NodeRef<BorrowType, K, V, marker::LeafOrInternal>, idx: usize) -> Self
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

impl<'a,K,V> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,marker::Edge> {
    unsafe fn insert_fit(self, key: K, val: V) -> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,marker::KV>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        <K>.own(t,key) &*& <V>.own(t,val) &*& leaf_slots(self.node.node.as_ptr(),?len,_,_) &*&
        0 <= self.idx &*& self.idx <= len &*& len < CAPACITY;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        result.node == self.node &*& result.idx == self.idx &*&
        dormant_pair(self.node.node.as_ptr(),self.idx,MaybeUninit::new(key),MaybeUninit::new(val)) &*&
        leaf_rest(self.node.node.as_ptr(),self.idx);
    @*/
    //@ on_unwind_ens false;
    {
        unsafe { fit_leaf(self.node.node, self.idx, key, val) };
        //@ open dormant_pair(self.node.node.as_ptr(),self.idx,MaybeUninit::new(key),MaybeUninit::new(val));
        let kv_handle = unsafe {
            Handle::<NodeRef<marker::Mut<'_>, K, V, marker::Leaf>, marker::KV>::new_kv(self.node, self.idx)
        };
        //@ close dormant_pair(self.node.node.as_ptr(),self.idx,MaybeUninit::new(key),MaybeUninit::new(val));
        kv_handle
    }
}

/*@
pred leaf_split_on_unwind<K,V>(
    t: thread_id_t, left: NonNull<LeafNode<K,V>>, index: usize,
    id: std::alloc::alloc_id_t, k: lifetime_t, keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>,
    sibling: Option<NonNull<LeafNode<K,V>>>
) =
    match sibling {
        Option::None => leaf_slots(left.as_ptr(),CAPACITY,keys,vals) &*& pivot_owner(t,CAPACITY,index,keys,vals),
        Option::Some(right) => allocated_leaf(right.as_ptr(),id,k,_) &*& detached_child(right.as_ptr()) &*&
            leaf_slots(left.as_ptr(),insertion_pivot(index),_,_) &*& leaf_slots(right.as_ptr(),CAPACITY-insertion_pivot(index)-1,_,_)
    };
@*/

impl<'a,K,V> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,marker::KV> {
    unsafe fn split<A: AllocatorClone>(self, alloc: A) -> SplitResult<'a,K,V,marker::Leaf>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t,alloc,?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k,id.lft) == true &*&
        exists::<usize>(?index) &*& self.idx == insertion_pivot(index) &*& self.node.height == 0 &*& 0 <= self.idx &*& self.idx < CAPACITY &*&
        leaf_slots(self.node.node.as_ptr(),CAPACITY,?keys,?vals) &*& pivot_owner(t,CAPACITY,index,keys,vals);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*& [available/2]lifetime_token(k) &*&
        result.left == self.node &*& result.right.height == 0 &*&
        exists::<NonNull<LeafNode<K,V>>>(?fresh) &*& result.right.node == fresh &*&
        allocated_leaf(result.right.node.as_ptr(),id,k,_) &*& detached_child(result.right.node.as_ptr()) &*&
        leaf_slots(result.left.node.as_ptr(),self.idx,_,_) &*& leaf_slots(result.right.node.as_ptr(),CAPACITY-self.idx-1,_,_) &*&
        <K>.own(t,result.kv.0) &*& <V>.own(t,result.kv.1);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [?rest]lifetime_token(k) &*& exists::<Option<NonNull<LeafNode<K,V>>>>(?sibling) &*&
        leaf_split_on_unwind(t,self.node.node,index,id,k,keys,vals,sibling);
    @*/
    {
        //@ open exists(index);
        //@ let left = self.node.node;
        //@ close exists::<Option<NonNull<LeafNode<K,V>>>>(Option::None);
        //@ close leaf_split_on_unwind(t,left,index,id,k,keys,vals,Option::None);
        let (right, allocator) = unsafe { fresh_leaf(alloc) };
        //@ open leaf_split_on_unwind(t,left,index,id,k,keys,vals,Option::None);
        //@ open exists::<Option<NonNull<LeafNode<K,V>>>>(Option::None);
        //@ open pivot_owner(t,CAPACITY,index,keys,vals);
        let kv = unsafe { split_full_leaf(self.node.node, right, self.idx) };
        //@ close exists(Option::Some(right));
        //@ close leaf_split_on_unwind(t,left,index,id,k,keys,vals,Option::Some(right));
        // MIR tracks the two fields separately because leaf_split_result moves them separately.
        unsafe { drop_allocator(allocator) };
        //@ open leaf_split_on_unwind(t,left,index,id,k,keys,vals,Option::Some(right));
        //@ open exists(Option::Some(right));
        //@ close exists(right);
        unsafe { leaf_split_result/*@::<'a,K,V>@*/(self.node.node,right,kv.0,kv.1) }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,marker::Edge> {
    unsafe fn insert<A: AllocatorClone>(
        self, key: K, val: V, alloc: A,
    ) -> (
        Option<SplitResult<'a, K, V, marker::Leaf>>,
        Handle<NodeRef<marker::DormantMut, K, V, marker::Leaf>, marker::KV>,
    )
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t,alloc,?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*&
        lifetime_inclusion(k,id.lft) == true &*& self.node.height == 0 &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        ancestors(self.node.node.as_ptr(),?path,?root) &*& (*root).parent_idx |-> ?root_index &*&
        struct_LeafNode_padding(self.node.node.as_ptr()) &*&
        leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= self.idx &*& self.idx <= len &*& pivot_owner(t,len,self.idx,keys,vals);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [?remaining]lifetime_token(k) &*& <K>.own(t,key) &*& <V>.own(t,val) &*& result.1.node.height == 0 &*&
        ancestors(self.node.node.as_ptr(),path,root) &*& (*root).parent_idx |-> root_index &*&
        struct_LeafNode_padding(self.node.node.as_ptr()) &*&
        dormant_pair(result.1.node.node.as_ptr(),result.1.idx,MaybeUninit::new(key),MaybeUninit::new(val)) &*&
        leaf_insert_sibling(result, self, t, len, id, k);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [?remaining]lifetime_token(k) &*& len == CAPACITY &*&
        ancestor_tail(self.node.node.as_ptr(),path,root,root_index,?parent,?idx) &*&
        leaf_header(self.node.node.as_ptr(),parent,idx) &*& leaf_slots(self.node.node.as_ptr(),len,keys,vals) &*&
        nth(insertion_pivot(self.idx),keys).inner() == some(?promoted_key) &*&
        nth(insertion_pivot(self.idx),vals).inner() == some(?promoted_val) &*&
        <K>.own(t,promoted_key) &*& <V>.own(t,promoted_val);
    @*/
    {
        //@ let entry = self;
        //@ let leaf = self.node.node.as_ptr();
        //@ open_ancestor_header(leaf,path,root);
        let result = unsafe { self.insert_leaf_production/*@::<'a,K,V,A>@*/(key, val, alloc) };
        //@ close_ancestor_header(leaf,path,root);
        //@ close leaf_insert_sibling(result,entry,t,len,id,k);
        result
    }
}

impl<'a,K,V> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Internal>,marker::Edge> {
    unsafe fn insert_fit(&mut self, key: K, val: V, edge: Root<K,V>)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> ?incoming &*& incoming.node.height > 0 &*& edge.height == incoming.node.height - 1 &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& incoming.node.node.as_ptr() == parent.as_ptr() as *LeafNode<K,V> &*&
        internal_slots(parent,?len,?children,_,_) &*& 0 <= incoming.idx &*& incoming.idx <= len &*& len < CAPACITY &*&
        ancestors(&(*parent.as_ptr()).data,?path,?root) &*& detached_child(edge.node.as_ptr()) &*&
        <K>.own(t,key) &*& <V>.own(t,val);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& *self |-> incoming &*&
        ancestors(&(*parent.as_ptr()).data,path,root) &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        internal_slots(parent,len+1,append(take(incoming.idx+1,children),cons(edge.node,drop(incoming.idx+1,children))),_,_);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(parent);
        //@ open_points_to(self);
        //@ open_points_to(&(*self).node);
        let ptr = self.node.node.as_ptr() as *mut InternalNode<K,V>;
        let index = self.idx;
        //@ close_points_to(&(*self).node);
        //@ close_points_to(self);
        let receiver = unsafe { NonNull::new_unchecked(ptr) };
        //@ std::ptr::NonNull_new_as_ptr(receiver);
        //@ std::ptr::NonNull_new_as_ptr(parent);
        //@ open detached_child(edge.node.as_ptr());
        unsafe { fit_node(receiver,index,key,val,edge.node) };
    }
}

impl<'a,K,V> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Internal>,marker::KV> {
    unsafe fn split<A: AllocatorClone>(self, alloc: A) -> SplitResult<'a,K,V,marker::Internal>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t,alloc,?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k,id.lft) == true &*&
        exists::<usize>(?index) &*& self.idx == insertion_pivot(index) &*& self.node.height > 0 &*& 0 <= self.idx &*& self.idx < CAPACITY &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& self.node.node.as_ptr() == parent.as_ptr() as *LeafNode<K,V> &*&
        ancestors(&(*parent.as_ptr()).data,?path,?root) &*& internal_slots(parent,CAPACITY,?children,?keys,?vals) &*&
        pivot_owner(t,CAPACITY,index,keys,vals);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*& [available/2]lifetime_token(k) &*&
        result.left == self.node &*& result.right.height == self.node.height &*&
        exists::<NonNull<InternalNode<K,V>>>(?fresh) &*& result.right.node.as_ptr() == fresh.as_ptr() as *LeafNode<K,V> &*&
        allocated_internal(fresh.as_ptr(),id,k,_) &*& (*fresh.as_ptr()).data.parent_idx |-> _ &*&
        ancestors(&(*parent.as_ptr()).data,path,root) &*& ancestors(&(*fresh.as_ptr()).data,[],&(*fresh.as_ptr()).data) &*&
        internal_slots(parent,self.idx,take(self.idx+1,children),_,_) &*&
        internal_slots(fresh,CAPACITY-self.idx-1,drop(self.idx+1,children),_,_) &*&
        <K>.own(t,result.kv.0) &*& <V>.own(t,result.kv.1) &*&
        nth(self.idx,keys).inner() == some(result.kv.0) &*& nth(self.idx,vals).inner() == some(result.kv.1);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [?remaining]lifetime_token(k) &*& ancestors(&(*parent.as_ptr()).data,path,root) &*&
        exists::<Option<NonNull<InternalNode<K,V>>>>(?sibling) &*& failed_full_parent(t,id,k,parent,index,children,keys,vals,sibling);
    @*/
    {
        //@ open exists(parent);
        //@ open exists(index);
        let parent_ptr = self.node.node.as_ptr() as *mut InternalNode<K,V>;
        let receiver = unsafe { NonNull::new_unchecked(parent_ptr) };
        //@ std::ptr::NonNull_new_as_ptr(receiver);
        //@ std::ptr::NonNull_new_as_ptr(parent);
        //@ close exists::<Option<NonNull<InternalNode<K,V>>>>(Option::None);
        //@ close failed_full_parent(t,id,k,parent,index,children,keys,vals,Option::None);
        let (fresh, allocator) = unsafe { fresh_internal(alloc) };
        //@ open exists::<Option<NonNull<InternalNode<K,V>>>>(Option::None);
        //@ open failed_full_parent(t,id,k,parent,index,children,keys,vals,Option::None);
        //@ open pivot_owner(t,CAPACITY,index,keys,vals);
        let kv = unsafe { split_full_node(receiver,fresh,self.idx) };
        //@ close exists(Option::Some(fresh));
        //@ close failed_full_parent(t,id,k,parent,index,children,keys,vals,Option::Some(fresh));
        //@ close_tuple_2_own(t,kv);
        unsafe { drop_allocator(allocator) };
        //@ open_tuple_2_own(t,kv);
        //@ open exists(Option::Some(fresh));
        //@ open failed_full_parent(t,id,k,parent,index,children,keys,vals,Option::Some(fresh));
        let right = unsafe { NonNull::new_unchecked(fresh.as_ptr() as *mut LeafNode<K,V>) };
        //@ close exists(fresh);
        let height = self.node.height;
        SplitResult {
            left: self.node,
            kv,
            right: NodeRef { height, node: right, _marker: PhantomData },
        }
    }
}

impl<'tree,K,V> Handle<NodeRef<marker::Mut<'tree>,K,V,marker::Internal>,marker::Edge> {
    // BEGIN_INTERNAL_DISPATCH
    unsafe fn insert_exact<A: AllocatorClone>(mut self, key: K, val: V, edge: Root<K,V>, alloc: A)
        -> Option<SplitResult<'tree,K,V,marker::Internal>>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t,alloc,?id) &*&
        exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k,id.lft) == true &*&
        <K>.own(t,key) &*& <V>.own(t,val) &*& 0 < self.node.height &*& self.node.height <= usize::MAX &*& edge.height == self.node.height - 1 &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& self.node.node.as_ptr() == parent.as_ptr() as *LeafNode<K,V> &*&
        ready_parent(t,parent,?len,self.idx,?children,?keys,?vals) &*&
        ancestors(&(*parent.as_ptr()).data,?path,?root) &*& 0 <= self.idx &*& self.idx <= len &*& len <= CAPACITY &*&
        detached_child(edge.node.as_ptr());
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        ancestors(&(*parent.as_ptr()).data,path,root) &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        [?remaining]lifetime_token(k) &*&
        match result {
            Option::None => len < CAPACITY &*& internal_slots(parent,len+1,append(take(self.idx+1,children),cons(edge.node,drop(self.idx+1,children))),_,_),
            Option::Some(split) => len == CAPACITY &*&
                split.left.node.as_ptr() == parent.as_ptr() as *LeafNode<K,V> &*&
                split.left.height == self.node.height &*& split.right.height == self.node.height &*&
                exists::<NonNull<InternalNode<K,V>>>(?fresh) &*& split.right.node.as_ptr() == fresh.as_ptr() as *LeafNode<K,V> &*&
                allocated_internal(fresh.as_ptr(),id,k,_) &*& (*fresh.as_ptr()).data.parent_idx |-> _ &*&
                ancestors(&(*fresh.as_ptr()).data,[],&(*fresh.as_ptr()).data) &*&
                internal_slots(parent,?left_len,_,_,_) &*& internal_slots(fresh,?right_len,_,_,_) &*& left_len + right_len == CAPACITY &*&
                <K>.own(t,split.kv.0) &*& <V>.own(t,split.kv.1) &*&
                nth(insertion_pivot(self.idx),keys).inner() == some(split.kv.0) &*& nth(insertion_pivot(self.idx),vals).inner() == some(split.kv.1)
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        ancestors(&(*parent.as_ptr()).data,path,root) &*&
        [?remaining]lifetime_token(k) &*&
        if len < CAPACITY {
            <K>.own(t,key) &*& <V>.own(t,val) &*& internal_slots(parent,len+1,append(take(self.idx+1,children),cons(edge.node,drop(self.idx+1,children))),_,_)
        } else {
            detached_child(edge.node.as_ptr()) &*&
            exists::<Option<NonNull<InternalNode<K,V>>>>(?sibling) &*& failed_full_parent(t,id,k,parent,self.idx,children,keys,vals,sibling)
        };
    @*/
    {
        //@ open exists(k);
        //@ open exists(parent);
        //@ assert [?fraction]points_to(&self,?incoming);
        //@ let index = incoming.idx;
        //@ open_points_to(&self);
        //@ open_points_to(&self.node);
        assert!(edge.height == self.node.height - 1);
        //@ close_points_to(&self.node,fraction);
        //@ open ready_parent(t,parent,len,index,children,keys,vals);
        //@ open internal_slots(parent,len,children,keys,vals);
        //@ let view = precreate_ref(&self.node);
        //@ init_ref_readonly(view,1/2);
        let fits = unsafe { self.node.len() < CAPACITY };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self.node,_);
        //@ close internal_slots(parent,len,children,keys,vals);
        if fits {
            //@ open pivot_owner(t,len,index,keys,vals);
            //@ close exists(parent);
            unsafe { self.insert_fit/*@::<'tree,K,V,'tree>@*/(key, val, edge) };
            //@ std::alloc::Allocator_to_own(alloc);
            None
        } else {
            let (middle_kv_idx, insertion) = unsafe { splitpoint(self.idx) };
            //@ open internal_slots(parent,len,children,keys,vals);
            //@ open_points_to(&self.node);
            let node = NodeRef::<marker::Mut<'tree>, K, V, marker::Internal> {
                height: self.node.height,
                node: self.node.node,
                _marker: PhantomData,
            };
            //@ close_points_to(&self.node);
            //@ close Handle_node_(&self, some(incoming.node));
            let middle = unsafe {
                Handle::<NodeRef<marker::Mut<'_>, K, V, marker::Internal>, marker::KV>::new_kv/*@::<marker::Mut<'tree>,K,V>@*/(
                    node, middle_kv_idx,
                )
            };
            //@ close internal_slots(parent,len,children,keys,vals);
            //@ close exists(k);
            //@ close exists(index);
            //@ close exists(parent);
            let mut result = unsafe { middle.split/*@::<'tree,K,V,A>@*/(alloc) };
            //@ open exists::<NonNull<InternalNode<K,V>>>(?fresh);
            let mut insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    //@ open internal_slots(parent,middle_kv_idx,take(middle_kv_idx+1,children),_,_);
                    let selected = Handle::<NodeRef<marker::Mut<'_>, K, V, marker::Internal>, marker::Edge>::new_edge(
                        result.left.reborrow_mut(), insert_idx,
                    );
                    //@ close internal_slots(parent,middle_kv_idx,take(middle_kv_idx+1,children),_,_);
                    selected
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    //@ open internal_slots(fresh,CAPACITY-middle_kv_idx-1,drop(middle_kv_idx+1,children),_,_);
                    let selected = Handle::<NodeRef<marker::Mut<'_>, K, V, marker::Internal>, marker::Edge>::new_edge(
                        result.right.borrow_mut(), insert_idx,
                    );
                    //@ close internal_slots(fresh,CAPACITY-middle_kv_idx-1,drop(middle_kv_idx+1,children),_,_);
                    selected
                },
            };
            /*@ match insertion {
                LeftOrRight::Left(at) => { close exists(parent); }
                LeftOrRight::Right(at) => { close exists(fresh); }
            } @*/
            //@ close_points_to(&insertion_edge.node);
            unsafe { insertion_edge.insert_fit/*@::<'tree,K,V,'tree>@*/(key, val, edge) };
            //@ open_points_to(&insertion_edge);
            //@ open_points_to(&insertion_edge.node);
            //@ close exists(fresh);
            let output = Some(result);
            output
        }
    }
    // END_INTERNAL_DISPATCH
}

// Project the two internal roots to their leaf prefixes for the propagation
// invariant. The dispatch itself uses the whole internal allocation.
impl<'tree, K: 'tree, V: 'tree> Handle<NodeRef<marker::Mut<'tree>, K, V, marker::Internal>, marker::Edge> {
    unsafe fn insert<A: AllocatorClone>(self, key: K, val: V, edge: Root<K,V>, alloc: A)
        -> Option<SplitResult<'tree,K,V,marker::Internal>>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t,alloc,?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*&
        lifetime_inclusion(k,id.lft) == true &*& self.node.height > 0 &*& edge.height == self.node.height - 1 &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& self.node.node.as_ptr() == &(*parent.as_ptr()).data &*&
        ready_parent(t,parent,?len,self.idx,?children,?keys,?vals) &*& 0 <= self.idx &*& self.idx <= len &*&
        ancestors(&(*parent.as_ptr()).data,?path,?root) &*& (*root).parent_idx |-> ?root_index &*&
        struct_LeafNode_padding(&(*parent.as_ptr()).data) &*& struct_InternalNode_padding(parent.as_ptr()) &*&
        detached_child(edge.node.as_ptr()) &*& <K>.own(t,key) &*& <V>.own(t,val);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        ancestors(&(*parent.as_ptr()).data,path,root) &*& (*root).parent_idx |-> root_index &*&
        struct_LeafNode_padding(&(*parent.as_ptr()).data) &*& struct_InternalNode_padding(parent.as_ptr()) &*&
        <K>.own(t,key) &*& <V>.own(t,val) &*&
        match result {
            Option::None => len < CAPACITY &*& [available]lifetime_token(k) &*&
                internal_slots(parent,len+1,insert_item(children,self.idx+1,edge.node),_,_),
            Option::Some(split) => len == CAPACITY &*& [available/2]lifetime_token(k) &*&
                split.left == self.node &*& split.right.height == self.node.height &*&
                exists::<NonNull<InternalNode<K,V>>>(?fresh) &*& split.right.node.as_ptr() == &(*fresh.as_ptr()).data &*&
                allocated_internal(fresh.as_ptr(),id,k,available/2) &*& detached_child(split.right.node.as_ptr()) &*&
                internal_slots(parent,?left_len,?left_children,_,_) &*&
                internal_slots(fresh,?right_len,?right_children,_,_) &*& left_len + right_len == len &*&
                append(left_children,right_children) == insert_item(children,self.idx+1,edge.node) &*&
                <K>.own(t,split.kv.0) &*& <V>.own(t,split.kv.1)
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available]lifetime_token(k) &*& struct_InternalNode_padding(parent.as_ptr()) &*&
        ancestor_tail(&(*parent.as_ptr()).data,path,root,root_index,?ancestor,?ancestor_idx) &*&
        leaf_header(&(*parent.as_ptr()).data,ancestor,ancestor_idx) &*&
        internal_slots(parent,len,children,keys,vals) &*& detached_child(edge.node.as_ptr()) &*&
        if len == CAPACITY {
            nth(insertion_pivot(self.idx), keys).inner() == some(?pivot_key) &*&
            nth(insertion_pivot(self.idx), vals).inner() == some(?pivot_val) &*&
            <K>.own(t,pivot_key) &*& <V>.own(t,pivot_val)
        } else { true };
    @*/
    {
        //@ open exists(parent);
        //@ open ready_parent(t,parent,len,self.idx,children,keys,vals);
        //@ let parent_data = &(*parent.as_ptr()).data;
        //@ open_ancestor_header(parent_data,path,root);
        //@ close exists(parent);
        let result = unsafe { self.insert_production/*@::<'tree,K,V,A>@*/(key,val,edge,alloc) };
        //@ close_ancestor_header(parent_data,path,root);
        /*@ match result {
            Option::None => {}
            Option::Some(split) => { close detached_child(split.right.node.as_ptr()); }
        } @*/
        result
    }
}


impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,marker::Edge> {
    unsafe fn clone_and_insert<A: AllocatorClone>(
        self, key: K, val: V, alloc: &A,
    ) -> (
        Option<SplitResult<'a, K, V, marker::Leaf>>,
        Handle<NodeRef<marker::DormantMut, K, V, marker::Leaf>, marker::KV>,
    )
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [_]allocator_clone_bound::<A>() &*&
        [_]std::alloc::Allocator_share::<A>(?alloc_lifetime,t,alloc,?id) &*&
        [_]frac_borrow(alloc_lifetime,ref_initialized_(alloc)) &*& [?qa]lifetime_token(alloc_lifetime) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*&
        lifetime_inclusion(k,id.lft) == true &*& self.node.height == 0 &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        ancestors(self.node.node.as_ptr(),?path,?root) &*& (*root).parent_idx |-> ?root_index &*&
        struct_LeafNode_padding(self.node.node.as_ptr()) &*&
        leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= self.idx &*& self.idx <= len &*& pivot_owner(t,len,self.idx,keys,vals);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [qa]lifetime_token(alloc_lifetime) &*& [?remaining]lifetime_token(k) &*& <K>.own(t,key) &*& <V>.own(t,val) &*& result.1.node.height == 0 &*&
        ancestors(self.node.node.as_ptr(),path,root) &*& (*root).parent_idx |-> root_index &*&
        struct_LeafNode_padding(self.node.node.as_ptr()) &*&
        dormant_pair(result.1.node.node.as_ptr(),result.1.idx,MaybeUninit::new(key),MaybeUninit::new(val)) &*&
        leaf_insert_sibling(result, self, t, len, id, k);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [qa]lifetime_token(alloc_lifetime) &*& [?remaining]lifetime_token(k) &*& len == CAPACITY &*&
        ancestor_tail(self.node.node.as_ptr(),path,root,root_index,?parent,?idx) &*&
        leaf_header(self.node.node.as_ptr(),parent,idx) &*& leaf_slots(self.node.node.as_ptr(),len,keys,vals) &*&
        nth(insertion_pivot(self.idx),keys).inner() == some(?promoted_key) &*&
        nth(insertion_pivot(self.idx),vals).inner() == some(?promoted_val) &*&
        <K>.own(t,promoted_key) &*& <V>.own(t,promoted_val);
    @*/
    {
        unsafe { self.insert/*@::<'a,K,V,A>@*/(key, val, alloc.clone()) }
    }
}

/*@
inductive Placement<K,V> = Placement(NonNull<InternalNode<K,V>>, NonNull<InternalNode<K,V>>, K, V);

pred completed_levels<K,V>(t: thread_id_t, alloc_id: std::alloc::alloc_id_t, k: lifetime_t, records: list<Placement<K,V>>) =
    match records {
        nil => true,
        cons(record, rest) =>
            match record {
                Placement(left, right, key, value) =>
                    internal_slots(left, _, _, _, _) &*& internal_slots(right, _, _, _, _) &*&
                    struct_LeafNode_padding(&(*left.as_ptr()).data) &*& struct_InternalNode_padding(left.as_ptr()) &*&
                    allocated_internal(right.as_ptr(),alloc_id,k,_) &*& <K>.own(t,key) &*& <V>.own(t,value) &*& completed_levels(t,alloc_id,k,rest)
            }
    };
@*/

/*@
pred detached_child<K,V>(child: *LeafNode<K,V>;) =
    (*child).parent |-> Option::None &*& (*child).parent_idx |-> _;
@*/

/*@
pred leaf_slots<K,V>(node: *LeafNode<K,V>, len: usize; keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>) =
    (*node).len |-> (len as u16) &*& 0 <= len &*& len <= CAPACITY &*&
    pointer_within_limits(&(*node).keys) == true &*& pointer_within_limits(&(*node).vals) == true &*&
    (*node).keys[..CAPACITY] |-> keys &*& (*node).vals[..CAPACITY] |-> vals;

pred leaf_rest<K,V>(node: *LeafNode<K,V>, index: usize;) =
    (*node).keys[..index] |-> ?keys_before &*& (*node).keys[index+1..CAPACITY] |-> ?keys_after &*&
    (*node).vals[..index] |-> ?vals_before &*& (*node).vals[index+1..CAPACITY] |-> ?vals_after;
@*/

unsafe fn fit_leaf<K, V>(leaf: NonNull<LeafNode<K, V>>, index: usize, key: K, value: V)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,value) &*&
    leaf_slots(leaf.as_ptr(),?len,?keys,?vals) &*& 0 <= index &*& index <= len &*& len < CAPACITY;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,value) &*&
    dormant_pair(leaf.as_ptr(), index, MaybeUninit::new(key), MaybeUninit::new(value)) &*& leaf_rest(leaf.as_ptr(),index);
@*/
//@ on_unwind_ens false;
{
    let leaf_ptr = leaf.as_ptr();
    //@ open leaf_slots(leaf_ptr,len,keys,vals);
    let new_len = unsafe { (*leaf_ptr).len } as usize + 1;
    let key_base = unsafe { (&raw mut (*leaf_ptr).keys) as *mut MaybeUninit<K> };
    let val_base = unsafe { (&raw mut (*leaf_ptr).vals) as *mut MaybeUninit<V> };
    //@ array_split(key_base,new_len);
    //@ array_split(val_base,new_len);
    //@ insertion_slot_limits(key_base);
    //@ insertion_slot_limits(val_base);
    unsafe {
        slice_insert(std::slice::from_raw_parts_mut(key_base, new_len), index, key);
        slice_insert(std::slice::from_raw_parts_mut(val_base, new_len), index, value);
        (*leaf_ptr).len = new_len as u16;
    }
    /*@ {
    assert key_base[..new_len] |-> ?fitted_keys;
    assert val_base[..new_len] |-> ?fitted_vals;
    array_join(key_base);
    array_join(val_base);
    length_take(new_len,keys);
    length_take(new_len,vals);
    length_take(index,take(new_len,keys));
    length_take(index,take(new_len,vals));
    btree_drop_append_left(index,fitted_keys,drop(new_len,keys));
    btree_drop_append_left(index,fitted_vals,drop(new_len,vals));
    drop_append(index,take(index,take(new_len,keys)),cons(MaybeUninit::new(key),take(len-index,drop(index,take(new_len,keys)))));
    drop_append(index,take(index,take(new_len,vals)),cons(MaybeUninit::new(value),take(len-index,drop(index,take(new_len,vals)))));
    array_split(key_base,index);
    array_split(val_base,index);
    array_split(key_base+index,1);
    array_split(val_base+index,1);
    open array(key_base+index,1,[MaybeUninit::new(key)]);
    open array(val_base+index,1,[MaybeUninit::new(value)]);
    close dormant_pair(leaf_ptr,index,MaybeUninit::new(key),MaybeUninit::new(value));
    close leaf_rest(leaf_ptr,index);
    } @*/
}

unsafe fn split_full_leaf<K, V>(
    left: NonNull<LeafNode<K, V>>,
    right: NonNull<LeafNode<K, V>>,
    pivot: usize,
) -> (K, V)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    leaf_slots(left.as_ptr(),CAPACITY,?keys,?vals) &*& leaf_slots(right.as_ptr(),0,?right_keys,?right_vals) &*&
    0 <= pivot &*& pivot < CAPACITY &*&
    nth(pivot,keys).inner() == some(?promoted_key) &*& nth(pivot,vals).inner() == some(?promoted_value) &*&
    <K>.own(t,promoted_key) &*& <V>.own(t,promoted_value);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    leaf_slots(left.as_ptr(),pivot,_,_) &*& leaf_slots(right.as_ptr(),CAPACITY-pivot-1,_,_) &*&
    result.0 == promoted_key &*& result.1 == promoted_value &*& <K>.own(t,promoted_key) &*& <V>.own(t,promoted_value);
@*/
//@ on_unwind_ens false;
{
    let src = left.as_ptr();
    let dst = right.as_ptr();
    //@ open leaf_slots(src,CAPACITY,keys,vals);
    //@ open leaf_slots(dst,0,right_keys,right_vals);
    let len = unsafe { (*src).len } as usize;
    let new_len = len - pivot - 1;
    unsafe { (*dst).len = new_len as u16 };
    let key_base = unsafe { (&raw const (*src).keys) as *const MaybeUninit<K> };
    let val_base = unsafe { (&raw const (*src).vals) as *const MaybeUninit<V> };
    let right_key_base = unsafe { (&raw mut (*dst).keys) as *mut MaybeUninit<K> };
    let right_val_base = unsafe { (&raw mut (*dst).vals) as *mut MaybeUninit<V> };
    /*@ {
    array_split(key_base,pivot);
    array_split(key_base+pivot,1);
    array_split(val_base,pivot);
    array_split(val_base+pivot,1);
    drop_n_plus_one(pivot,keys);
    drop_n_plus_one(pivot,vals);
    open array(key_base+pivot,1,take(1,drop(pivot,keys)));
    open array(val_base+pivot,1,take(1,drop(pivot,vals)));
    } @*/
    let key = unsafe { read_promoted(key_base.add(pivot)) };
    let value = unsafe { read_promoted(val_base.add(pivot)) };
    /*@ {
    close array(key_base+pivot,1,[MaybeUninit::new(key)]);
    close array(val_base+pivot,1,[MaybeUninit::new(value)]);
    array_split(right_key_base,new_len);
    array_split(right_val_base,new_len);
    array_to_array_(right_key_base);
    array_to_array_(right_val_base);
    } @*/
    unsafe {
        ptr::copy_nonoverlapping(key_base.add(pivot + 1), right_key_base, new_len);
        ptr::copy_nonoverlapping(val_base.add(pivot + 1), right_val_base, new_len);
        (*src).len = pivot as u16;
    }
    /*@ {
    array_join(key_base+pivot);
    array_join(key_base);
    array_join(val_base+pivot);
    array_join(val_base);
    array_join(right_key_base);
    array_join(right_val_base);
    close leaf_slots(src,pivot,_,_);
    close leaf_slots(dst,new_len,_,_);
    } @*/
    (key, value)
}

/*@
pred allocated_leaf<K,V>(node: *LeafNode<K,V>, alloc_id: std::alloc::alloc_id_t,k: lifetime_t, q: real) =
    std::alloc::alloc_block_in(alloc_id,node as *u8,std::alloc::Layout::new::<LeafNode<K,V>>()) &*&
    close_points_to_at_lft_token(1,alloc_id.lft,node,?alloc_fraction) &*&
    close_lifetime_trade_token(alloc_fraction,alloc_id.lft,q,k) &*& struct_LeafNode_padding(node);
@*/

unsafe fn fresh_leaf<K, V, A: AllocatorClone>(alloc: A) -> (NonNull<LeafNode<K, V>>, A)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<A>(t,alloc,?alloc_id) &*& exists::<lifetime_t>(?k) &*& [?q]lifetime_token(k) &*& lifetime_inclusion(k,alloc_id.lft) == true;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& [q/2]lifetime_token(k) &*&
    Allocator::<A>(t,result.1,alloc_id) &*& allocated_leaf(result.0.as_ptr(),alloc_id,k,q/2) &*& leaf_slots(result.0.as_ptr(),0,_,_) &*& detached_child(result.0.as_ptr());
@*/
//@ on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& [q]lifetime_token(k);
{
    let leaf = unsafe { LeafNode::<K, V>::new(alloc) };
    let (node, retained_allocator) = Box::into_non_null_with_allocator(leaf);
    //@ let pointer = node.as_ptr();
    //@ close reserve_allocation(k,q/2);
    //@ let q_alloc = lifetime_token_trade(k,q/2,alloc_id.lft);
    //@ open_points_to_at_lft(pointer, q_alloc);
    //@ points_to_limits(pointer);
    //@ open_points_to(pointer);
    //@ close allocated_leaf(pointer, alloc_id, k, q/2);
    //@ close leaf_slots(pointer, 0, _, _);
    //@ close detached_child(pointer);
    //@ open reserve_allocation(k,q/2);
    (node, retained_allocator)
}

/*@
pred insertion_leaves<K,V>(
    first: NonNull<LeafNode<K,V>>,
    inserted: NonNull<LeafNode<K,V>>,
    index: usize,
    split: Option<NonNull<LeafNode<K,V>>>,
    alloc_id: std::alloc::alloc_id_t,
    k: lifetime_t
) =
    leaf_rest(inserted.as_ptr(),index) &*&
    match split {
        Option::None => inserted == first,
        Option::Some(right) =>
            allocated_leaf(right.as_ptr(),alloc_id,k,_) &*&
            exists::<NonNull<LeafNode<K,V>>>(?other) &*&
            leaf_slots(other.as_ptr(),_,_,_) &*&
            ((inserted == first && other == right) || (inserted == right && other == first))
    };
@*/

// VeriFast 26.10 hoists Rust MIR's temporary storage to function scope.
// Preserve the compiler's private stack slots through the loop invariant.
/*@
pred cursor_node_buffer<B,K,V,T>(p: *NodeRef<B,K,V,T>;) =
    struct_NodeRef_padding(p) &*& (*p).height |-> _ &*& (*p).node |-> _;

pred cursor_pair_buffer<X,Y>(p: *std_tuple_2_<X,Y>;) =
    struct_std_tuple_2__padding(p) &*& (*p).0 |-> _ &*& (*p).1 |-> _;

pred cursor_split_buffer<'tree,K,V,T>(p: *SplitResult<'tree,K,V,T>;) =
    struct_SplitResult_padding(p) &*& cursor_node_buffer(&(*p).left) &*&
    cursor_pair_buffer(&(*p).kv) &*& cursor_node_buffer(&(*p).right);

pred cursor_handle_buffer<B,K,V,T,H>(p: *Handle<NodeRef<B,K,V,T>,H>;) =
    struct_Handle_padding(p) &*& cursor_node_buffer(&(*p).node) &*& (*p).idx |-> _;
@*/

/*@
pred root_split_header<K,V>(p: *LeafNode<K,V>;) =
    (*p).parent |-> _ &*& (*p).parent_idx |-> _;

pred root_split_inputs<K,V>(
    left: *LeafNode<K,V>, right: *LeafNode<K,V>, inserted: *LeafNode<K,V>, index: usize;
    left_index: MaybeUninit<u16>, key_cell: MaybeUninit<K>, val_cell: MaybeUninit<V>
) =
    ancestors(left, [], left) &*& (*left).parent_idx |-> left_index &*& detached_child(right) &*&
    dormant_pair(inserted,index,key_cell,val_cell);
@*/

// The production loop takes its split and dormant handle from leaf insertion.
// Its allocator is borrowed because the loop only uses it to clone.
// The root branch establishes the storage needed for concrete installation
// and awakening. The generic call uses the standard FnOnce ownership contract.
// BEGIN_PRODUCTION_LOOP

// END_PRODUCTION_LOOP

// Check the ownership transfer after the leaf call, including the early
// return when the leaf absorbs the insertion.
// BEGIN_LEAF_HANDOFF

// END_LEAF_HANDOFF

// The concrete root callbacks use these node operations after reborrowing
// the root slot. The guarded replacement is checked separately.
unsafe fn install_root_split<'tree, 'slot, K, V, A: AllocatorClone>(
    root_slot: &'slot mut DormantMutRef<'tree, Option<Root<K, V>>>,
    allocator: &mut A,
    left: NonNull<LeafNode<K, V>>,
    key: K,
    value: V,
    right: Root<K, V>,
)
/*@
req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
    type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    [_]allocator_clone_bound::<A>() &*&
    *allocator |-> ?original_allocator &*& Allocator::<A>(t,original_allocator,?id) &*&
    exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k,id.lft) == true &*&
    *root_slot |-> ?sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(?old_root) &*&
    old_root.node == left &*& old_root.height < usize::MAX &*& right.height == old_root.height &*&
    ancestors(left.as_ptr(),[],left.as_ptr()) &*& (*left.as_ptr()).parent_idx |-> ?left_index &*&
    detached_child(right.node.as_ptr()) &*& <K>.own(t,key) &*& <V>.own(t,value);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    *allocator |-> ?after &*& Allocator::<A>(t,after,id) &*& [available/2]lifetime_token(k) &*&
    *root_slot |-> sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(?installed) &*&
    installed.height == old_root.height + 1 &*&
    exists::<NonNull<InternalNode<K,V>>>(?root) &*& installed.node.as_ptr() == &(*root.as_ptr()).data &*&
    allocated_internal(root.as_ptr(),id,k,_) &*& (*root.as_ptr()).data.parent_idx |-> _ &*&
    ancestors(installed.node.as_ptr(),[],installed.node.as_ptr()) &*&
    internal_slots(root,1,[left,right.node],_,_) &*& <K>.own(t,key) &*& <V>.own(t,value);
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    *allocator |-> ?after &*& Allocator::<A>(t,after,id) &*& [?remaining]lifetime_token(k) &*&
    *root_slot |-> sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*&
    detached_child(right.node.as_ptr()) &*&
    exists::<Option<NonNull<InternalNode<K,V>>>>(?partial_root) &*& interrupted_root_change(left,left_index,id,k,partial_root);
@*/
{
    //@ open exists(k);
    let borrowed_root = unsafe { root_slot.reborrow/*@::<'tree, Option<Root<K,V>>, 'slot>@*/() };
    let root_payload = borrowed_root.as_mut().unwrap();
    let root_allocator = unsafe { clone_allocator(allocator) };
    let old = unsafe { ptr::read(root_payload) };
    //@ std::option::close_points_to_Option_Some(borrowed_root);
    //@ close exists(k);
    let new = unsafe {
        NodeRef::<marker::Owned,K,V,marker::Internal>::new_internal_production(old,root_allocator).forget_type()
    };
    //@ std::option::open_points_to_Option_Some(borrowed_root);
    unsafe { ptr::write(root_payload,new) };

    //@ open exists::<NonNull<InternalNode<K,V>>>(?root);
    //@ std::ptr::NonNull_Sized_as_ptr(root);
    //@ let data = &(*root.as_ptr()).data;
    //@ open allocated_internal(root.as_ptr(),id,k,available/2);
    //@ open_ancestor_header(data,[],data);
    //@ open_points_to(root_payload);
    let mut view = NodeRef::<marker::Mut<'slot>,K,V,marker::Internal> {
        height: root_payload.height, node: root_payload.node, _marker: PhantomData
    };
    //@ close_points_to(root_payload);
    //@ std::option::close_points_to_Option_Some(borrowed_root);
    //@ close exists(root);
    unsafe { view.push_production/*@::<'slot,K,V,'slot>@*/(key,value,right) }; //~track_ref_creation
    //@ assert ref_mut_end_token(?view_ref,&mut view);
    //@ end_ref_mut(view_ref);
    //@ close_ancestor_header(data,[],data);
    //@ close allocated_internal(root.as_ptr(),id,k,available/2);
    //@ close exists(root);
}

// Consume the physical root split before recovering the outstanding leaf handle.
// BEGIN_FINISH_ROOT_SPLIT
unsafe fn finish_root_split<'tree, 'slot, K, V, A: AllocatorClone>(
    split: SplitResult<'tree, K, V, marker::LeafOrInternal>,
    inserted: Handle<NodeRef<marker::DormantMut, K, V, marker::Leaf>, marker::KV>,
    root_slot: &'slot mut DormantMutRef<'tree, Option<Root<K, V>>>,
    allocator: &'slot mut A,
) -> Handle<NodeRef<marker::Mut<'tree>, K, V, marker::Leaf>, marker::KV>
/*@
req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
    type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    [_]allocator_clone_bound::<A>() &*&
    *allocator |-> ?original_allocator &*& Allocator::<A>(t,original_allocator,?id) &*&
    exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k,id.lft) == true &*&
    *root_slot |-> ?sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(?old_root) &*&
    old_root.node == split.left.node &*& old_root.height == split.left.height &*&
    old_root.height < usize::MAX &*& split.right.height == old_root.height &*&
    root_split_inputs(?left,?right,?leaf,?index,?left_index,?key_cell,?val_cell) &*&
    left == split.left.node.as_ptr() &*& right == split.right.node.as_ptr() &*&
    leaf == inserted.node.node.as_ptr() &*& index == inserted.idx &*& inserted.node.height == 0 &*&
    <K>.own(t,split.kv.0) &*& <V>.own(t,split.kv.1);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    *allocator |-> ?after &*& Allocator::<A>(t,after,id) &*& [available/2]lifetime_token(k) &*&
    *root_slot |-> sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(?installed) &*&
    installed.height == old_root.height + 1 &*&
    exists::<NonNull<InternalNode<K,V>>>(?root) &*& installed.node.as_ptr() == &(*root.as_ptr()).data &*&
    allocated_internal(root.as_ptr(),id,k,_) &*& (*root.as_ptr()).data.parent_idx |-> _ &*&
    ancestors(installed.node.as_ptr(),[],installed.node.as_ptr()) &*& internal_slots(root,1,[split.left.node,split.right.node],_,_) &*&
    <K>.own(t,split.kv.0) &*& <V>.own(t,split.kv.1) &*&
    result.node.height == 0 &*& result.node.node == inserted.node.node &*& result.idx == inserted.idx &*&
    dormant_pair(result.node.node.as_ptr(),result.idx,key_cell,val_cell);
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    *allocator |-> ?after &*& Allocator::<A>(t,after,id) &*& [?remaining]lifetime_token(k) &*&
    *root_slot |-> sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& detached_child(split.right.node.as_ptr()) &*&
    exists::<Option<NonNull<InternalNode<K,V>>>>(?partial_root) &*&
    interrupted_root_change(split.left.node,left_index,id,k,partial_root) &*&
    dormant_pair(inserted.node.node.as_ptr(),inserted.idx,key_cell,val_cell);
@*/
{
    //@ open root_split_inputs(left,right,leaf,index,left_index,key_cell,val_cell);
    //@ open_points_to(&split);
    //@ open_points_to(&split.left);
    let original_root = split.left.node;
    //@ close_points_to(&split.left, 1/2);
    //@ open_points_to(&split.kv);
    let key = split.kv.0;
    let value = split.kv.1;
    //@ close_points_to(&split.kv, 1/2);
    let sibling = split.right;
    //@ close_points_to(&split, 1/2);
    unsafe {
        install_root_split/*@::<K,V,A,'tree,'slot,'slot>@*/(root_slot, allocator, original_root, key, value, sibling);
        inserted.awaken/*@::<K,V,marker::Leaf,marker::KV,'tree>@*/()
    }
}
// END_FINISH_ROOT_SPLIT

/*@
pred interrupted_root_change<K,V>(
    old_root: NonNull<LeafNode<K,V>>, old_index: MaybeUninit<u16>,
    alloc_id: std::alloc::alloc_id_t, k: lifetime_t, new_root: Option<NonNull<InternalNode<K,V>>>
) =
    match new_root {
        Option::None =>
            ancestors(old_root.as_ptr(),[],old_root.as_ptr()) &*& (*old_root.as_ptr()).parent_idx |-> old_index,
        Option::Some(node) =>
            allocated_internal(node.as_ptr(),alloc_id,k,_) &*& (*node.as_ptr()).data.parent_idx |-> _ &*&
            ancestors(&(*node.as_ptr()).data,[],&(*node.as_ptr()).data) &*& internal_slots(node,0,[old_root],_,_)
    };
@*/

// BEGIN_NEW_INTERNAL

// END_NEW_INTERNAL

unsafe fn leaf_split_result<'tree,K,V>(left: NonNull<LeafNode<K,V>>, right: NonNull<LeafNode<K,V>>, key:K, val:V) -> SplitResult<'tree,K,V,marker::Leaf>
/*@
req true;
@*/
/*@
ens result == SplitResult::<'tree,K,V,marker::Leaf> {
    left: NodeRef::<marker::Mut<'tree>,K,V,marker::Leaf> { height: 0, node: left },
    kv: std_tuple_2_::<K,V> { 0: key, 1: val },
    right: NodeRef::<marker::Owned,K,V,marker::Leaf> { height: 0, node: right },
};
@*/
//@ on_unwind_ens false;
{
    SplitResult {
        left: NodeRef::<marker::Mut<'tree>,K,V,marker::Leaf> { height: 0, node: left, _marker: PhantomData },
        kv: (key,val),
        right: NodeRef::<marker::Owned,K,V,marker::Leaf> { height: 0, node: right, _marker: PhantomData },
    }
}

// The owned tuple is the normal result of Handle::insert. Keep its handoff
// separate so VeriFast need not unpack an uninitialized tuple on unwind
// from the call that creates it.
// BEGIN_ROOT_HANDOFF
unsafe fn resume_after_leaf_insert_for_root<'tree, 'alloc, 'slot, K: 'tree, V: 'tree, A: AllocatorClone>(
    initial: (Option<SplitResult<'tree,K,V,marker::Leaf>>, Handle<NodeRef<marker::DormantMut,K,V,marker::Leaf>,marker::KV>),
    alloc: &'alloc A,
    root_slot: &'slot mut DormantMutRef<'tree, Option<Root<K,V>>>,
    root_allocator: &'slot mut A,
) -> Handle<NodeRef<marker::Mut<'tree>,K,V,marker::Leaf>,marker::KV>
/*@
req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
    type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    [_]allocator_clone_bound::<A>() &*&
    [_]std::alloc::Allocator_share::<A>(?alloc_lifetime,t,alloc,?alloc_id) &*&
    [_]frac_borrow(alloc_lifetime, ref_initialized_(alloc)) &*& [?qa]lifetime_token(alloc_lifetime) &*&
    [?available]lifetime_token(?k) &*& lifetime_inclusion(k,alloc_id.lft) == true &*&
    exists::<NonNull<LeafNode<K,V>>>(?first) &*&
    ancestors(first.as_ptr(),?path,?root) &*& route_frames(t,path) &*& (*root).parent_idx |-> ?root_index &*&
    *root_allocator |-> ?root_alloc &*& Allocator::<A>(t,root_alloc,alloc_id) &*&
    *root_slot |-> ?sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(?old_root) &*&
    old_root.node.as_ptr() == root &*& old_root.height == length(path) &*&
    length(path) < usize::MAX &*& initial.1.node.height == 0 &*&
    dormant_pair(initial.1.node.node.as_ptr(),initial.1.idx,?key_cell,?val_cell) &*&
    key_cell.inner() == some(?key) &*& val_cell.inner() == some(?value) &*&
    <K>.own(t,key) &*& <V>.own(t,value) &*&
    match initial.0 {
        Option::None => insertion_leaves(first,initial.1.node.node,initial.1.idx,Option::None,alloc_id,k),
        Option::Some(leaf_split) => leaf_split.left.node == first &*& leaf_split.left.height == 0 &*& leaf_split.right.height == 0 &*&
            insertion_leaves(first,initial.1.node.node,initial.1.idx,Option::Some(leaf_split.right.node),alloc_id,k) &*&
            detached_child(leaf_split.right.node.as_ptr()) &*& <K>.own(t,leaf_split.kv.0) &*& <V>.own(t,leaf_split.kv.1)
    };
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    [qa]lifetime_token(alloc_lifetime) &*& [?remaining_fraction]lifetime_token(k) &*&
    *root_allocator |-> ?after &*& Allocator::<A>(t,after,alloc_id) &*& *root_slot |-> sleeper &*&
    result.node.height == 0 &*&
    <K>.own(t,key) &*& <V>.own(t,value) &*&
    dormant_pair(result.node.node.as_ptr(),result.idx,key_cell,val_cell) &*&
    exists::<Option<NonNull<LeafNode<K,V>>>>(?initial_sibling) &*&
    insertion_leaves(first,result.node.node,result.idx,initial_sibling,alloc_id,k) &*&
    match initial_sibling {
        Option::None =>
            *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& (*root).parent_idx |-> root_index &*&
            ancestors(first.as_ptr(),path,root) &*& route_frames(t,path),
        Option::Some(sibling) => completed_levels::<K,V>(t,alloc_id,k,?completed) &*&
            if length(completed) == length(path) {
                *sleeper.ptr.as_ptr() |-> Option::Some(?installed) &*& installed.height == old_root.height + 1 &*&
                exists::<NonNull<InternalNode<K,V>>>(?new_root) &*& installed.node.as_ptr() == &(*new_root.as_ptr()).data &*&
                allocated_internal(new_root.as_ptr(),alloc_id,k,_) &*& (*new_root.as_ptr()).data.parent_idx |-> _ &*&
                ancestors(installed.node.as_ptr(),[],installed.node.as_ptr()) &*&
                internal_slots(new_root,1,cons(old_root.node,cons(?right,nil)),_,_) &*& <K>.own(t,_) &*& <V>.own(t,_)
            } else {
                *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& (*root).parent_idx |-> root_index &*&
                exists::<NonNull<InternalNode<K,V>>>(?receiving) &*& ancestors(&(*receiving.as_ptr()).data,?remaining,root) &*&
                route_frames(t,remaining) &*& internal_slots(receiving,_,_,_,_) &*& struct_LeafNode_padding(&(*receiving.as_ptr()).data) &*& struct_InternalNode_padding(receiving.as_ptr()) &*& <K>.own(t,_) &*& <V>.own(t,_) &*&
                length(completed) + length(remaining) + 1 == length(path)
            }
    };
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    [qa]lifetime_token(alloc_lifetime) &*& [?remaining_fraction]lifetime_token(k) &*&
    *root_allocator |-> ?after &*& Allocator::<A>(t,after,alloc_id) &*& *root_slot |-> sleeper &*&
    <K>.own(t,key) &*& <V>.own(t,value) &*&
    dormant_pair(initial.1.node.node.as_ptr(),initial.1.idx,key_cell,val_cell) &*&
    match initial.0 {
        Option::None => *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& (*root).parent_idx |-> root_index &*&
            ancestors(first.as_ptr(),path,root) &*& route_frames(t,path) &*&
            insertion_leaves(first,initial.1.node.node,initial.1.idx,Option::None,alloc_id,k),
        Option::Some(leaf_split) =>
            insertion_leaves(first,initial.1.node.node,initial.1.idx,Option::Some(leaf_split.right.node),alloc_id,k) &*&
            completed_levels::<K,V>(t,alloc_id,k,?completed) &*&
            if length(completed) == length(path) {
                *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& detached_child::<K,V>(?pending_sibling) &*&
                exists::<Option<NonNull<InternalNode<K,V>>>>(?partial_root) &*&
                interrupted_root_change(old_root.node,root_index,alloc_id,k,partial_root)
            } else {
                *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& exists::<NonNull<InternalNode<K,V>>>(?receiving) &*&
                ancestor_tail(&(*receiving.as_ptr()).data,?remaining,root,root_index,?ancestor,?ancestor_idx) &*&
                leaf_header(&(*receiving.as_ptr()).data,ancestor,ancestor_idx) &*& struct_InternalNode_padding(receiving.as_ptr()) &*&
                route_frames(t,remaining) &*& length(completed) + length(remaining) + 1 == length(path) &*&
                internal_slots(receiving,?len,_,_,_) &*& detached_child::<K,V>(?detached) &*&
                if len == CAPACITY { <K>.own(t,_) &*& <V>.own(t,_) } else { true }
            }
    };
@*/
{
    //@ open exists(first);
    //@ open_points_to(&initial);
    let (pending, inserted) = match initial {
        (None, inserted) => {
            //@ close_points_to(&initial, 1/2);
            //@ close exists::<Option<NonNull<LeafNode<K,V>>>>(Option::None);
            return unsafe { inserted.awaken/*@::<K,V,marker::Leaf,marker::KV,'tree>@*/() };
        }
        (Some(leaf_split), inserted) => {
            //@ close_points_to(&initial, 1/2);
            (unsafe { leaf_split.forget_node_type/*@::<'tree,K,V>@*/() }, inserted)
        }
    };
    //@ let right = pending.right.node;
    //@ close exists(std_tuple_2_::<NonNull<LeafNode<K,V>>, NonNull<LeafNode<K,V>>> { 0: first, 1: right });
    //@ close exists(k);
    let result = unsafe { propagate_split_for_root/*@::<'tree,K,V,A,'slot,'alloc>@*/(pending, inserted, alloc, root_slot, root_allocator) };
    //@ close exists(Option::Some(right));
    result
}
// END_ROOT_HANDOFF


impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    unsafe fn as_internal_ptr(this: &Self) -> *mut InternalNode<K, V>
    //@ req [?f](*this |-> ?node);
    //@ ens [f](*this |-> node) &*& result == node.node.as_ptr() as *mut InternalNode<K, V>;
    //@ on_unwind_ens false;
    {
        //@ open_points_to(this);
        let ptr = this.node.as_ptr() as *mut InternalNode<K, V>;
        //@ close_points_to(this, f);
        ptr
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn as_leaf_mut<'short>(&'short mut self) -> &'short mut LeafNode<K, V>
    //@ req *self |-> ?node &*& *node.node.as_ptr() |-> ?contents;
    //@ ens *self |-> node &*& *result |-> contents &*& ref_mut_end_token(result, node.node.as_ptr()) &*& ref_origin(result) == ref_origin(node.node.as_ptr());
    //@ on_unwind_ens false;
    {
        //@ let view = precreate_ref(self);
        //@ init_ref_readonly(view, 1/2);
        let ptr = unsafe { Self::as_leaf_ptr(self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(self, _);
        unsafe { &mut *ptr } //~track_ref_creation
    }
}

/*@
pred leaf_without_keys<K,V>(leaf: *LeafNode<K,V>;
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>, len: u16,
    vals: list<MaybeUninit<V>>) =
    leaf_header(leaf, parent, index) &*& (*leaf).len |-> len &*&
    (*leaf).vals[..CAPACITY] |-> vals;

@*/

/*@
pred keys_loan<K,V>(
    owner: *LeafNode<K,V>, base: *MaybeUninit<K>, first: usize, last: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>, len: u16,
    vals: list<MaybeUninit<V>>, before: list<MaybeUninit<K>>, tail: list<MaybeUninit<K>>
) =
    exists::<*LeafNode<K,V>>(?view) &*& ref_mut_end_token(view, owner) &*&
    ref_mut_end_token(?array, &(*view).keys) &*& base == array as *MaybeUninit<K> &*&
    leaf_without_keys(view, parent, index, len, vals) &*&
    0 <= first &*& first <= last &*& last <= CAPACITY &*&
    (if first == 0 { before == nil } else { base[..first] |-> before }) &*&
    base[last..CAPACITY] |-> tail;

lem restore_keys<K,V>(owner: *LeafNode<K,V>, base: *MaybeUninit<K>)
    req keys_loan(owner, base, ?first, ?last, ?parent, ?index, ?len, ?vals, ?before, ?tail) &*&
        base[first..last] |-> ?active;
    ens leaf_without_keys(owner, parent, index, len, vals) &*&
        (*owner).keys[..CAPACITY] |-> append(before, append(active, tail));
{
    open keys_loan(owner, base, first, last, parent, index, len, vals, before, tail);
    open exists::<*LeafNode<K,V>>(?view);
    assert ref_mut_end_token(?array, &(*view).keys);
    if first != 0 {
        array_join(base + first);
    }
    array_join(base);
    close_points_to(array);
    end_ref_mut(array);
    open_points_to(&(*view).keys);
    open leaf_without_keys(view, parent, index, len, vals);
    
    close_points_to(view);
    end_ref_mut(view);
    open_points_to(owner);
    
    close leaf_without_keys(owner, parent, index, len, vals);
}

pred keys_range_loan<K,V>(
    owner: *LeafNode<K,V>, lent: *[MaybeUninit<K>], first: usize, last: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>, len: u16,
    vals: list<MaybeUninit<V>>, before: list<MaybeUninit<K>>, tail: list<MaybeUninit<K>>
) =
    keys_loan(owner, ?base, first, last, parent, index, len, vals, before, tail) &*&
    slice_ref_mut_end_token(lent, base + first, last - first);

pred keys_slot_loan<K,V>(
    owner: *LeafNode<K,V>, lent: *MaybeUninit<K>, first: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>, len: u16,
    vals: list<MaybeUninit<V>>, before: list<MaybeUninit<K>>, tail: list<MaybeUninit<K>>
) =
    keys_loan(owner, ?base, first, first + 1, parent, index, len, vals, before, tail) &*&
    ref_mut_end_token(lent, base + first);

lem end_keys_range<K,V>(owner: *LeafNode<K,V>, lent: *[MaybeUninit<K>])
    req keys_range_loan(owner, lent, ?first, ?last, ?parent, ?index, ?len, ?vals, ?before, ?tail) &*&
        move_slice(lent as *MaybeUninit<K>, last - first, ?active);
    ens leaf_without_keys(owner, parent, index, len, vals) &*&
        (*owner).keys[..CAPACITY] |-> append(before, append(active, tail));
{
    open keys_range_loan(owner, lent, first, last, parent, index, len, vals, before, tail);
    assert keys_loan(owner, ?base, first, last, parent, index, len, vals, before, tail);
    open move_slice(lent as *MaybeUninit<K>, last - first, active);
    end_slice_ref_mut(lent);
    restore_keys(owner, base);
}

lem end_keys_slot<K,V>(owner: *LeafNode<K,V>, lent: *MaybeUninit<K>)
    req keys_slot_loan(owner, lent, ?first, ?parent, ?index, ?len, ?vals, ?before, ?tail) &*&
        *lent |-> ?entry;
    ens leaf_without_keys(owner, parent, index, len, vals) &*&
        (*owner).keys[..CAPACITY] |-> append(before, cons(entry, tail));
{
    open keys_slot_loan(owner, lent, first, parent, index, len, vals, before, tail);
    assert keys_loan(owner, ?base, first, first + 1, parent, index, len, vals, before, tail);
    open keys_loan(owner, base, first, first + 1, parent, index, len, vals, before, tail);
    assert base[first + 1..CAPACITY] |-> tail;
    array_inv::<MaybeUninit<K>>();
    close keys_loan(owner, base, first, first + 1, parent, index, len, vals, before, tail);
    end_ref_mut(lent);
    points_to_limits(base + first);
    close array(base + first + 1, 0, []);
    close array(base + first, 1, [entry]);
    restore_keys(owner, base);
}
@*/

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn key_area_range_mut<'short>(
        &'short mut self, index: std::ops::Range<usize>,
    ) -> &'short mut [MaybeUninit<K>]
    /*@
    req *self |-> ?node &*& leaf_without_keys(node.node.as_ptr(), ?parent, ?idx, ?len, ?vals) &*&
        (*node.node.as_ptr()).keys[..CAPACITY] |-> ?slots &*& 0 <= index.start &*& index.start <= index.end &*& index.end <= CAPACITY;
    @*/
    /*@
    ens *self |-> node &*&
        keys_range_loan(node.node.as_ptr(), result, index.start, index.end, parent, idx, len, vals, take(index.start, slots), drop(index.end, slots)) &*&
        result.len() == index.end - index.start &*&
        move_slice(result as *MaybeUninit<K>, index.end - index.start, take(index.end - index.start, drop(index.start, slots))) &*& ref_origin((result as *MaybeUninit<K>)) == ref_origin(&(*node.node.as_ptr()).keys as *MaybeUninit<K> + index.start);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open leaf_without_keys(node.node.as_ptr(), parent, idx, len, vals);
        
        //@ close_points_to(node.node.as_ptr());
        let storage = unsafe { self.as_leaf_mut/*@::<'a,K,V, Type,'short>@*/() };
        //@ open_points_to(storage);
        
        //@ close_points_to(&(*storage).keys);
        let array = &mut storage.keys;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<K>;
        //@ let first = index.start;
        //@ let last = index.end;
        //@ insertion_slot_limits(base);
        //@ move_slice_offset(base, CAPACITY, first);
        //@ btree_aligned_offset(base, first);
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        
        let lent = unsafe { view.get_unchecked_mut(index) };
        //@ close move_slice(lent as *MaybeUninit<K>, last - first, _);
        //@ close leaf_without_keys(storage, parent, idx, len, vals);
        //@ close exists::<*LeafNode<K,V>>(storage);
        //@ close keys_loan(node.node.as_ptr(), base, first, last, parent, idx, len, vals, take(first, slots), drop(last, slots));
        //@ close keys_range_loan(node.node.as_ptr(), lent, first, last, parent, idx, len, vals, take(first, slots), drop(last, slots));
        lent
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn key_area_prefix_mut<'short>(
        &'short mut self, index: std::ops::RangeTo<usize>,
    ) -> &'short mut [MaybeUninit<K>]
    /*@
    req *self |-> ?node &*& leaf_without_keys(node.node.as_ptr(), ?parent, ?idx, ?len, ?vals) &*&
        (*node.node.as_ptr()).keys[..CAPACITY] |-> ?slots &*& 0 <= index.end &*& index.end <= CAPACITY;
    @*/
    /*@
    ens *self |-> node &*&
        keys_range_loan(node.node.as_ptr(), result, 0, index.end, parent, idx, len, vals, take(0, slots), drop(index.end, slots)) &*&
        result.len() == index.end - 0 &*&
        move_slice(result as *MaybeUninit<K>, index.end - 0, take(index.end - 0, drop(0, slots))) &*& ref_origin((result as *MaybeUninit<K>)) == ref_origin(&(*node.node.as_ptr()).keys as *MaybeUninit<K> + 0);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open leaf_without_keys(node.node.as_ptr(), parent, idx, len, vals);
        
        //@ close_points_to(node.node.as_ptr());
        let storage = unsafe { self.as_leaf_mut/*@::<'a,K,V, Type,'short>@*/() };
        //@ open_points_to(storage);
        
        //@ close_points_to(&(*storage).keys);
        let array = &mut storage.keys;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<K>;
        //@ let first = 0;
        //@ let last = index.end;
        //@ insertion_slot_limits(base);
        //@ move_slice_offset(base, CAPACITY, first);
        //@ btree_aligned_offset(base, first);
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        
        let lent = unsafe { view.get_unchecked_mut(index) };
        //@ close move_slice(lent as *MaybeUninit<K>, last - first, _);
        //@ close leaf_without_keys(storage, parent, idx, len, vals);
        //@ close exists::<*LeafNode<K,V>>(storage);
        //@ close keys_loan(node.node.as_ptr(), base, first, last, parent, idx, len, vals, take(first, slots), drop(last, slots));
        //@ close keys_range_loan(node.node.as_ptr(), lent, first, last, parent, idx, len, vals, take(first, slots), drop(last, slots));
        lent
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn key_area_slot_mut<'short>(
        &'short mut self, index: usize,
    ) -> &'short mut MaybeUninit<K>
    /*@
    req *self |-> ?node &*& leaf_without_keys(node.node.as_ptr(), ?parent, ?idx, ?len, ?vals) &*&
        (*node.node.as_ptr()).keys[..CAPACITY] |-> ?slots &*& 0 <= index &*& index < CAPACITY;
    @*/
    /*@
    ens *self |-> node &*&
        keys_slot_loan(node.node.as_ptr(), result, index, parent, idx, len, vals, take(index, slots), drop(index + 1, slots)) &*&
        *result |-> nth(index, slots) &*& ref_origin(result) == ref_origin(&(*node.node.as_ptr()).keys as *MaybeUninit<K> + index);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open leaf_without_keys(node.node.as_ptr(), parent, idx, len, vals);
        
        //@ close_points_to(node.node.as_ptr());
        let storage = unsafe { self.as_leaf_mut/*@::<'a,K,V, Type,'short>@*/() };
        //@ open_points_to(storage);
        
        //@ close_points_to(&(*storage).keys);
        let array = &mut storage.keys;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<K>;
        //@ let first = index;
        //@ let last = index + 1;
        
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        //@ open array(base + first, 1, _);
        //@ nth_drop(0, first, slots);
        let lent = unsafe { view.get_unchecked_mut(index) };
        
        //@ close leaf_without_keys(storage, parent, idx, len, vals);
        //@ close exists::<*LeafNode<K,V>>(storage);
        //@ close keys_loan(node.node.as_ptr(), base, first, last, parent, idx, len, vals, take(first, slots), drop(last, slots));
        //@ close keys_slot_loan(node.node.as_ptr(), lent, first, parent, idx, len, vals, take(first, slots), drop(last, slots));
        lent
    }
}

/*@
pred leaf_without_vals<K,V>(leaf: *LeafNode<K,V>;
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>, len: u16,
    keys: list<MaybeUninit<K>>) =
    leaf_header(leaf, parent, index) &*& (*leaf).len |-> len &*&
    (*leaf).keys[..CAPACITY] |-> keys;

@*/

/*@
pred vals_loan<K,V>(
    owner: *LeafNode<K,V>, base: *MaybeUninit<V>, first: usize, last: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>, len: u16,
    keys: list<MaybeUninit<K>>, before: list<MaybeUninit<V>>, tail: list<MaybeUninit<V>>
) =
    exists::<*LeafNode<K,V>>(?view) &*& ref_mut_end_token(view, owner) &*&
    ref_mut_end_token(?array, &(*view).vals) &*& base == array as *MaybeUninit<V> &*&
    leaf_without_vals(view, parent, index, len, keys) &*&
    0 <= first &*& first <= last &*& last <= CAPACITY &*&
    (if first == 0 { before == nil } else { base[..first] |-> before }) &*&
    base[last..CAPACITY] |-> tail;

lem restore_vals<K,V>(owner: *LeafNode<K,V>, base: *MaybeUninit<V>)
    req vals_loan(owner, base, ?first, ?last, ?parent, ?index, ?len, ?keys, ?before, ?tail) &*&
        base[first..last] |-> ?active;
    ens leaf_without_vals(owner, parent, index, len, keys) &*&
        (*owner).vals[..CAPACITY] |-> append(before, append(active, tail));
{
    open vals_loan(owner, base, first, last, parent, index, len, keys, before, tail);
    open exists::<*LeafNode<K,V>>(?view);
    assert ref_mut_end_token(?array, &(*view).vals);
    if first != 0 {
        array_join(base + first);
    }
    array_join(base);
    close_points_to(array);
    end_ref_mut(array);
    open_points_to(&(*view).vals);
    open leaf_without_vals(view, parent, index, len, keys);
    
    close_points_to(view);
    end_ref_mut(view);
    open_points_to(owner);
    
    close leaf_without_vals(owner, parent, index, len, keys);
}

pred vals_range_loan<K,V>(
    owner: *LeafNode<K,V>, lent: *[MaybeUninit<V>], first: usize, last: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>, len: u16,
    keys: list<MaybeUninit<K>>, before: list<MaybeUninit<V>>, tail: list<MaybeUninit<V>>
) =
    vals_loan(owner, ?base, first, last, parent, index, len, keys, before, tail) &*&
    slice_ref_mut_end_token(lent, base + first, last - first);

pred vals_slot_loan<K,V>(
    owner: *LeafNode<K,V>, lent: *MaybeUninit<V>, first: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>, len: u16,
    keys: list<MaybeUninit<K>>, before: list<MaybeUninit<V>>, tail: list<MaybeUninit<V>>
) =
    vals_loan(owner, ?base, first, first + 1, parent, index, len, keys, before, tail) &*&
    ref_mut_end_token(lent, base + first);

lem end_vals_range<K,V>(owner: *LeafNode<K,V>, lent: *[MaybeUninit<V>])
    req vals_range_loan(owner, lent, ?first, ?last, ?parent, ?index, ?len, ?keys, ?before, ?tail) &*&
        move_slice(lent as *MaybeUninit<V>, last - first, ?active);
    ens leaf_without_vals(owner, parent, index, len, keys) &*&
        (*owner).vals[..CAPACITY] |-> append(before, append(active, tail));
{
    open vals_range_loan(owner, lent, first, last, parent, index, len, keys, before, tail);
    assert vals_loan(owner, ?base, first, last, parent, index, len, keys, before, tail);
    open move_slice(lent as *MaybeUninit<V>, last - first, active);
    end_slice_ref_mut(lent);
    restore_vals(owner, base);
}

lem end_vals_slot<K,V>(owner: *LeafNode<K,V>, lent: *MaybeUninit<V>)
    req vals_slot_loan(owner, lent, ?first, ?parent, ?index, ?len, ?keys, ?before, ?tail) &*&
        *lent |-> ?entry;
    ens leaf_without_vals(owner, parent, index, len, keys) &*&
        (*owner).vals[..CAPACITY] |-> append(before, cons(entry, tail));
{
    open vals_slot_loan(owner, lent, first, parent, index, len, keys, before, tail);
    assert vals_loan(owner, ?base, first, first + 1, parent, index, len, keys, before, tail);
    open vals_loan(owner, base, first, first + 1, parent, index, len, keys, before, tail);
    assert base[first + 1..CAPACITY] |-> tail;
    array_inv::<MaybeUninit<V>>();
    close vals_loan(owner, base, first, first + 1, parent, index, len, keys, before, tail);
    end_ref_mut(lent);
    points_to_limits(base + first);
    close array(base + first + 1, 0, []);
    close array(base + first, 1, [entry]);
    restore_vals(owner, base);
}
@*/

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn val_area_range_mut<'short>(
        &'short mut self, index: std::ops::Range<usize>,
    ) -> &'short mut [MaybeUninit<V>]
    /*@
    req *self |-> ?node &*& leaf_without_vals(node.node.as_ptr(), ?parent, ?idx, ?len, ?keys) &*&
        (*node.node.as_ptr()).vals[..CAPACITY] |-> ?slots &*& 0 <= index.start &*& index.start <= index.end &*& index.end <= CAPACITY;
    @*/
    /*@
    ens *self |-> node &*&
        vals_range_loan(node.node.as_ptr(), result, index.start, index.end, parent, idx, len, keys, take(index.start, slots), drop(index.end, slots)) &*&
        result.len() == index.end - index.start &*&
        move_slice(result as *MaybeUninit<V>, index.end - index.start, take(index.end - index.start, drop(index.start, slots))) &*& ref_origin((result as *MaybeUninit<V>)) == ref_origin(&(*node.node.as_ptr()).vals as *MaybeUninit<V> + index.start);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open leaf_without_vals(node.node.as_ptr(), parent, idx, len, keys);
        
        //@ close_points_to(node.node.as_ptr());
        let storage = unsafe { self.as_leaf_mut/*@::<'a,K,V, Type,'short>@*/() };
        //@ open_points_to(storage);
        
        //@ close_points_to(&(*storage).vals);
        let array = &mut storage.vals;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<V>;
        //@ let first = index.start;
        //@ let last = index.end;
        //@ insertion_slot_limits(base);
        //@ move_slice_offset(base, CAPACITY, first);
        //@ btree_aligned_offset(base, first);
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        
        let lent = unsafe { view.get_unchecked_mut(index) };
        //@ close move_slice(lent as *MaybeUninit<V>, last - first, _);
        //@ close leaf_without_vals(storage, parent, idx, len, keys);
        //@ close exists::<*LeafNode<K,V>>(storage);
        //@ close vals_loan(node.node.as_ptr(), base, first, last, parent, idx, len, keys, take(first, slots), drop(last, slots));
        //@ close vals_range_loan(node.node.as_ptr(), lent, first, last, parent, idx, len, keys, take(first, slots), drop(last, slots));
        lent
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn val_area_prefix_mut<'short>(
        &'short mut self, index: std::ops::RangeTo<usize>,
    ) -> &'short mut [MaybeUninit<V>]
    /*@
    req *self |-> ?node &*& leaf_without_vals(node.node.as_ptr(), ?parent, ?idx, ?len, ?keys) &*&
        (*node.node.as_ptr()).vals[..CAPACITY] |-> ?slots &*& 0 <= index.end &*& index.end <= CAPACITY;
    @*/
    /*@
    ens *self |-> node &*&
        vals_range_loan(node.node.as_ptr(), result, 0, index.end, parent, idx, len, keys, take(0, slots), drop(index.end, slots)) &*&
        result.len() == index.end - 0 &*&
        move_slice(result as *MaybeUninit<V>, index.end - 0, take(index.end - 0, drop(0, slots))) &*& ref_origin((result as *MaybeUninit<V>)) == ref_origin(&(*node.node.as_ptr()).vals as *MaybeUninit<V> + 0);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open leaf_without_vals(node.node.as_ptr(), parent, idx, len, keys);
        
        //@ close_points_to(node.node.as_ptr());
        let storage = unsafe { self.as_leaf_mut/*@::<'a,K,V, Type,'short>@*/() };
        //@ open_points_to(storage);
        
        //@ close_points_to(&(*storage).vals);
        let array = &mut storage.vals;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<V>;
        //@ let first = 0;
        //@ let last = index.end;
        //@ insertion_slot_limits(base);
        //@ move_slice_offset(base, CAPACITY, first);
        //@ btree_aligned_offset(base, first);
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        
        let lent = unsafe { view.get_unchecked_mut(index) };
        //@ close move_slice(lent as *MaybeUninit<V>, last - first, _);
        //@ close leaf_without_vals(storage, parent, idx, len, keys);
        //@ close exists::<*LeafNode<K,V>>(storage);
        //@ close vals_loan(node.node.as_ptr(), base, first, last, parent, idx, len, keys, take(first, slots), drop(last, slots));
        //@ close vals_range_loan(node.node.as_ptr(), lent, first, last, parent, idx, len, keys, take(first, slots), drop(last, slots));
        lent
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn val_area_slot_mut<'short>(
        &'short mut self, index: usize,
    ) -> &'short mut MaybeUninit<V>
    /*@
    req *self |-> ?node &*& leaf_without_vals(node.node.as_ptr(), ?parent, ?idx, ?len, ?keys) &*&
        (*node.node.as_ptr()).vals[..CAPACITY] |-> ?slots &*& 0 <= index &*& index < CAPACITY;
    @*/
    /*@
    ens *self |-> node &*&
        vals_slot_loan(node.node.as_ptr(), result, index, parent, idx, len, keys, take(index, slots), drop(index + 1, slots)) &*&
        *result |-> nth(index, slots) &*& ref_origin(result) == ref_origin(&(*node.node.as_ptr()).vals as *MaybeUninit<V> + index);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open leaf_without_vals(node.node.as_ptr(), parent, idx, len, keys);
        
        //@ close_points_to(node.node.as_ptr());
        let storage = unsafe { self.as_leaf_mut/*@::<'a,K,V, Type,'short>@*/() };
        //@ open_points_to(storage);
        
        //@ close_points_to(&(*storage).vals);
        let array = &mut storage.vals;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<V>;
        //@ let first = index;
        //@ let last = index + 1;
        
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        //@ open array(base + first, 1, _);
        //@ nth_drop(0, first, slots);
        let lent = unsafe { view.get_unchecked_mut(index) };
        
        //@ close leaf_without_vals(storage, parent, idx, len, keys);
        //@ close exists::<*LeafNode<K,V>>(storage);
        //@ close vals_loan(node.node.as_ptr(), base, first, last, parent, idx, len, keys, take(first, slots), drop(last, slots));
        //@ close vals_slot_loan(node.node.as_ptr(), lent, first, parent, idx, len, keys, take(first, slots), drop(last, slots));
        lent
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn as_internal_mut<'short>(&'short mut self) -> &'short mut InternalNode<K, V>
    //@ req *self |-> ?node &*& *(node.node.as_ptr() as *mut InternalNode<K, V>) |-> ?contents;
    //@ ens *self |-> node &*& *result |-> contents &*& ref_mut_end_token(result, (node.node.as_ptr() as *mut InternalNode<K, V>)) &*& ref_origin(result) == ref_origin((node.node.as_ptr() as *mut InternalNode<K, V>));
    //@ on_unwind_ens false;
    {
        //@ let view = precreate_ref(self);
        //@ init_ref_readonly(view, 1/2);
        let ptr = unsafe { Self::as_internal_ptr(self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(self, _);
        unsafe { &mut *ptr } //~track_ref_creation
    }
}

/*@
pred internal_without_edges<K,V>(node: *InternalNode<K,V>; data: LeafNode<K,V>) =
    struct_InternalNode_padding(node) &*& *(&(*node).data) |-> data;
@*/

/*@
pred edges_loan<K,V>(
    owner: *InternalNode<K,V>, base: *MaybeUninit<BoxedNode<K, V>>, first: usize, last: usize,
    data: LeafNode<K,V>, before: list<MaybeUninit<BoxedNode<K, V>>>, tail: list<MaybeUninit<BoxedNode<K, V>>>
) =
    exists::<*InternalNode<K,V>>(?view) &*& ref_mut_end_token(view, owner) &*&
    ref_mut_end_token(?array, &(*view).edges) &*& base == array as *MaybeUninit<BoxedNode<K, V>> &*&
    internal_without_edges(view, data) &*&
    0 <= first &*& first <= last &*& last <= (CAPACITY + 1) &*&
    (if first == 0 { before == nil } else { base[..first] |-> before }) &*&
    base[last..(CAPACITY + 1)] |-> tail;

lem restore_edges<K,V>(owner: *InternalNode<K,V>, base: *MaybeUninit<BoxedNode<K, V>>)
    req edges_loan(owner, base, ?first, ?last, ?data, ?before, ?tail) &*&
        base[first..last] |-> ?active;
    ens internal_without_edges(owner, data) &*&
        (*owner).edges[..(CAPACITY + 1)] |-> append(before, append(active, tail));
{
    open edges_loan(owner, base, first, last, data, before, tail);
    open exists::<*InternalNode<K,V>>(?view);
    assert ref_mut_end_token(?array, &(*view).edges);
    if first != 0 {
        array_join(base + first);
    }
    array_join(base);
    close_points_to(array);
    end_ref_mut(array);
    open_points_to(&(*view).edges);
    open internal_without_edges(view, data);
    open_points_to(&(*view).data);
    close_points_to(view);
    end_ref_mut(view);
    open_points_to(owner);
    close_points_to(&(*owner).data);
    close internal_without_edges(owner, data);
}

pred edges_range_loan<K,V>(
    owner: *InternalNode<K,V>, lent: *[MaybeUninit<BoxedNode<K, V>>], first: usize, last: usize,
    data: LeafNode<K,V>, before: list<MaybeUninit<BoxedNode<K, V>>>, tail: list<MaybeUninit<BoxedNode<K, V>>>
) =
    edges_loan(owner, ?base, first, last, data, before, tail) &*&
    slice_ref_mut_end_token(lent, base + first, last - first);

pred edges_slot_loan<K,V>(
    owner: *InternalNode<K,V>, lent: *MaybeUninit<BoxedNode<K, V>>, first: usize,
    data: LeafNode<K,V>, before: list<MaybeUninit<BoxedNode<K, V>>>, tail: list<MaybeUninit<BoxedNode<K, V>>>
) =
    edges_loan(owner, ?base, first, first + 1, data, before, tail) &*&
    ref_mut_end_token(lent, base + first);

lem end_edges_range<K,V>(owner: *InternalNode<K,V>, lent: *[MaybeUninit<BoxedNode<K, V>>])
    req edges_range_loan(owner, lent, ?first, ?last, ?data, ?before, ?tail) &*&
        move_slice(lent as *MaybeUninit<BoxedNode<K, V>>, last - first, ?active);
    ens internal_without_edges(owner, data) &*&
        (*owner).edges[..(CAPACITY + 1)] |-> append(before, append(active, tail));
{
    open edges_range_loan(owner, lent, first, last, data, before, tail);
    assert edges_loan(owner, ?base, first, last, data, before, tail);
    open move_slice(lent as *MaybeUninit<BoxedNode<K, V>>, last - first, active);
    end_slice_ref_mut(lent);
    restore_edges(owner, base);
}

lem end_edges_slot<K,V>(owner: *InternalNode<K,V>, lent: *MaybeUninit<BoxedNode<K, V>>)
    req edges_slot_loan(owner, lent, ?first, ?data, ?before, ?tail) &*&
        *lent |-> ?entry;
    ens internal_without_edges(owner, data) &*&
        (*owner).edges[..(CAPACITY + 1)] |-> append(before, cons(entry, tail));
{
    open edges_slot_loan(owner, lent, first, data, before, tail);
    assert edges_loan(owner, ?base, first, first + 1, data, before, tail);
    open edges_loan(owner, base, first, first + 1, data, before, tail);
    assert base[first + 1..(CAPACITY + 1)] |-> tail;
    array_inv::<MaybeUninit<BoxedNode<K, V>>>();
    close edges_loan(owner, base, first, first + 1, data, before, tail);
    end_ref_mut(lent);
    points_to_limits(base + first);
    close array(base + first + 1, 0, []);
    close array(base + first, 1, [entry]);
    restore_edges(owner, base);
}
@*/

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn edge_area_range_mut<'short>(
        &'short mut self, index: std::ops::Range<usize>,
    ) -> &'short mut [MaybeUninit<BoxedNode<K, V>>]
    /*@
    req *self |-> ?node &*& internal_without_edges((node.node.as_ptr() as *mut InternalNode<K, V>), ?data) &*&
        (*(node.node.as_ptr() as *mut InternalNode<K, V>)).edges[..(CAPACITY + 1)] |-> ?slots &*& 0 <= index.start &*& index.start <= index.end &*& index.end <= (CAPACITY + 1);
    @*/
    /*@
    ens *self |-> node &*&
        edges_range_loan((node.node.as_ptr() as *mut InternalNode<K, V>), result, index.start, index.end, data, take(index.start, slots), drop(index.end, slots)) &*&
        result.len() == index.end - index.start &*&
        move_slice(result as *MaybeUninit<BoxedNode<K, V>>, index.end - index.start, take(index.end - index.start, drop(index.start, slots))) &*& ref_origin((result as *MaybeUninit<BoxedNode<K, V>>)) == ref_origin(&(*(node.node.as_ptr() as *mut InternalNode<K, V>)).edges as *MaybeUninit<BoxedNode<K, V>> + index.start);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open internal_without_edges((node.node.as_ptr() as *mut InternalNode<K, V>), data);
        //@ open_points_to(&(*(node.node.as_ptr() as *mut InternalNode<K, V>)).data);
        //@ close_points_to((node.node.as_ptr() as *mut InternalNode<K, V>));
        let storage = unsafe { self.as_internal_mut/*@::<'a,K,V,'short>@*/() };
        //@ open_points_to(storage);
        //@ close_points_to(&(*storage).data);
        //@ close_points_to(&(*storage).edges);
        let array = &mut storage.edges;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<BoxedNode<K, V>>;
        //@ let first = index.start;
        //@ let last = index.end;
        //@ insertion_slot_limits(base);
        //@ move_slice_offset(base, (CAPACITY + 1), first);
        //@ btree_aligned_offset(base, first);
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        
        let lent = unsafe { view.get_unchecked_mut(index) };
        //@ close move_slice(lent as *MaybeUninit<BoxedNode<K, V>>, last - first, _);
        //@ close internal_without_edges(storage, data);
        //@ close exists::<*InternalNode<K,V>>(storage);
        //@ close edges_loan((node.node.as_ptr() as *mut InternalNode<K, V>), base, first, last, data, take(first, slots), drop(last, slots));
        //@ close edges_range_loan((node.node.as_ptr() as *mut InternalNode<K, V>), lent, first, last, data, take(first, slots), drop(last, slots));
        lent
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn edge_area_prefix_mut<'short>(
        &'short mut self, index: std::ops::RangeTo<usize>,
    ) -> &'short mut [MaybeUninit<BoxedNode<K, V>>]
    /*@
    req *self |-> ?node &*& internal_without_edges((node.node.as_ptr() as *mut InternalNode<K, V>), ?data) &*&
        (*(node.node.as_ptr() as *mut InternalNode<K, V>)).edges[..(CAPACITY + 1)] |-> ?slots &*& 0 <= index.end &*& index.end <= (CAPACITY + 1);
    @*/
    /*@
    ens *self |-> node &*&
        edges_range_loan((node.node.as_ptr() as *mut InternalNode<K, V>), result, 0, index.end, data, take(0, slots), drop(index.end, slots)) &*&
        result.len() == index.end - 0 &*&
        move_slice(result as *MaybeUninit<BoxedNode<K, V>>, index.end - 0, take(index.end - 0, drop(0, slots))) &*& ref_origin((result as *MaybeUninit<BoxedNode<K, V>>)) == ref_origin(&(*(node.node.as_ptr() as *mut InternalNode<K, V>)).edges as *MaybeUninit<BoxedNode<K, V>> + 0);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open internal_without_edges((node.node.as_ptr() as *mut InternalNode<K, V>), data);
        //@ open_points_to(&(*(node.node.as_ptr() as *mut InternalNode<K, V>)).data);
        //@ close_points_to((node.node.as_ptr() as *mut InternalNode<K, V>));
        let storage = unsafe { self.as_internal_mut/*@::<'a,K,V,'short>@*/() };
        //@ open_points_to(storage);
        //@ close_points_to(&(*storage).data);
        //@ close_points_to(&(*storage).edges);
        let array = &mut storage.edges;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<BoxedNode<K, V>>;
        //@ let first = 0;
        //@ let last = index.end;
        //@ insertion_slot_limits(base);
        //@ move_slice_offset(base, (CAPACITY + 1), first);
        //@ btree_aligned_offset(base, first);
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        
        let lent = unsafe { view.get_unchecked_mut(index) };
        //@ close move_slice(lent as *MaybeUninit<BoxedNode<K, V>>, last - first, _);
        //@ close internal_without_edges(storage, data);
        //@ close exists::<*InternalNode<K,V>>(storage);
        //@ close edges_loan((node.node.as_ptr() as *mut InternalNode<K, V>), base, first, last, data, take(first, slots), drop(last, slots));
        //@ close edges_range_loan((node.node.as_ptr() as *mut InternalNode<K, V>), lent, first, last, data, take(first, slots), drop(last, slots));
        lent
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn edge_area_slot_mut<'short>(
        &'short mut self, index: usize,
    ) -> &'short mut MaybeUninit<BoxedNode<K, V>>
    /*@
    req *self |-> ?node &*& internal_without_edges((node.node.as_ptr() as *mut InternalNode<K, V>), ?data) &*&
        (*(node.node.as_ptr() as *mut InternalNode<K, V>)).edges[..(CAPACITY + 1)] |-> ?slots &*& 0 <= index &*& index < (CAPACITY + 1);
    @*/
    /*@
    ens *self |-> node &*&
        edges_slot_loan((node.node.as_ptr() as *mut InternalNode<K, V>), result, index, data, take(index, slots), drop(index + 1, slots)) &*&
        *result |-> nth(index, slots) &*& ref_origin(result) == ref_origin(&(*(node.node.as_ptr() as *mut InternalNode<K, V>)).edges as *MaybeUninit<BoxedNode<K, V>> + index);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open internal_without_edges((node.node.as_ptr() as *mut InternalNode<K, V>), data);
        //@ open_points_to(&(*(node.node.as_ptr() as *mut InternalNode<K, V>)).data);
        //@ close_points_to((node.node.as_ptr() as *mut InternalNode<K, V>));
        let storage = unsafe { self.as_internal_mut/*@::<'a,K,V,'short>@*/() };
        //@ open_points_to(storage);
        //@ close_points_to(&(*storage).data);
        //@ close_points_to(&(*storage).edges);
        let array = &mut storage.edges;
        let view = array.as_mut_slice();
        //@ open_points_to(array);
        //@ let base = view as *MaybeUninit<BoxedNode<K, V>>;
        //@ let first = index;
        //@ let last = index + 1;
        
        //@ if first != 0 { array_split(base, first); }
        //@ array_split(base + first, last - first);
        //@ drop_twice(last - first, first, slots);
        //@ open array(base + first, 1, _);
        //@ nth_drop(0, first, slots);
        let lent = unsafe { view.get_unchecked_mut(index) };
        
        //@ close internal_without_edges(storage, data);
        //@ close exists::<*InternalNode<K,V>>(storage);
        //@ close edges_loan((node.node.as_ptr() as *mut InternalNode<K, V>), base, first, last, data, take(first, slots), drop(last, slots));
        //@ close edges_slot_loan((node.node.as_ptr() as *mut InternalNode<K, V>), lent, first, data, take(first, slots), drop(last, slots));
        lent
    }
}

/*@
pred leaf_without_len<K,V>(leaf: *LeafNode<K,V>;
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>,
    keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>) =
    struct_LeafNode_padding(leaf) &*&
    (*leaf).parent |-> parent &*& (*leaf).parent_idx |-> index &*&
    (*leaf).keys[..CAPACITY] |-> keys &*& (*leaf).vals[..CAPACITY] |-> vals;

pred len_loan<K,V>(leaf: *LeafNode<K,V>, lent: *u16,
    parent: Option<NonNull<InternalNode<K,V>>>, index: MaybeUninit<u16>,
    keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>) =
    exists::<*LeafNode<K,V>>(?view) &*& ref_mut_end_token(view, leaf) &*&
    ref_mut_end_token(lent, &(*view).len) &*& leaf_without_len(view, parent, index, keys, vals);

lem end_len_loan<K,V>(leaf: *LeafNode<K,V>, lent: *u16)
    req len_loan(leaf, lent, ?parent, ?index, ?keys, ?vals) &*& *lent |-> ?updated;
    ens leaf_without_len(leaf, parent, index, keys, vals) &*& (*leaf).len |-> updated;
{
    open len_loan(leaf, lent, parent, index, keys, vals);
    open exists::<*LeafNode<K,V>>(?view);
    end_ref_mut(lent);
    open leaf_without_len(view, parent, index, keys, vals);
    close_points_to(view);
    end_ref_mut(view);
    open_points_to(leaf);
    close leaf_without_len(leaf, parent, index, keys, vals);
}
@*/

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn len_mut<'short>(&'short mut self) -> &'short mut u16
    /*@
    req *self |-> ?node &*&
        leaf_without_len(node.node.as_ptr(), ?parent, ?index, ?keys, ?vals) &*&
        (*node.node.as_ptr()).len |-> ?len;
    @*/
    /*@
    ens *self |-> node &*& *result |-> len &*&
        len_loan(node.node.as_ptr(), result, parent, index, keys, vals) &*&
        ref_origin(result) == ref_origin(&(*node.node.as_ptr()).len);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open leaf_without_len(node.node.as_ptr(), parent, index, keys, vals);
        //@ close_points_to(node.node.as_ptr());
        let storage = unsafe { self.as_leaf_mut/*@::<'a,K,V,Type,'short>@*/() };
        //@ open_points_to(storage);
        let lent = &mut storage.len; //~track_ref_creation
        //@ close leaf_without_len(storage, parent, index, keys, vals);
        //@ close exists::<*LeafNode<K,V>>(storage);
        //@ close len_loan(node.node.as_ptr(), lent, parent, index, keys, vals);
        lent
    }
}

impl<'a, K, V> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal> {
    unsafe fn cast_to_internal_unchecked(self) -> NodeRef<marker::Mut<'a>, K, V, marker::Internal>
    //@ req 0 < self.height;
    //@ ens result.node == self.node &*& result.height == self.height;
    //@ on_unwind_ens false;
    {
        debug_assert!(self.height > 0);
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

/*@
pred move_slice<T>(base: *MaybeUninit<T>, len: usize; slots: list<MaybeUninit<T>>) =
    base[..len] |-> slots &*& 0 <= len &*& len <= usize::MAX &*& base as usize != 0 &*&
    base as usize % std::mem::align_of::<MaybeUninit<T>>() == 0 &*&
    pointer_within_limits(base) == true &*& pointer_within_limits(base + len) == true;

lem move_slice_length<T>(base: *MaybeUninit<T>, len: usize)
    req move_slice(base, len, ?slots);
    ens move_slice(base, len, slots) &*& length(slots) == len;
{
    open move_slice(base, len, slots);
    array_inv::<MaybeUninit<T>>();
    close move_slice(base, len, slots);
}

lem move_slice_offset<T>(base: *T, len: usize, index: usize)
    req 0 <= index &*& index <= len &*&
        pointer_within_limits(base) == true &*& pointer_within_limits(base + len) == true;
    ens pointer_within_limits(base + index) == true &*&
        (base + index) as usize >= base as usize;
{
    std::alloc::is_valid_layout_size_of_align_of::<T>();
    mul_mono_l(0, index, std::mem::size_of::<T>());
    mul_mono_l(index, len, std::mem::size_of::<T>());
}

lem drop_twice<T>(outer: i32, inner: i32, slots: list<T>)
    req 0 <= inner &*& 0 <= outer &*& inner + outer <= length(slots);
    ens drop(outer, drop(inner, slots)) == drop(inner + outer, slots);
{
    match slots {
        nil => {}
        cons(slot, rest) => {
            if inner > 0 { drop_twice(outer, inner - 1, rest); }
        }
    }
}

lem btree_restore_shl<T>(p: *T, n: i32, distance: i32, values: list<T>, bytes: list<option<u8>>)
    req 0 <= distance &*& distance <= n &*& length(values) == n &*&
        btree_encoded(values, bytes) == true &*&
        (p as *u8)[..n * std::mem::size_of::<T>()] |-?->
            append(drop(distance * std::mem::size_of::<T>(), bytes), drop((n - distance) * std::mem::size_of::<T>(), bytes)) &*&
        p as usize % std::mem::align_of::<T>() == 0;
    ens p[..n] |-> append(drop(distance, values), drop(n - distance, values));
{
    btree_encoded_split(values, bytes, distance);
    btree_encoded_split(values, bytes, n - distance);
    btree_encoded_append(drop(distance, values), drop(distance * std::mem::size_of::<T>(), bytes),
        drop(n - distance, values), drop((n - distance) * std::mem::size_of::<T>(), bytes));
    btree_bytes_to_values(p, append(drop(distance, values), drop(n - distance, values)));
}
@*/

// BEGIN_SLICE_SHL
unsafe fn slice_shl<T>(slice: &mut [MaybeUninit<T>], distance: usize)
/*@
req 0 <= distance &*& distance <= slice.len() &*&
    move_slice(slice as *MaybeUninit<T>, slice.len(), ?slots);
@*/
/*@
ens move_slice(slice as *MaybeUninit<T>, slice.len(),
    append(drop(distance, slots), drop(slice.len() - distance, slots)));
@*/
//@ on_unwind_ens false;
{
    let slice_ptr = slice.as_mut_ptr();
    //@ open move_slice(slice_ptr, slice.len(), slots);
    //@ btree_values_to_bytes(slice_ptr, slice.len());
    //@ assert (slice_ptr as *u8)[..slice.len() * std::mem::size_of::<MaybeUninit<T>>()] |-?-> ?bytes;
    //@ move_slice_offset(slice_ptr, slice.len(), distance);
    //@ btree_aligned_offset(slice_ptr, distance);
    //@ close exists::<bool>(false);
    //@ close exists::<usize>(distance);
    unsafe {
        ptr::copy(slice_ptr.add(distance), slice_ptr, slice.len() - distance);
    }
    //@ btree_restore_shl(slice_ptr, slice.len(), distance, slots, bytes);
    //@ close move_slice(slice_ptr, slice.len(), _);
}
// END_SLICE_SHL

// BEGIN_SLICE_SHR
unsafe fn slice_shr<T>(slice: &mut [MaybeUninit<T>], distance: usize)
/*@
req 0 <= distance &*& distance <= slice.len() &*&
    move_slice(slice as *MaybeUninit<T>, slice.len(), ?slots);
@*/
/*@
ens move_slice(slice as *MaybeUninit<T>, slice.len(),
    append(take(distance, slots), take(slice.len() - distance, slots)));
@*/
//@ on_unwind_ens false;
{
    let slice_ptr = slice.as_mut_ptr();
    //@ open move_slice(slice_ptr, slice.len(), slots);
    //@ btree_values_to_bytes(slice_ptr, slice.len());
    //@ assert (slice_ptr as *u8)[..slice.len() * std::mem::size_of::<MaybeUninit<T>>()] |-?-> ?bytes;
    //@ move_slice_offset(slice_ptr, slice.len(), distance);
    //@ btree_aligned_offset(slice_ptr, distance);
    //@ close exists::<bool>(true);
    //@ close exists::<usize>(distance);
    unsafe {
        ptr::copy(slice_ptr, slice_ptr.add(distance), slice.len() - distance);
    }
    //@ btree_restore_shr(slice_ptr, slice.len(), distance, slots, bytes);
    //@ close move_slice(slice_ptr, slice.len(), _);
}
// END_SLICE_SHR

// The copied bytes do not duplicate ownership of T. The caller transfers the
// ownership of the initialized elements when it changes the active prefixes.
// BEGIN_MOVE_TO_SLICE
unsafe fn move_to_slice<T>(src: &mut [MaybeUninit<T>], dst: &mut [MaybeUninit<T>])
/*@
req src.len() == dst.len() &*&
    move_slice(src as *MaybeUninit<T>, src.len(), ?source) &*&
    move_slice(dst as *MaybeUninit<T>, dst.len(), _);
@*/
/*@
ens move_slice(src as *MaybeUninit<T>, src.len(), source) &*&
    move_slice(dst as *MaybeUninit<T>, dst.len(), source);
@*/
//@ on_unwind_ens false;
{
    assert!(src.len() == dst.len());
    //@ open move_slice(src as *MaybeUninit<T>, src.len(), source);
    //@ open move_slice(dst as *MaybeUninit<T>, dst.len(), _);
    //@ array_to_array_::<MaybeUninit<T>>(dst as *MaybeUninit<T>);
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
    //@ close move_slice(src as *MaybeUninit<T>, src.len(), source);
    //@ close move_slice(dst as *MaybeUninit<T>, dst.len(), source);
}
// END_MOVE_TO_SLICE

// BEGIN_SLICE_REMOVE
unsafe fn slice_remove<T>(slice: &mut [MaybeUninit<T>], idx: usize) -> T
/*@
req thread_token(?t) &*& type_interp::<T>() &*& 0 <= idx &*& idx < slice.len() &*&
    move_slice(slice as *MaybeUninit<T>, slice.len(), ?slots) &*&
    nth(idx, slots).inner() == some(?value) &*&
    nth(idx, slots) == MaybeUninit::new(value) &*& <T>.own(t, value);
@*/
/*@
ens thread_token(t) &*& type_interp::<T>() &*& result == value &*& <T>.own(t, result) &*&
    move_slice(slice as *MaybeUninit<T>, slice.len(),
        append(take(idx, slots), append(drop(idx + 1, slots), drop(slice.len() - 1, slots))));
@*/
//@ on_unwind_ens false;
{
    let len = slice.len();
    debug_assert!(idx < len);
    let slice_ptr = slice.as_mut_ptr();
    //@ open move_slice(slice_ptr, len, slots);
    //@ let base = slice_ptr + idx;
    //@ let suffix = drop(idx, slots);
    //@ move_slice_offset(slice_ptr, len, idx);
    //@ move_slice_offset(slice_ptr, len, idx + 1);
    //@ array_split(slice_ptr, idx);
    //@ array_split(base, 1);
    //@ drop_n_plus_one(idx, slots);
    //@ open array(base, 1, take(1, suffix));
    unsafe {
        //@ let view = precreate_ref(base);
        //@ init_ref_readonly(view, 1/2);
        let ret = (*slice_ptr.add(idx)).assume_init_read();
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(base, _);
        //@ close array(base, 1, take(1, suffix));
        //@ array_join(base);
        //@ btree_aligned_offset(slice_ptr, idx);
        //@ btree_values_to_bytes(base, len - idx);
        //@ assert (base as *u8)[..(len - idx) * std::mem::size_of::<MaybeUninit<T>>()] |-?-> ?bytes;
        //@ btree_aligned_offset(base, 1);
        //@ close exists::<bool>(false);
        //@ close exists::<usize>(1);
        ptr::copy(slice_ptr.add(idx + 1), slice_ptr.add(idx), len - idx - 1);
        //@ btree_restore_shl(base, len - idx, 1, suffix, bytes);
        //@ array_join(slice_ptr);
        //@ drop_twice(1, idx, slots);
        //@ drop_twice(len - idx - 1, idx, slots);
        //@ close move_slice(slice_ptr, len, _);
        ret
    }
}
// END_SLICE_REMOVE

/*@
pred slot_owners<T>(thread: thread_id_t, slots: list<MaybeUninit<T>>) =
    match slots {
        nil => true,
        cons(slot, rest) => slot.inner() == some(?value) &*& slot == MaybeUninit::new(value) &*&
            <T>.own(thread, value) &*& slot_owners(thread, rest)
    };

lem split_slot_owners<T>(thread: thread_id_t, slots: list<MaybeUninit<T>>, index: usize)
    req slot_owners(thread, slots) &*& 0 <= index &*& index <= length(slots);
    ens slot_owners(thread, take(index, slots)) &*& slot_owners(thread, drop(index, slots));
{
    if index == 0 {
        close slot_owners::<T>(thread, nil);
    } else {
        open slot_owners(thread, slots);
        match slots {
            nil => {}
            cons(slot, rest) => {
                split_slot_owners(thread, rest, index - 1);
                close slot_owners(thread, take(index, slots));
            }
        }
    }
}

lem join_slot_owners<T>(thread: thread_id_t, left: list<MaybeUninit<T>>, right: list<MaybeUninit<T>>)
    req slot_owners(thread, left) &*& slot_owners(thread, right);
    ens slot_owners(thread, append(left, right));
{
    open slot_owners(thread, left);
    match left {
        nil => {}
        cons(slot, rest) => {
            join_slot_owners(thread, rest, right);
            close slot_owners(thread, append(left, right));
        }
    }
}

lem split_move_slice<T>(base: *MaybeUninit<T>, len: usize, index: usize)
    req move_slice(base, len, ?slots) &*& 0 <= index &*& index <= len;
    ens move_slice(base, index, take(index, slots)) &*&
        move_slice(base + index, len - index, drop(index, slots)) &*&
        pointer_within_limits(base + index) == true;
{
    open move_slice(base, len, slots);
    move_slice_offset(base, len, index);
    btree_aligned_offset(base, index);
    array_split(base, index);
    close move_slice(base, index, take(index, slots));
    close move_slice(base + index, len - index, drop(index, slots));
}

lem join_move_slices<T>(base: *MaybeUninit<T>, first: usize, second: usize)
    req move_slice(base, first, ?prefix) &*& move_slice(base + first, second, ?suffix) &*&
        first + second <= usize::MAX;
    ens move_slice(base, first + second, append(prefix, suffix));
{
    open move_slice(base, first, prefix);
    open move_slice(base + first, second, suffix);
    array_join(base);
    close move_slice(base, first + second, append(prefix, suffix));
}
@*/

// Array accessors in the node code produce views of this form. The proof
// retains the permissions for the selected range across view creation.
// BEGIN_MOVE_SLICE_VIEW
unsafe fn move_slice_mut<'a, T>(base: *mut MaybeUninit<T>, len: usize) -> &'a mut [MaybeUninit<T>]
//@ req move_slice(base, len, ?slots);
//@ ens move_slice(base, len, slots) &*& result as *MaybeUninit<T> == base &*& result.len() == len;
//@ on_unwind_ens false;
{
    //@ open move_slice(base, len, slots);
    let slice = unsafe { std::slice::from_raw_parts_mut(base, len) };
    //@ close move_slice(base, len, slots);
    slice
}
// END_MOVE_SLICE_VIEW

// BEGIN_MERGE_PAYLOAD
unsafe fn merge_payload<T>(
    parent: *mut MaybeUninit<T>,
    left: *mut MaybeUninit<T>,
    right: *mut MaybeUninit<T>,
    parent_idx: usize,
    old_parent_len: usize,
    old_left_len: usize,
    right_len: usize,
    new_left_len: usize,
)
/*@
req thread_token(?t) &*& type_interp::<T>() &*&
    0 <= parent_idx &*& parent_idx < old_parent_len &*&
    0 <= old_left_len &*& 0 <= right_len &*& new_left_len == old_left_len + 1 + right_len &*&
    move_slice(parent, old_parent_len, ?p) &*& move_slice(left, new_left_len, ?l) &*&
    move_slice(right, right_len, ?r) &*& slot_owners(t, p) &*&
    slot_owners(t, take(old_left_len, l)) &*& slot_owners(t, r);
@*/
/*@
ens thread_token(t) &*& type_interp::<T>() &*&
    move_slice(parent, old_parent_len, ?p_after) &*&
    take(old_parent_len - 1, p_after) == append(take(parent_idx, p), drop(parent_idx + 1, p)) &*&
    move_slice(left, new_left_len, append(take(old_left_len, l), cons(nth(parent_idx, p), r))) &*&
    move_slice(right, right_len, r) &*& slot_owners(t, take(old_parent_len - 1, p_after)) &*&
    slot_owners(t, append(take(old_left_len, l), cons(nth(parent_idx, p), r)));
@*/
//@ on_unwind_ens false;
{
    //@ move_slice_length(parent, old_parent_len);
    //@ split_slot_owners(t, p, parent_idx);
    //@ drop_n_plus_one(parent_idx, p);
    //@ open slot_owners(t, drop(parent_idx, p));
    unsafe {
        let entry = slice_remove(move_slice_mut(parent, old_parent_len), parent_idx);
        //@ split_move_slice(left, new_left_len, old_left_len);
        //@ split_move_slice(left + old_left_len, new_left_len - old_left_len, 1);
        //@ let target = left + old_left_len;
        //@ open move_slice(target, 1, _);
        //@ open array(target, 1, _);
        //@ open array(target + 1, 0, _);
        //@ close array(target + 1, 0, nil);
        (*left.add(old_left_len)).write(entry);
        //@ close array(target, 1, [MaybeUninit::new(entry)]);
        //@ close move_slice(target, 1, [MaybeUninit::new(entry)]);
        move_to_slice(
            move_slice_mut(right, right_len),
            move_slice_mut(left.add(old_left_len + 1), new_left_len - (old_left_len + 1)),
        );
        //@ join_move_slices(target, 1, right_len);
        //@ join_move_slices(left, old_left_len, 1 + right_len);
        //@ close slot_owners(t, cons(nth(parent_idx, p), r));
        //@ join_slot_owners(t, take(old_left_len, l), cons(nth(parent_idx, p), r));
        //@ let surviving = append(take(parent_idx, p), drop(parent_idx + 1, p));
        //@ join_slot_owners(t, take(parent_idx, p), drop(parent_idx + 1, p));
        //@ append_assoc(take(parent_idx, p), drop(parent_idx + 1, p), drop(old_parent_len - 1, p));
        //@ length_take(parent_idx, p);
        //@ length_drop(parent_idx + 1, p);
        //@ take_append_l(old_parent_len - 1, surviving, drop(old_parent_len - 1, p));
        //@ take_length(surviving);
    }
}
// END_MERGE_PAYLOAD

unsafe fn move_array_prefix<T>(
    src: *mut [MaybeUninit<T>; CAPACITY],
    start: usize,
    end: usize,
    dst: *mut [MaybeUninit<T>; CAPACITY],
    from: usize,
    to: usize,
)
/*@
req (src as *MaybeUninit<T>)[..CAPACITY] |-> ?s &*&
    (dst as *MaybeUninit<T>)[..CAPACITY] |-> ?d &*&
    0 <= start &*& start <= end &*& end <= CAPACITY &*&
    from == 0 &*& 0 <= from &*& from <= to &*& to <= CAPACITY &*& end - start == to - from;
@*/
/*@
ens (src as *MaybeUninit<T>)[..CAPACITY] |-> s &*&
    (dst as *MaybeUninit<T>)[..CAPACITY] |->
        append(take(from, d), append(take(end - start, drop(start, s)), drop(to, d)));
@*/
//@ on_unwind_ens false;
{
    //@ close_points_to(src);
    //@ close_points_to(dst);
    unsafe {
        let source_array = &mut *src;
        let target_array = &mut *dst;
        let source = source_array.as_mut_slice();
        let target = target_array.as_mut_slice();
        //@ points_to_limits(source_array);
        //@ points_to_limits(target_array);
        //@ open_points_to(source_array);
        //@ open_points_to(target_array);
        //@ let source_base = source as *MaybeUninit<T>;
        //@ let target_base = target as *MaybeUninit<T>;
        //@ insertion_slot_limits(source_base);
        //@ insertion_slot_limits(target_base);
        //@ move_slice_offset(source_base, CAPACITY, start);
        //@ move_slice_offset(target_base, CAPACITY, from);
        //@ btree_aligned_offset(source_base, start);
        //@ btree_aligned_offset(target_base, from);
        //@ array_split(source_base, start);
        //@ array_split(source_base + start, end - start);
        
        //@ array_split(target_base + from, to - from);
        let source_range = source.get_unchecked_mut(start..end);
        let target_range = target.get_unchecked_mut(..to);
        //@ close move_slice(source_range as *MaybeUninit<T>, end - start, _);
        //@ close move_slice(target_range as *MaybeUninit<T>, to - from, _);
        move_to_slice(source_range, target_range);
        //@ open move_slice(source_range as *MaybeUninit<T>, end - start, _);
        //@ open move_slice(target_range as *MaybeUninit<T>, to - from, _);
        //@ end_slice_ref_mut(source_range);
        //@ end_slice_ref_mut(target_range);
        //@ array_join(source_base + start);
        //@ array_join(source_base);
        //@ array_join(target_base + from);
        
        //@ close_points_to(source_array);
        //@ close_points_to(target_array);
        //@ end_ref_mut(source_array);
        //@ end_ref_mut(target_array);
    }
    //@ open_points_to(src);
    //@ open_points_to(dst);
    //@ drop_twice(to - from, from, d);
}

unsafe fn move_edge_range<T>(
    src: *mut [MaybeUninit<T>; CAPACITY + 1],
    start: usize,
    end: usize,
    dst: *mut [MaybeUninit<T>; CAPACITY + 1],
    from: usize,
    to: usize,
)
/*@
req (src as *MaybeUninit<T>)[..CAPACITY + 1] |-> ?s &*&
    (dst as *MaybeUninit<T>)[..CAPACITY + 1] |-> ?d &*&
    0 <= start &*& start <= end &*& end <= CAPACITY + 1 &*&
    0 <= from &*& from <= to &*& to <= CAPACITY + 1 &*& end - start == to - from;
@*/
/*@
ens (src as *MaybeUninit<T>)[..CAPACITY + 1] |-> s &*&
    (dst as *MaybeUninit<T>)[..CAPACITY + 1] |->
        append(take(from, d), append(take(end - start, drop(start, s)), drop(to, d)));
@*/
//@ on_unwind_ens false;
{
    //@ close_points_to(src);
    //@ close_points_to(dst);
    unsafe {
        let source_array = &mut *src;
        let target_array = &mut *dst;
        let source = source_array.as_mut_slice();
        let target = target_array.as_mut_slice();
        //@ points_to_limits(source_array);
        //@ points_to_limits(target_array);
        //@ open_points_to(source_array);
        //@ open_points_to(target_array);
        //@ let source_base = source as *MaybeUninit<T>;
        //@ let target_base = target as *MaybeUninit<T>;
        //@ insertion_slot_limits(source_base);
        //@ insertion_slot_limits(target_base);
        //@ move_slice_offset(source_base, CAPACITY + 1, start);
        //@ move_slice_offset(target_base, CAPACITY + 1, from);
        //@ btree_aligned_offset(source_base, start);
        //@ btree_aligned_offset(target_base, from);
        //@ array_split(source_base, start);
        //@ array_split(source_base + start, end - start);
        //@ array_split(target_base, from);
        //@ array_split(target_base + from, to - from);
        let source_range = source.get_unchecked_mut(start..end);
        let target_range = target.get_unchecked_mut(from..to);
        //@ close move_slice(source_range as *MaybeUninit<T>, end - start, _);
        //@ close move_slice(target_range as *MaybeUninit<T>, to - from, _);
        move_to_slice(source_range, target_range);
        //@ open move_slice(source_range as *MaybeUninit<T>, end - start, _);
        //@ open move_slice(target_range as *MaybeUninit<T>, to - from, _);
        //@ end_slice_ref_mut(source_range);
        //@ end_slice_ref_mut(target_range);
        //@ array_join(source_base + start);
        //@ array_join(source_base);
        //@ array_join(target_base + from);
        //@ array_join(target_base);
        //@ close_points_to(source_array);
        //@ close_points_to(target_array);
        //@ end_ref_mut(source_array);
        //@ end_ref_mut(target_array);
    }
    //@ open_points_to(src);
    //@ open_points_to(dst);
    //@ drop_twice(to - from, from, d);
}

/*@
lem own_move_array<T>(base: *MaybeUninit<T>, len: usize)
    req base[..len] |-> ?slots &*& 0 < len &*& len <= usize::MAX;
    ens move_slice(base, len, slots);
{
    insertion_slot_limits(base);
    array_inv::<MaybeUninit<T>>();
    close move_slice(base, len, slots);
}

pred balancing_edges<K,V>(
    node: NonNull<InternalNode<K,V>>, children: list<BoxedNode<K,V>>;
    slots: list<MaybeUninit<BoxedNode<K,V>>>
) =
    length(children) <= CAPACITY + 1 &*&
    pointer_within_limits(&(*node.as_ptr()).edges) == true &*&
    (*node.as_ptr()).edges[..CAPACITY + 1] |-> slots &*&
    take(length(children), slots) == initialized_edges(children) &*&
    linked_headers(children, node, 0);
@*/

// BEGIN_MERGE_PARENT_EDGES
unsafe fn remove_merged_edge<'a, 'short, K, V>(
    parent_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
    parent_idx: usize,
    old_parent_len: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *parent_node |-> ?node &*& 0 < node.height &*& node.height <= usize::MAX &*&
    exists::<NonNull<InternalNode<K,V>>>(?parent) &*&
    node.node.as_ptr() as *InternalNode<K,V> == parent.as_ptr() &*&
    node.node.as_ptr() == &(*parent.as_ptr()).data &*&
    struct_InternalNode_padding(parent.as_ptr()) &*&
    leaf_without_len(&(*parent.as_ptr()).data, ?ancestor, ?ancestor_idx, ?keys, ?vals) &*&
    balancing_edges(parent, ?children, ?slots) &*& (*parent.as_ptr()).data.len |-> (old_parent_len as u16) &*&
    length(children) == old_parent_len + 1 &*&
    0 <= parent_idx &*& parent_idx < old_parent_len &*& old_parent_len <= CAPACITY &*&
    nth(parent_idx + 1, children).as_ptr() as usize != 0;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *parent_node |-> node &*& struct_InternalNode_padding(parent.as_ptr()) &*&
    leaf_without_len(&(*parent.as_ptr()).data, ancestor, ancestor_idx, keys, vals) &*&
    (*parent.as_ptr()).data.len |-> (old_parent_len - 1) as u16 &*&
    balancing_edges(parent, append(take(parent_idx + 1, children), drop(parent_idx + 2, children)), _) &*&
    (*nth((parent_idx + 1) as i32, children).as_ptr()).parent |-> Option::Some(parent) &*&
    (*nth((parent_idx + 1) as i32, children).as_ptr()).parent_idx |-> MaybeUninit::new((parent_idx + 1) as u16);
@*/
//@ on_unwind_ens false;
{
    //@ open exists(parent);
    //@ open balancing_edges(parent, children, slots);
    //@ let parent_ptr = parent.as_ptr();
    //@ let prefix = take(parent_idx + 1, children);
    //@ let rest = drop(parent_idx + 2, children);
    //@ let removed = nth(parent_idx + 1, children);
    //@ split_linked_headers(children, parent, 0, parent_idx + 1);
    //@ drop_n_plus_one(parent_idx + 1, children);
    //@ open linked_headers(cons(removed, rest), parent, parent_idx + 1);
    //@ forget_link_indices(rest, parent, parent_idx + 2);
    //@ let active = initialized_edges(children);
    //@ nth_initialized_edge(children, parent_idx + 1);
    //@ std::ptr::close_NonNull_own(t, removed);
    //@ produce_type_interp::<BoxedNode<K,V>>();
    unsafe {
        //@ nth_take_range(slots, old_parent_len + 1, parent_idx + 1);
        //@ open leaf_without_len(&(*parent_ptr).data, ancestor, ancestor_idx, keys, vals);
        //@ close_points_to(&(*parent_ptr).data);
        //@ close internal_without_edges(parent_ptr, ?data);
        slice_remove(
            parent_node.edge_area_prefix_mut/*@::<'a,K,V,'short>@*/(..old_parent_len + 1), parent_idx + 1,
        );
        //@ assert edges_range_loan(parent_ptr, ?removed_prefix, 0, old_parent_len + 1, data, _, _);
        //@ end_edges_range(parent_ptr, removed_prefix);
        //@ open internal_without_edges(parent_ptr, data);
        //@ open_points_to(&(*parent_ptr).data);
        //@ close leaf_without_len(&(*parent_ptr).data, ancestor, ancestor_idx, keys, vals);
        //@ leak <BoxedNode<K,V>>.own(t, removed);
        //@ std::ptr::open_NonNull_own(t, removed);
        //@ leak type_interp::<BoxedNode<K,V>>();
        //@ initialized_edge_split(children, parent_idx + 1);
        //@ initialized_edge_split(children, parent_idx + 2);
        //@ let surviving = append(initialized_edges(prefix), initialized_edges(rest));
        //@ let residual = drop(old_parent_len, active);
        //@ append_assoc(initialized_edges(prefix), initialized_edges(rest), residual);
        //@ initialized_edge_count(prefix);
        //@ initialized_edge_count(rest);
        //@ length_take(parent_idx + 1, children);
        //@ length_drop(parent_idx + 2, children);
// BEGIN_MERGE_PARENT_RELINK
        //@ assert (*parent_ptr).edges[..CAPACITY + 1] |-> ?new_edges;
        //@ let before = initialized_edges(prefix);
        //@ let tail = drop(old_parent_len + 1, slots);
        //@ append_assoc(before, append(initialized_edges(rest), residual), tail);
        //@ append_assoc(initialized_edges(rest), residual, tail);
        //@ close exists(parent);
        //@ close exists(pair(before, append(residual, tail)));
        parent_node.relink_range/*@::<'a,K,V,'short>@*/(parent_idx + 1..old_parent_len);
        *parent_node.len_mut/*@::<'a,K,V,marker::Internal,'short>@*/() -= 1;
        //@ assert len_loan(&(*parent_ptr).data, ?slot, ancestor, ancestor_idx, keys, vals);
        //@ end_len_loan(&(*parent_ptr).data, slot);
// END_MERGE_PARENT_RELINK
        //@ take_append_l(parent_idx + 1, initialized_edges(prefix), initialized_edges(rest));
        //@ take_length(initialized_edges(prefix));
        //@ take_append_l(old_parent_len, surviving, residual);
        //@ take_append_l(old_parent_len, append(surviving, residual), drop(old_parent_len + 1, slots));
        //@ join_linked_headers(prefix, rest, parent, 0);
        //@ initialized_edges_append(prefix, rest);
        //@ close balancing_edges(parent, append(prefix, rest), new_edges);
    }
}
// END_MERGE_PARENT_EDGES

// BEGIN_MERGE_CHILD_EDGES
unsafe fn append_merged_edges<'a, 'short, K, V>(
    left_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
    right_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
    old_left_len: usize,
    right_len: usize,
    new_left_len: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *left_node |-> ?ln &*& *right_node |-> ?rn &*&
    exists::<pair<NonNull<InternalNode<K,V>>, NonNull<InternalNode<K,V>>>>(pair(?left, ?right)) &*&
    ln.node.as_ptr() == &(*left.as_ptr()).data &*& ln.node.as_ptr() as *InternalNode<K,V> == left.as_ptr() &*&
    rn.node.as_ptr() as *InternalNode<K,V> == right.as_ptr() &*&
    0 < ln.height &*& ln.height <= usize::MAX &*&
    internal_without_edges(left.as_ptr(), ?left_data) &*& internal_without_edges(right.as_ptr(), ?right_data) &*&
    left_data.len == new_left_len as u16 &*&
    balancing_edges(left, ?left_children, ?left_slots) &*& balancing_edges(right, ?right_children, ?right_slots) &*&
    length(left_children) == old_left_len + 1 &*& length(right_children) == right_len + 1 &*&
    0 <= old_left_len &*& 0 <= right_len &*& new_left_len == old_left_len + 1 + right_len &*& new_left_len <= CAPACITY;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *left_node |-> ln &*& *right_node |-> rn &*&
    internal_without_edges(left.as_ptr(), left_data) &*& internal_without_edges(right.as_ptr(), right_data) &*&
    balancing_edges(left, append(left_children, right_children), _) &*&
    (*right.as_ptr()).edges[..CAPACITY + 1] |-> right_slots;
@*/
//@ on_unwind_ens false;
{
    //@ open exists(pair(left, right));
    //@ open balancing_edges(left, left_children, left_slots);
    //@ open balancing_edges(right, right_children, right_slots);
    //@ forget_link_indices(right_children, right, 0);
    unsafe {
        move_to_slice(
            right_node.edge_area_prefix_mut/*@::<'a,K,V,'short>@*/(..right_len + 1),
            left_node.edge_area_range_mut/*@::<'a,K,V,'short>@*/(old_left_len + 1..new_left_len + 1),
        );
        //@ assert edges_range_loan(right.as_ptr(), ?source, 0, right_len + 1, right_data, _, _);
        //@ assert edges_range_loan(left.as_ptr(), ?destination, old_left_len + 1, new_left_len + 1, left_data, _, _);
        //@ end_edges_range(right.as_ptr(), source);
        //@ append_take_drop_n(right_slots, right_len + 1);
        //@ end_edges_range(left.as_ptr(), destination);
        //@ let before = take(old_left_len + 1, left_slots);
        //@ let after_copy = drop(new_left_len + 1, left_slots);
        //@ length_take(old_left_len + 1, left_slots);
        //@ open internal_without_edges(left.as_ptr(), left_data);
        //@ open_points_to(&(*left.as_ptr()).data);
        //@ close exists(left);
        //@ close exists(pair(before, after_copy));
        left_node.relink_range/*@::<'a,K,V,'short>@*/(old_left_len + 1..new_left_len + 1);
        //@ close_points_to(&(*left.as_ptr()).data);
        //@ close internal_without_edges(left.as_ptr(), left_data);
        //@ assert (*left.as_ptr()).edges[..CAPACITY + 1] |-> ?merged_slots;
        //@ append_assoc(before, initialized_edges(right_children), after_copy);
        //@ let active = append(initialized_edges(left_children), initialized_edges(right_children));
        //@ initialized_edge_count(left_children);
        //@ initialized_edge_count(right_children);
        //@ take_twice(left_slots, old_left_len + 1, new_left_len + 1);
        //@ take_append_l(new_left_len + 1, active, drop(new_left_len + 1, left_slots));
        //@ take_length(active);
        //@ join_linked_headers(left_children, right_children, left, 0);
        //@ initialized_edges_append(left_children, right_children);
        //@ close balancing_edges(left, append(left_children, right_children), merged_slots);
    }
}
// END_MERGE_CHILD_EDGES

// BEGIN_RELEASE_BALANCING_NODE
unsafe fn release_balancing_node<'alloc, T, A: std::alloc::Allocator>(
    node: NonNull<T>,
    alloc: &'alloc A,
)
/*@
req thread_token(?t) &*& Allocator::<&'alloc A>(t, alloc, ?id) &*&
    [_]frac_borrow('alloc, ref_initialized_(alloc)) &*& [?shared]lifetime_token('alloc) &*&
    std::alloc::alloc_block_in(id, node.as_ptr() as *u8, std::alloc::Layout::new::<T>()) &*&
    *node.as_ptr() |-> _ &*&
    close_points_to_at_lft_token(1, id.lft, node.as_ptr(), ?alloc_fraction) &*&
    close_lifetime_trade_token(alloc_fraction, id.lft, ?q, ?k);
@*/
//@ ens thread_token(t) &*& Allocator::<&'alloc A>(t, alloc, id) &*& [q]lifetime_token(k) &*& [shared]lifetime_token('alloc);
//@ on_unwind_ens thread_token(t) &*& Allocator::<&'alloc A>(t, alloc, id) &*& [q]lifetime_token(k) &*& [shared]lifetime_token('alloc);
{
    let ptr = node.as_ptr();
    //@ points_to__limits(ptr);
    let bytes = unsafe { NonNull::new_unchecked(ptr as *mut u8) };
    //@ to_u8s_(ptr);
    //@ close_points_to_at_lft_token_to_close_u8s_at_lft_token(ptr);
    //@ close_array_at_lft_(ptr as *u8);
    //@ lifetime_token_trade_back(alloc_fraction, id.lft);
    unsafe { alloc.deallocate/*@::<A, 'alloc>@*/(bytes, std::alloc::Layout::new::<T>()) }
}
// END_RELEASE_BALANCING_NODE

// BEGIN_MERGE_FIELD
unsafe fn merge_keys<'a, 'short, K, V>(
    parent_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
    left_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    right_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    parent_idx: usize,
    old_parent_len: usize,
    old_left_len: usize,
    right_len: usize,
    new_left_len: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*&
    *parent_node |-> ?pn &*& *left_node |-> ?ln &*& *right_node |-> ?rn &*&
    leaf_without_keys(pn.node.as_ptr(), ?p_parent, ?p_idx, ?p_len, ?p_vals) &*&
    leaf_without_keys(ln.node.as_ptr(), ?l_parent, ?l_idx, ?l_len, ?l_vals) &*&
    leaf_without_keys(rn.node.as_ptr(), ?r_parent, ?r_idx, ?r_len, ?r_vals) &*&
    (*pn.node.as_ptr()).keys[..CAPACITY] |-> ?p &*&
    (*ln.node.as_ptr()).keys[..CAPACITY] |-> ?l &*&
    (*rn.node.as_ptr()).keys[..CAPACITY] |-> ?r &*&
    0 <= parent_idx &*& parent_idx < old_parent_len &*& old_parent_len <= CAPACITY &*&
    0 <= old_left_len &*& 0 <= right_len &*& new_left_len == old_left_len + 1 + right_len &*& new_left_len <= CAPACITY &*&
    slot_owners(t, take(old_parent_len, p)) &*& slot_owners(t, take(old_left_len, l)) &*& slot_owners(t, take(right_len, r));
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*&
    *parent_node |-> pn &*& *left_node |-> ln &*& *right_node |-> rn &*&
    leaf_without_keys(pn.node.as_ptr(), p_parent, p_idx, p_len, p_vals) &*&
    leaf_without_keys(ln.node.as_ptr(), l_parent, l_idx, l_len, l_vals) &*&
    leaf_without_keys(rn.node.as_ptr(), r_parent, r_idx, r_len, r_vals) &*&
    (*pn.node.as_ptr()).keys[..CAPACITY] |-> ?p_after &*&
    (*ln.node.as_ptr()).keys[..CAPACITY] |-> ?l_after &*&
    (*rn.node.as_ptr()).keys[..CAPACITY] |-> r &*&
    take(old_parent_len - 1, p_after) ==
        append(take(parent_idx, take(old_parent_len, p)), drop(parent_idx + 1, take(old_parent_len, p))) &*&
    take(new_left_len, l_after) == append(take(old_left_len, l), cons(nth(parent_idx, p), take(right_len, r))) &*&
    drop(old_parent_len, p_after) == drop(old_parent_len, p) &*&
    drop(new_left_len, l_after) == drop(new_left_len, l) &*&
    slot_owners(t, take(old_parent_len - 1, p_after)) &*& slot_owners(t, take(new_left_len, l_after));
@*/
//@ on_unwind_ens false;
{
    //@ let parent = pn.node.as_ptr();
    //@ let left = ln.node.as_ptr();
    //@ let right = rn.node.as_ptr();
    //@ let old_parent = take(old_parent_len, p);
    //@ let old_left = take(old_left_len, l);
    //@ let incoming = take(right_len, r);
    //@ length_take(old_parent_len, p);
    //@ length_take(old_left_len, l);
    //@ length_take(right_len, r);
    //@ nth_take_range(p, old_parent_len, parent_idx);
    //@ split_slot_owners(t, old_parent, parent_idx);
    //@ drop_n_plus_one(parent_idx, old_parent);
    //@ open slot_owners(t, drop(parent_idx, old_parent));
    unsafe {
        let entry = slice_remove(
            parent_node.key_area_prefix_mut/*@::<'a,K,V,marker::Internal,'short>@*/(..old_parent_len), parent_idx,
        );
        //@ assert keys_range_loan(parent, ?active, 0, old_parent_len, p_parent, p_idx, p_len, p_vals, _, _);
        //@ assert move_slice(active as *MaybeUninit<K>, old_parent_len, ?active_after);
        //@ end_keys_range(parent, active);
        //@ let surviving = append(take(parent_idx, old_parent), drop(parent_idx + 1, old_parent));
        //@ join_slot_owners(t, take(parent_idx, old_parent), drop(parent_idx + 1, old_parent));
        //@ length_take(parent_idx, old_parent);
        //@ length_drop(parent_idx + 1, old_parent);
        //@ append_assoc(take(parent_idx, old_parent), drop(parent_idx + 1, old_parent), drop(old_parent_len - 1, old_parent));
        //@ take_append_l(old_parent_len - 1, surviving, drop(old_parent_len - 1, old_parent));
        //@ take_length(surviving);
        //@ length_append(surviving, drop(old_parent_len - 1, old_parent));
        //@ length_drop(old_parent_len - 1, old_parent);
        //@ take_append_l(old_parent_len - 1, active_after, drop(old_parent_len, p));
        //@ drop_append(old_parent_len, active_after, drop(old_parent_len, p));

        left_node.key_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(old_left_len).write(entry);
        //@ assert keys_slot_loan(left, ?slot, old_left_len, l_parent, l_idx, l_len, l_vals, _, _);
        //@ end_keys_slot(left, slot);
        //@ assert (*left).keys[..CAPACITY] |-> ?left_with_entry;
        //@ let with_entry = append(old_left, [MaybeUninit::new(entry)]);
        //@ append_assoc(old_left, [MaybeUninit::new(entry)], drop(old_left_len + 1, l));
        //@ take_append_l(old_left_len + 1, with_entry, drop(old_left_len + 1, l));
        //@ take_length(with_entry);

        move_to_slice(
            right_node.key_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..right_len),
            left_node.key_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(old_left_len + 1..new_left_len),
        );
        //@ assert keys_range_loan(right, ?source, 0, right_len, r_parent, r_idx, r_len, r_vals, _, _);
        //@ assert keys_range_loan(left, ?destination, old_left_len + 1, new_left_len, l_parent, l_idx, l_len, l_vals, _, _);
        //@ end_keys_range(right, source);
        //@ append_take_drop_n(r, right_len);
        //@ end_keys_range(left, destination);
        //@ close slot_owners::<K>(t, cons(MaybeUninit::new(entry), incoming));
        //@ join_slot_owners(t, old_left, cons(MaybeUninit::new(entry), incoming));
        //@ let merged = append(old_left, cons(MaybeUninit::new(entry), incoming));
        //@ append_assoc(with_entry, incoming, drop(new_left_len, left_with_entry));
        //@ append_assoc(old_left, [MaybeUninit::new(entry)], incoming);
        //@ take_append_l(new_left_len, merged, drop(new_left_len, left_with_entry));
        //@ take_length(merged);
        //@ length_append(with_entry, incoming);
        //@ drop_append(new_left_len, merged, drop(new_left_len, left_with_entry));
        //@ drop_append(new_left_len, with_entry, drop(old_left_len + 1, l));
        //@ drop_twice(right_len, old_left_len + 1, l);
    }
}

unsafe fn merge_vals<'a, 'short, K, V>(
    parent_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
    left_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    right_node: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    parent_idx: usize,
    old_parent_len: usize,
    old_left_len: usize,
    right_len: usize,
    new_left_len: usize,
)
/*@
req thread_token(?t) &*& type_interp::<V>() &*&
    *parent_node |-> ?pn &*& *left_node |-> ?ln &*& *right_node |-> ?rn &*&
    leaf_without_vals(pn.node.as_ptr(), ?p_parent, ?p_idx, ?p_len, ?p_keys) &*&
    leaf_without_vals(ln.node.as_ptr(), ?l_parent, ?l_idx, ?l_len, ?l_keys) &*&
    leaf_without_vals(rn.node.as_ptr(), ?r_parent, ?r_idx, ?r_len, ?r_keys) &*&
    (*pn.node.as_ptr()).vals[..CAPACITY] |-> ?p &*&
    (*ln.node.as_ptr()).vals[..CAPACITY] |-> ?l &*&
    (*rn.node.as_ptr()).vals[..CAPACITY] |-> ?r &*&
    0 <= parent_idx &*& parent_idx < old_parent_len &*& old_parent_len <= CAPACITY &*&
    0 <= old_left_len &*& 0 <= right_len &*& new_left_len == old_left_len + 1 + right_len &*& new_left_len <= CAPACITY &*&
    slot_owners(t, take(old_parent_len, p)) &*& slot_owners(t, take(old_left_len, l)) &*& slot_owners(t, take(right_len, r));
@*/
/*@
ens thread_token(t) &*& type_interp::<V>() &*&
    *parent_node |-> pn &*& *left_node |-> ln &*& *right_node |-> rn &*&
    leaf_without_vals(pn.node.as_ptr(), p_parent, p_idx, p_len, p_keys) &*&
    leaf_without_vals(ln.node.as_ptr(), l_parent, l_idx, l_len, l_keys) &*&
    leaf_without_vals(rn.node.as_ptr(), r_parent, r_idx, r_len, r_keys) &*&
    (*pn.node.as_ptr()).vals[..CAPACITY] |-> ?p_after &*&
    (*ln.node.as_ptr()).vals[..CAPACITY] |-> ?l_after &*&
    (*rn.node.as_ptr()).vals[..CAPACITY] |-> r &*&
    take(old_parent_len - 1, p_after) ==
        append(take(parent_idx, take(old_parent_len, p)), drop(parent_idx + 1, take(old_parent_len, p))) &*&
    take(new_left_len, l_after) == append(take(old_left_len, l), cons(nth(parent_idx, p), take(right_len, r))) &*&
    drop(old_parent_len, p_after) == drop(old_parent_len, p) &*&
    drop(new_left_len, l_after) == drop(new_left_len, l) &*&
    slot_owners(t, take(old_parent_len - 1, p_after)) &*& slot_owners(t, take(new_left_len, l_after));
@*/
//@ on_unwind_ens false;
{
    //@ let parent = pn.node.as_ptr();
    //@ let left = ln.node.as_ptr();
    //@ let right = rn.node.as_ptr();
    //@ let old_parent = take(old_parent_len, p);
    //@ let old_left = take(old_left_len, l);
    //@ let incoming = take(right_len, r);
    //@ length_take(old_parent_len, p);
    //@ length_take(old_left_len, l);
    //@ length_take(right_len, r);
    //@ nth_take_range(p, old_parent_len, parent_idx);
    //@ split_slot_owners(t, old_parent, parent_idx);
    //@ drop_n_plus_one(parent_idx, old_parent);
    //@ open slot_owners(t, drop(parent_idx, old_parent));
    unsafe {
        let entry = slice_remove(
            parent_node.val_area_prefix_mut/*@::<'a,K,V,marker::Internal,'short>@*/(..old_parent_len), parent_idx,
        );
        //@ assert vals_range_loan(parent, ?active, 0, old_parent_len, p_parent, p_idx, p_len, p_keys, _, _);
        //@ assert move_slice(active as *MaybeUninit<V>, old_parent_len, ?active_after);
        //@ end_vals_range(parent, active);
        //@ let surviving = append(take(parent_idx, old_parent), drop(parent_idx + 1, old_parent));
        //@ join_slot_owners(t, take(parent_idx, old_parent), drop(parent_idx + 1, old_parent));
        //@ length_take(parent_idx, old_parent);
        //@ length_drop(parent_idx + 1, old_parent);
        //@ append_assoc(take(parent_idx, old_parent), drop(parent_idx + 1, old_parent), drop(old_parent_len - 1, old_parent));
        //@ take_append_l(old_parent_len - 1, surviving, drop(old_parent_len - 1, old_parent));
        //@ take_length(surviving);
        //@ length_append(surviving, drop(old_parent_len - 1, old_parent));
        //@ length_drop(old_parent_len - 1, old_parent);
        //@ take_append_l(old_parent_len - 1, active_after, drop(old_parent_len, p));
        //@ drop_append(old_parent_len, active_after, drop(old_parent_len, p));

        left_node.val_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(old_left_len).write(entry);
        //@ assert vals_slot_loan(left, ?slot, old_left_len, l_parent, l_idx, l_len, l_keys, _, _);
        //@ end_vals_slot(left, slot);
        //@ assert (*left).vals[..CAPACITY] |-> ?left_with_entry;
        //@ let with_entry = append(old_left, [MaybeUninit::new(entry)]);
        //@ append_assoc(old_left, [MaybeUninit::new(entry)], drop(old_left_len + 1, l));
        //@ take_append_l(old_left_len + 1, with_entry, drop(old_left_len + 1, l));
        //@ take_length(with_entry);

        move_to_slice(
            right_node.val_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..right_len),
            left_node.val_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(old_left_len + 1..new_left_len),
        );
        //@ assert vals_range_loan(right, ?source, 0, right_len, r_parent, r_idx, r_len, r_keys, _, _);
        //@ assert vals_range_loan(left, ?destination, old_left_len + 1, new_left_len, l_parent, l_idx, l_len, l_keys, _, _);
        //@ end_vals_range(right, source);
        //@ append_take_drop_n(r, right_len);
        //@ end_vals_range(left, destination);
        //@ close slot_owners::<V>(t, cons(MaybeUninit::new(entry), incoming));
        //@ join_slot_owners(t, old_left, cons(MaybeUninit::new(entry), incoming));
        //@ let merged = append(old_left, cons(MaybeUninit::new(entry), incoming));
        //@ append_assoc(with_entry, incoming, drop(new_left_len, left_with_entry));
        //@ append_assoc(old_left, [MaybeUninit::new(entry)], incoming);
        //@ take_append_l(new_left_len, merged, drop(new_left_len, left_with_entry));
        //@ take_length(merged);
        //@ length_append(with_entry, incoming);
        //@ drop_append(new_left_len, merged, drop(new_left_len, left_with_entry));
        //@ drop_append(new_left_len, with_entry, drop(old_left_len + 1, l));
        //@ drop_twice(right_len, old_left_len + 1, l);
    }
}
// END_MERGE_FIELD

/*@
pred owned_leaf_slots<K,V>(
    thread: thread_id_t, node: *LeafNode<K,V>, len: usize
) =
    leaf_slots(node, len, ?keys, ?vals) &*&
    slot_owners(thread, take(len, keys)) &*& slot_owners(thread, take(len, vals));

pred balancing_child_edges<K,V>(
    child: NonNull<LeafNode<K,V>>, height: usize, len: usize,
    descendants: list<BoxedNode<K,V>>
) =
    if height == 0 {
        descendants == []
    } else {
        balancing_edges(NonNull::new(child.as_ptr() as *InternalNode<K,V>), descendants, _) &*&
        length(descendants) == len + 1
    };

pred balancing_child_allocation<K,V>(
    child: NonNull<LeafNode<K,V>>, height: usize, id: std::alloc::alloc_id_t, k: lifetime_t, q: real
) =
    if height == 0 {
        allocated_leaf(child.as_ptr(), id, k, q)
    } else {
        allocated_internal(child.as_ptr() as *InternalNode<K,V>, id, k, q)
    };

pred leaf_header<K,V>(node: *LeafNode<K,V>;
    ancestor: Option<NonNull<InternalNode<K,V>>>, ancestor_idx: MaybeUninit<u16>) =
    struct_LeafNode_padding(node) &*& (*node).parent |-> ancestor &*& (*node).parent_idx |-> ancestor_idx;

pred balancing_child_padding<K,V>(child: NonNull<LeafNode<K,V>>, height: usize) =
    if height > 0 { struct_InternalNode_padding(child.as_ptr() as *InternalNode<K,V>) } else { true };

pred merge_inputs<K,V>(
    t: thread_id_t, parent: NonNull<InternalNode<K,V>>, left: NonNull<LeafNode<K,V>>, right: NonNull<LeafNode<K,V>>,
    parent_height: usize, parent_idx: usize, id: std::alloc::alloc_id_t, k: lifetime_t, released: real,
    parent_len: usize, left_len: usize, right_len: usize,
    parent_children: list<BoxedNode<K,V>>, left_children: list<BoxedNode<K,V>>, right_children: list<BoxedNode<K,V>>
) =
    0 < parent_height &*& parent_height <= usize::MAX &*&
    struct_InternalNode_padding(parent.as_ptr()) &*& leaf_header(&(*parent.as_ptr()).data, _, _) &*&
    owned_leaf_slots(t, &(*parent.as_ptr()).data, parent_len) &*&
    balancing_edges(parent, parent_children, _) &*& length(parent_children) == parent_len + 1 &*&
    0 <= parent_idx &*& parent_idx < parent_len &*&
    nth(parent_idx, parent_children) == left &*& nth(parent_idx + 1, parent_children) == right &*&
    left.as_ptr() as usize != 0 &*& right.as_ptr() as usize != 0 &*&
    struct_LeafNode_padding(left.as_ptr()) &*&
    balancing_child_padding(left, parent_height - 1) &*&
    owned_leaf_slots(t, left.as_ptr(), left_len) &*& owned_leaf_slots(t, right.as_ptr(), right_len) &*&
    balancing_child_edges(left, parent_height - 1, left_len, left_children) &*&
    balancing_child_edges(right, parent_height - 1, right_len, right_children) &*&
    balancing_child_allocation(right, parent_height - 1, id, k, released);

pred merged_nodes<K,V>(
    t: thread_id_t, parent: NonNull<InternalNode<K,V>>, left: NonNull<LeafNode<K,V>>,
    child_height: usize, parent_len: usize, left_len: usize,
    parent_children: list<BoxedNode<K,V>>, left_children: list<BoxedNode<K,V>>
) =
    struct_InternalNode_padding(parent.as_ptr()) &*& leaf_header(&(*parent.as_ptr()).data, _, _) &*&
    owned_leaf_slots(t, &(*parent.as_ptr()).data, parent_len) &*&
    balancing_edges(parent, parent_children, _) &*&
    struct_LeafNode_padding(left.as_ptr()) &*&
    balancing_child_padding(left, child_height) &*&
    owned_leaf_slots(t, left.as_ptr(), left_len) &*&
    balancing_child_edges(left, child_height, left_len, left_children);
@*/

// BEGIN_MERGE_NODES
unsafe fn merge_nodes<'alloc, K, V, A: std::alloc::Allocator>(
    parent: NonNull<InternalNode<K, V>>,
    left: NonNull<LeafNode<K, V>>,
    right: NonNull<LeafNode<K, V>>,
    parent_height: usize,
    parent_idx: usize,
    alloc: &'alloc A,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, ?id) &*& [_]frac_borrow('alloc, ref_initialized_(alloc)) &*&
    [?shared]lifetime_token('alloc) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?released) &*&
    merge_inputs(t, parent, left, right, parent_height, parent_idx, id, k, released,
        ?parent_len, ?left_len, ?right_len_0, ?parent_children, ?left_children, ?right_children) &*&
    left_len + 1 + right_len_0 <= CAPACITY;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, id) &*& [shared]lifetime_token('alloc) &*& [released]lifetime_token(k) &*&
    merged_nodes(t, parent, left, parent_height - 1, parent_len - 1, left_len + 1 + right_len_0,
        append(take(parent_idx + 1, parent_children), drop(parent_idx + 2, parent_children)),
        append(left_children, right_children));
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, id) &*& [shared]lifetime_token('alloc) &*& [released]lifetime_token(k) &*&
    merged_nodes(t, parent, left, parent_height - 1, parent_len - 1, left_len + 1 + right_len_0,
        append(take(parent_idx + 1, parent_children), drop(parent_idx + 2, parent_children)),
        append(left_children, right_children));
@*/
{
    //@ open exists(k);
    //@ open exists(released);
    //@ open merge_inputs(t, parent, left, right, parent_height, parent_idx, id, k, released, parent_len, left_len, right_len_0, parent_children, left_children, right_children);
    //@ open owned_leaf_slots(t, &(*parent.as_ptr()).data, parent_len);
    //@ open leaf_slots(&(*parent.as_ptr()).data, parent_len, ?p_keys, ?p_vals);
    let parent_ptr = unsafe { &raw mut (*parent.as_ptr()).data };
    let old_parent_len = unsafe { (*parent_ptr).len } as usize;
    //@ open owned_leaf_slots(t, left.as_ptr(), left_len);
    //@ open leaf_slots(left.as_ptr(), left_len, ?l_keys, ?l_vals);
    let left_ptr = left.as_ptr();
    let old_left_len = unsafe { (*left_ptr).len } as usize;
    //@ open owned_leaf_slots(t, right.as_ptr(), right_len_0);
    //@ open leaf_slots(right.as_ptr(), right_len_0, ?r_keys, ?r_vals);
    let right_ptr = right.as_ptr();
    let right_len = unsafe { (*right_ptr).len } as usize;
    let new_left_len = old_left_len + 1 + right_len;
    assert!(new_left_len <= CAPACITY);

// BEGIN_MERGE_MODEL_PAYLOAD
    let mut parent_node = NodeRef::<marker::Mut<'_>, K, V, marker::Internal> {
        height: parent_height, node: parent.cast(), _marker: PhantomData,
    };
    //@ std::ptr::NonNull_new_as_ptr(parent_node.node);
    let mut left_node = NodeRef::<marker::Mut<'_>, K, V, marker::LeafOrInternal> {
        height: parent_height - 1, node: left, _marker: PhantomData,
    };
    let mut right_node = NodeRef::<marker::Mut<'_>, K, V, marker::LeafOrInternal> {
        height: parent_height - 1, node: right, _marker: PhantomData,
    };
    //@ open balancing_edges(parent, parent_children, ?parent_slots);
    //@ split_linked_headers(parent_children, parent, 0, parent_idx);
    //@ drop_n_plus_one(parent_idx, parent_children);
    //@ open linked_headers(drop(parent_idx, parent_children), parent, parent_idx);
    //@ drop_n_plus_one(parent_idx + 1, parent_children);
    //@ open linked_headers(drop(parent_idx + 1, parent_children), parent, parent_idx + 1);
    //@ close leaf_without_len(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16), l_keys, l_vals);
    unsafe {
        let slot = left_node.len_mut();
        *slot = new_left_len as u16;
        //@ end_len_loan(left_ptr, slot);
        //@ open leaf_without_len(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16), l_keys, l_vals);
        //@ open balancing_child_allocation(right, parent_height - 1, id, k, released);
        /*@
        if parent_height > 1 {
            let internal = right_ptr as *InternalNode<K,V>;
            open allocated_internal(internal, id, k, released);
            assert &(*internal).data == right_ptr;
        } else {
            open allocated_leaf(right_ptr, id, k, released);
        }
        @*/
        //@ close leaf_header(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16));
        //@ close leaf_header(right_ptr, Option::Some(parent), MaybeUninit::new((parent_idx + 1) as u16));
        //@ close leaf_without_keys(parent_ptr, _, _, old_parent_len as u16, _);
        //@ close leaf_without_keys(left_ptr, _, _, new_left_len as u16, _);
        //@ close leaf_without_keys(right_ptr, _, _, right_len as u16, _);
        merge_keys(
            &mut parent_node, &mut left_node, &mut right_node,
            parent_idx, old_parent_len, old_left_len, right_len, new_left_len,
        );
        //@ open leaf_without_keys(parent_ptr, _, _, old_parent_len as u16, _);
        //@ open leaf_without_keys(left_ptr, _, _, new_left_len as u16, _);
        //@ open leaf_without_keys(right_ptr, _, _, right_len as u16, _);
        //@ close leaf_without_vals(parent_ptr, _, _, old_parent_len as u16, _);
        //@ close leaf_without_vals(left_ptr, _, _, new_left_len as u16, _);
        //@ close leaf_without_vals(right_ptr, _, _, right_len as u16, _);
        merge_vals(
            &mut parent_node, &mut left_node, &mut right_node,
            parent_idx, old_parent_len, old_left_len, right_len, new_left_len,
        );
        //@ open leaf_without_vals(parent_ptr, _, _, old_parent_len as u16, _);
        //@ open leaf_without_vals(left_ptr, _, _, new_left_len as u16, _);
        //@ open leaf_without_vals(right_ptr, _, _, right_len as u16, _);
        //@ open leaf_header(right_ptr, _, _);
        //@ open leaf_header(left_ptr, _, _);
        /*@
        if parent_height > 1 {
            close allocated_internal(right_ptr as *InternalNode<K,V>, id, k, released);
        } else {
            close allocated_leaf(right_ptr, id, k, released);
        }
        @*/
        //@ close balancing_child_allocation(right, parent_height - 1, id, k, released);
        //@ close linked_headers(drop(parent_idx + 1, parent_children), parent, parent_idx + 1);
        //@ close linked_headers(drop(parent_idx, parent_children), parent, parent_idx);
        //@ length_take(parent_idx, parent_children);
        //@ join_linked_headers(take(parent_idx, parent_children), drop(parent_idx, parent_children), parent, 0);
        //@ append_take_drop_n(parent_children, parent_idx);
        //@ close balancing_edges(parent, parent_children, parent_slots);
// END_MERGE_MODEL_PAYLOAD
// BEGIN_MERGE_MODEL_PARENT_CALL
        //@ open leaf_header(parent_ptr, ?ancestor, ?ancestor_idx);
        //@ close leaf_without_len(parent_ptr, ancestor, ancestor_idx, _, _);
        //@ close exists(parent);
        remove_merged_edge(&mut parent_node, parent_idx, old_parent_len);
        //@ open leaf_without_len(parent_ptr, ancestor, ancestor_idx, _, _);
        //@ close leaf_header(parent_ptr, ancestor, ancestor_idx);
// END_MERGE_MODEL_PARENT_CALL
        //@ close leaf_slots(parent_ptr, old_parent_len - 1, _, _);
        //@ close owned_leaf_slots(t, parent_ptr, old_parent_len - 1);
        //@ close leaf_slots(left_ptr, new_left_len, _, _);
        //@ close owned_leaf_slots(t, left_ptr, new_left_len);
        //@ open balancing_child_edges(left, parent_height - 1, left_len, left_children);
        //@ open balancing_child_edges(right, parent_height - 1, right_len, right_children);
        //@ open balancing_child_allocation(right, parent_height - 1, id, k, released);
        //@ let surviving = append(take(parent_idx + 1, parent_children), drop(parent_idx + 2, parent_children));
        if parent_height > 1 {
// BEGIN_MERGE_MODEL_INTERNAL
            let mut left_node = left_node.reborrow_mut().cast_to_internal_unchecked();
            let mut right_node = right_node.cast_to_internal_unchecked();
            let left_internal: NonNull<InternalNode<K, V>> = left_node.node.cast();
            let right_internal: NonNull<InternalNode<K, V>> = right_node.node.cast();
// END_MERGE_MODEL_CASTS
            //@ std::ptr::NonNull_new_as_ptr(left_internal);
            //@ std::ptr::NonNull_new_as_ptr(right_internal);
            //@ assert &(*left_internal.as_ptr()).data == left_ptr;
            //@ assert &(*right_internal.as_ptr()).data == right_ptr;
            //@ open owned_leaf_slots(t, left_ptr, new_left_len);
            //@ open leaf_slots(left_ptr, new_left_len, _, _);
            //@ open balancing_child_padding(left, parent_height - 1);
            //@ open allocated_internal(right_internal.as_ptr(), id, k, released);
            //@ open balancing_edges(parent, surviving, ?parent_edges);
            //@ let before_left = take(parent_idx + 1, parent_children);
            //@ let after_right = drop(parent_idx + 2, parent_children);
            //@ length_take(parent_idx + 1, parent_children);
            //@ length_drop(parent_idx + 2, parent_children);
            //@ length_append(before_left, after_right);
            //@ take_append_l(parent_idx + 1, before_left, after_right);
            //@ take_length(before_left);
            //@ nth_take_range(surviving, parent_idx + 1, parent_idx);
            //@ nth_take_range(parent_children, parent_idx + 1, parent_idx);
            //@ split_linked_headers(surviving, parent, 0, parent_idx);
            //@ drop_n_plus_one(parent_idx, surviving);
            //@ open linked_headers(drop(parent_idx, surviving), parent, parent_idx);
            //@ close_points_to(left_ptr);
            //@ close_points_to(right_ptr);
            //@ close internal_without_edges(left_internal.as_ptr(), ?left_data);
            //@ close internal_without_edges(right_internal.as_ptr(), ?right_data);
            //@ close exists(pair(left_internal, right_internal));
            append_merged_edges(&mut left_node, &mut right_node, old_left_len, right_len, new_left_len);
            //@ open internal_without_edges(left_internal.as_ptr(), left_data);
            //@ open_points_to(left_ptr);
            //@ close linked_headers(drop(parent_idx, surviving), parent, parent_idx);
            //@ length_take(parent_idx, surviving);
            //@ join_linked_headers(take(parent_idx, surviving), drop(parent_idx, surviving), parent, 0);
            //@ append_take_drop_n(surviving, parent_idx);
            //@ close balancing_edges(parent, surviving, parent_edges);
            //@ close leaf_slots(left_ptr, new_left_len, _, _);
            //@ close owned_leaf_slots(t, left_ptr, new_left_len);
            //@ close balancing_child_edges(left, parent_height - 1, new_left_len, append(left_children, right_children));
            //@ close balancing_child_padding(left, parent_height - 1);
            //@ close merged_nodes(t, parent, left, parent_height - 1, old_parent_len - 1, new_left_len, surviving, append(left_children, right_children));
            //@ open internal_without_edges(right_internal.as_ptr(), right_data);
            //@ open_points_to(right_ptr);
            //@ close_points_to(right_internal.as_ptr(), 1);
            release_balancing_node/*@::<InternalNode<K,V>,A,'alloc>@*/(right_internal, alloc);
// END_MERGE_MODEL_INTERNAL
        } else {
            //@ close balancing_child_edges(left, parent_height - 1, new_left_len, append(left_children, right_children));
            //@ close merged_nodes(t, parent, left, parent_height - 1, old_parent_len - 1, new_left_len, surviving, append(left_children, right_children));
            //@ open allocated_leaf(right_ptr, id, k, released);
            //@ close_points_to(right_ptr, 1);
            release_balancing_node/*@::<LeafNode<K,V>,A,'alloc>@*/(right, alloc);
        }
    }
}
// END_MERGE_NODES

struct BalancingContext<'a, K, V> {
    parent: Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV>,
    left_child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    right_child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
}

/*@
inductive MergeLengths<K,V> = MergeLengths(
    usize, usize, usize, list<BoxedNode<K,V>>, list<BoxedNode<K,V>>, list<BoxedNode<K,V>>
);

pred context_merge_inputs<'tree,K,V>(
    t: thread_id_t, context: BalancingContext<'tree,K,V>, id: std::alloc::alloc_id_t,
    k: lifetime_t, released: real, shape: MergeLengths<K,V>
) =
    context.parent.node.node.as_ptr() as usize != 0 &*& context.left_child.node.as_ptr() as usize != 0 &*&
    context.left_child.height == context.parent.node.height - 1 &*&
    context.right_child.height == context.parent.node.height - 1 &*&
    match shape {
        MergeLengths(p, l, r, pc, lc, rc) =>
            merge_inputs(t, NonNull::new(context.parent.node.node.as_ptr() as *InternalNode<K,V>),
                context.left_child.node, context.right_child.node, context.parent.node.height, context.parent.idx,
                id, k, released, p, l, r, pc, lc, rc)
    };

pred context_can_merge<'tree,K,V>(
    t: thread_id_t, context: BalancingContext<'tree,K,V>, id: std::alloc::alloc_id_t,
    k: lifetime_t, released: real, shape: MergeLengths<K,V>
) =
    context_merge_inputs(t, context, id, k, released, shape) &*&
    match shape { MergeLengths(p, l, r, pc, lc, rc) => l + 1 + r <= CAPACITY };

@*/

// BEGIN_MERGE_LEFT_CHILD
unsafe fn merge_left_child<'tree, 'alloc, K, V, A: std::alloc::Allocator>(
    context: BalancingContext<'tree, K, V>,
    alloc: &'alloc A,
) -> NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, ?id) &*& [_]frac_borrow('alloc, ref_initialized_(alloc)) &*&
    [?shared]lifetime_token('alloc) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?released) &*&
    context_can_merge(t, context, id, k, released, ?shape);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, id) &*& [shared]lifetime_token('alloc) &*& [released]lifetime_token(k) &*&
    result == context.left_child &*&
    match shape {
        MergeLengths(p, l, r, pc, lc, rc) =>
            merged_nodes(t, NonNull::new(context.parent.node.node.as_ptr() as *InternalNode<K,V>),
                context.left_child.node, context.parent.node.height - 1, p - 1, l + 1 + r,
                append(take(context.parent.idx + 1, pc), drop(context.parent.idx + 2, pc)), append(lc, rc))
    };
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, id) &*& [shared]lifetime_token('alloc) &*& [released]lifetime_token(k) &*&
    match shape {
        MergeLengths(p, l, r, pc, lc, rc) =>
            merged_nodes(t, NonNull::new(context.parent.node.node.as_ptr() as *InternalNode<K,V>),
                context.left_child.node, context.parent.node.height - 1, p - 1, l + 1 + r,
                append(take(context.parent.idx + 1, pc), drop(context.parent.idx + 2, pc)), append(lc, rc))
    };
@*/
{
    //@ open context_can_merge(t, context, id, k, released, shape);
    //@ open context_merge_inputs(t, context, id, k, released, shape);
    let Handle { node: parent_node, idx: parent_idx, .. } = context.parent;
    let left_node = context.left_child;
    let right_node = context.right_child;
    let parent = unsafe { NonNull::new_unchecked(parent_node.node.as_ptr() as *mut InternalNode<K, V>) };
    //@ std::ptr::NonNull_new_as_ptr(parent);
    unsafe {
        merge_nodes/*@::<K,V,A,'alloc>@*/(parent, left_node.node, right_node.node, parent_node.height, parent_idx, alloc);
    }
    left_node
}
// END_MERGE_LEFT_CHILD

// BEGIN_MERGE_CALLBACK
unsafe fn call_merge__VeriFast_wrapper<P, C, F: FnOnce(P, C) -> R, R>(finish: F, parent: P, child: C) -> R
//@ req thread_token(?t) &*& <F>.own(t, finish) &*& <P>.own(t, parent) &*& <C>.own(t, child);
//@ ens thread_token(t) &*& <R>.own(t, result);
//@ on_unwind_ens thread_token(t);
{
    //@ close_tuple_2_own(t, std_tuple_2_::<P,C> { 0: parent, 1: child });
    finish(parent, child)
}
// END_MERGE_CALLBACK

// BEGIN_DO_MERGE
unsafe fn do_merge<'tree, 'alloc, K, V, F, R, A>(
    context: BalancingContext<'tree, K, V>,
    finish: F,
    alloc: &'alloc A,
) -> R
where
    F: FnOnce(
        NodeRef<marker::Mut<'tree>, K, V, marker::Internal>,
        NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>,
    ) -> R,
    A: std::alloc::Allocator,
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <F>.own(t, finish) &*&
    Allocator::<&'alloc A>(t, alloc, ?id) &*& [_]frac_borrow('alloc, ref_initialized_(alloc)) &*&
    [?shared]lifetime_token('alloc) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?released) &*&
    context_can_merge(t, context, id, k, released, ?shape);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <R>.own(t, result) &*&
    Allocator::<&'alloc A>(t, alloc, id) &*& [shared]lifetime_token('alloc) &*& [released]lifetime_token(k) &*&
    match shape {
        MergeLengths(p, l, r, pc, lc, rc) =>
            merged_nodes(t, NonNull::new(context.parent.node.node.as_ptr() as *InternalNode<K,V>),
                context.left_child.node, context.parent.node.height - 1, p - 1, l + 1 + r,
                append(take(context.parent.idx + 1, pc), drop(context.parent.idx + 2, pc)), append(lc, rc))
    };
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, id) &*& [shared]lifetime_token('alloc) &*& [released]lifetime_token(k) &*&
    match shape {
        MergeLengths(p, l, r, pc, lc, rc) =>
            merged_nodes(t, NonNull::new(context.parent.node.node.as_ptr() as *InternalNode<K,V>),
                context.left_child.node, context.parent.node.height - 1, p - 1, l + 1 + r,
                append(take(context.parent.idx + 1, pc), drop(context.parent.idx + 2, pc)), append(lc, rc))
    };
@*/
{
    //@ open context_can_merge(t, context, id, k, released, shape);
    //@ open context_merge_inputs(t, context, id, k, released, shape);
    let Handle { node: parent_node, idx: parent_idx, .. } = context.parent;
    let left_node = context.left_child;
    let right_node = context.right_child;
    let parent = unsafe { NonNull::new_unchecked(parent_node.node.as_ptr() as *mut InternalNode<K, V>) };
    //@ std::ptr::NonNull_new_as_ptr(parent);
    unsafe {
        merge_nodes/*@::<K,V,A,'alloc>@*/(parent, left_node.node, right_node.node, parent_node.height, parent_idx, alloc);
    }
    //@ close NodeRef_own::<marker::Mut<'tree>,K,V,marker::Internal>(t,parent_node);
    //@ close NodeRef_own::<marker::Mut<'tree>,K,V,marker::LeafOrInternal>(t,left_node);
    unsafe { call_merge__VeriFast_wrapper(finish, parent_node, left_node) }
}
// END_DO_MERGE

// BEGIN_FINISH_MERGE_TRACKING
unsafe fn finish_merge_tracking__VeriFast_wrapper<'tree, K, V>(
    child: NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>,
    old_left_len: usize,
    track_edge_idx: LeftOrRight<usize>,
) -> Handle<NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>, marker::Edge>
/*@
req (*child.node.as_ptr()).len |-> ?len &*& 0 <= old_left_len &*& old_left_len < len &*&
    match track_edge_idx {
        LeftOrRight::Left(idx) => 0 <= idx &*& idx <= old_left_len,
        LeftOrRight::Right(idx) => 0 <= idx &*& idx <= len - old_left_len - 1
    };
@*/
/*@
ens (*child.node.as_ptr()).len |-> len &*& result.node == child &*&
    match track_edge_idx {
        LeftOrRight::Left(idx) => result.idx == idx,
        LeftOrRight::Right(idx) => result.idx == old_left_len + 1 + idx
    };
@*/
//@ on_unwind_ens false;
{
    let new_idx = match track_edge_idx {
        LeftOrRight::Left(idx) => idx,
        LeftOrRight::Right(idx) => old_left_len + 1 + idx,
    };
    unsafe {
        Handle::<NodeRef<marker::Mut<'_>, K, V, marker::LeafOrInternal>, marker::Edge>::new_edge(child, new_idx)
    }
}
// END_FINISH_MERGE_TRACKING

// BEGIN_MERGE_TRACKED_EDGE
unsafe fn merge_tracking_child_edge<'tree, 'alloc, K, V, A: std::alloc::Allocator>(
    parent: NonNull<InternalNode<K, V>>,
    left: NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>,
    right: NonNull<LeafNode<K, V>>,
    parent_height: usize,
    parent_idx: usize,
    track_edge_idx: LeftOrRight<usize>,
    alloc: &'alloc A,
) -> Handle<NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>, marker::Edge>
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, ?id) &*& [_]frac_borrow('alloc, ref_initialized_(alloc)) &*&
    [?shared]lifetime_token('alloc) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?released) &*&
    merge_inputs(t, parent, left.node, right, parent_height, parent_idx, id, k, released,
        ?parent_len, ?left_len, ?right_len_0, ?parent_children, ?left_children, ?right_children) &*&
    left_len + 1 + right_len_0 <= CAPACITY &*&
    left.height == parent_height - 1 &*&
    match track_edge_idx {
        LeftOrRight::Left(idx) => 0 <= idx &*& idx <= left_len,
        LeftOrRight::Right(idx) => 0 <= idx &*& idx <= right_len_0
    };
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, id) &*& [shared]lifetime_token('alloc) &*& [released]lifetime_token(k) &*&
    merged_nodes(t, parent, left.node, parent_height - 1, parent_len - 1, left_len + 1 + right_len_0,
        append(take(parent_idx + 1, parent_children), drop(parent_idx + 2, parent_children)),
        append(left_children, right_children)) &*& result.node == left &*&
    match track_edge_idx {
        LeftOrRight::Left(idx) => result.idx == idx,
        LeftOrRight::Right(idx) => result.idx == left_len + 1 + idx
    };
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    Allocator::<&'alloc A>(t, alloc, id) &*& [shared]lifetime_token('alloc) &*& [released]lifetime_token(k) &*&
    merged_nodes(t, parent, left.node, parent_height - 1, parent_len - 1, left_len + 1 + right_len_0,
        append(take(parent_idx + 1, parent_children), drop(parent_idx + 2, parent_children)),
        append(left_children, right_children));
@*/
{
    //@ open merge_inputs(t, parent, left.node, right, parent_height, parent_idx, id, k, released, parent_len, left_len, right_len_0, parent_children, left_children, right_children);
    //@ open owned_leaf_slots(t, left.node.as_ptr(), left_len);
    //@ open leaf_slots(left.node.as_ptr(), left_len, ?lk, ?lv);
    let old_left_len = unsafe { (*left.node.as_ptr()).len } as usize;
    //@ close leaf_slots(left.node.as_ptr(), left_len, lk, lv);
    //@ close owned_leaf_slots(t, left.node.as_ptr(), left_len);
    //@ open owned_leaf_slots(t, right.as_ptr(), right_len_0);
    //@ open leaf_slots(right.as_ptr(), right_len_0, ?rk, ?rv);
    let right_len = unsafe { (*right.as_ptr()).len } as usize;
    //@ close leaf_slots(right.as_ptr(), right_len_0, rk, rv);
    //@ close owned_leaf_slots(t, right.as_ptr(), right_len_0);
    //@ close merge_inputs(t, parent, left.node, right, parent_height, parent_idx, id, k, released, parent_len, left_len, right_len_0, parent_children, left_children, right_children);
    assert!(match track_edge_idx {
        LeftOrRight::Left(idx) => idx <= old_left_len,
        LeftOrRight::Right(idx) => idx <= right_len,
    });
    unsafe { merge_nodes/*@::<K,V,A,'alloc>@*/(parent, left.node, right, parent_height, parent_idx, alloc) };
    //@ let pc = append(take(parent_idx + 1, parent_children), drop(parent_idx + 2, parent_children));
    //@ let lc = append(left_children, right_children);
    //@ let new_len = left_len + 1 + right_len_0;
    //@ open merged_nodes(t, parent, left.node, parent_height - 1, parent_len - 1, new_len, pc, lc);
    //@ open owned_leaf_slots(t, left.node.as_ptr(), new_len);
    //@ open leaf_slots(left.node.as_ptr(), new_len, ?keys, ?vals);
    let edge = unsafe {
        finish_merge_tracking__VeriFast_wrapper/*@::<K,V,'tree>@*/(left, old_left_len, track_edge_idx)
    };
    //@ close leaf_slots(left.node.as_ptr(), new_len, keys, vals);
    //@ close owned_leaf_slots(t, left.node.as_ptr(), new_len);
    //@ close merged_nodes(t, parent, left.node, parent_height - 1, parent_len - 1, new_len, pc, lc);
    edge
}
// END_MERGE_TRACKED_EDGE

// Verify the read, separator exchange, and write used by both steal directions.
unsafe fn move_steal_separator<T>(
    parent: *mut MaybeUninit<T>,
    source: *mut MaybeUninit<T>,
    destination: *mut MaybeUninit<T>,
)
/*@
req thread_token(?t) &*& type_interp::<T>() &*&
    move_slice(parent, 1, ?p) &*& head(p).inner() == some(?old) &*& p == [MaybeUninit::new(old)] &*&
    move_slice(source, 1, ?s) &*& head(s).inner() == some(?donated) &*& s == [MaybeUninit::new(donated)] &*&
    move_slice(destination, 1, _) &*& <T>.own(t, old) &*& <T>.own(t, donated);
@*/
/*@
ens thread_token(t) &*& type_interp::<T>() &*&
    move_slice(parent, 1, [MaybeUninit::new(donated)]) &*&
    move_slice(source, 1, [MaybeUninit::new(donated)]) &*&
    move_slice(destination, 1, [MaybeUninit::new(old)]) &*& <T>.own(t, old) &*& <T>.own(t, donated);
@*/
//@ on_unwind_ens false;
{
    //@ open move_slice(source, 1, [MaybeUninit::new(donated)]);
    //@ open array(source, 1, [MaybeUninit::new(donated)]);
    let entry = unsafe { read_promoted(source) };
    //@ close array(source, 1, [MaybeUninit::new(donated)]);
    //@ close move_slice(source, 1, [MaybeUninit::new(donated)]);
    //@ open move_slice(parent, 1, [MaybeUninit::new(old)]);
    //@ open array(parent, 1, [MaybeUninit::new(old)]);
    //@ open_MaybeUninit(parent);
    let saved = unsafe { std::mem::replace(&mut *(parent as *mut T), entry) };
    //@ close_MaybeUninit(parent);
    //@ close array(parent, 1, [MaybeUninit::new(donated)]);
    //@ close move_slice(parent, 1, [MaybeUninit::new(donated)]);
    //@ open move_slice(destination, 1, _);
    //@ open array(destination, 1, _);
    //@ open array(destination + 1, 0, _);
    //@ close array(destination + 1, 0, nil);
    unsafe { (*destination).write(saved) };
    //@ close array(destination, 1, [MaybeUninit::new(old)]);
    //@ close move_slice(destination, 1, [MaybeUninit::new(old)]);
}

unsafe fn steal_left_field<T>(
    parent: *mut MaybeUninit<T>,
    left: *mut MaybeUninit<T>,
    right: *mut MaybeUninit<T>,
    old_left_len: usize,
    old_right_len: usize,
    count: usize,
)
/*@
req thread_token(?t) &*& type_interp::<T>() &*&
    0 < count &*& count <= old_left_len &*& old_left_len <= CAPACITY &*&
    0 <= old_right_len &*& old_right_len + count <= CAPACITY &*&
    move_slice(parent, 1, ?p) &*& move_slice(left, old_left_len, ?l) &*&
    move_slice(right, old_right_len + count, ?r) &*&
    slot_owners(t, p) &*& slot_owners(t, l) &*& slot_owners(t, take(old_right_len, r));
@*/
/*@
ens thread_token(t) &*& type_interp::<T>() &*&
    move_slice(parent, 1, ?new_p) &*& move_slice(left, old_left_len, l) &*&
    move_slice(right, old_right_len + count, ?new_r) &*&
    slot_owners(t, new_p) &*& slot_owners(t, take(old_left_len - count, l)) &*& slot_owners(t, new_r);
@*/
//@ on_unwind_ens false;
{
    let new_left_len = old_left_len - count;
    let new_right_len = old_right_len + count;
    //@ move_slice_length(left, old_left_len);
    //@ move_slice_length(parent, 1);
    //@ move_slice_length(right, new_right_len);
    //@ split_slot_owners(t, l, new_left_len);
    //@ let donated = nth(new_left_len, l);
    //@ let remaining = drop(new_left_len + 1, l);
    //@ drop_n_plus_one(new_left_len, l);
    //@ open slot_owners(t, drop(new_left_len, l));
    //@ split_move_slice(left, old_left_len, new_left_len);
    //@ split_move_slice(left + new_left_len, count, 1);
    //@ drop_twice(1, new_left_len, l);
    //@ drop_n_plus_one(0, p);
    //@ length_drop(1, p);
    //@ empty_list_if_zero(drop(1, p));
    //@ open slot_owners(t, p);
    unsafe {
        slice_shr(move_slice_mut(right, new_right_len), count);
        //@ split_move_slice(right, new_right_len, count);
        //@ length_take(count, r);
        //@ take_append_l(count, take(count, r), take(old_right_len, r));
        //@ take_length(take(count, r));
        //@ drop_append(count, take(count, r), take(old_right_len, r));
        //@ split_move_slice(right, count, count - 1);
        move_to_slice(
            move_slice_mut(left.add(new_left_len + 1), old_left_len - (new_left_len + 1)),
            move_slice_mut(right, count - 1),
        );
        move_steal_separator(parent, left.add(new_left_len), right.add(count - 1));
        //@ join_move_slices(left + new_left_len, 1, count - 1);
        //@ join_move_slices(left, new_left_len, count);
        //@ join_move_slices(right, count - 1, 1);
        //@ join_move_slices(right, count, old_right_len);
        //@ close slot_owners(t, [donated]);
        //@ close slot_owners::<T>(t, nil);
        //@ close slot_owners(t, p);
        //@ join_slot_owners(t, remaining, p);
        //@ join_slot_owners(t, append(remaining, p), take(old_right_len, r));
    }
}

unsafe fn steal_right_field<T>(
    parent: *mut MaybeUninit<T>,
    left: *mut MaybeUninit<T>,
    right: *mut MaybeUninit<T>,
    old_left_len: usize,
    old_right_len: usize,
    count: usize,
)
/*@
req thread_token(?t) &*& type_interp::<T>() &*&
    0 < count &*& count <= old_right_len &*& old_right_len <= CAPACITY &*&
    0 <= old_left_len &*& old_left_len + count <= CAPACITY &*&
    move_slice(parent, 1, ?p) &*& move_slice(left, old_left_len + count, ?l) &*&
    move_slice(right, old_right_len, ?r) &*&
    slot_owners(t, p) &*& slot_owners(t, take(old_left_len, l)) &*& slot_owners(t, r);
@*/
/*@
ens thread_token(t) &*& type_interp::<T>() &*&
    move_slice(parent, 1, ?new_p) &*& move_slice(left, old_left_len + count, ?new_l) &*&
    move_slice(right, old_right_len, ?new_r) &*&
    slot_owners(t, new_p) &*& slot_owners(t, new_l) &*& slot_owners(t, take(old_right_len - count, new_r));
@*/
//@ on_unwind_ens false;
{
    let new_left_len = old_left_len + count;
    //@ move_slice_length(right, old_right_len);
    //@ move_slice_length(parent, 1);
    //@ move_slice_length(left, new_left_len);
    //@ split_slot_owners(t, r, count - 1);
    //@ let donated = nth(count - 1, r);
    //@ drop_n_plus_one(count - 1, r);
    //@ open slot_owners(t, drop(count - 1, r));
    //@ split_move_slice(right, old_right_len, count - 1);
    //@ split_move_slice(right + count - 1, old_right_len - count + 1, 1);
    //@ split_move_slice(left, new_left_len, old_left_len);
    //@ split_move_slice(left + old_left_len, count, 1);
    //@ drop_n_plus_one(0, p);
    //@ length_drop(1, p);
    //@ empty_list_if_zero(drop(1, p));
    //@ open slot_owners(t, p);
    unsafe {
        move_steal_separator(parent, right.add(count - 1), left.add(old_left_len));
        move_to_slice(
            move_slice_mut(right, count - 1),
            move_slice_mut(left.add(old_left_len + 1), new_left_len - (old_left_len + 1)),
        );
        //@ join_move_slices(left + old_left_len, 1, count - 1);
        //@ join_move_slices(left, old_left_len, count);
        //@ join_move_slices(right + count - 1, 1, old_right_len - count);
        //@ join_move_slices(right, count - 1, old_right_len - count + 1);
        //@ append_take_drop_n(drop(count - 1, r), 1);
        //@ append_take_drop_n(r, count - 1);
        slice_shl(move_slice_mut(right, old_right_len), count);
        //@ length_drop(count, r);
        //@ take_append_l(old_right_len - count, drop(count, r), drop(old_right_len - count, r));
        //@ take_length(drop(count, r));
        //@ close slot_owners(t, [donated]);
        //@ close slot_owners::<T>(t, nil);
        //@ close slot_owners(t, p);
        //@ join_slot_owners(t, p, take(count - 1, r));
        //@ join_slot_owners(t, take(old_left_len, l), append(p, take(count - 1, r)));
    }
}

/*@
lem join_child_headers<K,V>(left: list<BoxedNode<K,V>>, right: list<BoxedNode<K,V>>)
    req child_headers(left) &*& child_headers(right);
    ens child_headers(append(left, right));
{
    open child_headers(left);
    match left {
        nil => {}
        cons(child, rest) => {
            join_child_headers(rest, right);
            close child_headers(append(left, right));
        }
    }
}
@*/

unsafe fn steal_left_edges<K, V>(
    left: NonNull<InternalNode<K, V>>,
    right: NonNull<InternalNode<K, V>>,
    old_left_len: usize,
    old_right_len: usize,
    count: usize,
    height: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    balancing_edges(left, ?left_children, ?left_slots) &*& balancing_edges(right, ?right_children, ?right_slots) &*&
    length(left_children) == old_left_len + 1 &*& length(right_children) == old_right_len + 1 &*&
    (*right.as_ptr()).data.len |-> ((old_right_len + count) as u16) &*& 0 < height &*&
    0 < count &*& count <= old_left_len &*& 0 <= old_right_len &*& old_right_len + count <= CAPACITY;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    (*right.as_ptr()).data.len |-> ((old_right_len + count) as u16) &*&
    balancing_edges(left, take(old_left_len - count + 1, left_children), left_slots) &*&
    balancing_edges(right, append(drop(old_left_len - count + 1, left_children), right_children), _);
@*/
//@ on_unwind_ens false;
{
    let new_left_len = old_left_len - count;
    let new_right_len = old_right_len + count;
    //@ open balancing_edges(left, left_children, left_slots);
    //@ open balancing_edges(right, right_children, right_slots);
    let left_base = unsafe { (&raw mut (*left.as_ptr()).edges) as *mut MaybeUninit<BoxedNode<K, V>> };
    let right_base = unsafe { (&raw mut (*right.as_ptr()).edges) as *mut MaybeUninit<BoxedNode<K, V>> };
    //@ own_move_array(left_base, CAPACITY + 1);
    //@ own_move_array(right_base, CAPACITY + 1);
    //@ split_move_slice(left_base, CAPACITY + 1, old_left_len + 1);
    //@ split_move_slice(left_base, old_left_len + 1, new_left_len + 1);
    //@ split_move_slice(right_base, CAPACITY + 1, new_right_len + 1);
    //@ let kept = take(new_left_len + 1, left_children);
    //@ let moved = drop(new_left_len + 1, left_children);
    //@ initialized_edge_split(left_children, new_left_len + 1);
    //@ initialized_edge_count(kept);
    //@ initialized_edge_count(moved);
    //@ initialized_edge_count(right_children);
    //@ length_take(new_left_len + 1, left_children);
    //@ length_drop(new_left_len + 1, left_children);
    //@ split_linked_headers(left_children, left, 0, new_left_len + 1);
    //@ forget_link_indices(moved, left, new_left_len + 1);
    //@ forget_link_indices(right_children, right, 0);
    //@ join_child_headers(moved, right_children);
    //@ let after = append(moved, right_children);
    //@ initialized_edges_append(moved, right_children);
    //@ let right_before = take(new_right_len + 1, right_slots);
    unsafe {
        slice_shr(move_slice_mut(right_base, new_right_len + 1), count);
        //@ take_twice(right_slots, old_right_len + 1, new_right_len + 1);
        //@ split_move_slice(right_base, new_right_len + 1, count);
        //@ length_take(count, right_before);
        //@ take_append_l(count, take(count, right_before), initialized_edges(right_children));
        //@ take_length(take(count, right_before));
        //@ drop_append(count, take(count, right_before), initialized_edges(right_children));
        move_to_slice(
            move_slice_mut(left_base.add(new_left_len + 1), old_left_len + 1 - (new_left_len + 1)),
            move_slice_mut(right_base, count),
        );
        //@ join_move_slices(right_base, count, old_right_len + 1);
        //@ join_move_slices(right_base, new_right_len + 1, CAPACITY - new_right_len);
        //@ open move_slice(right_base, CAPACITY + 1, ?full);
        let mut right_node = NodeRef::<marker::Mut<'_>, K, V, marker::Internal> {
            height, node: right.cast(), _marker: PhantomData,
        };
        //@ std::ptr::NonNull_new_as_ptr(right_node.node);
        //@ close exists(right);
        //@ close exists(pair(nil::<MaybeUninit<BoxedNode<K,V>>>, drop(new_right_len + 1, right_slots)));
        //@ initialized_edge_count(after);
        right_node.relink_range(0..new_right_len + 1);
    }
    //@ let old_left = take(old_left_len + 1, left_slots);
    //@ append_take_drop_n(old_left, new_left_len + 1);
    //@ append_take_drop_n(left_slots, old_left_len + 1);
    //@ join_move_slices(left_base, new_left_len + 1, count);
    //@ join_move_slices(left_base, old_left_len + 1, CAPACITY - old_left_len);
    //@ open move_slice(left_base, CAPACITY + 1, left_slots);
    //@ take_twice(left_slots, new_left_len + 1, old_left_len + 1);
    //@ close balancing_edges(left, kept, left_slots);
    //@ assert (*right.as_ptr()).edges[..CAPACITY + 1] |-> ?packed;
    //@ initialized_edge_count(after);
    //@ take_append_l(new_right_len + 1, initialized_edges(after), drop(new_right_len + 1, right_slots));
    //@ take_length(initialized_edges(after));
    //@ close balancing_edges(right, after, packed);
}

unsafe fn steal_right_edges<K, V>(
    left: NonNull<InternalNode<K, V>>,
    right: NonNull<InternalNode<K, V>>,
    old_left_len: usize,
    old_right_len: usize,
    count: usize,
    height: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    balancing_edges(left, ?left_children, ?left_slots) &*& balancing_edges(right, ?right_children, ?right_slots) &*&
    length(left_children) == old_left_len + 1 &*& length(right_children) == old_right_len + 1 &*&
    (*left.as_ptr()).data.len |-> ((old_left_len + count) as u16) &*&
    (*right.as_ptr()).data.len |-> ((old_right_len - count) as u16) &*& 0 < height &*&
    0 < count &*& count <= old_right_len &*& 0 <= old_left_len &*& old_left_len + count <= CAPACITY;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    (*left.as_ptr()).data.len |-> ((old_left_len + count) as u16) &*&
    (*right.as_ptr()).data.len |-> ((old_right_len - count) as u16) &*&
    balancing_edges(left, append(left_children, take(count, right_children)), _) &*&
    balancing_edges(right, drop(count, right_children), _);
@*/
//@ on_unwind_ens false;
{
    let new_left_len = old_left_len + count;
    let new_right_len = old_right_len - count;
    //@ open balancing_edges(left, left_children, left_slots);
    //@ open balancing_edges(right, right_children, right_slots);
    let left_base = unsafe { (&raw mut (*left.as_ptr()).edges) as *mut MaybeUninit<BoxedNode<K, V>> };
    let right_base = unsafe { (&raw mut (*right.as_ptr()).edges) as *mut MaybeUninit<BoxedNode<K, V>> };
    //@ own_move_array(left_base, CAPACITY + 1);
    //@ own_move_array(right_base, CAPACITY + 1);
    //@ split_move_slice(left_base, CAPACITY + 1, new_left_len + 1);
    //@ split_move_slice(left_base, new_left_len + 1, old_left_len + 1);
    //@ split_move_slice(right_base, CAPACITY + 1, old_right_len + 1);
    //@ split_move_slice(right_base, old_right_len + 1, count);
    //@ let moved = take(count, right_children);
    //@ let kept = drop(count, right_children);
    //@ let right_before = initialized_edges(right_children);
    //@ let inactive = drop(new_right_len + 1, right_before);
    //@ initialized_edge_split(right_children, count);
    //@ initialized_edge_count(left_children);
    //@ initialized_edge_count(moved);
    //@ initialized_edge_count(kept);
    //@ length_take(count, right_children);
    //@ length_drop(count, right_children);
    //@ split_linked_headers(right_children, right, 0, count);
    //@ forget_link_indices(kept, right, count);
    //@ forget_link_indices(moved, right, 0);
    unsafe {
        move_to_slice(
            move_slice_mut(right_base, count),
            move_slice_mut(left_base.add(old_left_len + 1), new_left_len + 1 - (old_left_len + 1)),
        );
        //@ join_move_slices(right_base, count, new_right_len + 1);
        //@ append_take_drop_n(right_before, count);
        slice_shl(move_slice_mut(right_base, old_right_len + 1), count);
        //@ split_move_slice(right_base, old_right_len + 1, new_right_len + 1);
        //@ take_append_l(new_right_len + 1, initialized_edges(kept), inactive);
        //@ take_length(initialized_edges(kept));
        //@ join_move_slices(left_base, old_left_len + 1, count);
        //@ join_move_slices(left_base, new_left_len + 1, CAPACITY - new_left_len);
        //@ open move_slice(left_base, CAPACITY + 1, _);
        //@ join_move_slices(right_base, new_right_len + 1, count);
        //@ join_move_slices(right_base, old_right_len + 1, CAPACITY - old_right_len);
        //@ open move_slice(right_base, CAPACITY + 1, _);
        let mut left_node = NodeRef::<marker::Mut<'_>, K, V, marker::Internal> {
            height, node: left.cast(), _marker: PhantomData,
        };
        let mut right_node = NodeRef::<marker::Mut<'_>, K, V, marker::Internal> {
            height, node: right.cast(), _marker: PhantomData,
        };
        //@ std::ptr::NonNull_new_as_ptr(left_node.node);
        //@ std::ptr::NonNull_new_as_ptr(right_node.node);
        //@ take_twice(left_slots, old_left_len + 1, new_left_len + 1);
        //@ append_assoc(initialized_edges(left_children), initialized_edges(moved), drop(new_left_len + 1, left_slots));
        //@ close exists(left);
        //@ close exists(pair(initialized_edges(left_children), drop(new_left_len + 1, left_slots)));
        left_node.relink_range(old_left_len + 1..new_left_len + 1);
        //@ close exists(right);
        //@ close exists(pair(nil::<MaybeUninit<BoxedNode<K,V>>>, append(inactive, drop(old_right_len + 1, right_slots))));
        //@ append_assoc(initialized_edges(kept), inactive, drop(old_right_len + 1, right_slots));
        right_node.relink_range(0..new_right_len + 1);
    }
    //@ let after_left = append(left_children, moved);
    //@ initialized_edges_append(left_children, moved);
    //@ initialized_edge_count(after_left);
    //@ take_twice(left_slots, old_left_len + 1, new_left_len + 1);
    //@ join_linked_headers(left_children, moved, left, 0);
    //@ assert (*left.as_ptr()).edges[..CAPACITY + 1] |-> ?packed_left;
    //@ take_append_l(new_left_len + 1, initialized_edges(after_left), drop(new_left_len + 1, left_slots));
    //@ take_length(initialized_edges(after_left));
    //@ close balancing_edges(left, after_left, packed_left);
    //@ assert (*right.as_ptr()).edges[..CAPACITY + 1] |-> ?packed_right;
    //@ take_append_l(new_right_len + 1, initialized_edges(kept), inactive);
    //@ take_append_l(new_right_len + 1, append(initialized_edges(kept), inactive), drop(old_right_len + 1, right_slots));
    //@ close balancing_edges(right, kept, packed_right);
}

/*@
fix steal_len(receives: bool, old_len: usize, count: usize) -> usize {
    if receives { old_len + count } else { old_len - count }
}
@*/

unsafe fn steal_field<T>(
    parent: *mut MaybeUninit<T>,
    left: *mut MaybeUninit<T>,
    right: *mut MaybeUninit<T>,
    parent_idx: usize,
    old_left_len: usize,
    old_right_len: usize,
    count: usize,
    from_left: bool,
)
/*@
req thread_token(?t) &*& type_interp::<T>() &*& exists::<usize>(?parent_len) &*&
    0 <= parent_idx &*& parent_idx < parent_len &*& parent_len <= CAPACITY &*&
    0 <= old_left_len &*& old_left_len <= CAPACITY &*& 0 <= old_right_len &*& old_right_len <= CAPACITY &*&
    0 < count &*&
    (if from_left { count <= old_left_len && old_right_len + count <= CAPACITY }
     else { count <= old_right_len && old_left_len + count <= CAPACITY }) == true &*&
    parent[..CAPACITY] |-> ?p &*& left[..CAPACITY] |-> ?l &*& right[..CAPACITY] |-> ?r &*&
    slot_owners(t, take(parent_len, p)) &*& slot_owners(t, take(old_left_len, l)) &*& slot_owners(t, take(old_right_len, r));
@*/
/*@
ens thread_token(t) &*& type_interp::<T>() &*&
    parent[..CAPACITY] |-> ?new_p &*& left[..CAPACITY] |-> ?new_l &*& right[..CAPACITY] |-> ?new_r &*&
    slot_owners(t, take(parent_len, new_p)) &*&
    slot_owners(t, take(steal_len(!from_left, old_left_len, count), new_l)) &*&
    slot_owners(t, take(steal_len(from_left, old_right_len, count), new_r));
@*/
//@ on_unwind_ens false;
{
    //@ open exists(parent_len);
    //@ let left_view = if from_left { old_left_len } else { old_left_len + count };
    //@ let right_view = if from_left { old_right_len + count } else { old_right_len };
    //@ own_move_array(parent, CAPACITY);
    //@ own_move_array(left, CAPACITY);
    //@ own_move_array(right, CAPACITY);
    //@ split_move_slice(parent, CAPACITY, parent_idx);
    //@ split_move_slice(parent + parent_idx, CAPACITY - parent_idx, 1);
    //@ split_move_slice(left, CAPACITY, left_view);
    //@ split_move_slice(right, CAPACITY, right_view);
    //@ take_twice(l, old_left_len, left_view);
    //@ take_twice(r, old_right_len, right_view);
    //@ let active = take(parent_len, p);
    //@ length_take(parent_len, p);
    //@ split_slot_owners(t, active, parent_idx);
    //@ length_drop(parent_idx, active);
    //@ split_slot_owners(t, drop(parent_idx, active), 1);
    //@ take_twice(p, parent_idx, parent_len);
    //@ take_after_drop(p, parent_idx, parent_len - parent_idx);
    //@ take_twice(drop(parent_idx, p), 1, parent_len - parent_idx);
    let separator = unsafe { parent.add(parent_idx) };
    if from_left {
        unsafe { steal_left_field(separator, left, right, old_left_len, old_right_len, count) };
    } else {
        unsafe { steal_right_field(separator, left, right, old_left_len, old_right_len, count) };
    }
    //@ assert move_slice(separator, 1, ?new_separator);
    //@ assert move_slice(left, left_view, ?moved_left);
    //@ assert move_slice(right, right_view, ?moved_right);
    //@ move_slice_length(separator, 1);
    //@ move_slice_length(left, left_view);
    //@ move_slice_length(right, right_view);
    //@ join_move_slices(parent, parent_idx, 1);
    //@ join_move_slices(parent, parent_idx + 1, CAPACITY - parent_idx - 1);
    //@ join_move_slices(left, left_view, CAPACITY - left_view);
    //@ join_move_slices(right, right_view, CAPACITY - right_view);
    //@ take_append_l(steal_len(!from_left, old_left_len, count), moved_left, drop(left_view, l));
    //@ take_append_l(steal_len(from_left, old_right_len, count), moved_right, drop(right_view, r));
    //@ drop_twice(1, parent_idx, p);
    //@ drop_twice(1, parent_idx, active);
    //@ take_after_drop(p, parent_idx + 1, parent_len - parent_idx - 1);
    //@ length_take(parent_idx, p);
    //@ take_append(parent_len, append(take(parent_idx, p), new_separator), drop(parent_idx + 1, p));
    //@ join_slot_owners(t, take(parent_idx, p), new_separator);
    //@ join_slot_owners(t, append(take(parent_idx, p), new_separator), drop(parent_idx + 1, active));
    //@ open move_slice(parent, CAPACITY, _);
    //@ open move_slice(left, CAPACITY, _);
    //@ open move_slice(right, CAPACITY, _);
}

unsafe fn bulk_steal_nodes<K, V>(
    parent: NonNull<LeafNode<K, V>>,
    left: NonNull<LeafNode<K, V>>,
    right: NonNull<LeafNode<K, V>>,
    child_height: usize,
    parent_idx: usize,
    count: usize,
    from_left: bool,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    owned_leaf_slots(t, parent.as_ptr(), ?parent_len) &*& 0 <= parent_idx &*& parent_idx < parent_len &*&
    owned_leaf_slots(t, left.as_ptr(), ?left_len) &*& owned_leaf_slots(t, right.as_ptr(), ?right_len) &*&
    left.as_ptr() as usize != 0 &*& right.as_ptr() as usize != 0 &*& 0 <= child_height &*& child_height <= usize::MAX &*&
    balancing_child_edges(left, child_height, left_len, ?lc) &*& balancing_child_edges(right, child_height, right_len, ?rc) &*&
    0 < count &*&
    (if from_left { count <= left_len && right_len + count <= CAPACITY }
     else { count <= right_len && left_len + count <= CAPACITY }) == true;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    owned_leaf_slots(t, parent.as_ptr(), parent_len) &*&
    owned_leaf_slots(t, left.as_ptr(), steal_len(!from_left, left_len, count)) &*&
    owned_leaf_slots(t, right.as_ptr(), steal_len(from_left, right_len, count)) &*&
    balancing_child_edges(left, child_height, steal_len(!from_left, left_len, count),
        if from_left { take(left_len - count + 1, lc) } else { append(lc, take(count, rc)) }) &*&
    balancing_child_edges(right, child_height, steal_len(from_left, right_len, count),
        if from_left { append(drop(left_len - count + 1, lc), rc) } else { drop(count, rc) });
@*/
//@ on_unwind_ens false;
{
    assert!(count > 0);
    //@ open owned_leaf_slots(t, left.as_ptr(), left_len);
    //@ open leaf_slots(left.as_ptr(), left_len, ?lk, ?lv);
    let left_ptr = left.as_ptr();
    let old_left_len = unsafe { (*left_ptr).len } as usize;
    //@ open owned_leaf_slots(t, right.as_ptr(), right_len);
    //@ open leaf_slots(right.as_ptr(), right_len, ?rk, ?rv);
    let right_ptr = right.as_ptr();
    let old_right_len = unsafe { (*right_ptr).len } as usize;
    let new_left_len;
    let new_right_len;
    if from_left {
        assert!(old_right_len + count <= CAPACITY);
        assert!(old_left_len >= count);
        new_left_len = old_left_len - count;
        new_right_len = old_right_len + count;
    } else {
        assert!(old_left_len + count <= CAPACITY);
        assert!(old_right_len >= count);
        new_left_len = old_left_len + count;
        new_right_len = old_right_len - count;
    }
    //@ open owned_leaf_slots(t, parent.as_ptr(), parent_len);
    //@ open leaf_slots(parent.as_ptr(), parent_len, ?pk, ?pv);
    let parent_ptr = parent.as_ptr();
    unsafe {
        (*left_ptr).len = new_left_len as u16;
        (*right_ptr).len = new_right_len as u16;
        //@ close exists(parent_len);
        steal_field(
            (&raw mut (*parent_ptr).keys) as *mut MaybeUninit<K>,
            (&raw mut (*left_ptr).keys) as *mut MaybeUninit<K>,
            (&raw mut (*right_ptr).keys) as *mut MaybeUninit<K>,
            parent_idx, old_left_len, old_right_len, count, from_left,
        );
        //@ close exists(parent_len);
        steal_field(
            (&raw mut (*parent_ptr).vals) as *mut MaybeUninit<V>,
            (&raw mut (*left_ptr).vals) as *mut MaybeUninit<V>,
            (&raw mut (*right_ptr).vals) as *mut MaybeUninit<V>,
            parent_idx, old_left_len, old_right_len, count, from_left,
        );
        //@ close leaf_slots(parent_ptr, parent_len, _, _);
        //@ close owned_leaf_slots(t, parent_ptr, parent_len);
        //@ close leaf_slots(left_ptr, new_left_len, _, _);
        //@ close owned_leaf_slots(t, left_ptr, new_left_len);
        //@ close leaf_slots(right_ptr, new_right_len, _, _);
        //@ close owned_leaf_slots(t, right_ptr, new_right_len);
        //@ open balancing_child_edges(left, child_height, left_len, lc);
        //@ open balancing_child_edges(right, child_height, right_len, rc);
        let left_node = NodeRef::<marker::Mut<'_>, K, V, marker::LeafOrInternal> {
            height: child_height, node: left, _marker: PhantomData,
        };
        let right_node = NodeRef::<marker::Mut<'_>, K, V, marker::LeafOrInternal> {
            height: child_height, node: right, _marker: PhantomData,
        };
        match (left_node.force(), right_node.force()) {
            (ForceResult::Internal(left), ForceResult::Internal(right)) => {
                let left_internal = left.node.cast::<InternalNode<K, V>>();
                let right_internal = right.node.cast::<InternalNode<K, V>>();
                //@ std::ptr::NonNull_new_as_ptr(left_internal);
                //@ std::ptr::NonNull_new_as_ptr(right_internal);
                //@ assert &(*right_internal.as_ptr()).data == right_ptr;
                //@ open owned_leaf_slots(t, right_ptr, new_right_len);
                //@ open leaf_slots(right_ptr, new_right_len, _, _);
                if from_left {
                    steal_left_edges(left_internal, right_internal, old_left_len, old_right_len, count, child_height);
                    //@ length_take(new_left_len + 1, lc);
                    //@ length_drop(new_left_len + 1, lc);
                } else {
                    //@ assert &(*left_internal.as_ptr()).data == left_ptr;
                    //@ open owned_leaf_slots(t, left_ptr, new_left_len);
                    //@ open leaf_slots(left_ptr, new_left_len, _, _);
                    steal_right_edges(left_internal, right_internal, old_left_len, old_right_len, count, child_height);
                    //@ close leaf_slots(left_ptr, new_left_len, _, _);
                    //@ close owned_leaf_slots(t, left_ptr, new_left_len);
                    //@ length_take(count, rc);
                    //@ length_drop(count, rc);
                }
                //@ close leaf_slots(right_ptr, new_right_len, _, _);
                //@ close owned_leaf_slots(t, right_ptr, new_right_len);
            }
            (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
            _ => unreachable!(),
        }
        //@ close balancing_child_edges(left, child_height, new_left_len, if from_left { take(new_left_len + 1, lc) } else { append(lc, take(count, rc)) });
        //@ close balancing_child_edges(right, child_height, new_right_len, if from_left { append(drop(new_left_len + 1, lc), rc) } else { drop(count, rc) });
    }
}

// BEGIN_FINISH_STEAL
unsafe fn finish_steal_left__VeriFast_wrapper<'tree, K, V>(
    child: NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>,
    tracked_idx: usize,
) -> Handle<NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>, marker::Edge>
/*@
req (*child.node.as_ptr()).len |-> ?len &*& 0 <= tracked_idx &*&
    1 + tracked_idx <= len;
@*/
/*@
ens (*child.node.as_ptr()).len |-> len &*& result.node == child &*&
    result.idx == 1 + tracked_idx;
@*/
//@ on_unwind_ens false;
{
    unsafe {
        Handle::<NodeRef<marker::Mut<'_>, K, V, marker::LeafOrInternal>, marker::Edge>::new_edge(child, 1 + tracked_idx)
    }
}

unsafe fn finish_steal_right__VeriFast_wrapper<'tree, K, V>(
    child: NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>,
    tracked_idx: usize,
) -> Handle<NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>, marker::Edge>
/*@
req (*child.node.as_ptr()).len |-> ?len &*& 0 <= tracked_idx &*&
    tracked_idx <= len;
@*/
/*@
ens (*child.node.as_ptr()).len |-> len &*& result.node == child &*&
    result.idx == tracked_idx;
@*/
//@ on_unwind_ens false;
{
    unsafe {
        Handle::<NodeRef<marker::Mut<'_>, K, V, marker::LeafOrInternal>, marker::Edge>::new_edge(child, tracked_idx)
    }
}
// END_FINISH_STEAL

unsafe fn steal_one<'tree, K, V>(
    parent: NonNull<LeafNode<K, V>>,
    left: NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>,
    right: NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>,
    parent_idx: usize,
    tracked_idx: usize,
    from_left: bool,
) -> Handle<NodeRef<marker::Mut<'tree>, K, V, marker::LeafOrInternal>, marker::Edge>
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    owned_leaf_slots(t, parent.as_ptr(), ?parent_len) &*& 0 <= parent_idx &*& parent_idx < parent_len &*&
    owned_leaf_slots(t, left.node.as_ptr(), ?left_len) &*& owned_leaf_slots(t, right.node.as_ptr(), ?right_len) &*&
    left.node.as_ptr() as usize != 0 &*& right.node.as_ptr() as usize != 0 &*&
    left.height == right.height &*& 0 <= left.height &*& left.height <= usize::MAX &*&
    balancing_child_edges(left.node, left.height, left_len, ?lc) &*& balancing_child_edges(right.node, right.height, right_len, ?rc) &*&
    0 <= tracked_idx &*&
    (if from_left { 1 <= left_len && right_len < CAPACITY && tracked_idx <= right_len }
     else { 1 <= right_len && left_len < CAPACITY && tracked_idx <= left_len }) == true;
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    owned_leaf_slots(t, parent.as_ptr(), parent_len) &*&
    owned_leaf_slots(t, left.node.as_ptr(), steal_len(!from_left, left_len, 1)) &*&
    owned_leaf_slots(t, right.node.as_ptr(), steal_len(from_left, right_len, 1)) &*&
    balancing_child_edges(left.node, left.height, steal_len(!from_left, left_len, 1),
        if from_left { take(left_len, lc) } else { append(lc, take(1, rc)) }) &*&
    balancing_child_edges(right.node, right.height, steal_len(from_left, right_len, 1),
        if from_left { append(drop(left_len, lc), rc) } else { drop(1, rc) }) &*&
    result.node == (if from_left { right } else { left }) &*&
    result.idx == tracked_idx + (if from_left { 1 } else { 0 });
@*/
//@ on_unwind_ens false;
{
    unsafe { bulk_steal_nodes(parent, left.node, right.node, left.height, parent_idx, 1, from_left) };
    let child = if from_left { right } else { left };
    //@ let child_len = if from_left { right_len + 1 } else { left_len + 1 };
    //@ open owned_leaf_slots(t, child.node.as_ptr(), child_len);
    //@ open leaf_slots(child.node.as_ptr(), child_len, ?keys, ?vals);
    let edge = if from_left {
        unsafe { finish_steal_left__VeriFast_wrapper/*@::<K,V,'tree>@*/(child, tracked_idx) }
    } else {
        unsafe { finish_steal_right__VeriFast_wrapper/*@::<K,V,'tree>@*/(child, tracked_idx) }
    };
    //@ close leaf_slots(child.node.as_ptr(), child_len, keys, vals);
    //@ close owned_leaf_slots(t, child.node.as_ptr(), child_len);
    edge
}


enum ForceResult<Leaf, Internal> {
    Leaf(Leaf),
    Internal(Internal),
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
    unsafe fn force(
        self,
    ) -> ForceResult<
        NodeRef<BorrowType, K, V, marker::Leaf>,
        NodeRef<BorrowType, K, V, marker::Internal>,
    >
    //@ req 0 <= self.height;
    /*@
    ens match result {
        ForceResult::Leaf(leaf) => self.height == 0 &*& leaf.height == self.height &*& leaf.node == self.node,
        ForceResult::Internal(internal) => self.height > 0 &*& internal.height == self.height &*& internal.node == self.node
    };
    @*/
    //@ on_unwind_ens false;
    {
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


// BEGIN_DROP_VALUE
unsafe fn drop_slot_production<'slot, T>(slot: &'slot mut MaybeUninit<T>)
/*@
req thread_token(?t) &*& type_interp::<T>() &*& *slot |-> ?bits &*&
    bits.inner() == some(?value) &*& <T>.own(t, value);
@*/
//@ ens thread_token(t) &*& type_interp::<T>() &*& *(slot as *T) |-> _;
//@ on_unwind_ens thread_token(t) &*& type_interp::<T>() &*& *(slot as *T) |-> _;
{
    let ptr = slot.as_mut_ptr();
    //@ open_MaybeUninit(slot);
    unsafe { std::ptr::drop_in_place(ptr) }
}

struct Dropper<'a, T>(&'a mut MaybeUninit<T>);

impl<'a, T> Dropper<'a, T> {
    unsafe fn drop_value_guard(&mut self)
    /*@
    req thread_token(?t) &*& type_interp::<T>() &*& *self |-> ?guard &*&
        *guard.0 |-> ?bits &*& bits.inner() == some(?value) &*& <T>.own(t, value);
    @*/
    //@ ens thread_token(t) &*& type_interp::<T>() &*& *self |-> guard &*& *(guard.0 as *T) |-> _;
    //@ on_unwind_ens thread_token(t) &*& type_interp::<T>() &*& *self |-> guard &*& *(guard.0 as *T) |-> _;
    {
        //@ open_points_to(self);
        let slot = &mut *self.0;
        //@ close_points_to(self);
        unsafe { drop_slot_production(slot) };
    }
}
// END_DROP_VALUE

// The storage remains reusable after either exit from the destructor.
unsafe fn drop_initialized_slot<T>(slot: *mut MaybeUninit<T>)
/*@
req thread_token(?t) &*& type_interp::<T>() &*& *slot |-> ?bits &*&
    bits.inner() == some(?value) &*& <T>.own(t, value);
@*/
//@ ens thread_token(t) &*& type_interp::<T>() &*& *(slot as *T) |-> _;
//@ on_unwind_ens thread_token(t) &*& type_interp::<T>() &*& *(slot as *T) |-> _;
{
    unsafe { drop_slot_production(&mut *slot) }
}

unsafe fn drop_guarded_value<T>(slot: *mut MaybeUninit<T>)
/*@
req thread_token(?t) &*& type_interp::<T>() &*& *slot |-> ?bits &*&
    bits.inner() == some(?value) &*& <T>.own(t, value);
@*/
//@ ens thread_token(t) &*& type_interp::<T>() &*& *(slot as *T) |-> _;
//@ on_unwind_ens thread_token(t) &*& type_interp::<T>() &*& *(slot as *T) |-> _;
{
    let mut guard = Dropper(unsafe { &mut *slot });
    //@ close_points_to(&mut guard);
    unsafe { guard.drop_value_guard() };
    //@ open_points_to(&mut guard);
}

unsafe fn drop_pair<K, V>(key: *mut MaybeUninit<K>, value: *mut MaybeUninit<V>)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *key |-> ?key_bits &*& key_bits.inner() == some(?k) &*& <K>.own(t, k) &*&
    *value |-> ?value_bits &*& value_bits.inner() == some(?v) &*& <V>.own(t, v);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *(key as *K) |-> _ &*& *(value as *V) |-> _;
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    *(key as *K) |-> _ &*& exists::<bool>(?value_pending) &*&
    if value_pending { *value |-> value_bits &*& <V>.own(t, v) }
    else { *(value as *V) |-> _ };
@*/
{
    //@ close exists::<bool>(true);
    unsafe { drop_initialized_slot(key) };
    //@ open exists::<bool>(true);
    //@ close exists::<bool>(false);
    unsafe { drop_guarded_value(value) };
    //@ open exists::<bool>(false);
}


unsafe fn maybe_uninit_storage_ptr<T>(storage: &mut MaybeUninit<T>) -> *mut T
//@ req true;
//@ ens result == storage as *mut T;
//@ on_unwind_ens false;
{
    storage as *mut _ as *mut T
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Leaf> {
    unsafe fn forget_type(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal>
    //@ req true;
    /*@
    ens result.node == self.node &*& result.height == self.height;
    @*/
    //@ on_unwind_ens false;
    {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<BorrowType, K, V> NodeRef<BorrowType, K, V, marker::Internal> {
    unsafe fn forget_type(self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal>
    //@ req true;
    /*@
    ens result.node == self.node &*& result.height == self.height;
    @*/
    //@ on_unwind_ens false;
    {
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<'a, K, V> SplitResult<'a, K, V, marker::Leaf> {
    unsafe fn forget_node_type(self) -> SplitResult<'a, K, V, marker::LeafOrInternal>
    //@ req true;
    /*@
    ens result.left.node == self.left.node &*& result.left.height == self.left.height &*&
        result.right.node == self.right.node &*& result.right.height == self.right.height &*&
        result.kv == self.kv;
    @*/
    //@ on_unwind_ens false;
    {
        //@ open_points_to(&self);
        let rebuilt = unsafe { SplitResult { left: self.left.forget_type(), kv: self.kv, right: self.right.forget_type() } };
        //@ close_points_to(&self, 1/2);
        rebuilt
    }
}

impl<'a, K, V> SplitResult<'a, K, V, marker::Internal> {
    unsafe fn forget_node_type(self) -> SplitResult<'a, K, V, marker::LeafOrInternal>
    //@ req true;
    /*@
    ens result.left.node == self.left.node &*& result.left.height == self.left.height &*&
        result.right.node == self.right.node &*& result.right.height == self.right.height &*&
        result.kv == self.kv;
    @*/
    //@ on_unwind_ens false;
    {
        //@ open_points_to(&self);
        let rebuilt = unsafe { SplitResult { left: self.left.forget_type(), kv: self.kv, right: self.right.forget_type() } };
        //@ close_points_to(&self, 1/2);
        rebuilt
    }
}

unsafe fn propagate_split_for_root<'tree, 'slot, K: 'tree, V: 'tree, A: AllocatorClone>(
    initial_split: SplitResult<'tree,K,V,marker::LeafOrInternal>,
    inserted: Handle<NodeRef<marker::DormantMut,K,V,marker::Leaf>,marker::KV>,
    alloc: &A,
    root_slot: &'slot mut DormantMutRef<'tree, Option<Root<K,V>>>,
    root_allocator: &'slot mut A,
) -> Handle<NodeRef<marker::Mut<'tree>,K,V,marker::Leaf>,marker::KV>
/*@
req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
    type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    [_]allocator_clone_bound::<A>() &*&
    [_]std::alloc::Allocator_share::<A>(?alloc_lifetime,t,alloc,?alloc_id) &*&
    [_]frac_borrow(alloc_lifetime, ref_initialized_(alloc)) &*& [?qa]lifetime_token(alloc_lifetime) &*&
    exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k,alloc_id.lft) == true &*&
    exists::<(NonNull<LeafNode<K,V>>, NonNull<LeafNode<K,V>>)>(?leaf_nodes) &*&
    ancestors(initial_split.left.node.as_ptr(),?path,?root) &*& route_frames(t,path) &*&
    (*root).parent_idx |-> ?root_index &*& detached_child(initial_split.right.node.as_ptr()) &*&
    *root_allocator |-> ?root_alloc &*& Allocator::<A>(t,root_alloc,alloc_id) &*&
    *root_slot |-> ?sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(?old_root) &*& old_root.node.as_ptr() == root &*& old_root.height == length(path) &*&
    initial_split.left.node == leaf_nodes.0 &*& initial_split.right.node == leaf_nodes.1 &*&
    initial_split.left.height == 0 &*& initial_split.right.height == 0 &*& length(path) < usize::MAX &*&
    <K>.own(t,initial_split.kv.0) &*& <V>.own(t,initial_split.kv.1) &*&
    inserted.node.height == 0 &*& insertion_leaves(leaf_nodes.0,inserted.node.node,inserted.idx,Option::Some(leaf_nodes.1),alloc_id,k) &*&
    dormant_pair(inserted.node.node.as_ptr(),inserted.idx,?key_cell,?value_cell) &*&
    key_cell.inner() == some(?leaf_key) &*& value_cell.inner() == some(?leaf_value) &*&
    <K>.own(t,leaf_key) &*& <V>.own(t,leaf_value);
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    [qa]lifetime_token(alloc_lifetime) &*& [?remaining_fraction]lifetime_token(k) &*&
    *root_allocator |-> ?after &*& Allocator::<A>(t,after,alloc_id) &*& *root_slot |-> sleeper &*&
    result.node.node == inserted.node.node &*& result.idx == inserted.idx &*& result.node.height == 0 &*&
    <K>.own(t,leaf_key) &*& <V>.own(t,leaf_value) &*&
    dormant_pair(inserted.node.node.as_ptr(),inserted.idx,key_cell,value_cell) &*&
    insertion_leaves(leaf_nodes.0,inserted.node.node,inserted.idx,Option::Some(leaf_nodes.1),alloc_id,k) &*&
    completed_levels::<K,V>(t,alloc_id,k,?completed) &*&
    if length(completed) == length(path) {
        *sleeper.ptr.as_ptr() |-> Option::Some(?installed) &*& installed.height == old_root.height + 1 &*&
        exists::<NonNull<InternalNode<K,V>>>(?new_root) &*& installed.node.as_ptr() == &(*new_root.as_ptr()).data &*&
        allocated_internal(new_root.as_ptr(),alloc_id,k,_) &*& (*new_root.as_ptr()).data.parent_idx |-> _ &*&
        ancestors(installed.node.as_ptr(),[],installed.node.as_ptr()) &*&
        internal_slots(new_root,1,cons(old_root.node,cons(?sibling,nil)),_,_) &*& <K>.own(t,_) &*& <V>.own(t,_)
    } else {
        *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& (*root).parent_idx |-> root_index &*&
        exists::<NonNull<InternalNode<K,V>>>(?receiving) &*& ancestors(&(*receiving.as_ptr()).data,?remaining,root) &*&
        route_frames(t,remaining) &*& internal_slots(receiving,_,_,_,_) &*& struct_LeafNode_padding(&(*receiving.as_ptr()).data) &*& struct_InternalNode_padding(receiving.as_ptr()) &*& <K>.own(t,_) &*& <V>.own(t,_) &*&
        length(completed) + length(remaining) + 1 == length(path)
    };
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
    [qa]lifetime_token(alloc_lifetime) &*& [?remaining_fraction]lifetime_token(k) &*&
    *root_allocator |-> ?after &*& Allocator::<A>(t,after,alloc_id) &*& *root_slot |-> sleeper &*&
    <K>.own(t,leaf_key) &*& <V>.own(t,leaf_value) &*&
    dormant_pair(inserted.node.node.as_ptr(),inserted.idx,key_cell,value_cell) &*&
    insertion_leaves(leaf_nodes.0,inserted.node.node,inserted.idx,Option::Some(leaf_nodes.1),alloc_id,k) &*&
    completed_levels::<K,V>(t,alloc_id,k,?completed) &*&
    if length(completed) == length(path) {
        *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& detached_child::<K,V>(?sibling) &*&
        exists::<Option<NonNull<InternalNode<K,V>>>>(?partial_root) &*&
        interrupted_root_change(old_root.node,root_index,alloc_id,k,partial_root)
    } else {
        *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*&
        exists::<NonNull<InternalNode<K,V>>>(?receiving) &*&
        ancestor_tail(&(*receiving.as_ptr()).data,?remaining,root,root_index,?ancestor,?ancestor_idx) &*&
        leaf_header(&(*receiving.as_ptr()).data,ancestor,ancestor_idx) &*& struct_InternalNode_padding(receiving.as_ptr()) &*&
        route_frames(t,remaining) &*& length(completed) + length(remaining) + 1 == length(path) &*&
        internal_slots(receiving,?len,_,_,_) &*& detached_child::<K,V>(?detached) &*&
        if len == CAPACITY { <K>.own(t,_) &*& <V>.own(t,_) } else { true }
    };
@*/
{
    //@ open exists(k);
    //@ open exists(leaf_nodes);
    //@ let inserted_value = inserted;
    //@ let inserted_node = inserted_value.node.node;
    //@ let inserted_index = inserted_value.idx;
    //@ open_points_to(&initial_split);
    let mut split = initial_split;
    //@ close_points_to(&initial_split, 1/2);
    //@ close_points_to(&split.left);
    //@ close_points_to(&split.kv);
    //@ close_points_to(&split.right);
    //@ close_points_to(&split);
    /*@
    assert struct_SplitResult_padding::<'tree,K,V,marker::LeafOrInternal>(?loop_result) &*&
        struct_SplitResult_padding::<'tree,K,V,marker::LeafOrInternal>(?payload_arg) &*&
        [1/2]struct_SplitResult_padding::<'tree,K,V,marker::LeafOrInternal>(&payload) &*&
        struct_SplitResult_padding::<'tree,K,V,marker::Internal>(?forget_arg) &*&
        [1/2]struct_SplitResult_padding::<'tree,K,V,marker::Internal>(&pending);
    @*/
    //@ close cursor_split_buffer(loop_result);
    //@ close cursor_split_buffer(payload_arg);
    //@ close [1/2]cursor_split_buffer(&payload);
    //@ close cursor_split_buffer(forget_arg);
    //@ close [1/2]cursor_split_buffer(&pending);
    /*@
    assert struct_Handle_padding::<NodeRef<marker::Mut<'tree>, K, V, marker::Internal>,marker::Edge>(?parent_arg) &*&
        [1/2]struct_Handle_padding::<NodeRef<marker::Mut<'tree>, K, V, marker::Internal>,marker::Edge>(&parent) &*&
        struct_Handle_padding::<NodeRef<marker::Mut<'tree>, K, V, marker::Leaf>,marker::KV>(?return_addr) &*&
        struct_Handle_padding::<NodeRef<marker::DormantMut,K,V,marker::Leaf>,marker::KV>(?wake_root_arg) &*&
        struct_Handle_padding::<NodeRef<marker::DormantMut,K,V,marker::Leaf>,marker::KV>(?wake_fit_arg);
    @*/
    //@ close cursor_handle_buffer(parent_arg);
    //@ close [1/2]cursor_handle_buffer(&parent);
    //@ close cursor_handle_buffer(return_addr);
    //@ close cursor_handle_buffer(wake_root_arg);
    //@ close cursor_handle_buffer(wake_fit_arg);
    /*@
    assert struct_NodeRef_padding::<marker::Mut<'tree>,K,V,marker::LeafOrInternal>(?ascend_arg) &*&
        [1/2]struct_NodeRef_padding::<marker::Mut<'tree>,K,V,marker::LeafOrInternal>(&detached) &*&
        struct_NodeRef_padding::<marker::Owned,K,V,marker::LeafOrInternal>(?insert_right_arg);
    @*/
    //@ close cursor_node_buffer(ascend_arg);
    //@ close [1/2]cursor_node_buffer(&detached);
    //@ close cursor_node_buffer(insert_right_arg);
    //@ assert points_to_::<K>(?key_argument,_) &*& points_to_::<V>(?value_argument,_);
    //@ close completed_levels::<K,V>(t,alloc_id,k,[]);
    loop {
        /*@
        inv *&split |-> ?loop_split &*&
            cursor_split_buffer(loop_result) &*&
            cursor_split_buffer(payload_arg) &*&
            [1/2]cursor_split_buffer(&payload) &*&
            cursor_split_buffer(forget_arg) &*&
            [1/2]cursor_split_buffer(&pending) &*&
            cursor_node_buffer(ascend_arg) &*&
            [1/2]cursor_node_buffer(&detached) &*&
            cursor_node_buffer(insert_right_arg) &*&
            cursor_handle_buffer(parent_arg) &*&
            [1/2]cursor_handle_buffer(&parent) &*&
            cursor_handle_buffer(return_addr) &*&
            cursor_handle_buffer(wake_root_arg) &*& cursor_handle_buffer(wake_fit_arg) &*&
            *key_argument |-> _ &*& *value_argument |-> _ &*&
            *root_allocator |-> root_alloc &*& Allocator::<A>(t,root_alloc,alloc_id) &*&
            *root_slot |-> sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*&
            lifetime_token(func_lft) &*& thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
            [_]allocator_clone_bound::<A>() &*&
            [_]std::alloc::Allocator_share::<A>(alloc_lifetime,t,alloc,alloc_id) &*&
            [_]frac_borrow(alloc_lifetime, ref_initialized_(alloc)) &*& [qa]lifetime_token(alloc_lifetime) &*&
            [?remaining_fraction]lifetime_token(k) &*&
            (*root).parent_idx |-> root_index &*&
            dormant_pair(inserted_node.as_ptr(), inserted_index, key_cell,value_cell) &*&
            insertion_leaves(leaf_nodes.0,inserted_node,inserted_index,Option::Some(leaf_nodes.1),alloc_id,k) &*&
            <K>.own(t,leaf_key) &*& <V>.own(t,leaf_value) &*&
            detached_child(loop_split.right.node.as_ptr()) &*&
            <K>.own(t,loop_split.kv.0) &*& <V>.own(t,loop_split.kv.1) &*&
            ancestors(loop_split.left.node.as_ptr(), ?remaining, root) &*& route_frames(t, remaining) &*& completed_levels::<K,V>(t,alloc_id,k,?completed) &*&
            length(completed) + length(remaining) == length(path) &*& loop_split.left.height == length(completed) &*&
            loop_split.right.height == loop_split.left.height &*& loop_split.left.height + length(remaining) < usize::MAX;
        @*/
        //@ let current_key = loop_split.kv.0;
        //@ let current_value = loop_split.kv.1;
        //@ open_points_to(&split);
        //@ open_points_to(&split.left);
        //@ open_points_to(&split.kv);
        //@ open_points_to(&split.right);
        split = match unsafe { split.left.ascend() } {
            Err(detached) => {
                let root_node = detached.node;
                //@ open ancestors(root_node.as_ptr(), [], root);
                //@ close ancestors(root_node.as_ptr(), [], root);
                let payload = SplitResult { left: detached, ..split };
                //@ close root_split_inputs(root,payload.right.node.as_ptr(),inserted_node.as_ptr(),inserted_index,root_index,key_cell,value_cell);
                //@ open route_frames(t,[]);
                //@ close exists(k);
                //@ std::ptr::NonNull_new_as_ptr(old_root.node);
                //@ std::ptr::NonNull_new_as_ptr(root_node);
                return unsafe { finish_root_split/*@::<K,V,A,'tree,'slot>@*/(payload, inserted, root_slot, root_allocator) };
            }
            Ok(parent) => {
                //@ assert exists::<NonNull<InternalNode<K,V>>>(?receiving);
                //@ std::ptr::NonNull_Sized_as_ptr(receiving);
                //@ assert &(*receiving.as_ptr()).data == (receiving.as_ptr() as *LeafNode<K,V>);
                //@ close exists(receiving);
                //@ close exists(k);
                match unsafe { parent.insert(split.kv.0, split.kv.1, split.right, alloc.clone()) } {
                    None => {
                        return unsafe { inserted.awaken/*@::<K,V,marker::Leaf,marker::KV,'tree>@*/() };
                    }
                    Some(pending) => {
                        //@ open exists(receiving);
                        //@ assert exists::<NonNull<InternalNode<K,V>>>(?fresh);
                        //@ open exists(fresh);
                        //@ close completed_levels::<K,V>(t,alloc_id,k, cons(Placement(receiving,fresh,current_key,current_value),completed));
                        unsafe { pending.forget_node_type() }
                    }
                }
            }
        };
        //@ close_points_to(&split.left);
        //@ close_points_to(&split.kv);
        //@ close_points_to(&split.right);
    }
}
// The production iterator is specialized to the two range types used by its
// callers. The invariant preserves the edge slots and separates the repaired
// prefix from the pending suffix.

// BEGIN_NODE_LEN
impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    unsafe fn relink_len(&self) -> usize
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
    unsafe fn relink_reborrow<'b>(&'b mut self) -> NodeRef<marker::Mut<'b>, K, V, Type>
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
    unsafe fn new_relink_edge(node: NodeRef<BorrowType, K, V, Type>, idx: usize) -> Self
    //@ req (*node.node.as_ptr()).len |-> ?len &*& idx <= len;
    //@ ens result.node == node &*& result.idx == idx &*& (*node.node.as_ptr()).len |-> len;
    //@ on_unwind_ens false;
    {
        unsafe { debug_assert!(idx <= node.relink_len()) };
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
    unsafe { Handle::new_relink_edge/*@::<marker::Mut<'b>,K,V,marker::Internal>@*/(
        node.relink_reborrow/*@::<marker::Mut<'a>,K,V,marker::Internal,'b>@*/(), i
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
                    unsafe { debug_assert!(i <= self.relink_len()) };
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
                    unsafe { debug_assert!(i <= self.relink_len()) };
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
    unsafe fn correct_all_childrens_parent_links<'b>(&'b mut self)
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
        let len = unsafe { self.relink_len() };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(self, _);
        //@ close exists(parent);
        //@ let prefix = nil::<MaybeUninit<BoxedNode<K,V>>>;
        //@ close exists(pair(prefix, tail));
        unsafe { self.relink_inclusive/*@::<'a,K,V,'b>@*/(0..=len) };
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    unsafe fn merge_len(&self) -> usize
    //@ req [?f](*self |-> ?node) &*& [?ql]((*node.node.as_ptr()).len |-> ?len) &*& ref_initialized(self);
    //@ ens [f](*self |-> node) &*& [ql]((*node.node.as_ptr()).len |-> len) &*& result == len &*& ref_initialized(self);
    //@ on_unwind_ens false;
    {
        //@ let local = begin_lifetime();
        //@ close ref_initialized_::<NodeRef<BorrowType,K,V,Type>>(self)();
        //@ borrow(local, ref_initialized_::<NodeRef<BorrowType,K,V,Type>>(self));
        //@ full_borrow_into_frac(local, ref_initialized_::<NodeRef<BorrowType,K,V,Type>>(self));
        let length = unsafe { usize::from((*Self::as_leaf_ptr(self)).len) };
        //@ end_lifetime(local);
        //@ borrow_end(local, ref_initialized_::<NodeRef<BorrowType,K,V,Type>>(self));
        //@ open ref_initialized_::<NodeRef<BorrowType,K,V,Type>>(self)();
        length
    }
}

impl<'a, K: 'a, V: 'a> BalancingContext<'a, K, V> {
    unsafe fn do_merge_production<
        F: FnOnce(
            NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
            NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
        ) -> R,
        R,
        A: std::alloc::Allocator,
    >(
        self,
        finish: F,
        /*@~mut@*/ alloc: A,
    ) -> R
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*& <F>.own(t, finish) &*&
        Allocator::<A>(t, alloc, ?id) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?released) &*&
        context_merge_inputs(t, self, id, k, released, ?shape);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*& <R>.own(t, result) &*&
        [released]lifetime_token(k) &*&
        match shape {
            MergeLengths(p, l, r, pc, lc, rc) =>
                merged_nodes(t, NonNull::new(self.parent.node.node.as_ptr() as *InternalNode<K,V>),
                    self.left_child.node, self.parent.node.height - 1, p - 1, l + 1 + r,
                    append(take(self.parent.idx + 1, pc), drop(self.parent.idx + 2, pc)), append(lc, rc))
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        match shape {
            MergeLengths(p, l, r, pc, lc, rc) =>
                if l + 1 + r <= CAPACITY {
                    [released]lifetime_token(k) &*&
                    merged_nodes(t, NonNull::new(self.parent.node.node.as_ptr() as *InternalNode<K,V>),
                        self.left_child.node, self.parent.node.height - 1, p - 1, l + 1 + r,
                        append(take(self.parent.idx + 1, pc), drop(self.parent.idx + 2, pc)), append(lc, rc))
                } else {
                    context_merge_inputs(t, self, id, k, released, shape)
                }
        };
    @*/
    {
        //@ open exists(k);
        //@ open exists(released);
        //@ let context = self;
        //@ open context_merge_inputs(t, context, id, k, released, shape);
        //@ let parent = NonNull::new(self.parent.node.node.as_ptr() as *InternalNode<K,V>);
        //@ std::ptr::NonNull_Sized_as_ptr(self.parent.node.node);
        //@ std::ptr::NonNull_as_ptr_new(self.parent.node.node.as_ptr() as *InternalNode<K,V>);
        //@ std::ptr::NonNull_Sized_as_ptr(parent);
        //@ let left = self.left_child.node;
        //@ let right = self.right_child.node;
        //@ std::ptr::NonNull_Sized_as_ptr(left);
        //@ std::ptr::NonNull_Sized_as_ptr(right);
        //@ let parent_height = self.parent.node.height;
        //@ let index = self.parent.idx;
        //@ assert merge_inputs(t, parent, left, right, parent_height, index, id, k, released, ?parent_len, ?left_len, ?right_len_0, ?parent_children, ?left_children, ?right_children);
        //@ open merge_inputs(t, parent, left, right, parent_height, index, id, k, released, parent_len, left_len, right_len_0, parent_children, left_children, right_children);
        let Handle { node: mut parent_node, idx: parent_idx, .. } = self.parent;
        //@ let parent_ptr = &(*parent.as_ptr()).data;
        //@ assert parent_ptr == parent_node.node.as_ptr();
        //@ open owned_leaf_slots(t, parent_ptr, parent_len);
        //@ open leaf_slots(parent_ptr, parent_len, ?p_keys, ?p_vals);
        //@ let parent_view = precreate_ref(&parent_node);
        //@ init_ref_readonly(parent_view, 1/2);
        let old_parent_len = unsafe { parent_node.merge_len() };
        //@ end_ref_readonly(parent_view);
        //@ merge_fractions points_to(&parent_node, _);
        let mut left_node = self.left_child;
        //@ let left_ptr = left.as_ptr();
        //@ assert left_ptr == left_node.node.as_ptr();
        //@ open owned_leaf_slots(t, left_ptr, left_len);
        //@ open leaf_slots(left_ptr, left_len, ?l_keys, ?l_vals);
        //@ let left_view = precreate_ref(&left_node);
        //@ init_ref_readonly(left_view, 1/2);
        let old_left_len = unsafe { left_node.merge_len() };
        //@ end_ref_readonly(left_view);
        //@ merge_fractions points_to(&left_node, _);
        let mut right_node = self.right_child;
        //@ let right_ptr = right.as_ptr();
        //@ assert right_ptr == right_node.node.as_ptr();
        //@ open owned_leaf_slots(t, right_ptr, right_len_0);
        //@ open leaf_slots(right_ptr, right_len_0, ?r_keys, ?r_vals);
        //@ let right_view = precreate_ref(&right_node);
        //@ init_ref_readonly(right_view, 1/2);
        let right_len = unsafe { right_node.merge_len() };
        //@ end_ref_readonly(right_view);
        //@ merge_fractions points_to(&right_node, _);
        let new_left_len = old_left_len + 1 + right_len;
        /*@
        if new_left_len > CAPACITY {
            close leaf_slots(parent_ptr, parent_len, p_keys, p_vals);
            close owned_leaf_slots(t, parent_ptr, parent_len);
            close leaf_slots(left_ptr, left_len, l_keys, l_vals);
            close owned_leaf_slots(t, left_ptr, left_len);
            close leaf_slots(right_ptr, right_len, r_keys, r_vals);
            close owned_leaf_slots(t, right_ptr, right_len);
            close merge_inputs(t, parent, left, right, parent_height, index, id, k, released,
                parent_len, left_len, right_len, parent_children, left_children, right_children);
            close context_merge_inputs(t, context, id, k, released, shape);
            std::alloc::Allocator_to_own(alloc);
        }
        @*/
        assert!(new_left_len <= CAPACITY);
        //@ open balancing_edges(parent, parent_children, ?parent_slots);
        //@ split_linked_headers(parent_children, parent, 0, parent_idx);
        //@ drop_n_plus_one(parent_idx, parent_children);
        //@ open linked_headers(drop(parent_idx, parent_children), parent, parent_idx);
        //@ drop_n_plus_one(parent_idx + 1, parent_children);
        //@ open linked_headers(drop(parent_idx + 1, parent_children), parent, parent_idx + 1);
        //@ close leaf_without_len(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16), l_keys, l_vals);
        unsafe {
            *left_node.len_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/() = new_left_len as u16;
            //@ assert len_loan(left_ptr, ?slot, Option::Some(parent), MaybeUninit::new(parent_idx as u16), l_keys, l_vals);
            //@ end_len_loan(left_ptr, slot);
            //@ open leaf_without_len(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16), l_keys, l_vals);
            //@ open balancing_child_allocation(right, parent_height - 1, id, k, released);
            /*@
            if parent_height > 1 {
                let internal = right_ptr as *InternalNode<K,V>;
                open allocated_internal(internal, id, k, released);
                assert &(*internal).data == right_ptr;
            } else {
                open allocated_leaf(right_ptr, id, k, released);
            }
            @*/
            //@ close leaf_header(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16));
            //@ close leaf_header(right_ptr, Option::Some(parent), MaybeUninit::new((parent_idx + 1) as u16));
            //@ close leaf_without_keys(parent_ptr, _, _, old_parent_len as u16, _);
            //@ close leaf_without_keys(left_ptr, _, _, new_left_len as u16, _);
            //@ close leaf_without_keys(right_ptr, _, _, right_len as u16, _);
            {
                //@ assert leaf_without_keys(parent_ptr, ?keys_p_parent, ?keys_p_idx, ?keys_p_len, ?keys_p_vals);
                //@ assert leaf_without_keys(left_ptr, ?keys_l_parent, ?keys_l_idx, ?keys_l_len, ?keys_l_vals);
                //@ assert leaf_without_keys(right_ptr, ?keys_r_parent, ?keys_r_idx, ?keys_r_len, ?keys_r_vals);
                //@ let keys_old_parent = take(old_parent_len, p_keys);
                //@ let keys_old_left = take(old_left_len, l_keys);
                //@ let keys_incoming = take(right_len, r_keys);
                //@ length_take(old_parent_len, p_keys);
                //@ length_take(old_left_len, l_keys);
                //@ length_take(right_len, r_keys);
                //@ nth_take_range(p_keys, old_parent_len, parent_idx);
                //@ split_slot_owners(t, keys_old_parent, parent_idx);
                //@ drop_n_plus_one(parent_idx, keys_old_parent);
                //@ open slot_owners(t, drop(parent_idx, keys_old_parent));
                unsafe {
                    let parent_key = slice_remove(
                        parent_node.key_area_prefix_mut/*@::<'a,K,V,marker::Internal,'a>@*/(..old_parent_len), parent_idx,
                    );
                    //@ assert keys_range_loan(parent_ptr, ?keys_active, 0, old_parent_len, keys_p_parent, keys_p_idx, keys_p_len, keys_p_vals, _, _);
                    //@ assert move_slice(keys_active as *MaybeUninit<K>, old_parent_len, ?keys_active_after);
                    //@ end_keys_range(parent_ptr, keys_active);
                    //@ let keys_surviving = append(take(parent_idx, keys_old_parent), drop(parent_idx + 1, keys_old_parent));
                    //@ join_slot_owners(t, take(parent_idx, keys_old_parent), drop(parent_idx + 1, keys_old_parent));
                    //@ length_take(parent_idx, keys_old_parent);
                    //@ length_drop(parent_idx + 1, keys_old_parent);
                    //@ append_assoc(take(parent_idx, keys_old_parent), drop(parent_idx + 1, keys_old_parent), drop(old_parent_len - 1, keys_old_parent));
                    //@ take_append_l(old_parent_len - 1, keys_surviving, drop(old_parent_len - 1, keys_old_parent));
                    //@ take_length(keys_surviving);
                    //@ length_append(keys_surviving, drop(old_parent_len - 1, keys_old_parent));
                    //@ length_drop(old_parent_len - 1, keys_old_parent);
                    //@ take_append_l(old_parent_len - 1, keys_active_after, drop(old_parent_len, p_keys));
                    //@ drop_append(old_parent_len, keys_active_after, drop(old_parent_len, p_keys));

                    left_node.key_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(old_left_len).write(parent_key);
                    //@ assert keys_slot_loan(left_ptr, ?keys_slot, old_left_len, keys_l_parent, keys_l_idx, keys_l_len, keys_l_vals, _, _);
                    //@ end_keys_slot(left_ptr, keys_slot);
                    //@ assert (*left_ptr).keys[..CAPACITY] |-> ?keys_left_with_entry;
                    //@ let keys_with_entry = append(keys_old_left, [MaybeUninit::new(parent_key)]);
                    //@ append_assoc(keys_old_left, [MaybeUninit::new(parent_key)], drop(old_left_len + 1, l_keys));
                    //@ take_append_l(old_left_len + 1, keys_with_entry, drop(old_left_len + 1, l_keys));
                    //@ take_length(keys_with_entry);

                    move_to_slice(
                        right_node.key_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(..right_len),
                        left_node.key_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(old_left_len + 1..new_left_len),
                    );
                    //@ assert keys_range_loan(right_ptr, ?keys_source, 0, right_len, keys_r_parent, keys_r_idx, keys_r_len, keys_r_vals, _, _);
                    //@ assert keys_range_loan(left_ptr, ?keys_destination, old_left_len + 1, new_left_len, keys_l_parent, keys_l_idx, keys_l_len, keys_l_vals, _, _);
                    //@ end_keys_range(right_ptr, keys_source);
                    //@ append_take_drop_n(r_keys, right_len);
                    //@ end_keys_range(left_ptr, keys_destination);
                    //@ close slot_owners::<K>(t, cons(MaybeUninit::new(parent_key), keys_incoming));
                    //@ join_slot_owners(t, keys_old_left, cons(MaybeUninit::new(parent_key), keys_incoming));
                    //@ let keys_merged = append(keys_old_left, cons(MaybeUninit::new(parent_key), keys_incoming));
                    //@ append_assoc(keys_with_entry, keys_incoming, drop(new_left_len, keys_left_with_entry));
                    //@ append_assoc(keys_old_left, [MaybeUninit::new(parent_key)], keys_incoming);
                    //@ take_append_l(new_left_len, keys_merged, drop(new_left_len, keys_left_with_entry));
                    //@ take_length(keys_merged);
                    //@ length_append(keys_with_entry, keys_incoming);
                    //@ drop_append(new_left_len, keys_merged, drop(new_left_len, keys_left_with_entry));
                    //@ drop_append(new_left_len, keys_with_entry, drop(old_left_len + 1, l_keys));
                    //@ drop_twice(right_len, old_left_len + 1, l_keys);
                }
            }
            //@ open leaf_without_keys(parent_ptr, _, _, old_parent_len as u16, _);
            //@ open leaf_without_keys(left_ptr, _, _, new_left_len as u16, _);
            //@ open leaf_without_keys(right_ptr, _, _, right_len as u16, _);
            //@ close leaf_without_vals(parent_ptr, _, _, old_parent_len as u16, _);
            //@ close leaf_without_vals(left_ptr, _, _, new_left_len as u16, _);
            //@ close leaf_without_vals(right_ptr, _, _, right_len as u16, _);
            {
                //@ assert leaf_without_vals(parent_ptr, ?vals_p_parent, ?vals_p_idx, ?vals_p_len, ?vals_p_keys);
                //@ assert leaf_without_vals(left_ptr, ?vals_l_parent, ?vals_l_idx, ?vals_l_len, ?vals_l_keys);
                //@ assert leaf_without_vals(right_ptr, ?vals_r_parent, ?vals_r_idx, ?vals_r_len, ?vals_r_keys);
                //@ let vals_old_parent = take(old_parent_len, p_vals);
                //@ let vals_old_left = take(old_left_len, l_vals);
                //@ let vals_incoming = take(right_len, r_vals);
                //@ length_take(old_parent_len, p_vals);
                //@ length_take(old_left_len, l_vals);
                //@ length_take(right_len, r_vals);
                //@ nth_take_range(p_vals, old_parent_len, parent_idx);
                //@ split_slot_owners(t, vals_old_parent, parent_idx);
                //@ drop_n_plus_one(parent_idx, vals_old_parent);
                //@ open slot_owners(t, drop(parent_idx, vals_old_parent));
                unsafe {
                    let parent_val = slice_remove(
                        parent_node.val_area_prefix_mut/*@::<'a,K,V,marker::Internal,'a>@*/(..old_parent_len), parent_idx,
                    );
                    //@ assert vals_range_loan(parent_ptr, ?vals_active, 0, old_parent_len, vals_p_parent, vals_p_idx, vals_p_len, vals_p_keys, _, _);
                    //@ assert move_slice(vals_active as *MaybeUninit<V>, old_parent_len, ?vals_active_after);
                    //@ end_vals_range(parent_ptr, vals_active);
                    //@ let vals_surviving = append(take(parent_idx, vals_old_parent), drop(parent_idx + 1, vals_old_parent));
                    //@ join_slot_owners(t, take(parent_idx, vals_old_parent), drop(parent_idx + 1, vals_old_parent));
                    //@ length_take(parent_idx, vals_old_parent);
                    //@ length_drop(parent_idx + 1, vals_old_parent);
                    //@ append_assoc(take(parent_idx, vals_old_parent), drop(parent_idx + 1, vals_old_parent), drop(old_parent_len - 1, vals_old_parent));
                    //@ take_append_l(old_parent_len - 1, vals_surviving, drop(old_parent_len - 1, vals_old_parent));
                    //@ take_length(vals_surviving);
                    //@ length_append(vals_surviving, drop(old_parent_len - 1, vals_old_parent));
                    //@ length_drop(old_parent_len - 1, vals_old_parent);
                    //@ take_append_l(old_parent_len - 1, vals_active_after, drop(old_parent_len, p_vals));
                    //@ drop_append(old_parent_len, vals_active_after, drop(old_parent_len, p_vals));

                    left_node.val_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(old_left_len).write(parent_val);
                    //@ assert vals_slot_loan(left_ptr, ?vals_slot, old_left_len, vals_l_parent, vals_l_idx, vals_l_len, vals_l_keys, _, _);
                    //@ end_vals_slot(left_ptr, vals_slot);
                    //@ assert (*left_ptr).vals[..CAPACITY] |-> ?vals_left_with_entry;
                    //@ let vals_with_entry = append(vals_old_left, [MaybeUninit::new(parent_val)]);
                    //@ append_assoc(vals_old_left, [MaybeUninit::new(parent_val)], drop(old_left_len + 1, l_vals));
                    //@ take_append_l(old_left_len + 1, vals_with_entry, drop(old_left_len + 1, l_vals));
                    //@ take_length(vals_with_entry);

                    move_to_slice(
                        right_node.val_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(..right_len),
                        left_node.val_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(old_left_len + 1..new_left_len),
                    );
                    //@ assert vals_range_loan(right_ptr, ?vals_source, 0, right_len, vals_r_parent, vals_r_idx, vals_r_len, vals_r_keys, _, _);
                    //@ assert vals_range_loan(left_ptr, ?vals_destination, old_left_len + 1, new_left_len, vals_l_parent, vals_l_idx, vals_l_len, vals_l_keys, _, _);
                    //@ end_vals_range(right_ptr, vals_source);
                    //@ append_take_drop_n(r_vals, right_len);
                    //@ end_vals_range(left_ptr, vals_destination);
                    //@ close slot_owners::<V>(t, cons(MaybeUninit::new(parent_val), vals_incoming));
                    //@ join_slot_owners(t, vals_old_left, cons(MaybeUninit::new(parent_val), vals_incoming));
                    //@ let vals_merged = append(vals_old_left, cons(MaybeUninit::new(parent_val), vals_incoming));
                    //@ append_assoc(vals_with_entry, vals_incoming, drop(new_left_len, vals_left_with_entry));
                    //@ append_assoc(vals_old_left, [MaybeUninit::new(parent_val)], vals_incoming);
                    //@ take_append_l(new_left_len, vals_merged, drop(new_left_len, vals_left_with_entry));
                    //@ take_length(vals_merged);
                    //@ length_append(vals_with_entry, vals_incoming);
                    //@ drop_append(new_left_len, vals_merged, drop(new_left_len, vals_left_with_entry));
                    //@ drop_append(new_left_len, vals_with_entry, drop(old_left_len + 1, l_vals));
                    //@ drop_twice(right_len, old_left_len + 1, l_vals);
                }
            }
            //@ open leaf_without_vals(parent_ptr, _, _, old_parent_len as u16, _);
            //@ open leaf_without_vals(left_ptr, _, _, new_left_len as u16, _);
            //@ open leaf_without_vals(right_ptr, _, _, right_len as u16, _);
            //@ open leaf_header(right_ptr, _, _);
            //@ open leaf_header(left_ptr, _, _);
            /*@
            if parent_height > 1 {
                close allocated_internal(right_ptr as *InternalNode<K,V>, id, k, released);
            } else {
                close allocated_leaf(right_ptr, id, k, released);
            }
            @*/
            //@ close balancing_child_allocation(right, parent_height - 1, id, k, released);
            //@ close linked_headers(drop(parent_idx + 1, parent_children), parent, parent_idx + 1);
            //@ close linked_headers(drop(parent_idx, parent_children), parent, parent_idx);
            //@ length_take(parent_idx, parent_children);
            //@ join_linked_headers(take(parent_idx, parent_children), drop(parent_idx, parent_children), parent, 0);
            //@ append_take_drop_n(parent_children, parent_idx);
            //@ close balancing_edges(parent, parent_children, parent_slots);
            //@ open leaf_header(parent_ptr, ?ancestor, ?ancestor_idx);
            //@ close leaf_without_len(parent_ptr, ancestor, ancestor_idx, _, _);
            {
                //@ assert balancing_edges(parent, parent_children, ?slots_before_removal);
                //@ assert leaf_without_len(parent_ptr, ancestor, ancestor_idx, ?parent_keys_for_relink, ?parent_vals_for_relink);
                    //@ open exists(parent);
                    //@ open balancing_edges(parent, parent_children, slots_before_removal);
                    //@ let parent_storage = parent.as_ptr();
                    //@ let prefix = take(parent_idx + 1, parent_children);
                    //@ let rest = drop(parent_idx + 2, parent_children);
                    //@ let removed = nth(parent_idx + 1, parent_children);
                    //@ split_linked_headers(parent_children, parent, 0, parent_idx + 1);
                    //@ drop_n_plus_one(parent_idx + 1, parent_children);
                    //@ open linked_headers(cons(removed, rest), parent, parent_idx + 1);
                    //@ forget_link_indices(rest, parent, parent_idx + 2);
                    //@ let parent_active_edges = initialized_edges(parent_children);
                    //@ nth_initialized_edge(parent_children, parent_idx + 1);
                    //@ std::ptr::close_NonNull_own(t, removed);
                    //@ produce_type_interp::<BoxedNode<K,V>>();
                    unsafe {
                        //@ nth_take_range(slots_before_removal, old_parent_len + 1, parent_idx + 1);
                        //@ open leaf_without_len(&(*parent_storage).data, ancestor, ancestor_idx, parent_keys_for_relink, parent_vals_for_relink);
                        //@ close_points_to(&(*parent_storage).data);
                        //@ close internal_without_edges(parent_storage, ?data);
                        slice_remove(
                            parent_node.edge_area_prefix_mut/*@::<'a,K,V,'a>@*/(..old_parent_len + 1), parent_idx + 1,
                        );
                        //@ assert edges_range_loan(parent_storage, ?removed_prefix, 0, old_parent_len + 1, data, _, _);
                        //@ end_edges_range(parent_storage, removed_prefix);
                        //@ open internal_without_edges(parent_storage, data);
                        //@ open_points_to(&(*parent_storage).data);
                        //@ close leaf_without_len(&(*parent_storage).data, ancestor, ancestor_idx, parent_keys_for_relink, parent_vals_for_relink);
                        //@ leak <BoxedNode<K,V>>.own(t, removed);
                        //@ std::ptr::open_NonNull_own(t, removed);
                        //@ leak type_interp::<BoxedNode<K,V>>();
                        //@ initialized_edge_split(parent_children, parent_idx + 1);
                        //@ initialized_edge_split(parent_children, parent_idx + 2);
                        //@ let parent_children_after = append(initialized_edges(prefix), initialized_edges(rest));
                        //@ let residual = drop(old_parent_len, parent_active_edges);
                        //@ append_assoc(initialized_edges(prefix), initialized_edges(rest), residual);
                        //@ initialized_edge_count(prefix);
                        //@ initialized_edge_count(rest);
                        //@ length_take(parent_idx + 1, parent_children);
                        //@ length_drop(parent_idx + 2, parent_children);
                // BEGIN_MERGE_PARENT_RELINK
                        //@ assert (*parent_storage).edges[..CAPACITY + 1] |-> ?new_edges;
                        //@ let parent_relink_before = initialized_edges(prefix);
                        //@ let tail = drop(old_parent_len + 1, slots_before_removal);
                        //@ append_assoc(parent_relink_before, append(initialized_edges(rest), residual), tail);
                        //@ append_assoc(initialized_edges(rest), residual, tail);
                        //@ close exists(parent);
                        //@ close exists(pair(parent_relink_before, append(residual, tail)));
                        parent_node.relink_range/*@::<'a,K,V,'a>@*/(parent_idx + 1..old_parent_len);
                        *parent_node.len_mut/*@::<'a,K,V,marker::Internal,'a>@*/() -= 1;
                        //@ assert len_loan(&(*parent_storage).data, ?parent_length_slot, ancestor, ancestor_idx, parent_keys_for_relink, parent_vals_for_relink);
                        //@ end_len_loan(&(*parent_storage).data, parent_length_slot);
                // END_MERGE_PARENT_RELINK
                        //@ take_append_l(parent_idx + 1, initialized_edges(prefix), initialized_edges(rest));
                        //@ take_length(initialized_edges(prefix));
                        //@ take_append_l(old_parent_len, parent_children_after, residual);
                        //@ take_append_l(old_parent_len, append(parent_children_after, residual), drop(old_parent_len + 1, slots_before_removal));
                        //@ join_linked_headers(prefix, rest, parent, 0);
                        //@ initialized_edges_append(prefix, rest);
                        //@ close balancing_edges(parent, append(prefix, rest), new_edges);
                    }
            }
            //@ open leaf_without_len(parent_ptr, ancestor, ancestor_idx, _, _);
            //@ close leaf_header(parent_ptr, ancestor, ancestor_idx);
            //@ close leaf_slots(parent_ptr, old_parent_len - 1, _, _);
            //@ close owned_leaf_slots(t, parent_ptr, old_parent_len - 1);
            //@ close leaf_slots(left_ptr, new_left_len, _, _);
            //@ close owned_leaf_slots(t, left_ptr, new_left_len);
            //@ open balancing_child_edges(left, parent_height - 1, left_len, left_children);
            //@ open balancing_child_edges(right, parent_height - 1, right_len, right_children);
            //@ open balancing_child_allocation(right, parent_height - 1, id, k, released);
            //@ let surviving = append(take(parent_idx + 1, parent_children), drop(parent_idx + 2, parent_children));
            if parent_node.height > 1 {
                let mut left_internal_node = left_node.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'a>@*/().cast_to_internal_unchecked/*@::<'a,K,V>@*/();
                let mut right_internal_node = right_node.cast_to_internal_unchecked/*@::<'a,K,V>@*/();
                //@ let left_internal = NonNull::new(left_internal_node.node.as_ptr() as *InternalNode<K,V>);
                //@ let right_internal = NonNull::new(right_internal_node.node.as_ptr() as *InternalNode<K,V>);
                //@ std::ptr::NonNull_as_ptr_new(left_internal_node.node.as_ptr() as *InternalNode<K,V>);
                //@ std::ptr::NonNull_Sized_as_ptr(left_internal);
                //@ std::ptr::NonNull_as_ptr_new(right_internal_node.node.as_ptr() as *InternalNode<K,V>);
                //@ std::ptr::NonNull_Sized_as_ptr(right_internal);
                //@ assert &(*left_internal.as_ptr()).data == left_ptr;
                //@ assert &(*right_internal.as_ptr()).data == right_ptr;
                //@ open owned_leaf_slots(t, left_ptr, new_left_len);
                //@ open leaf_slots(left_ptr, new_left_len, _, _);
                //@ open balancing_child_padding(left, parent_height - 1);
                //@ open allocated_internal(right_internal.as_ptr(), id, k, released);
                //@ open balancing_edges(parent, surviving, ?parent_edges);
                //@ let before_left = take(parent_idx + 1, parent_children);
                //@ let after_right = drop(parent_idx + 2, parent_children);
                //@ length_take(parent_idx + 1, parent_children);
                //@ length_drop(parent_idx + 2, parent_children);
                //@ length_append(before_left, after_right);
                //@ take_append_l(parent_idx + 1, before_left, after_right);
                //@ take_length(before_left);
                //@ nth_take_range(surviving, parent_idx + 1, parent_idx);
                //@ nth_take_range(parent_children, parent_idx + 1, parent_idx);
                //@ split_linked_headers(surviving, parent, 0, parent_idx);
                //@ drop_n_plus_one(parent_idx, surviving);
                //@ open linked_headers(drop(parent_idx, surviving), parent, parent_idx);
                //@ close_points_to(left_ptr);
                //@ close_points_to(right_ptr);
                //@ close internal_without_edges(left_internal.as_ptr(), ?left_data);
                //@ close internal_without_edges(right_internal.as_ptr(), ?right_data);
                {
                    //@ assert balancing_edges(left_internal, left_children, ?left_slots);
                    //@ assert balancing_edges(right_internal, right_children, ?right_slots);
                    //@ open exists(pair(left_internal, right_internal));
                    //@ open balancing_edges(left_internal, left_children, left_slots);
                    //@ open balancing_edges(right_internal, right_children, right_slots);
                    //@ forget_link_indices(right_children, right_internal, 0);
                    unsafe {
                        move_to_slice(
                            right_internal_node.edge_area_prefix_mut/*@::<'a,K,V,'a>@*/(..right_len + 1),
                            left_internal_node.edge_area_range_mut/*@::<'a,K,V,'a>@*/(old_left_len + 1..new_left_len + 1),
                        );
                        //@ assert edges_range_loan(right_internal.as_ptr(), ?edge_source, 0, right_len + 1, right_data, _, _);
                        //@ assert edges_range_loan(left_internal.as_ptr(), ?edge_destination, old_left_len + 1, new_left_len + 1, left_data, _, _);
                        //@ end_edges_range(right_internal.as_ptr(), edge_source);
                        //@ append_take_drop_n(right_slots, right_len + 1);
                        //@ end_edges_range(left_internal.as_ptr(), edge_destination);
                        //@ let before = take(old_left_len + 1, left_slots);
                        //@ let after_copy = drop(new_left_len + 1, left_slots);
                        //@ length_take(old_left_len + 1, left_slots);
                        //@ open internal_without_edges(left_internal.as_ptr(), left_data);
                        //@ open_points_to(&(*left_internal.as_ptr()).data);
                        //@ close exists(left_internal);
                        //@ close exists(pair(before, after_copy));
                        left_internal_node.relink_range/*@::<'a,K,V,'a>@*/(old_left_len + 1..new_left_len + 1);
                        //@ close_points_to(&(*left_internal.as_ptr()).data);
                        //@ close internal_without_edges(left_internal.as_ptr(), left_data);
                        //@ assert (*left_internal.as_ptr()).edges[..CAPACITY + 1] |-> ?merged_slots;
                        //@ append_assoc(before, initialized_edges(right_children), after_copy);
                        //@ let active = append(initialized_edges(left_children), initialized_edges(right_children));
                        //@ initialized_edge_count(left_children);
                        //@ initialized_edge_count(right_children);
                        //@ take_twice(left_slots, old_left_len + 1, new_left_len + 1);
                        //@ take_append_l(new_left_len + 1, active, drop(new_left_len + 1, left_slots));
                        //@ take_length(active);
                        //@ join_linked_headers(left_children, right_children, left_internal, 0);
                        //@ initialized_edges_append(left_children, right_children);
                        //@ close balancing_edges(left_internal, append(left_children, right_children), merged_slots);
                    }
                }
                //@ open internal_without_edges(left_internal.as_ptr(), left_data);
                //@ open_points_to(left_ptr);
                //@ close linked_headers(drop(parent_idx, surviving), parent, parent_idx);
                //@ length_take(parent_idx, surviving);
                //@ join_linked_headers(take(parent_idx, surviving), drop(parent_idx, surviving), parent, 0);
                //@ append_take_drop_n(surviving, parent_idx);
                //@ close balancing_edges(parent, surviving, parent_edges);
                //@ close leaf_slots(left_ptr, new_left_len, _, _);
                //@ close owned_leaf_slots(t, left_ptr, new_left_len);
                //@ close balancing_child_edges(left, parent_height - 1, new_left_len, append(left_children, right_children));
                //@ close balancing_child_padding(left, parent_height - 1);
                //@ close merged_nodes(t, parent, left, parent_height - 1, old_parent_len - 1, new_left_len, surviving, append(left_children, right_children));
                //@ open internal_without_edges(right_internal.as_ptr(), right_data);
                //@ open_points_to(right_ptr);
                //@ close_points_to(right_internal.as_ptr(), 1);
                //@ let target = right_internal.as_ptr();
                //@ points_to__limits(target);
                //@ assert close_points_to_at_lft_token(1, id.lft, target, ?allocation_fraction);
                //@ to_u8s_(target);
                //@ close_points_to_at_lft_token_to_close_u8s_at_lft_token(target);
                //@ close_array_at_lft_(target as *u8);
                //@ lifetime_token_trade_back(allocation_fraction, id.lft);
                //@ let view = precreate_ref(&alloc);
                //@ let call_lifetime = begin_lifetime();
                {
                    //@ let_lft 'call = call_lifetime;
                    //@ std::alloc::init_ref_Allocator_at_lifetime::<'call, A>(view);
                    //@ open_points_to(&right_internal_node);
                    //@ std::ptr::NonNull_Sized_as_ptr(right_internal_node.node);
                    //@ std::ptr::NonNull_as_ptr_new(right_internal_node.node.as_ptr() as *u8);
                    alloc.deallocate/*@::<A,'call>@*/(right_internal_node.node.cast(), std::alloc::Layout::new::<InternalNode<K,V>>());
                    //@ close_points_to(&right_internal_node);
                    //@ leak Allocator::<&'call A>(t, view, id);
                }
                //@ end_lifetime(call_lifetime);
                //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
            } else {
                //@ close balancing_child_edges(left, parent_height - 1, new_left_len, append(left_children, right_children));
                //@ close merged_nodes(t, parent, left, parent_height - 1, old_parent_len - 1, new_left_len, surviving, append(left_children, right_children));
                //@ open allocated_leaf(right_ptr, id, k, released);
                //@ close_points_to(right_ptr, 1);
                //@ let target = right.as_ptr();
                //@ points_to__limits(target);
                //@ assert close_points_to_at_lft_token(1, id.lft, target, ?allocation_fraction);
                //@ to_u8s_(target);
                //@ close_points_to_at_lft_token_to_close_u8s_at_lft_token(target);
                //@ close_array_at_lft_(target as *u8);
                //@ lifetime_token_trade_back(allocation_fraction, id.lft);
                //@ let view = precreate_ref(&alloc);
                //@ let call_lifetime = begin_lifetime();
                {
                    //@ let_lft 'call = call_lifetime;
                    //@ std::alloc::init_ref_Allocator_at_lifetime::<'call, A>(view);
                    //@ open_points_to(&right_node);
                    //@ std::ptr::NonNull_Sized_as_ptr(right_node.node);
                    //@ std::ptr::NonNull_as_ptr_new(right_node.node.as_ptr() as *u8);
                    alloc.deallocate/*@::<A,'call>@*/(right_node.node.cast(), std::alloc::Layout::new::<LeafNode<K,V>>());
                    //@ close_points_to(&right_node);
                    //@ leak Allocator::<&'call A>(t, view, id);
                }
                //@ end_lifetime(call_lifetime);
                //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
            }
        }
        //@ std::alloc::Allocator_to_own::<A>(alloc);
        //@ close NodeRef_own::<marker::Mut<'a>,K,V,marker::Internal>(t, parent_node);
        //@ close NodeRef_own::<marker::Mut<'a>,K,V,marker::LeafOrInternal>(t, left_node);
        unsafe { call_merge__VeriFast_wrapper(finish, parent_node, left_node) }
    }
}

impl<'a, K: 'a, V: 'a> BalancingContext<'a, K, V> {
    unsafe fn merge_tracking_child<A: std::alloc::Allocator>(
        self,
        alloc: A,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t, alloc, ?id) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?released) &*&
        context_merge_inputs(t, self, id, k, released, ?shape);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*& result == self.left_child &*&
        [released]lifetime_token(k) &*&
        match shape {
            MergeLengths(p, l, r, pc, lc, rc) =>
                merged_nodes(t, NonNull::new(self.parent.node.node.as_ptr() as *InternalNode<K,V>),
                    self.left_child.node, self.parent.node.height - 1, p - 1, l + 1 + r,
                    append(take(self.parent.idx + 1, pc), drop(self.parent.idx + 2, pc)), append(lc, rc))
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        context_merge_inputs(t, self, id, k, released, shape);
    @*/
    {
        unsafe { self.merge_child_production/*@::<'a,K,V,A>@*/(alloc) }
    }

    unsafe fn merge_child_production<A: std::alloc::Allocator>(
        self,
        /*@~mut@*/ alloc: A,
    ) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t, alloc, ?id) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?released) &*&
        context_merge_inputs(t, self, id, k, released, ?shape);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*& result == self.left_child &*&
        [released]lifetime_token(k) &*&
        match shape {
            MergeLengths(p, l, r, pc, lc, rc) =>
                merged_nodes(t, NonNull::new(self.parent.node.node.as_ptr() as *InternalNode<K,V>),
                    self.left_child.node, self.parent.node.height - 1, p - 1, l + 1 + r,
                    append(take(self.parent.idx + 1, pc), drop(self.parent.idx + 2, pc)), append(lc, rc))
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        context_merge_inputs(t, self, id, k, released, shape);
    @*/
    {
        //@ open exists(k);
        //@ open exists(released);
        //@ let context = self;
        //@ open context_merge_inputs(t, context, id, k, released, shape);
        //@ let parent = NonNull::new(self.parent.node.node.as_ptr() as *InternalNode<K,V>);
        //@ std::ptr::NonNull_Sized_as_ptr(self.parent.node.node);
        //@ std::ptr::NonNull_as_ptr_new(self.parent.node.node.as_ptr() as *InternalNode<K,V>);
        //@ std::ptr::NonNull_Sized_as_ptr(parent);
        //@ let left = self.left_child.node;
        //@ let right = self.right_child.node;
        //@ std::ptr::NonNull_Sized_as_ptr(left);
        //@ std::ptr::NonNull_Sized_as_ptr(right);
        //@ let parent_height = self.parent.node.height;
        //@ let index = self.parent.idx;
        //@ assert merge_inputs(t, parent, left, right, parent_height, index, id, k, released, ?parent_len, ?left_len, ?right_len_0, ?parent_children, ?left_children, ?right_children);
        //@ open merge_inputs(t, parent, left, right, parent_height, index, id, k, released, parent_len, left_len, right_len_0, parent_children, left_children, right_children);
        let Handle { node: mut parent_node, idx: parent_idx, .. } = self.parent;
        //@ let parent_ptr = &(*parent.as_ptr()).data;
        //@ assert parent_ptr == parent_node.node.as_ptr();
        //@ open owned_leaf_slots(t, parent_ptr, parent_len);
        //@ open leaf_slots(parent_ptr, parent_len, ?p_keys, ?p_vals);
        //@ let parent_view = precreate_ref(&parent_node);
        //@ init_ref_readonly(parent_view, 1/2);
        let old_parent_len = unsafe { parent_node.merge_len() };
        //@ end_ref_readonly(parent_view);
        //@ merge_fractions points_to(&parent_node, _);
        let mut left_node = self.left_child;
        //@ let left_ptr = left.as_ptr();
        //@ assert left_ptr == left_node.node.as_ptr();
        //@ open owned_leaf_slots(t, left_ptr, left_len);
        //@ open leaf_slots(left_ptr, left_len, ?l_keys, ?l_vals);
        //@ let left_view = precreate_ref(&left_node);
        //@ init_ref_readonly(left_view, 1/2);
        let old_left_len = unsafe { left_node.merge_len() };
        //@ end_ref_readonly(left_view);
        //@ merge_fractions points_to(&left_node, _);
        let mut right_node = self.right_child;
        //@ let right_ptr = right.as_ptr();
        //@ assert right_ptr == right_node.node.as_ptr();
        //@ open owned_leaf_slots(t, right_ptr, right_len_0);
        //@ open leaf_slots(right_ptr, right_len_0, ?r_keys, ?r_vals);
        //@ let right_view = precreate_ref(&right_node);
        //@ init_ref_readonly(right_view, 1/2);
        let right_len = unsafe { right_node.merge_len() };
        //@ end_ref_readonly(right_view);
        //@ merge_fractions points_to(&right_node, _);
        let new_left_len = old_left_len + 1 + right_len;
        /*@
        if new_left_len > CAPACITY {
            close leaf_slots(parent_ptr, parent_len, p_keys, p_vals);
            close owned_leaf_slots(t, parent_ptr, parent_len);
            close leaf_slots(left_ptr, left_len, l_keys, l_vals);
            close owned_leaf_slots(t, left_ptr, left_len);
            close leaf_slots(right_ptr, right_len, r_keys, r_vals);
            close owned_leaf_slots(t, right_ptr, right_len);
            close merge_inputs(t, parent, left, right, parent_height, index, id, k, released,
                parent_len, left_len, right_len, parent_children, left_children, right_children);
            close context_merge_inputs(t, context, id, k, released, shape);
            std::alloc::Allocator_to_own(alloc);
        }
        @*/
        assert!(new_left_len <= CAPACITY);
        //@ open balancing_edges(parent, parent_children, ?parent_slots);
        //@ split_linked_headers(parent_children, parent, 0, parent_idx);
        //@ drop_n_plus_one(parent_idx, parent_children);
        //@ open linked_headers(drop(parent_idx, parent_children), parent, parent_idx);
        //@ drop_n_plus_one(parent_idx + 1, parent_children);
        //@ open linked_headers(drop(parent_idx + 1, parent_children), parent, parent_idx + 1);
        //@ close leaf_without_len(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16), l_keys, l_vals);
        unsafe {
            *left_node.len_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/() = new_left_len as u16;
            //@ assert len_loan(left_ptr, ?slot, Option::Some(parent), MaybeUninit::new(parent_idx as u16), l_keys, l_vals);
            //@ end_len_loan(left_ptr, slot);
            //@ open leaf_without_len(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16), l_keys, l_vals);
            //@ open balancing_child_allocation(right, parent_height - 1, id, k, released);
            /*@
            if parent_height > 1 {
                let internal = right_ptr as *InternalNode<K,V>;
                open allocated_internal(internal, id, k, released);
                assert &(*internal).data == right_ptr;
            } else {
                open allocated_leaf(right_ptr, id, k, released);
            }
            @*/
            //@ close leaf_header(left_ptr, Option::Some(parent), MaybeUninit::new(parent_idx as u16));
            //@ close leaf_header(right_ptr, Option::Some(parent), MaybeUninit::new((parent_idx + 1) as u16));
            //@ close leaf_without_keys(parent_ptr, _, _, old_parent_len as u16, _);
            //@ close leaf_without_keys(left_ptr, _, _, new_left_len as u16, _);
            //@ close leaf_without_keys(right_ptr, _, _, right_len as u16, _);
            {
                //@ assert leaf_without_keys(parent_ptr, ?keys_p_parent, ?keys_p_idx, ?keys_p_len, ?keys_p_vals);
                //@ assert leaf_without_keys(left_ptr, ?keys_l_parent, ?keys_l_idx, ?keys_l_len, ?keys_l_vals);
                //@ assert leaf_without_keys(right_ptr, ?keys_r_parent, ?keys_r_idx, ?keys_r_len, ?keys_r_vals);
                //@ let keys_old_parent = take(old_parent_len, p_keys);
                //@ let keys_old_left = take(old_left_len, l_keys);
                //@ let keys_incoming = take(right_len, r_keys);
                //@ length_take(old_parent_len, p_keys);
                //@ length_take(old_left_len, l_keys);
                //@ length_take(right_len, r_keys);
                //@ nth_take_range(p_keys, old_parent_len, parent_idx);
                //@ split_slot_owners(t, keys_old_parent, parent_idx);
                //@ drop_n_plus_one(parent_idx, keys_old_parent);
                //@ open slot_owners(t, drop(parent_idx, keys_old_parent));
                unsafe {
                    let parent_key = slice_remove(
                        parent_node.key_area_prefix_mut/*@::<'a,K,V,marker::Internal,'a>@*/(..old_parent_len), parent_idx,
                    );
                    //@ assert keys_range_loan(parent_ptr, ?keys_active, 0, old_parent_len, keys_p_parent, keys_p_idx, keys_p_len, keys_p_vals, _, _);
                    //@ assert move_slice(keys_active as *MaybeUninit<K>, old_parent_len, ?keys_active_after);
                    //@ end_keys_range(parent_ptr, keys_active);
                    //@ let keys_surviving = append(take(parent_idx, keys_old_parent), drop(parent_idx + 1, keys_old_parent));
                    //@ join_slot_owners(t, take(parent_idx, keys_old_parent), drop(parent_idx + 1, keys_old_parent));
                    //@ length_take(parent_idx, keys_old_parent);
                    //@ length_drop(parent_idx + 1, keys_old_parent);
                    //@ append_assoc(take(parent_idx, keys_old_parent), drop(parent_idx + 1, keys_old_parent), drop(old_parent_len - 1, keys_old_parent));
                    //@ take_append_l(old_parent_len - 1, keys_surviving, drop(old_parent_len - 1, keys_old_parent));
                    //@ take_length(keys_surviving);
                    //@ length_append(keys_surviving, drop(old_parent_len - 1, keys_old_parent));
                    //@ length_drop(old_parent_len - 1, keys_old_parent);
                    //@ take_append_l(old_parent_len - 1, keys_active_after, drop(old_parent_len, p_keys));
                    //@ drop_append(old_parent_len, keys_active_after, drop(old_parent_len, p_keys));

                    left_node.key_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(old_left_len).write(parent_key);
                    //@ assert keys_slot_loan(left_ptr, ?keys_slot, old_left_len, keys_l_parent, keys_l_idx, keys_l_len, keys_l_vals, _, _);
                    //@ end_keys_slot(left_ptr, keys_slot);
                    //@ assert (*left_ptr).keys[..CAPACITY] |-> ?keys_left_with_entry;
                    //@ let keys_with_entry = append(keys_old_left, [MaybeUninit::new(parent_key)]);
                    //@ append_assoc(keys_old_left, [MaybeUninit::new(parent_key)], drop(old_left_len + 1, l_keys));
                    //@ take_append_l(old_left_len + 1, keys_with_entry, drop(old_left_len + 1, l_keys));
                    //@ take_length(keys_with_entry);

                    move_to_slice(
                        right_node.key_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(..right_len),
                        left_node.key_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(old_left_len + 1..new_left_len),
                    );
                    //@ assert keys_range_loan(right_ptr, ?keys_source, 0, right_len, keys_r_parent, keys_r_idx, keys_r_len, keys_r_vals, _, _);
                    //@ assert keys_range_loan(left_ptr, ?keys_destination, old_left_len + 1, new_left_len, keys_l_parent, keys_l_idx, keys_l_len, keys_l_vals, _, _);
                    //@ end_keys_range(right_ptr, keys_source);
                    //@ append_take_drop_n(r_keys, right_len);
                    //@ end_keys_range(left_ptr, keys_destination);
                    //@ close slot_owners::<K>(t, cons(MaybeUninit::new(parent_key), keys_incoming));
                    //@ join_slot_owners(t, keys_old_left, cons(MaybeUninit::new(parent_key), keys_incoming));
                    //@ let keys_merged = append(keys_old_left, cons(MaybeUninit::new(parent_key), keys_incoming));
                    //@ append_assoc(keys_with_entry, keys_incoming, drop(new_left_len, keys_left_with_entry));
                    //@ append_assoc(keys_old_left, [MaybeUninit::new(parent_key)], keys_incoming);
                    //@ take_append_l(new_left_len, keys_merged, drop(new_left_len, keys_left_with_entry));
                    //@ take_length(keys_merged);
                    //@ length_append(keys_with_entry, keys_incoming);
                    //@ drop_append(new_left_len, keys_merged, drop(new_left_len, keys_left_with_entry));
                    //@ drop_append(new_left_len, keys_with_entry, drop(old_left_len + 1, l_keys));
                    //@ drop_twice(right_len, old_left_len + 1, l_keys);
                }
            }
            //@ open leaf_without_keys(parent_ptr, _, _, old_parent_len as u16, _);
            //@ open leaf_without_keys(left_ptr, _, _, new_left_len as u16, _);
            //@ open leaf_without_keys(right_ptr, _, _, right_len as u16, _);
            //@ close leaf_without_vals(parent_ptr, _, _, old_parent_len as u16, _);
            //@ close leaf_without_vals(left_ptr, _, _, new_left_len as u16, _);
            //@ close leaf_without_vals(right_ptr, _, _, right_len as u16, _);
            {
                //@ assert leaf_without_vals(parent_ptr, ?vals_p_parent, ?vals_p_idx, ?vals_p_len, ?vals_p_keys);
                //@ assert leaf_without_vals(left_ptr, ?vals_l_parent, ?vals_l_idx, ?vals_l_len, ?vals_l_keys);
                //@ assert leaf_without_vals(right_ptr, ?vals_r_parent, ?vals_r_idx, ?vals_r_len, ?vals_r_keys);
                //@ let vals_old_parent = take(old_parent_len, p_vals);
                //@ let vals_old_left = take(old_left_len, l_vals);
                //@ let vals_incoming = take(right_len, r_vals);
                //@ length_take(old_parent_len, p_vals);
                //@ length_take(old_left_len, l_vals);
                //@ length_take(right_len, r_vals);
                //@ nth_take_range(p_vals, old_parent_len, parent_idx);
                //@ split_slot_owners(t, vals_old_parent, parent_idx);
                //@ drop_n_plus_one(parent_idx, vals_old_parent);
                //@ open slot_owners(t, drop(parent_idx, vals_old_parent));
                unsafe {
                    let parent_val = slice_remove(
                        parent_node.val_area_prefix_mut/*@::<'a,K,V,marker::Internal,'a>@*/(..old_parent_len), parent_idx,
                    );
                    //@ assert vals_range_loan(parent_ptr, ?vals_active, 0, old_parent_len, vals_p_parent, vals_p_idx, vals_p_len, vals_p_keys, _, _);
                    //@ assert move_slice(vals_active as *MaybeUninit<V>, old_parent_len, ?vals_active_after);
                    //@ end_vals_range(parent_ptr, vals_active);
                    //@ let vals_surviving = append(take(parent_idx, vals_old_parent), drop(parent_idx + 1, vals_old_parent));
                    //@ join_slot_owners(t, take(parent_idx, vals_old_parent), drop(parent_idx + 1, vals_old_parent));
                    //@ length_take(parent_idx, vals_old_parent);
                    //@ length_drop(parent_idx + 1, vals_old_parent);
                    //@ append_assoc(take(parent_idx, vals_old_parent), drop(parent_idx + 1, vals_old_parent), drop(old_parent_len - 1, vals_old_parent));
                    //@ take_append_l(old_parent_len - 1, vals_surviving, drop(old_parent_len - 1, vals_old_parent));
                    //@ take_length(vals_surviving);
                    //@ length_append(vals_surviving, drop(old_parent_len - 1, vals_old_parent));
                    //@ length_drop(old_parent_len - 1, vals_old_parent);
                    //@ take_append_l(old_parent_len - 1, vals_active_after, drop(old_parent_len, p_vals));
                    //@ drop_append(old_parent_len, vals_active_after, drop(old_parent_len, p_vals));

                    left_node.val_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(old_left_len).write(parent_val);
                    //@ assert vals_slot_loan(left_ptr, ?vals_slot, old_left_len, vals_l_parent, vals_l_idx, vals_l_len, vals_l_keys, _, _);
                    //@ end_vals_slot(left_ptr, vals_slot);
                    //@ assert (*left_ptr).vals[..CAPACITY] |-> ?vals_left_with_entry;
                    //@ let vals_with_entry = append(vals_old_left, [MaybeUninit::new(parent_val)]);
                    //@ append_assoc(vals_old_left, [MaybeUninit::new(parent_val)], drop(old_left_len + 1, l_vals));
                    //@ take_append_l(old_left_len + 1, vals_with_entry, drop(old_left_len + 1, l_vals));
                    //@ take_length(vals_with_entry);

                    move_to_slice(
                        right_node.val_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(..right_len),
                        left_node.val_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'a>@*/(old_left_len + 1..new_left_len),
                    );
                    //@ assert vals_range_loan(right_ptr, ?vals_source, 0, right_len, vals_r_parent, vals_r_idx, vals_r_len, vals_r_keys, _, _);
                    //@ assert vals_range_loan(left_ptr, ?vals_destination, old_left_len + 1, new_left_len, vals_l_parent, vals_l_idx, vals_l_len, vals_l_keys, _, _);
                    //@ end_vals_range(right_ptr, vals_source);
                    //@ append_take_drop_n(r_vals, right_len);
                    //@ end_vals_range(left_ptr, vals_destination);
                    //@ close slot_owners::<V>(t, cons(MaybeUninit::new(parent_val), vals_incoming));
                    //@ join_slot_owners(t, vals_old_left, cons(MaybeUninit::new(parent_val), vals_incoming));
                    //@ let vals_merged = append(vals_old_left, cons(MaybeUninit::new(parent_val), vals_incoming));
                    //@ append_assoc(vals_with_entry, vals_incoming, drop(new_left_len, vals_left_with_entry));
                    //@ append_assoc(vals_old_left, [MaybeUninit::new(parent_val)], vals_incoming);
                    //@ take_append_l(new_left_len, vals_merged, drop(new_left_len, vals_left_with_entry));
                    //@ take_length(vals_merged);
                    //@ length_append(vals_with_entry, vals_incoming);
                    //@ drop_append(new_left_len, vals_merged, drop(new_left_len, vals_left_with_entry));
                    //@ drop_append(new_left_len, vals_with_entry, drop(old_left_len + 1, l_vals));
                    //@ drop_twice(right_len, old_left_len + 1, l_vals);
                }
            }
            //@ open leaf_without_vals(parent_ptr, _, _, old_parent_len as u16, _);
            //@ open leaf_without_vals(left_ptr, _, _, new_left_len as u16, _);
            //@ open leaf_without_vals(right_ptr, _, _, right_len as u16, _);
            //@ open leaf_header(right_ptr, _, _);
            //@ open leaf_header(left_ptr, _, _);
            /*@
            if parent_height > 1 {
                close allocated_internal(right_ptr as *InternalNode<K,V>, id, k, released);
            } else {
                close allocated_leaf(right_ptr, id, k, released);
            }
            @*/
            //@ close balancing_child_allocation(right, parent_height - 1, id, k, released);
            //@ close linked_headers(drop(parent_idx + 1, parent_children), parent, parent_idx + 1);
            //@ close linked_headers(drop(parent_idx, parent_children), parent, parent_idx);
            //@ length_take(parent_idx, parent_children);
            //@ join_linked_headers(take(parent_idx, parent_children), drop(parent_idx, parent_children), parent, 0);
            //@ append_take_drop_n(parent_children, parent_idx);
            //@ close balancing_edges(parent, parent_children, parent_slots);
            //@ open leaf_header(parent_ptr, ?ancestor, ?ancestor_idx);
            //@ close leaf_without_len(parent_ptr, ancestor, ancestor_idx, _, _);
            {
                //@ assert balancing_edges(parent, parent_children, ?slots_before_removal);
                //@ assert leaf_without_len(parent_ptr, ancestor, ancestor_idx, ?parent_keys_for_relink, ?parent_vals_for_relink);
                    //@ open exists(parent);
                    //@ open balancing_edges(parent, parent_children, slots_before_removal);
                    //@ let parent_storage = parent.as_ptr();
                    //@ let prefix = take(parent_idx + 1, parent_children);
                    //@ let rest = drop(parent_idx + 2, parent_children);
                    //@ let removed = nth(parent_idx + 1, parent_children);
                    //@ split_linked_headers(parent_children, parent, 0, parent_idx + 1);
                    //@ drop_n_plus_one(parent_idx + 1, parent_children);
                    //@ open linked_headers(cons(removed, rest), parent, parent_idx + 1);
                    //@ forget_link_indices(rest, parent, parent_idx + 2);
                    //@ let parent_active_edges = initialized_edges(parent_children);
                    //@ nth_initialized_edge(parent_children, parent_idx + 1);
                    //@ std::ptr::close_NonNull_own(t, removed);
                    //@ produce_type_interp::<BoxedNode<K,V>>();
                    unsafe {
                        //@ nth_take_range(slots_before_removal, old_parent_len + 1, parent_idx + 1);
                        //@ open leaf_without_len(&(*parent_storage).data, ancestor, ancestor_idx, parent_keys_for_relink, parent_vals_for_relink);
                        //@ close_points_to(&(*parent_storage).data);
                        //@ close internal_without_edges(parent_storage, ?data);
                        slice_remove(
                            parent_node.edge_area_prefix_mut/*@::<'a,K,V,'a>@*/(..old_parent_len + 1), parent_idx + 1,
                        );
                        //@ assert edges_range_loan(parent_storage, ?removed_prefix, 0, old_parent_len + 1, data, _, _);
                        //@ end_edges_range(parent_storage, removed_prefix);
                        //@ open internal_without_edges(parent_storage, data);
                        //@ open_points_to(&(*parent_storage).data);
                        //@ close leaf_without_len(&(*parent_storage).data, ancestor, ancestor_idx, parent_keys_for_relink, parent_vals_for_relink);
                        //@ leak <BoxedNode<K,V>>.own(t, removed);
                        //@ std::ptr::open_NonNull_own(t, removed);
                        //@ leak type_interp::<BoxedNode<K,V>>();
                        //@ initialized_edge_split(parent_children, parent_idx + 1);
                        //@ initialized_edge_split(parent_children, parent_idx + 2);
                        //@ let parent_children_after = append(initialized_edges(prefix), initialized_edges(rest));
                        //@ let residual = drop(old_parent_len, parent_active_edges);
                        //@ append_assoc(initialized_edges(prefix), initialized_edges(rest), residual);
                        //@ initialized_edge_count(prefix);
                        //@ initialized_edge_count(rest);
                        //@ length_take(parent_idx + 1, parent_children);
                        //@ length_drop(parent_idx + 2, parent_children);
                // BEGIN_MERGE_PARENT_RELINK
                        //@ assert (*parent_storage).edges[..CAPACITY + 1] |-> ?new_edges;
                        //@ let parent_relink_before = initialized_edges(prefix);
                        //@ let tail = drop(old_parent_len + 1, slots_before_removal);
                        //@ append_assoc(parent_relink_before, append(initialized_edges(rest), residual), tail);
                        //@ append_assoc(initialized_edges(rest), residual, tail);
                        //@ close exists(parent);
                        //@ close exists(pair(parent_relink_before, append(residual, tail)));
                        parent_node.relink_range/*@::<'a,K,V,'a>@*/(parent_idx + 1..old_parent_len);
                        *parent_node.len_mut/*@::<'a,K,V,marker::Internal,'a>@*/() -= 1;
                        //@ assert len_loan(&(*parent_storage).data, ?parent_length_slot, ancestor, ancestor_idx, parent_keys_for_relink, parent_vals_for_relink);
                        //@ end_len_loan(&(*parent_storage).data, parent_length_slot);
                // END_MERGE_PARENT_RELINK
                        //@ take_append_l(parent_idx + 1, initialized_edges(prefix), initialized_edges(rest));
                        //@ take_length(initialized_edges(prefix));
                        //@ take_append_l(old_parent_len, parent_children_after, residual);
                        //@ take_append_l(old_parent_len, append(parent_children_after, residual), drop(old_parent_len + 1, slots_before_removal));
                        //@ join_linked_headers(prefix, rest, parent, 0);
                        //@ initialized_edges_append(prefix, rest);
                        //@ close balancing_edges(parent, append(prefix, rest), new_edges);
                    }
            }
            //@ open leaf_without_len(parent_ptr, ancestor, ancestor_idx, _, _);
            //@ close leaf_header(parent_ptr, ancestor, ancestor_idx);
            //@ close leaf_slots(parent_ptr, old_parent_len - 1, _, _);
            //@ close owned_leaf_slots(t, parent_ptr, old_parent_len - 1);
            //@ close leaf_slots(left_ptr, new_left_len, _, _);
            //@ close owned_leaf_slots(t, left_ptr, new_left_len);
            //@ open balancing_child_edges(left, parent_height - 1, left_len, left_children);
            //@ open balancing_child_edges(right, parent_height - 1, right_len, right_children);
            //@ open balancing_child_allocation(right, parent_height - 1, id, k, released);
            //@ let surviving = append(take(parent_idx + 1, parent_children), drop(parent_idx + 2, parent_children));
            if parent_node.height > 1 {
                let mut left_internal_node = left_node.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'a>@*/().cast_to_internal_unchecked/*@::<'a,K,V>@*/();
                let mut right_internal_node = right_node.cast_to_internal_unchecked/*@::<'a,K,V>@*/();
                //@ let left_internal = NonNull::new(left_internal_node.node.as_ptr() as *InternalNode<K,V>);
                //@ let right_internal = NonNull::new(right_internal_node.node.as_ptr() as *InternalNode<K,V>);
                //@ std::ptr::NonNull_as_ptr_new(left_internal_node.node.as_ptr() as *InternalNode<K,V>);
                //@ std::ptr::NonNull_Sized_as_ptr(left_internal);
                //@ std::ptr::NonNull_as_ptr_new(right_internal_node.node.as_ptr() as *InternalNode<K,V>);
                //@ std::ptr::NonNull_Sized_as_ptr(right_internal);
                //@ assert &(*left_internal.as_ptr()).data == left_ptr;
                //@ assert &(*right_internal.as_ptr()).data == right_ptr;
                //@ open owned_leaf_slots(t, left_ptr, new_left_len);
                //@ open leaf_slots(left_ptr, new_left_len, _, _);
                //@ open balancing_child_padding(left, parent_height - 1);
                //@ open allocated_internal(right_internal.as_ptr(), id, k, released);
                //@ open balancing_edges(parent, surviving, ?parent_edges);
                //@ let before_left = take(parent_idx + 1, parent_children);
                //@ let after_right = drop(parent_idx + 2, parent_children);
                //@ length_take(parent_idx + 1, parent_children);
                //@ length_drop(parent_idx + 2, parent_children);
                //@ length_append(before_left, after_right);
                //@ take_append_l(parent_idx + 1, before_left, after_right);
                //@ take_length(before_left);
                //@ nth_take_range(surviving, parent_idx + 1, parent_idx);
                //@ nth_take_range(parent_children, parent_idx + 1, parent_idx);
                //@ split_linked_headers(surviving, parent, 0, parent_idx);
                //@ drop_n_plus_one(parent_idx, surviving);
                //@ open linked_headers(drop(parent_idx, surviving), parent, parent_idx);
                //@ close_points_to(left_ptr);
                //@ close_points_to(right_ptr);
                //@ close internal_without_edges(left_internal.as_ptr(), ?left_data);
                //@ close internal_without_edges(right_internal.as_ptr(), ?right_data);
                {
                    //@ assert balancing_edges(left_internal, left_children, ?left_slots);
                    //@ assert balancing_edges(right_internal, right_children, ?right_slots);
                    //@ open exists(pair(left_internal, right_internal));
                    //@ open balancing_edges(left_internal, left_children, left_slots);
                    //@ open balancing_edges(right_internal, right_children, right_slots);
                    //@ forget_link_indices(right_children, right_internal, 0);
                    unsafe {
                        move_to_slice(
                            right_internal_node.edge_area_prefix_mut/*@::<'a,K,V,'a>@*/(..right_len + 1),
                            left_internal_node.edge_area_range_mut/*@::<'a,K,V,'a>@*/(old_left_len + 1..new_left_len + 1),
                        );
                        //@ assert edges_range_loan(right_internal.as_ptr(), ?edge_source, 0, right_len + 1, right_data, _, _);
                        //@ assert edges_range_loan(left_internal.as_ptr(), ?edge_destination, old_left_len + 1, new_left_len + 1, left_data, _, _);
                        //@ end_edges_range(right_internal.as_ptr(), edge_source);
                        //@ append_take_drop_n(right_slots, right_len + 1);
                        //@ end_edges_range(left_internal.as_ptr(), edge_destination);
                        //@ let before = take(old_left_len + 1, left_slots);
                        //@ let after_copy = drop(new_left_len + 1, left_slots);
                        //@ length_take(old_left_len + 1, left_slots);
                        //@ open internal_without_edges(left_internal.as_ptr(), left_data);
                        //@ open_points_to(&(*left_internal.as_ptr()).data);
                        //@ close exists(left_internal);
                        //@ close exists(pair(before, after_copy));
                        left_internal_node.relink_range/*@::<'a,K,V,'a>@*/(old_left_len + 1..new_left_len + 1);
                        //@ close_points_to(&(*left_internal.as_ptr()).data);
                        //@ close internal_without_edges(left_internal.as_ptr(), left_data);
                        //@ assert (*left_internal.as_ptr()).edges[..CAPACITY + 1] |-> ?merged_slots;
                        //@ append_assoc(before, initialized_edges(right_children), after_copy);
                        //@ let active = append(initialized_edges(left_children), initialized_edges(right_children));
                        //@ initialized_edge_count(left_children);
                        //@ initialized_edge_count(right_children);
                        //@ take_twice(left_slots, old_left_len + 1, new_left_len + 1);
                        //@ take_append_l(new_left_len + 1, active, drop(new_left_len + 1, left_slots));
                        //@ take_length(active);
                        //@ join_linked_headers(left_children, right_children, left_internal, 0);
                        //@ initialized_edges_append(left_children, right_children);
                        //@ close balancing_edges(left_internal, append(left_children, right_children), merged_slots);
                    }
                }
                //@ open internal_without_edges(left_internal.as_ptr(), left_data);
                //@ open_points_to(left_ptr);
                //@ close linked_headers(drop(parent_idx, surviving), parent, parent_idx);
                //@ length_take(parent_idx, surviving);
                //@ join_linked_headers(take(parent_idx, surviving), drop(parent_idx, surviving), parent, 0);
                //@ append_take_drop_n(surviving, parent_idx);
                //@ close balancing_edges(parent, surviving, parent_edges);
                //@ close leaf_slots(left_ptr, new_left_len, _, _);
                //@ close owned_leaf_slots(t, left_ptr, new_left_len);
                //@ close balancing_child_edges(left, parent_height - 1, new_left_len, append(left_children, right_children));
                //@ close balancing_child_padding(left, parent_height - 1);
                //@ close merged_nodes(t, parent, left, parent_height - 1, old_parent_len - 1, new_left_len, surviving, append(left_children, right_children));
                //@ open internal_without_edges(right_internal.as_ptr(), right_data);
                //@ open_points_to(right_ptr);
                //@ close_points_to(right_internal.as_ptr(), 1);
                //@ let target = right_internal.as_ptr();
                //@ points_to__limits(target);
                //@ assert close_points_to_at_lft_token(1, id.lft, target, ?allocation_fraction);
                //@ to_u8s_(target);
                //@ close_points_to_at_lft_token_to_close_u8s_at_lft_token(target);
                //@ close_array_at_lft_(target as *u8);
                //@ lifetime_token_trade_back(allocation_fraction, id.lft);
                //@ let view = precreate_ref(&alloc);
                //@ let call_lifetime = begin_lifetime();
                {
                    //@ let_lft 'call = call_lifetime;
                    //@ std::alloc::init_ref_Allocator_at_lifetime::<'call, A>(view);
                    //@ open_points_to(&right_internal_node);
                    //@ std::ptr::NonNull_Sized_as_ptr(right_internal_node.node);
                    //@ std::ptr::NonNull_as_ptr_new(right_internal_node.node.as_ptr() as *u8);
                    alloc.deallocate/*@::<A,'call>@*/(right_internal_node.node.cast(), std::alloc::Layout::new::<InternalNode<K,V>>());
                    //@ close_points_to(&right_internal_node);
                    //@ leak Allocator::<&'call A>(t, view, id);
                }
                //@ end_lifetime(call_lifetime);
                //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
            } else {
                //@ close balancing_child_edges(left, parent_height - 1, new_left_len, append(left_children, right_children));
                //@ close merged_nodes(t, parent, left, parent_height - 1, old_parent_len - 1, new_left_len, surviving, append(left_children, right_children));
                //@ open allocated_leaf(right_ptr, id, k, released);
                //@ close_points_to(right_ptr, 1);
                //@ let target = right.as_ptr();
                //@ points_to__limits(target);
                //@ assert close_points_to_at_lft_token(1, id.lft, target, ?allocation_fraction);
                //@ to_u8s_(target);
                //@ close_points_to_at_lft_token_to_close_u8s_at_lft_token(target);
                //@ close_array_at_lft_(target as *u8);
                //@ lifetime_token_trade_back(allocation_fraction, id.lft);
                //@ let view = precreate_ref(&alloc);
                //@ let call_lifetime = begin_lifetime();
                {
                    //@ let_lft 'call = call_lifetime;
                    //@ std::alloc::init_ref_Allocator_at_lifetime::<'call, A>(view);
                    //@ open_points_to(&right_node);
                    //@ std::ptr::NonNull_Sized_as_ptr(right_node.node);
                    //@ std::ptr::NonNull_as_ptr_new(right_node.node.as_ptr() as *u8);
                    alloc.deallocate/*@::<A,'call>@*/(right_node.node.cast(), std::alloc::Layout::new::<LeafNode<K,V>>());
                    //@ close_points_to(&right_node);
                    //@ leak Allocator::<&'call A>(t, view, id);
                }
                //@ end_lifetime(call_lifetime);
                //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
            }
        }
        //@ std::alloc::Allocator_to_own::<A>(alloc);
        unsafe { select_merged_child(parent_node, left_node) }
    }

    unsafe fn merge_tracking_child_edge<A: std::alloc::Allocator>(
        /*@~mut@*/ self,
        track_edge_idx: LeftOrRight<usize>,
        alloc: A,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t, alloc, ?id) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?released) &*&
        context_merge_inputs(t, self, id, k, released, ?shape) &*&
        match track_edge_idx {
            LeftOrRight::Left(idx) => 0 <= idx,
            LeftOrRight::Right(idx) => 0 <= idx
        };
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*& [released]lifetime_token(k) &*&
        result.node == self.left_child &*&
        match shape {
            MergeLengths(p, l, r, pc, lc, rc) =>
                merged_nodes(t, NonNull::new(self.parent.node.node.as_ptr() as *InternalNode<K,V>),
                    self.left_child.node, self.parent.node.height - 1, p - 1, l + 1 + r,
                    append(take(self.parent.idx + 1, pc), drop(self.parent.idx + 2, pc)), append(lc, rc)) &*&
                match track_edge_idx {
                    LeftOrRight::Left(idx) => result.idx == idx &*& idx <= l,
                    LeftOrRight::Right(idx) => result.idx == l + 1 + idx &*& idx <= r
                }
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        context_merge_inputs(t, self, id, k, released, shape);
    @*/
    {
        //@ open exists(k);
        //@ open exists(released);
        //@ assert context_merge_inputs(t, ?context, id, k, released, shape);
        //@ open context_merge_inputs(t, context, id, k, released, shape);
        //@ let parent = NonNull::new(context.parent.node.node.as_ptr() as *InternalNode<K,V>);
        //@ std::ptr::NonNull_Sized_as_ptr(context.parent.node.node);
        //@ std::ptr::NonNull_as_ptr_new(context.parent.node.node.as_ptr() as *InternalNode<K,V>);
        //@ std::ptr::NonNull_Sized_as_ptr(parent);
        //@ let left = context.left_child.node;
        //@ let right = context.right_child.node;
        //@ std::ptr::NonNull_Sized_as_ptr(left);
        //@ std::ptr::NonNull_Sized_as_ptr(right);
        //@ let height = context.parent.node.height;
        //@ let index = context.parent.idx;
        //@ assert merge_inputs(t, parent, left, right, height, index, id, k, released, ?p, ?l, ?r, ?pc, ?lc, ?rc);
        //@ open merge_inputs(t, parent, left, right, height, index, id, k, released, p, l, r, pc, lc, rc);
        //@ let left_ptr = left.as_ptr();
        //@ let right_ptr = right.as_ptr();
        //@ open owned_leaf_slots(t, left_ptr, l);
        //@ open leaf_slots(left_ptr, l, ?lk, ?lv);
        //@ open_points_to(&self);
        //@ let left_view = precreate_ref(&self.left_child);
        //@ init_ref_readonly(left_view, 1/2);
        let old_left_len = unsafe { self.left_child.merge_len() };
        //@ end_ref_readonly(left_view);
        //@ merge_fractions points_to(&self.left_child, _);
        //@ close leaf_slots(left_ptr, l, lk, lv);
        //@ close owned_leaf_slots(t, left_ptr, l);
        //@ open owned_leaf_slots(t, right_ptr, r);
        //@ open leaf_slots(right_ptr, r, ?rk, ?rv);
        //@ let right_view = precreate_ref(&self.right_child);
        //@ init_ref_readonly(right_view, 1/2);
        let right_len = unsafe { self.right_child.merge_len() };
        //@ end_ref_readonly(right_view);
        //@ merge_fractions points_to(&self.right_child, _);
        //@ close_points_to(&self);
        //@ close leaf_slots(right_ptr, r, rk, rv);
        //@ close owned_leaf_slots(t, right_ptr, r);
        //@ close merge_inputs(t, parent, left, right, height, index, id, k, released, p, l, r, pc, lc, rc);
        //@ close context_merge_inputs(t, context, id, k, released, shape);
        /*@
        if !(match track_edge_idx {
            LeftOrRight::Left(at) => at <= old_left_len,
            LeftOrRight::Right(at) => at <= right_len
        }) {
            std::alloc::Allocator_to_own(alloc);
        }
        @*/
        assert!(match track_edge_idx {
            LeftOrRight::Left(idx) => idx <= old_left_len,
            LeftOrRight::Right(idx) => idx <= right_len,
        });
        //@ close exists(k);
        //@ close exists(released);
        //@ open_points_to(&self);
        let merging = self;
        //@ close_points_to(&self);
        let child = unsafe { merging.merge_tracking_child/*@::<'a,K,V,A>@*/(alloc) };
        //@ let new_len = l + 1 + r;
        //@ let surviving = append(take(index + 1, pc), drop(index + 2, pc));
        //@ open merged_nodes(t, parent, left, height - 1, p - 1, new_len, surviving, append(lc, rc));
        //@ open owned_leaf_slots(t, left_ptr, new_len);
        //@ open leaf_slots(left_ptr, new_len, ?keys, ?vals);
        let edge = unsafe { finish_merge_tracking__VeriFast_wrapper/*@::<K,V,'a>@*/(child, old_left_len, track_edge_idx) };
        //@ close leaf_slots(left_ptr, new_len, keys, vals);
        //@ close owned_leaf_slots(t, left_ptr, new_len);
        //@ close merged_nodes(t, parent, left, height - 1, p - 1, new_len, surviving, append(lc, rc));
        edge
    }
}

unsafe fn select_merged_child<'a,K,V>(
    _parent: NodeRef<marker::Mut<'a>, K, V, marker::Internal>,
    child: NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
) -> NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>
//@ req true;
//@ ens result == child;
//@ on_unwind_ens false;
{
    child
}

// The separator replacement shared by the production steal methods.

// BEGIN_BORROW_INITIALIZED_SLOT
unsafe fn borrow_initialized_slot<'short,T>(slot: &'short mut MaybeUninit<T>) -> &'short mut T
//@ req *slot |-> ?bits &*& bits.inner() == some(?entry);
//@ ens *result |-> entry &*& ref_mut_end_token(result, slot as *T) &*& ref_origin(result) == ref_origin(slot as *T);
//@ on_unwind_ens false;
{
    let ptr = slot.as_mut_ptr();
    //@ open_MaybeUninit(slot);
    let lent = unsafe { &mut *ptr }; //~track_ref_creation
    lent
}
// END_BORROW_INITIALIZED_SLOT

/*@
pred initialized_array_slot<T>(
    base: *MaybeUninit<T>, index: usize, lent: *T,
    before: list<MaybeUninit<T>>, after: list<MaybeUninit<T>>
) =
    array(base,index,before) &*&
    array(base+index+1,CAPACITY-index-1,after) &*&
    exists::<*MaybeUninit<T>>(?slot) &*& ref_mut_end_token(slot,base+index) &*& ref_mut_end_token(lent,slot as *T);

lem end_initialized_array_slot<T>(base: *MaybeUninit<T>, index: usize, lent: *T)
    req 0 <= index &*& index < CAPACITY &*& initialized_array_slot(base,index,lent,?before,?after) &*& *lent |-> ?entry;
    ens base[..CAPACITY] |-> append(before,cons(MaybeUninit::new(entry),after));
{
    open initialized_array_slot(base,index,lent,before,after);
    open exists::<*MaybeUninit<T>>(?slot);
    end_ref_mut(lent);
    std::mem::close_MaybeUninit(slot);
    end_ref_mut(slot);
    close array(base+index,1,[MaybeUninit::new(entry)]);
    array_join(base+index);
    array_join(base);
}
@*/

/*@
fix replace_slot<T>(index: usize, entry: T, slots: list<T>) -> list<T> {
    append(take(index,slots),cons(entry,drop(index+1,slots)))
}
@*/

impl<'a, K:'a, V:'a, NodeType> Handle<NodeRef<marker::Mut<'a>,K,V,NodeType>,marker::KV> {
    unsafe fn replace_kv_production<'short>(&'short mut self, k:K, v:V) -> (K,V)
    /*@
    req *self |-> ?incoming &*& leaf_header(incoming.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(incoming.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= incoming.idx &*& incoming.idx < len &*&
        nth(incoming.idx,keys).inner() == some(?old_key) &*& nth(incoming.idx,vals).inner() == some(?old_val);
    @*/
    /*@
    ens *self |-> incoming &*& leaf_header(incoming.node.node.as_ptr(),parent,parent_idx) &*&
        leaf_slots(incoming.node.node.as_ptr(),len,replace_slot(incoming.idx,MaybeUninit::new(k),keys),replace_slot(incoming.idx,MaybeUninit::new(v),vals)) &*&
        result.0 == old_key &*& result.1 == old_val;
    @*/
    //@ on_unwind_ens false;
    {
        //@ let node = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open leaf_slots(node,len,keys,vals);
        //@ open_points_to(self);
        //@ let view = precreate_ref(&(*self).node);
        //@ init_ref_readonly(view,1/2);
        debug_assert!(self.idx < self.node.merge_len());
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&(*self).node, _);
        //@ open leaf_header(node,parent,parent_idx);
        //@ close_points_to(node);
        let leaf = unsafe { self.node.as_leaf_mut/*@::<'a,K,V,NodeType,'short>@*/() }; //~track_ref_creation
        //@ open_points_to(leaf);
        //@ close_points_to(&(*leaf).keys);
        let key_slot = unsafe {
            <[MaybeUninit<K>]>::get_unchecked_mut(
                {
                    let key_array = &mut leaf.keys; //~track_ref_creation
                    let slice: &mut [MaybeUninit<K>] = key_array;
                    //@ open_points_to(key_array);
                    //@ let key_base = key_array as *MaybeUninit<K>;
                    //@ array_split(key_base,index);
                    //@ array_split(key_base+index,1);
                    //@ open array(key_base+index,1,_);
                    //@ open array(key_base+index+1,0,_);
                    //@ nth_drop(0,index,keys);
                    //@ drop_twice(1,index,keys);
                    slice
                },
                self.idx,
            )
        };
        let key = unsafe { borrow_initialized_slot(key_slot) };
        //@ close exists::<*MaybeUninit<K>>(key_slot);
        //@ close initialized_array_slot(key_base,index,key,take(index,keys),drop(index+1,keys));
        //@ close_points_to(&(*leaf).vals);
        let val_slot = unsafe {
            <[MaybeUninit<V>]>::get_unchecked_mut(
                {
                    let val_array = &mut leaf.vals; //~track_ref_creation
                    let slice: &mut [MaybeUninit<V>] = val_array;
                    //@ open_points_to(val_array);
                    //@ let val_base = val_array as *MaybeUninit<V>;
                    //@ array_split(val_base,index);
                    //@ array_split(val_base+index,1);
                    //@ open array(val_base+index,1,_);
                    //@ open array(val_base+index+1,0,_);
                    //@ nth_drop(0,index,vals);
                    //@ drop_twice(1,index,vals);
                    slice
                },
                self.idx,
            )
        };
        let val = unsafe { borrow_initialized_slot(val_slot) };
        //@ close exists::<*MaybeUninit<V>>(val_slot);
        //@ close initialized_array_slot(val_base,index,val,take(index,vals),drop(index+1,vals));
        let result = (std::mem::replace(key,k), std::mem::replace(val,v));
        //@ end_initialized_array_slot(key_base,index,key);
        //@ close_points_to(key_array);
        //@ end_ref_mut(key_array);
        //@ open_points_to(&(*leaf).keys);
        //@ end_initialized_array_slot(val_base,index,val);
        //@ close_points_to(val_array);
        //@ end_ref_mut(val_array);
        //@ open_points_to(&(*leaf).vals);
        //@ close_points_to(leaf);
        //@ end_ref_mut(leaf);
        //@ assert ref_mut_end_token(?receiver,&(*self).node);
        //@ end_ref_mut(receiver);
        //@ open_points_to(node);
        //@ close leaf_header(node,parent,parent_idx);
        //@ close leaf_slots(node,len,replace_slot(index,MaybeUninit::new(k),keys),replace_slot(index,MaybeUninit::new(v),vals));
        //@ close_points_to(self);
        result
    }
}

/*@
lem open_slot_owner<T>(t: thread_id_t, slots: list<MaybeUninit<T>>, len: usize, idx: usize)
    req 0 <= idx &*& idx < len &*& len <= length(slots) &*& slot_owners(t,take(len,slots));
    ens slot_owners(t,take(idx,slots)) &*& slot_owners(t,drop(idx+1,take(len,slots))) &*&
        nth(idx,slots).inner() == some(?value) &*& nth(idx,slots) == MaybeUninit::new(value) &*& <T>.own(t,value);
{
    let live = take(len,slots);
    length_take(len,slots);
    split_slot_owners(t,live,idx);
    take_twice(slots,idx,len);
    drop_n_plus_one(idx,live);
    drop_twice(1,idx,live);
    open slot_owners(t,drop(idx,live));
    nth_take_range(slots,len,idx);
}

lem restore_slot_owner<T>(t: thread_id_t, slots: list<MaybeUninit<T>>, len: usize, idx: usize, value: T)
    req 0 <= idx &*& idx < len &*& len <= length(slots) &*&
        slot_owners(t,take(idx,slots)) &*& slot_owners(t,drop(idx+1,take(len,slots))) &*& <T>.own(t,value);
    ens slot_owners(t,take(len,replace_slot(idx,MaybeUninit::new(value),slots)));
{
    let head = take(idx,slots);
    let middle = [MaybeUninit::new(value)];
    let tail = drop(idx+1,take(len,slots));
    take_after_drop(slots,idx+1,len-idx-1);
    length_take(idx,slots);
    length_append(head,middle);
    append_assoc(head,middle,drop(idx+1,slots));
    take_append(len,append(head,middle),drop(idx+1,slots));
    close slot_owners::<T>(t,nil);
    close slot_owners(t,middle);
    join_slot_owners(t,head,middle);
    join_slot_owners(t,append(head,middle),tail);
}

lem join_stolen_prefix<T>(
    t: thread_id_t, l: list<MaybeUninit<T>>, r: list<MaybeUninit<T>>,
    shifted: list<MaybeUninit<T>>, copied: list<MaybeUninit<T>>, written: list<MaybeUninit<T>>,
    left_len: usize, right_len: usize, count: usize, saved: T
)
    req 0 < count &*& count <= left_len &*& left_len <= length(l) &*&
        0 <= right_len &*& right_len+count <= length(r) &*&
        shifted == append(take(count,take(right_len+count,r)),append(take(right_len,r),drop(right_len+count,r))) &*&
        copied == append(take(count-1,drop(left_len-count+1,l)),drop(count-1,shifted)) &*&
        written == replace_slot(count-1,MaybeUninit::new(saved),copied) &*&
        slot_owners(t,drop(left_len-count+1,take(left_len,l))) &*&
        slot_owners(t,take(right_len,r)) &*& <T>.own(t,saved);
    ens slot_owners(t,take(right_len+count,written));
{
    let stolen = take(count-1,drop(left_len-count+1,l));
    let kept = take(right_len,r);
    let prefix = take(count,take(right_len+count,r));
    let tail = drop(right_len+count,r);
    let separator = [MaybeUninit::new(saved)];
    length_take(right_len+count,r);
    length_take(count,take(right_len+count,r));
    take_after_drop(l,left_len-count+1,count-1);
    length_drop(left_len-count+1,l);
    length_take(count-1,drop(left_len-count+1,l));
    take_append_l(count-1,stolen,drop(count-1,shifted));
    take_length(stolen);
    drop_append(count,stolen,drop(count-1,shifted));
    drop_twice(1,count-1,shifted);
    drop_append(count,prefix,append(kept,tail));
    drop_0(append(kept,tail));
    append_assoc(stolen,separator,append(kept,tail));
    append_assoc(append(stolen,separator),kept,tail);
    length_take(right_len,r);
    length_append(stolen,separator);
    length_append(append(stolen,separator),kept);
    take_append_l(right_len+count,append(append(stolen,separator),kept),tail);
    take_length(append(append(stolen,separator),kept));
    close slot_owners::<T>(t,nil);
    close slot_owners(t,separator);
    join_slot_owners(t,stolen,separator);
    join_slot_owners(t,append(stolen,separator),kept);
}

lem join_right_steal<T>(
    t: thread_id_t, l: list<MaybeUninit<T>>, r: list<MaybeUninit<T>>,
    written: list<MaybeUninit<T>>, copied: list<MaybeUninit<T>>, shifted: list<MaybeUninit<T>>,
    left_len: usize, right_len: usize, count: usize, saved: T
)
    req 0 < count &*& count <= right_len &*& right_len <= length(r) &*&
        0 <= left_len &*& left_len+count <= length(l) &*&
        written == replace_slot(left_len,MaybeUninit::new(saved),l) &*&
        copied == append(take(left_len+1,written),append(take(count-1,r),drop(left_len+count,written))) &*&
        shifted == append(append(drop(count,take(right_len,r)),drop(right_len-count,take(right_len,r))),drop(right_len,r)) &*&
        slot_owners(t,take(count-1,take(right_len,r))) &*& slot_owners(t,drop(count,take(right_len,r))) &*&
        slot_owners(t,take(left_len,l)) &*& <T>.own(t,saved);
    ens slot_owners(t,take(left_len+count,copied)) &*& slot_owners(t,take(right_len-count,shifted));
{
    let kept_left = take(left_len,l);
    let separator = [MaybeUninit::new(saved)];
    let left_head = append(kept_left,separator);
    let stolen = take(count-1,r);
    let kept_right = drop(count,take(right_len,r));
    length_take(left_len,l);
    length_append(kept_left,separator);
    append_assoc(kept_left,separator,drop(left_len+1,l));
    assert written == append(left_head,drop(left_len+1,l));
    take_append_l(left_len+1,left_head,drop(left_len+1,l));
    take_length(left_head);
    assert take(left_len+1,written) == left_head;
    take_twice(r,count-1,right_len);
    length_take(count-1,r);
    append_assoc(left_head,stolen,drop(left_len+count,written));
    length_append(left_head,stolen);
    take_append_l(left_len+count,append(left_head,stolen),drop(left_len+count,written));
    take_length(append(left_head,stolen));
    close slot_owners::<T>(t,nil);
    close slot_owners(t,separator);
    join_slot_owners(t,kept_left,separator);
    join_slot_owners(t,left_head,stolen);
    length_take(right_len,r);
    length_drop(count,take(right_len,r));
    append_assoc(kept_right,drop(right_len-count,take(right_len,r)),drop(right_len,r));
    take_append_l(right_len-count,kept_right,append(drop(right_len-count,take(right_len,r)),drop(right_len,r)));
    take_length(kept_right);
}
@*/

impl<'a, K: 'a, V: 'a> BalancingContext<'a, K, V> {
    unsafe fn bulk_steal_left_production<'short>(&'short mut self, count: usize)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& *self |-> ?incoming &*&
        leaf_header(incoming.parent.node.node.as_ptr(),?parent_parent,?parent_index) &*&
        owned_leaf_slots(t,incoming.parent.node.node.as_ptr(),?parent_len) &*&
        0 <= incoming.parent.idx &*& incoming.parent.idx < parent_len &*&
        leaf_header(incoming.left_child.node.as_ptr(),?left_parent,?left_index) &*&
        leaf_header(incoming.right_child.node.as_ptr(),?right_parent,?right_index) &*&
        owned_leaf_slots(t,incoming.left_child.node.as_ptr(),?left_len) &*&
        owned_leaf_slots(t,incoming.right_child.node.as_ptr(),?right_len) &*&
        0 < count &*& count <= left_len &*& right_len + count <= CAPACITY
        &*& incoming.left_child.height == incoming.right_child.height
        &*& 0 <= incoming.left_child.height &*& incoming.left_child.height <= usize::MAX
        &*& balancing_child_padding(incoming.left_child.node,incoming.left_child.height)
        &*& balancing_child_padding(incoming.right_child.node,incoming.right_child.height)
        &*& balancing_child_edges(incoming.left_child.node,incoming.left_child.height,left_len,?left_children)
        &*& balancing_child_edges(incoming.right_child.node,incoming.right_child.height,right_len,?right_children);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& *self |-> incoming &*&
        leaf_header(incoming.parent.node.node.as_ptr(),parent_parent,parent_index) &*&
        owned_leaf_slots(t,incoming.parent.node.node.as_ptr(),parent_len) &*&
        leaf_header(incoming.left_child.node.as_ptr(),left_parent,left_index) &*&
        leaf_header(incoming.right_child.node.as_ptr(),right_parent,right_index) &*&
        owned_leaf_slots(t,incoming.left_child.node.as_ptr(),left_len - count) &*&
        owned_leaf_slots(t,incoming.right_child.node.as_ptr(),right_len + count)
        &*& balancing_child_padding(incoming.left_child.node,incoming.left_child.height)
        &*& balancing_child_padding(incoming.right_child.node,incoming.right_child.height)
        &*& balancing_child_edges(incoming.left_child.node,incoming.left_child.height,left_len - count,take(left_len-count+1,left_children))
        &*& balancing_child_edges(incoming.right_child.node,incoming.right_child.height,right_len + count,append(drop(left_len-count+1,left_children),right_children));
    @*/
    //@ on_unwind_ens false;
    {
        assert!(count > 0);
        //@ let left = incoming.left_child.node.as_ptr();
        //@ let right = incoming.right_child.node.as_ptr();
        //@ open_points_to(self);
        //@ close_points_to(&(*self).left_child);
        let left_node = &mut self.left_child; //~track_ref_creation
        //@ open owned_leaf_slots(t,left,left_len);
        //@ open leaf_slots(left,left_len,?left_keys,?left_vals);
        //@ let left_view = precreate_ref(left_node);
        //@ init_ref_readonly(left_view,1/2);
        let old_left_len = unsafe { left_node.merge_len() };
        //@ end_ref_readonly(left_view);
        //@ merge_fractions points_to(left_node, _);

        //@ close_points_to(&(*self).right_child);
        let right_node = &mut self.right_child; //~track_ref_creation
        //@ open owned_leaf_slots(t,right,right_len);
        //@ open leaf_slots(right,right_len,?right_keys,?right_vals);
        //@ let right_view = precreate_ref(right_node);
        //@ init_ref_readonly(right_view,1/2);
        let old_right_len = unsafe { right_node.merge_len() };
        //@ end_ref_readonly(right_view);
        //@ merge_fractions points_to(right_node, _);
        assert!(old_right_len + count <= CAPACITY);
        assert!(old_left_len >= count);

        let new_left_len = old_left_len - count;
        let new_right_len = old_right_len + count;
        //@ open leaf_header(left,left_parent,left_index);
        //@ close leaf_without_len(left,left_parent,left_index,left_keys,left_vals);
        *left_node.len_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/() = new_left_len as u16;
        //@ assert len_loan(left,?left_mut,left_parent,left_index,left_keys,left_vals);
        //@ end_len_loan(left,left_mut);
        //@ open leaf_without_len(left,left_parent,left_index,left_keys,left_vals);
        //@ close leaf_header(left,left_parent,left_index);
        //@ close leaf_slots(left,new_left_len,left_keys,left_vals);
        //@ open leaf_header(right,right_parent,right_index);
        //@ close leaf_without_len(right,right_parent,right_index,right_keys,right_vals);
        *right_node.len_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/() = new_right_len as u16;
        //@ assert len_loan(right,?right_mut,right_parent,right_index,right_keys,right_vals);
        //@ end_len_loan(right,right_mut);
        //@ open leaf_without_len(right,right_parent,right_index,right_keys,right_vals);
        //@ close leaf_header(right,right_parent,right_index);
        //@ close leaf_slots(right,new_right_len,right_keys,right_vals);
        //@ open leaf_slots(left,new_left_len,left_keys,left_vals);
        //@ open leaf_slots(right,new_right_len,right_keys,right_vals);
        //@ assert length(left_keys) == CAPACITY;
        //@ assert length(left_vals) == CAPACITY;
        //@ assert length(right_keys) == CAPACITY;
        //@ assert length(right_vals) == CAPACITY;
        {
            //@ close leaf_without_keys(right,right_parent,right_index,new_right_len as u16,right_vals);
            slice_shr(right_node.key_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..new_right_len), count);
            //@ assert keys_range_loan(right,?keys_shift,0,new_right_len,right_parent,right_index,new_right_len as u16,right_vals,_,_);
            //@ end_keys_range(right,keys_shift);
            //@ open leaf_without_keys(right,right_parent,right_index,new_right_len as u16,right_vals);
            //@ take_0(right_keys);
            //@ drop_0(right_keys);
            //@ take_twice(right_keys,old_right_len,new_right_len);
            //@ length_take(new_right_len,right_keys);
            //@ length_take(count,take(new_right_len,right_keys));
            //@ append_assoc(take(count,take(new_right_len,right_keys)),take(old_right_len,right_keys),drop(new_right_len,right_keys));
            //@ drop_append(count,take(count,take(new_right_len,right_keys)),append(take(old_right_len,right_keys),drop(new_right_len,right_keys)));
            //@ drop_0(append(take(old_right_len,right_keys),drop(new_right_len,right_keys)));
            //@ assert (*right).keys[..CAPACITY] |-> ?shifted_keys;
            //@ close leaf_without_vals(right,right_parent,right_index,new_right_len as u16,shifted_keys);
            slice_shr(right_node.val_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..new_right_len), count);
            //@ assert vals_range_loan(right,?vals_shift,0,new_right_len,right_parent,right_index,new_right_len as u16,shifted_keys,_,_);
            //@ end_vals_range(right,vals_shift);
            //@ open leaf_without_vals(right,right_parent,right_index,new_right_len as u16,shifted_keys);
            //@ take_0(right_vals);
            //@ drop_0(right_vals);
            //@ take_twice(right_vals,old_right_len,new_right_len);
            //@ length_take(new_right_len,right_vals);
            //@ length_take(count,take(new_right_len,right_vals));
            //@ append_assoc(take(count,take(new_right_len,right_vals)),take(old_right_len,right_vals),drop(new_right_len,right_vals));
            //@ drop_append(count,take(count,take(new_right_len,right_vals)),append(take(old_right_len,right_vals),drop(new_right_len,right_vals)));
            //@ drop_0(append(take(old_right_len,right_vals),drop(new_right_len,right_vals)));
            //@ assert (*right).vals[..CAPACITY] |-> ?shifted_vals;
            //@ close leaf_without_keys(left,left_parent,left_index,new_left_len as u16,left_vals);
            //@ close leaf_without_keys(right,right_parent,right_index,new_right_len as u16,shifted_vals);
            move_to_slice(
                left_node.key_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(new_left_len + 1..old_left_len),
                right_node.key_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..count - 1),
            );
            //@ assert keys_range_loan(left,?keys_source,new_left_len+1,old_left_len,left_parent,left_index,new_left_len as u16,left_vals,_,_);
            //@ end_keys_range(left,keys_source);
            //@ open leaf_without_keys(left,left_parent,left_index,new_left_len as u16,left_vals);
            //@ assert keys_range_loan(right,?keys_dest,0,count-1,right_parent,right_index,new_right_len as u16,shifted_vals,_,_);
            //@ end_keys_range(right,keys_dest);
            //@ open leaf_without_keys(right,right_parent,right_index,new_right_len as u16,shifted_vals);
            //@ take_0(left_keys);
            //@ drop_0(left_keys);
            //@ take_after_drop(left_keys,new_left_len+1,count-1);
            //@ take_twice(left_keys,new_left_len+1,old_left_len);
            //@ append_take_drop_n(take(old_left_len,left_keys),new_left_len+1);
            //@ append_assoc(take(new_left_len+1,left_keys),take(count-1,drop(new_left_len+1,left_keys)),drop(old_left_len,left_keys));
            //@ append_take_drop_n(left_keys,old_left_len);
            //@ assert (*left).keys[..CAPACITY] |-> left_keys;
            //@ take_0(shifted_keys);
            //@ drop_0(left_keys);
            //@ assert (*right).keys[..CAPACITY] |-> ?copied_keys;
            //@ close leaf_without_vals(left,left_parent,left_index,new_left_len as u16,left_keys);
            //@ close leaf_without_vals(right,right_parent,right_index,new_right_len as u16,copied_keys);
            move_to_slice(
                left_node.val_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(new_left_len + 1..old_left_len),
                right_node.val_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..count - 1),
            );
            //@ assert vals_range_loan(left,?vals_source,new_left_len+1,old_left_len,left_parent,left_index,new_left_len as u16,left_keys,_,_);
            //@ end_vals_range(left,vals_source);
            //@ open leaf_without_vals(left,left_parent,left_index,new_left_len as u16,left_keys);
            //@ assert vals_range_loan(right,?vals_dest,0,count-1,right_parent,right_index,new_right_len as u16,copied_keys,_,_);
            //@ end_vals_range(right,vals_dest);
            //@ open leaf_without_vals(right,right_parent,right_index,new_right_len as u16,copied_keys);
            //@ take_0(left_vals);
            //@ drop_0(left_vals);
            //@ take_after_drop(left_vals,new_left_len+1,count-1);
            //@ take_twice(left_vals,new_left_len+1,old_left_len);
            //@ append_take_drop_n(take(old_left_len,left_vals),new_left_len+1);
            //@ append_assoc(take(new_left_len+1,left_vals),take(count-1,drop(new_left_len+1,left_vals)),drop(old_left_len,left_vals));
            //@ append_take_drop_n(left_vals,old_left_len);
            //@ assert (*left).vals[..CAPACITY] |-> left_vals;
            //@ take_0(shifted_vals);
            //@ drop_0(left_vals);
            //@ assert (*right).vals[..CAPACITY] |-> ?copied_vals;
            //@ let original_keys = take(old_left_len,left_keys);
            //@ length_take(old_left_len,left_keys);
            //@ split_slot_owners(t,original_keys,new_left_len);
            //@ drop_n_plus_one(new_left_len,original_keys);
            //@ open slot_owners(t,drop(new_left_len,original_keys));
            //@ nth_take_range(left_keys,old_left_len,new_left_len);
            //@ close leaf_without_keys(left,left_parent,left_index,new_left_len as u16,left_vals);
            let donated_keys_slot = left_node.key_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(new_left_len);
            //@ assert keys_slot_loan(left,donated_keys_slot,new_left_len,left_parent,left_index,new_left_len as u16,left_vals,_,_);
            //@ let keys_view = precreate_ref(donated_keys_slot);
            //@ init_ref_readonly(keys_view,1/2);
            let k = donated_keys_slot.assume_init_read();
            //@ end_ref_readonly(keys_view);
            //@ merge_fractions points_to(donated_keys_slot, _);
            //@ end_keys_slot(left,donated_keys_slot);
            //@ open leaf_without_keys(left,left_parent,left_index,new_left_len as u16,left_vals);
            //@ nth_at_partition(left_keys,new_left_len);
            //@ assert (*left).keys[..CAPACITY] |-> left_keys;
            //@ let donation_keys = k;
            //@ let original_vals = take(old_left_len,left_vals);
            //@ length_take(old_left_len,left_vals);
            //@ split_slot_owners(t,original_vals,new_left_len);
            //@ drop_n_plus_one(new_left_len,original_vals);
            //@ open slot_owners(t,drop(new_left_len,original_vals));
            //@ nth_take_range(left_vals,old_left_len,new_left_len);
            //@ close leaf_without_vals(left,left_parent,left_index,new_left_len as u16,left_keys);
            let donated_vals_slot = left_node.val_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(new_left_len);
            //@ assert vals_slot_loan(left,donated_vals_slot,new_left_len,left_parent,left_index,new_left_len as u16,left_keys,_,_);
            //@ let vals_view = precreate_ref(donated_vals_slot);
            //@ init_ref_readonly(vals_view,1/2);
            let v = donated_vals_slot.assume_init_read();
            //@ end_ref_readonly(vals_view);
            //@ merge_fractions points_to(donated_vals_slot, _);
            //@ end_vals_slot(left,donated_vals_slot);
            //@ open leaf_without_vals(left,left_parent,left_index,new_left_len as u16,left_keys);
            //@ nth_at_partition(left_vals,new_left_len);
            //@ assert (*left).vals[..CAPACITY] |-> left_vals;
            //@ let donation_vals = v;
            //@ let parent = incoming.parent.node.node.as_ptr();
            //@ let separator = incoming.parent.idx;
            //@ open owned_leaf_slots(t,parent,parent_len);
            //@ assert leaf_slots(parent,parent_len,?parent_keys,?parent_vals);
            //@ open leaf_slots(parent,parent_len,parent_keys,parent_vals);
            //@ open_slot_owner(t,parent_keys,parent_len,separator);
            //@ open_slot_owner(t,parent_vals,parent_len,separator);
            //@ close leaf_slots(parent,parent_len,parent_keys,parent_vals);
            //@ close_points_to(&(*self).parent);
            let (separator_key, separator_value) = self.parent.replace_kv_production/*@::<'a,K,V,marker::Internal,'short>@*/(k, v); //~track_ref_creation
            //@ assert ref_mut_end_token(?parent_view,&(*self).parent);
            //@ end_ref_mut(parent_view);
            //@ open_points_to(&(*self).parent);
            //@ assert leaf_slots(parent,parent_len,?replaced_keys,?replaced_vals);
            //@ restore_slot_owner(t,parent_keys,parent_len,separator,donation_keys);
            //@ restore_slot_owner(t,parent_vals,parent_len,separator,donation_vals);
            //@ close owned_leaf_slots(t,parent,parent_len);
            //@ close leaf_without_keys(right,right_parent,right_index,new_right_len as u16,copied_vals);
            right_node.key_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(count - 1).write(separator_key);
            //@ assert keys_slot_loan(right,?recipient_keys_slot,count - 1,right_parent,right_index,new_right_len as u16,copied_vals,_,_);
            //@ end_keys_slot(right,recipient_keys_slot);
            //@ open leaf_without_keys(right,right_parent,right_index,new_right_len as u16,copied_vals);
            //@ assert (*right).keys[..CAPACITY] |-> ?written_keys;
            //@ close leaf_without_vals(right,right_parent,right_index,new_right_len as u16,written_keys);
            right_node.val_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(count - 1).write(separator_value);
            //@ assert vals_slot_loan(right,?recipient_vals_slot,count - 1,right_parent,right_index,new_right_len as u16,written_keys,_,_);
            //@ end_vals_slot(right,recipient_vals_slot);
            //@ open leaf_without_vals(right,right_parent,right_index,new_right_len as u16,written_keys);
            //@ assert (*right).vals[..CAPACITY] |-> ?written_vals;
            //@ take_twice(left_keys,new_left_len,old_left_len);
            //@ take_after_drop(left_keys,new_left_len+1,count-1);
            //@ drop_twice(1,new_left_len,original_keys);
            //@ join_stolen_prefix(t,left_keys,right_keys,shifted_keys,copied_keys,written_keys,old_left_len,old_right_len,count,separator_key);
            //@ take_twice(left_vals,new_left_len,old_left_len);
            //@ take_after_drop(left_vals,new_left_len+1,count-1);
            //@ drop_twice(1,new_left_len,original_vals);
            //@ join_stolen_prefix(t,left_vals,right_vals,shifted_vals,copied_vals,written_vals,old_left_len,old_right_len,count,separator_value);
        }
        //@ close leaf_slots(left,new_left_len,left_keys,left_vals);
        //@ close leaf_slots(right,new_right_len,written_keys,written_vals);
        //@ close owned_leaf_slots(t,left,new_left_len);
        //@ close owned_leaf_slots(t,right,new_right_len);
        //@ let height = incoming.left_child.height;
        //@ open balancing_child_edges(incoming.left_child.node,height,left_len,left_children);
        //@ open balancing_child_edges(incoming.right_child.node,height,right_len,right_children);
        match (
            left_node.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'short>@*/().force/*@::<marker::Mut<'short>,K,V>@*/(),
            right_node.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'short>@*/().force/*@::<marker::Mut<'short>,K,V>@*/(),
        ) {
            (ForceResult::Internal(mut left_internal), ForceResult::Internal(mut right_internal)) => {
                //@ let left_edges = NonNull::new(left as *InternalNode<K,V>);
                //@ let right_edges = NonNull::new(right as *InternalNode<K,V>);
                //@ std::ptr::NonNull_as_ptr_new(left as *InternalNode<K,V>);
                //@ std::ptr::NonNull_as_ptr_new(right as *InternalNode<K,V>);
                //@ std::ptr::NonNull_Sized_as_ptr(left_edges);
                //@ std::ptr::NonNull_Sized_as_ptr(right_edges);
                //@ assert &(*left_edges.as_ptr()).data == left;
                //@ assert &(*right_edges.as_ptr()).data == right;
                //@ open owned_leaf_slots(t,left,new_left_len);
                //@ open owned_leaf_slots(t,right,new_right_len);
                //@ open leaf_slots(left,new_left_len,_,_);
                //@ open leaf_slots(right,new_right_len,_,_);
                //@ open leaf_header(left,left_parent,left_index);
                //@ open leaf_header(right,right_parent,right_index);
                //@ open balancing_child_padding(incoming.left_child.node,height);
                //@ open balancing_child_padding(incoming.right_child.node,height);
                //@ close_points_to(left);
                //@ close_points_to(right);
                //@ close internal_without_edges(left_edges.as_ptr(),?left_data);
                //@ close internal_without_edges(right_edges.as_ptr(),?right_data);
                //@ close_points_to(&mut left_internal);
                //@ close_points_to(&mut right_internal);
                //@ open balancing_edges(left_edges,left_children,?left_slots);
                //@ open balancing_edges(right_edges,right_children,?right_slots);
                //@ let kept = take(new_left_len+1,left_children);
                //@ let moved = drop(new_left_len+1,left_children);
                //@ let shifted_children = append(moved,right_children);
                //@ let tail = drop(new_right_len+1,right_slots);
                //@ let saved = take(count,take(new_right_len+1,right_slots));
                //@ initialized_edge_split(left_children,new_left_len+1);
                //@ initialized_edge_count(kept);
                //@ initialized_edge_count(moved);
                //@ initialized_edge_count(right_children);
                //@ length_take(new_left_len+1,left_children);
                //@ length_drop(new_left_len+1,left_children);
                //@ split_linked_headers(left_children,left_edges,0,new_left_len+1);
                //@ forget_link_indices(moved,left_edges,new_left_len+1);
                //@ forget_link_indices(right_children,right_edges,0);
                //@ join_child_headers(moved,right_children);
                //@ initialized_edges_append(moved,right_children);
                unsafe {
                    slice_shr(right_internal.edge_area_prefix_mut/*@::<'a,K,V,'short>@*/(..new_right_len + 1), count);
                    //@ assert edges_range_loan(right_edges.as_ptr(),?shifted,0,new_right_len+1,right_data,_,_);
                    //@ end_edges_range(right_edges.as_ptr(),shifted);
                    //@ take_twice(right_slots,old_right_len+1,new_right_len+1);
                    //@ append_assoc(saved,initialized_edges(right_children),tail);
                    //@ length_take(new_right_len+1,right_slots);
                    //@ length_take(count,take(new_right_len+1,right_slots));
                    //@ drop_append(count,saved,append(initialized_edges(right_children),tail));
                    //@ drop_0(append(initialized_edges(right_children),tail));
                    move_to_slice(
                        left_internal.edge_area_range_mut/*@::<'a,K,V,'short>@*/(new_left_len + 1..old_left_len + 1),
                        right_internal.edge_area_prefix_mut/*@::<'a,K,V,'short>@*/(..count),
                    );
                    //@ assert edges_range_loan(left_edges.as_ptr(),?source,new_left_len+1,old_left_len+1,left_data,_,_);
                    //@ assert edges_range_loan(right_edges.as_ptr(),?destination,0,count,right_data,_,_);
                    //@ end_edges_range(left_edges.as_ptr(),source);
                    //@ end_edges_range(right_edges.as_ptr(),destination);
                    //@ take_after_drop(left_slots,new_left_len+1,count);
                    //@ append_take_drop_n(take(old_left_len+1,left_slots),new_left_len+1);
                    //@ append_take_drop_n(left_slots,old_left_len+1);
                    //@ take_twice(left_slots,new_left_len+1,old_left_len+1);
                    //@ append_assoc(take(new_left_len+1,left_slots),take(count,drop(new_left_len+1,left_slots)),drop(old_left_len+1,left_slots));
                    //@ append_assoc(initialized_edges(moved),initialized_edges(right_children),tail);

                    //@ open internal_without_edges(right_edges.as_ptr(),right_data);
                    //@ open_points_to(&(*right_edges.as_ptr()).data);
                    //@ close exists(right_edges);
                    //@ close exists(pair(nil::<MaybeUninit<BoxedNode<K,V>>>,tail));
                    //@ length_append(moved,right_children);
                    right_internal.relink_range/*@::<'a,K,V,'short>@*/(0..new_right_len + 1);
                    //@ close_points_to(&(*right_edges.as_ptr()).data);
                    //@ close internal_without_edges(right_edges.as_ptr(),right_data);
                    //@ initialized_edge_count(shifted_children);
                    //@ take_append_l(new_right_len+1,initialized_edges(shifted_children),tail);
                    //@ take_length(initialized_edges(shifted_children));
                    //@ take_twice(left_slots,new_left_len+1,old_left_len+1);
                    //@ close balancing_edges(left_edges,kept,left_slots);
                    //@ close balancing_edges(right_edges,shifted_children,_);
                }
                //@ open internal_without_edges(left_edges.as_ptr(),left_data);
                //@ open_points_to(left);
                //@ close leaf_header(left,left_parent,left_index);
                //@ close leaf_slots(left,new_left_len,_,_);
                //@ close owned_leaf_slots(t,left,new_left_len);
                //@ close balancing_child_padding(incoming.left_child.node,height);
                //@ open internal_without_edges(right_edges.as_ptr(),right_data);
                //@ open_points_to(right);
                //@ close leaf_header(right,right_parent,right_index);
                //@ close leaf_slots(right,new_right_len,_,_);
                //@ close owned_leaf_slots(t,right,new_right_len);
                //@ close balancing_child_padding(incoming.right_child.node,height);
                //@ open_points_to(&mut left_internal);
                //@ open_points_to(&mut right_internal);
            }
            (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
            _ => unreachable!(),
        }
        //@ close balancing_child_edges(incoming.left_child.node,height,new_left_len,take(left_len-count+1,left_children));
        //@ close balancing_child_edges(incoming.right_child.node,height,new_right_len,append(drop(left_len-count+1,left_children),right_children));
        //@ end_ref_mut(right_node);
        //@ end_ref_mut(left_node);
        //@ close_points_to(self);
    }

    unsafe fn bulk_steal_right_production<'short>(&'short mut self, count: usize)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& *self |-> ?incoming &*&
        leaf_header(incoming.parent.node.node.as_ptr(),?parent_parent,?parent_index) &*&
        owned_leaf_slots(t,incoming.parent.node.node.as_ptr(),?parent_len) &*&
        0 <= incoming.parent.idx &*& incoming.parent.idx < parent_len &*&
        leaf_header(incoming.left_child.node.as_ptr(),?left_parent,?left_index) &*&
        leaf_header(incoming.right_child.node.as_ptr(),?right_parent,?right_index) &*&
        owned_leaf_slots(t,incoming.left_child.node.as_ptr(),?left_len) &*&
        owned_leaf_slots(t,incoming.right_child.node.as_ptr(),?right_len) &*&
        0 < count &*& count <= right_len &*& left_len + count <= CAPACITY
        &*& incoming.left_child.height == incoming.right_child.height
        &*& 0 <= incoming.left_child.height &*& incoming.left_child.height <= usize::MAX
        &*& balancing_child_padding(incoming.left_child.node,incoming.left_child.height)
        &*& balancing_child_padding(incoming.right_child.node,incoming.right_child.height)
        &*& balancing_child_edges(incoming.left_child.node,incoming.left_child.height,left_len,?left_children)
        &*& balancing_child_edges(incoming.right_child.node,incoming.right_child.height,right_len,?right_children);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& *self |-> incoming &*&
        leaf_header(incoming.parent.node.node.as_ptr(),parent_parent,parent_index) &*&
        owned_leaf_slots(t,incoming.parent.node.node.as_ptr(),parent_len) &*&
        leaf_header(incoming.left_child.node.as_ptr(),left_parent,left_index) &*&
        leaf_header(incoming.right_child.node.as_ptr(),right_parent,right_index) &*&
        owned_leaf_slots(t,incoming.left_child.node.as_ptr(),left_len + count) &*&
        owned_leaf_slots(t,incoming.right_child.node.as_ptr(),right_len - count)
        &*& balancing_child_padding(incoming.left_child.node,incoming.left_child.height)
        &*& balancing_child_padding(incoming.right_child.node,incoming.right_child.height)
        &*& balancing_child_edges(incoming.left_child.node,incoming.left_child.height,left_len + count,append(left_children,take(count,right_children)))
        &*& balancing_child_edges(incoming.right_child.node,incoming.right_child.height,right_len - count,drop(count,right_children));
    @*/
    //@ on_unwind_ens false;
    {
        assert!(count > 0);
        //@ let left = incoming.left_child.node.as_ptr();
        //@ let right = incoming.right_child.node.as_ptr();
        //@ open_points_to(self);
        //@ close_points_to(&(*self).left_child);
        let left_node = &mut self.left_child; //~track_ref_creation
        //@ open owned_leaf_slots(t,left,left_len);
        //@ open leaf_slots(left,left_len,?left_keys,?left_vals);
        //@ let left_view = precreate_ref(left_node);
        //@ init_ref_readonly(left_view,1/2);
        let old_left_len = unsafe { left_node.merge_len() };
        //@ end_ref_readonly(left_view);
        //@ merge_fractions points_to(left_node, _);

        //@ close_points_to(&(*self).right_child);
        let right_node = &mut self.right_child; //~track_ref_creation
        //@ open owned_leaf_slots(t,right,right_len);
        //@ open leaf_slots(right,right_len,?right_keys,?right_vals);
        //@ let right_view = precreate_ref(right_node);
        //@ init_ref_readonly(right_view,1/2);
        let old_right_len = unsafe { right_node.merge_len() };
        //@ end_ref_readonly(right_view);
        //@ merge_fractions points_to(right_node, _);
        assert!(old_left_len + count <= CAPACITY);
        assert!(old_right_len >= count);

        let new_left_len = old_left_len + count;
        let new_right_len = old_right_len - count;
        //@ open leaf_header(left,left_parent,left_index);
        //@ close leaf_without_len(left,left_parent,left_index,left_keys,left_vals);
        *left_node.len_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/() = new_left_len as u16;
        //@ assert len_loan(left,?left_mut,left_parent,left_index,left_keys,left_vals);
        //@ end_len_loan(left,left_mut);
        //@ open leaf_without_len(left,left_parent,left_index,left_keys,left_vals);
        //@ close leaf_header(left,left_parent,left_index);
        //@ close leaf_slots(left,new_left_len,left_keys,left_vals);
        //@ open leaf_header(right,right_parent,right_index);
        //@ close leaf_without_len(right,right_parent,right_index,right_keys,right_vals);
        *right_node.len_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/() = new_right_len as u16;
        //@ assert len_loan(right,?right_mut,right_parent,right_index,right_keys,right_vals);
        //@ end_len_loan(right,right_mut);
        //@ open leaf_without_len(right,right_parent,right_index,right_keys,right_vals);
        //@ close leaf_header(right,right_parent,right_index);
        //@ close leaf_slots(right,new_right_len,right_keys,right_vals);
        //@ open leaf_slots(left,new_left_len,left_keys,left_vals);
        //@ open leaf_slots(right,new_right_len,right_keys,right_vals);
        //@ assert length(left_keys) == CAPACITY;
        //@ assert length(left_vals) == CAPACITY;
        //@ assert length(right_keys) == CAPACITY;
        //@ assert length(right_vals) == CAPACITY;
        {
            //@ let original_keys = take(old_right_len,right_keys);
            //@ length_take(old_right_len,right_keys);
            //@ split_slot_owners(t,original_keys,count - 1);
            //@ drop_n_plus_one(count - 1,original_keys);
            //@ open slot_owners(t,drop(count - 1,original_keys));
            //@ nth_take_range(right_keys,old_right_len,count - 1);
            //@ close leaf_without_keys(right,right_parent,right_index,new_right_len as u16,right_vals);
            let donated_keys_slot = right_node.key_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(count - 1);
            //@ assert keys_slot_loan(right,donated_keys_slot,count - 1,right_parent,right_index,new_right_len as u16,right_vals,_,_);
            //@ let keys_view = precreate_ref(donated_keys_slot);
            //@ init_ref_readonly(keys_view,1/2);
            let k = donated_keys_slot.assume_init_read();
            //@ end_ref_readonly(keys_view);
            //@ merge_fractions points_to(donated_keys_slot, _);
            //@ end_keys_slot(right,donated_keys_slot);
            //@ open leaf_without_keys(right,right_parent,right_index,new_right_len as u16,right_vals);
            //@ nth_at_partition(right_keys,count - 1);
            //@ assert (*right).keys[..CAPACITY] |-> right_keys;
            //@ let donation_keys = k;
            //@ let original_vals = take(old_right_len,right_vals);
            //@ length_take(old_right_len,right_vals);
            //@ split_slot_owners(t,original_vals,count - 1);
            //@ drop_n_plus_one(count - 1,original_vals);
            //@ open slot_owners(t,drop(count - 1,original_vals));
            //@ nth_take_range(right_vals,old_right_len,count - 1);
            //@ close leaf_without_vals(right,right_parent,right_index,new_right_len as u16,right_keys);
            let donated_vals_slot = right_node.val_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(count - 1);
            //@ assert vals_slot_loan(right,donated_vals_slot,count - 1,right_parent,right_index,new_right_len as u16,right_keys,_,_);
            //@ let vals_view = precreate_ref(donated_vals_slot);
            //@ init_ref_readonly(vals_view,1/2);
            let v = donated_vals_slot.assume_init_read();
            //@ end_ref_readonly(vals_view);
            //@ merge_fractions points_to(donated_vals_slot, _);
            //@ end_vals_slot(right,donated_vals_slot);
            //@ open leaf_without_vals(right,right_parent,right_index,new_right_len as u16,right_keys);
            //@ nth_at_partition(right_vals,count - 1);
            //@ assert (*right).vals[..CAPACITY] |-> right_vals;
            //@ let donation_vals = v;
            //@ let parent = incoming.parent.node.node.as_ptr();
            //@ let separator = incoming.parent.idx;
            //@ open owned_leaf_slots(t,parent,parent_len);
            //@ assert leaf_slots(parent,parent_len,?parent_keys,?parent_vals);
            //@ open leaf_slots(parent,parent_len,parent_keys,parent_vals);
            //@ open_slot_owner(t,parent_keys,parent_len,separator);
            //@ open_slot_owner(t,parent_vals,parent_len,separator);
            //@ close leaf_slots(parent,parent_len,parent_keys,parent_vals);
            //@ close_points_to(&(*self).parent);
            let (separator_key, separator_value) = self.parent.replace_kv_production/*@::<'a,K,V,marker::Internal,'short>@*/(k, v); //~track_ref_creation
            //@ assert ref_mut_end_token(?parent_view,&(*self).parent);
            //@ end_ref_mut(parent_view);
            //@ open_points_to(&(*self).parent);
            //@ assert leaf_slots(parent,parent_len,?replaced_keys,?replaced_vals);
            //@ restore_slot_owner(t,parent_keys,parent_len,separator,donation_keys);
            //@ restore_slot_owner(t,parent_vals,parent_len,separator,donation_vals);
            //@ close owned_leaf_slots(t,parent,parent_len);
            //@ close leaf_without_keys(left,left_parent,left_index,new_left_len as u16,left_vals);
            left_node.key_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(old_left_len).write(separator_key);
            //@ assert keys_slot_loan(left,?recipient_keys_slot,old_left_len,left_parent,left_index,new_left_len as u16,left_vals,_,_);
            //@ end_keys_slot(left,recipient_keys_slot);
            //@ open leaf_without_keys(left,left_parent,left_index,new_left_len as u16,left_vals);
            //@ assert (*left).keys[..CAPACITY] |-> ?written_keys;
            //@ close leaf_without_vals(left,left_parent,left_index,new_left_len as u16,written_keys);
            left_node.val_area_slot_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(old_left_len).write(separator_value);
            //@ assert vals_slot_loan(left,?recipient_vals_slot,old_left_len,left_parent,left_index,new_left_len as u16,written_keys,_,_);
            //@ end_vals_slot(left,recipient_vals_slot);
            //@ open leaf_without_vals(left,left_parent,left_index,new_left_len as u16,written_keys);
            //@ assert (*left).vals[..CAPACITY] |-> ?written_vals;
            //@ close leaf_without_keys(right,right_parent,right_index,new_right_len as u16,right_vals);
            //@ close leaf_without_keys(left,left_parent,left_index,new_left_len as u16,written_vals);
            move_to_slice(
                right_node.key_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..count - 1),
                left_node.key_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(old_left_len + 1..new_left_len),
            );
            //@ assert keys_range_loan(right,?keys_source,0,count-1,right_parent,right_index,new_right_len as u16,right_vals,_,_);
            //@ end_keys_range(right,keys_source);
            //@ open leaf_without_keys(right,right_parent,right_index,new_right_len as u16,right_vals);
            //@ assert keys_range_loan(left,?keys_dest,old_left_len+1,new_left_len,left_parent,left_index,new_left_len as u16,written_vals,_,_);
            //@ end_keys_range(left,keys_dest);
            //@ open leaf_without_keys(left,left_parent,left_index,new_left_len as u16,written_vals);
            //@ take_0(right_keys);
            //@ drop_0(right_keys);
            //@ append_take_drop_n(right_keys,count-1);
            //@ assert (*right).keys[..CAPACITY] |-> right_keys;
            //@ take_0(written_keys);
            //@ drop_0(right_keys);
            //@ assert (*left).keys[..CAPACITY] |-> ?copied_keys;
            //@ close leaf_without_vals(right,right_parent,right_index,new_right_len as u16,right_keys);
            //@ close leaf_without_vals(left,left_parent,left_index,new_left_len as u16,copied_keys);
            move_to_slice(
                right_node.val_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..count - 1),
                left_node.val_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(old_left_len + 1..new_left_len),
            );
            //@ assert vals_range_loan(right,?vals_source,0,count-1,right_parent,right_index,new_right_len as u16,right_keys,_,_);
            //@ end_vals_range(right,vals_source);
            //@ open leaf_without_vals(right,right_parent,right_index,new_right_len as u16,right_keys);
            //@ assert vals_range_loan(left,?vals_dest,old_left_len+1,new_left_len,left_parent,left_index,new_left_len as u16,copied_keys,_,_);
            //@ end_vals_range(left,vals_dest);
            //@ open leaf_without_vals(left,left_parent,left_index,new_left_len as u16,copied_keys);
            //@ take_0(right_vals);
            //@ drop_0(right_vals);
            //@ append_take_drop_n(right_vals,count-1);
            //@ assert (*right).vals[..CAPACITY] |-> right_vals;
            //@ take_0(written_vals);
            //@ drop_0(right_vals);
            //@ assert (*left).vals[..CAPACITY] |-> ?copied_vals;
            //@ close leaf_without_keys(right,right_parent,right_index,new_right_len as u16,right_vals);
            slice_shl(right_node.key_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..old_right_len), count);
            //@ assert keys_range_loan(right,?keys_shift,0,old_right_len,right_parent,right_index,new_right_len as u16,right_vals,_,_);
            //@ end_keys_range(right,keys_shift);
            //@ open leaf_without_keys(right,right_parent,right_index,new_right_len as u16,right_vals);
            //@ take_0(right_keys);
            //@ drop_0(right_keys);
            //@ assert (*right).keys[..CAPACITY] |-> ?shifted_keys;
            //@ close leaf_without_vals(right,right_parent,right_index,new_right_len as u16,shifted_keys);
            slice_shl(right_node.val_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..old_right_len), count);
            //@ assert vals_range_loan(right,?vals_shift,0,old_right_len,right_parent,right_index,new_right_len as u16,shifted_keys,_,_);
            //@ end_vals_range(right,vals_shift);
            //@ open leaf_without_vals(right,right_parent,right_index,new_right_len as u16,shifted_keys);
            //@ take_0(right_vals);
            //@ drop_0(right_vals);
            //@ assert (*right).vals[..CAPACITY] |-> ?shifted_vals;
            //@ join_right_steal(t,left_keys,right_keys,written_keys,copied_keys,shifted_keys,old_left_len,old_right_len,count,separator_key);
            //@ join_right_steal(t,left_vals,right_vals,written_vals,copied_vals,shifted_vals,old_left_len,old_right_len,count,separator_value);
        }
        //@ close leaf_slots(left,new_left_len,copied_keys,copied_vals);
        //@ close leaf_slots(right,new_right_len,shifted_keys,shifted_vals);
        //@ close owned_leaf_slots(t,left,new_left_len);
        //@ close owned_leaf_slots(t,right,new_right_len);
        //@ let height = incoming.left_child.height;
        //@ open balancing_child_edges(incoming.left_child.node,height,left_len,left_children);
        //@ open balancing_child_edges(incoming.right_child.node,height,right_len,right_children);
        match (
            left_node.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'short>@*/().force/*@::<marker::Mut<'short>,K,V>@*/(),
            right_node.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'short>@*/().force/*@::<marker::Mut<'short>,K,V>@*/(),
        ) {
            (ForceResult::Internal(mut left_internal), ForceResult::Internal(mut right_internal)) => {
                //@ let left_edges = NonNull::new(left as *InternalNode<K,V>);
                //@ let right_edges = NonNull::new(right as *InternalNode<K,V>);
                //@ std::ptr::NonNull_as_ptr_new(left as *InternalNode<K,V>);
                //@ std::ptr::NonNull_as_ptr_new(right as *InternalNode<K,V>);
                //@ std::ptr::NonNull_Sized_as_ptr(left_edges);
                //@ std::ptr::NonNull_Sized_as_ptr(right_edges);
                //@ assert &(*left_edges.as_ptr()).data == left;
                //@ assert &(*right_edges.as_ptr()).data == right;
                //@ open owned_leaf_slots(t,left,new_left_len);
                //@ open owned_leaf_slots(t,right,new_right_len);
                //@ open leaf_slots(left,new_left_len,_,_);
                //@ open leaf_slots(right,new_right_len,_,_);
                //@ open leaf_header(left,left_parent,left_index);
                //@ open leaf_header(right,right_parent,right_index);
                //@ open balancing_child_padding(incoming.left_child.node,height);
                //@ open balancing_child_padding(incoming.right_child.node,height);
                //@ close_points_to(left);
                //@ close_points_to(right);
                //@ close internal_without_edges(left_edges.as_ptr(),?left_data);
                //@ close internal_without_edges(right_edges.as_ptr(),?right_data);
                //@ close_points_to(&mut left_internal);
                //@ close_points_to(&mut right_internal);
                //@ open balancing_edges(left_edges,left_children,?left_slots);
                //@ open balancing_edges(right_edges,right_children,?right_slots);
                //@ let moved = take(count,right_children);
                //@ let kept = drop(count,right_children);
                //@ let before = take(old_left_len+1,left_slots);
                //@ let left_tail = drop(new_left_len+1,left_slots);
                //@ let inactive = drop(new_right_len+1,take(old_right_len+1,right_slots));
                //@ let right_tail = append(inactive,drop(old_right_len+1,right_slots));
                //@ let joined = append(left_children,moved);
                //@ initialized_edge_split(right_children,count);
                //@ initialized_edge_count(left_children);
                //@ initialized_edge_count(moved);
                //@ initialized_edge_count(kept);
                //@ length_take(count,right_children);
                //@ length_drop(count,right_children);
                //@ split_linked_headers(right_children,right_edges,0,count);
                //@ forget_link_indices(moved,right_edges,0);
                //@ initialized_edges_append(left_children,moved);
                unsafe {
                    move_to_slice(
                        right_internal.edge_area_prefix_mut/*@::<'a,K,V,'short>@*/(..count),
                        left_internal.edge_area_range_mut/*@::<'a,K,V,'short>@*/(old_left_len + 1..new_left_len + 1),
                    );
                    //@ assert edges_range_loan(right_edges.as_ptr(),?source,0,count,right_data,_,_);
                    //@ assert edges_range_loan(left_edges.as_ptr(),?destination,old_left_len+1,new_left_len+1,left_data,_,_);
                    //@ end_edges_range(right_edges.as_ptr(),source);
                    //@ end_edges_range(left_edges.as_ptr(),destination);
                    //@ take_0(right_slots);
                    //@ drop_0(right_slots);
                    //@ append_take_drop_n(right_slots,count);
                    //@ take_twice(right_slots,count,old_right_len+1);
                    //@ append_assoc(before,initialized_edges(moved),left_tail);
                    slice_shl(right_internal.edge_area_prefix_mut/*@::<'a,K,V,'short>@*/(..old_right_len + 1), count);
                    //@ assert edges_range_loan(right_edges.as_ptr(),?shifted,0,old_right_len+1,right_data,_,_);
                    //@ end_edges_range(right_edges.as_ptr(),shifted);
                    //@ open internal_without_edges(left_edges.as_ptr(),left_data);
                    //@ open_points_to(&(*left_edges.as_ptr()).data);
                    //@ close exists(left_edges);
                    //@ close exists(pair(before,left_tail));
                    //@ length_take(old_left_len+1,left_slots);
                    left_internal.relink_range/*@::<'a,K,V,'short>@*/(old_left_len + 1..new_left_len + 1);
                    //@ close_points_to(&(*left_edges.as_ptr()).data);
                    //@ close internal_without_edges(left_edges.as_ptr(),left_data);

                    //@ forget_link_indices(kept,right_edges,count);
                    //@ open internal_without_edges(right_edges.as_ptr(),right_data);
                    //@ open_points_to(&(*right_edges.as_ptr()).data);
                    //@ close exists(right_edges);
                    //@ close exists(pair(nil::<MaybeUninit<BoxedNode<K,V>>>,right_tail));
                    //@ take_0(right_slots);
                    //@ drop_0(right_slots);
                    //@ append_assoc(initialized_edges(kept),inactive,drop(old_right_len+1,right_slots));
                    right_internal.relink_range/*@::<'a,K,V,'short>@*/(0..new_right_len + 1);
                    //@ close_points_to(&(*right_edges.as_ptr()).data);
                    //@ close internal_without_edges(right_edges.as_ptr(),right_data);
                    //@ join_linked_headers(left_children,moved,left_edges,0);
                    //@ length_append(left_children,moved);
                    //@ initialized_edge_count(joined);
                    //@ take_append_l(new_left_len+1,initialized_edges(joined),left_tail);
                    //@ take_length(initialized_edges(joined));
                    //@ take_append_l(new_right_len+1,initialized_edges(kept),right_tail);
                    //@ take_length(initialized_edges(kept));
                    //@ close balancing_edges(left_edges,joined,_);
                    //@ close balancing_edges(right_edges,kept,_);
                }
                //@ open internal_without_edges(left_edges.as_ptr(),left_data);
                //@ open_points_to(left);
                //@ close leaf_header(left,left_parent,left_index);
                //@ close leaf_slots(left,new_left_len,_,_);
                //@ close owned_leaf_slots(t,left,new_left_len);
                //@ close balancing_child_padding(incoming.left_child.node,height);
                //@ open internal_without_edges(right_edges.as_ptr(),right_data);
                //@ open_points_to(right);
                //@ close leaf_header(right,right_parent,right_index);
                //@ close leaf_slots(right,new_right_len,_,_);
                //@ close owned_leaf_slots(t,right,new_right_len);
                //@ close balancing_child_padding(incoming.right_child.node,height);
                //@ open_points_to(&mut left_internal);
                //@ open_points_to(&mut right_internal);
            }
            (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
            _ => unreachable!(),
        }
        //@ close balancing_child_edges(incoming.left_child.node,height,new_left_len,append(left_children,take(count,right_children)));
        //@ close balancing_child_edges(incoming.right_child.node,height,new_right_len,drop(count,right_children));
        //@ end_ref_mut(right_node);
        //@ end_ref_mut(left_node);
        //@ close_points_to(self);
    }

    unsafe fn steal_left_production(
        mut self, track_right_edge_idx: usize,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.parent.node.node.as_ptr(),?parent_parent,?parent_index) &*&
        owned_leaf_slots(t,self.parent.node.node.as_ptr(),?parent_len) &*&
        0 <= self.parent.idx &*& self.parent.idx < parent_len &*&
        leaf_header(self.left_child.node.as_ptr(),?left_parent,?left_index) &*&
        leaf_header(self.right_child.node.as_ptr(),?right_parent,?right_index) &*&
        owned_leaf_slots(t,self.left_child.node.as_ptr(),?left_len) &*&
        owned_leaf_slots(t,self.right_child.node.as_ptr(),?right_len) &*&
        0 <= track_right_edge_idx &*& track_right_edge_idx <= right_len &*& 1 <= left_len &*& right_len + 1 <= CAPACITY
        &*& self.left_child.height == self.right_child.height
        &*& 0 <= self.left_child.height &*& self.left_child.height <= usize::MAX
        &*& balancing_child_padding(self.left_child.node,self.left_child.height)
        &*& balancing_child_padding(self.right_child.node,self.right_child.height)
        &*& balancing_child_edges(self.left_child.node,self.left_child.height,left_len,?left_children)
        &*& balancing_child_edges(self.right_child.node,self.right_child.height,right_len,?right_children);
    @*/
    /*@
    ens result.node == self.right_child &*& result.idx == 1 + track_right_edge_idx &*&
        thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.parent.node.node.as_ptr(),parent_parent,parent_index) &*&
        owned_leaf_slots(t,self.parent.node.node.as_ptr(),parent_len) &*&
        leaf_header(self.left_child.node.as_ptr(),left_parent,left_index) &*&
        leaf_header(self.right_child.node.as_ptr(),right_parent,right_index) &*&
        owned_leaf_slots(t,self.left_child.node.as_ptr(),left_len - 1) &*&
        owned_leaf_slots(t,self.right_child.node.as_ptr(),right_len + 1)
        &*& balancing_child_padding(self.left_child.node,self.left_child.height)
        &*& balancing_child_padding(self.right_child.node,self.right_child.height)
        &*& balancing_child_edges(self.left_child.node,self.left_child.height,left_len - 1,take(left_len-1+1,left_children))
        &*& balancing_child_edges(self.right_child.node,self.right_child.height,right_len + 1,append(drop(left_len-1+1,left_children),right_children));
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert *(&mut self) |-> ?original;
        self.bulk_steal_left_production/*@::<'a,K,V,'a>@*/(1); //~track_ref_creation
        //@ assert ref_mut_end_token(?context, &mut self);
        //@ end_ref_mut(context);
        //@ open_points_to(&mut self);
        //@ let recipient = self.right_child.node.as_ptr();
        //@ close_points_to(&self.right_child);
        //@ open owned_leaf_slots(t,recipient,right_len + 1);
        //@ open leaf_slots(recipient,right_len + 1,_,_);
        let edge = unsafe {
            Handle::<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge>::new_edge/*@::<marker::Mut<'a>,K,V>@*/(self.right_child, 1 + track_right_edge_idx)
        };
        //@ close leaf_slots(recipient,right_len + 1,_,_);
        //@ close owned_leaf_slots(t,recipient,right_len + 1);
        //@ close_points_to(&self.parent.node);
        //@ close Handle_node_(&self.parent, some(original.parent.node));
        //@ close BalancingContext_parent_(&self, _);
        //@ close NodeRef_node_(&self.left_child, some(original.left_child.node));
        //@ close BalancingContext_left_child_(&self, _);
        //@ close NodeRef_node_(&self.right_child, _);
        //@ close BalancingContext_right_child_(&self, _);
        edge
    }

    unsafe fn steal_right_production(
        mut self, track_left_edge_idx: usize,
    ) -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.parent.node.node.as_ptr(),?parent_parent,?parent_index) &*&
        owned_leaf_slots(t,self.parent.node.node.as_ptr(),?parent_len) &*&
        0 <= self.parent.idx &*& self.parent.idx < parent_len &*&
        leaf_header(self.left_child.node.as_ptr(),?left_parent,?left_index) &*&
        leaf_header(self.right_child.node.as_ptr(),?right_parent,?right_index) &*&
        owned_leaf_slots(t,self.left_child.node.as_ptr(),?left_len) &*&
        owned_leaf_slots(t,self.right_child.node.as_ptr(),?right_len) &*&
        0 <= track_left_edge_idx &*& track_left_edge_idx <= left_len &*& 1 <= right_len &*& left_len + 1 <= CAPACITY
        &*& self.left_child.height == self.right_child.height
        &*& 0 <= self.left_child.height &*& self.left_child.height <= usize::MAX
        &*& balancing_child_padding(self.left_child.node,self.left_child.height)
        &*& balancing_child_padding(self.right_child.node,self.right_child.height)
        &*& balancing_child_edges(self.left_child.node,self.left_child.height,left_len,?left_children)
        &*& balancing_child_edges(self.right_child.node,self.right_child.height,right_len,?right_children);
    @*/
    /*@
    ens result.node == self.left_child &*& result.idx == track_left_edge_idx &*&
        thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.parent.node.node.as_ptr(),parent_parent,parent_index) &*&
        owned_leaf_slots(t,self.parent.node.node.as_ptr(),parent_len) &*&
        leaf_header(self.left_child.node.as_ptr(),left_parent,left_index) &*&
        leaf_header(self.right_child.node.as_ptr(),right_parent,right_index) &*&
        owned_leaf_slots(t,self.left_child.node.as_ptr(),left_len + 1) &*&
        owned_leaf_slots(t,self.right_child.node.as_ptr(),right_len - 1)
        &*& balancing_child_padding(self.left_child.node,self.left_child.height)
        &*& balancing_child_padding(self.right_child.node,self.right_child.height)
        &*& balancing_child_edges(self.left_child.node,self.left_child.height,left_len + 1,append(left_children,take(1,right_children)))
        &*& balancing_child_edges(self.right_child.node,self.right_child.height,right_len - 1,drop(1,right_children));
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert *(&mut self) |-> ?original;
        self.bulk_steal_right_production/*@::<'a,K,V,'a>@*/(1); //~track_ref_creation
        //@ assert ref_mut_end_token(?context, &mut self);
        //@ end_ref_mut(context);
        //@ open_points_to(&mut self);
        //@ let recipient = self.left_child.node.as_ptr();
        //@ close_points_to(&self.left_child);
        //@ open owned_leaf_slots(t,recipient,left_len + 1);
        //@ open leaf_slots(recipient,left_len + 1,_,_);
        let edge = unsafe {
            Handle::<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge>::new_edge/*@::<marker::Mut<'a>,K,V>@*/(self.left_child, track_left_edge_idx)
        };
        //@ close leaf_slots(recipient,left_len + 1,_,_);
        //@ close owned_leaf_slots(t,recipient,left_len + 1);
        //@ close_points_to(&self.parent.node);
        //@ close Handle_node_(&self.parent, some(original.parent.node));
        //@ close BalancingContext_parent_(&self, _);
        //@ close NodeRef_node_(&self.right_child, some(original.right_child.node));
        //@ close BalancingContext_right_child_(&self, _);
        //@ close NodeRef_node_(&self.left_child, _);
        //@ close BalancingContext_left_child_(&self, _);
        edge
    }
}


impl<'a, K, V, Type, Kind> Handle<NodeRef<marker::Mut<'a>, K, V, Type>, Kind> {
    unsafe fn reborrow_handle_mut<'short>(&'short mut self) -> Handle<NodeRef<marker::Mut<'short>, K, V, Type>, Kind>
    //@ req *self |-> ?incoming;
    //@ ens *self |-> incoming &*& result.idx == incoming.idx &*& result.node.node == incoming.node.node &*& result.node.height == incoming.node.height;
    //@ on_unwind_ens false;
    {
        //@ open_points_to(self);
        //@ close_points_to(&(*self).node);
        let reborrowed = Handle {
            node: unsafe { self.node.reborrow_mut/*@::<marker::Mut<'a>,K,V,Type,'short>@*/() }, //~track_ref_creation
            idx: self.idx,
            _marker: PhantomData,
        };
        //@ assert ref_mut_end_token(?loan, &(*self).node);
        //@ end_ref_mut(loan);
        //@ open_points_to(&(*self).node);
        //@ close_points_to(self);
        reborrowed
    }
}

impl<Node, Kind> Handle<Node, Kind> {
    unsafe fn into_node(self) -> Node
    //@ req true;
    //@ ens result == self.node;
    //@ on_unwind_ens false;
    {
        self.node
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>, marker::Edge> {
    unsafe fn move_suffix_production<'short>(
        &'short mut self,
        right: &'short mut NodeRef<marker::Mut<'a>, K, V, marker::LeafOrInternal>,
    )
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> ?edge &*& *right |-> ?target &*&
        leaf_header(edge.node.node.as_ptr(), ?left_parent, ?left_index) &*&
        leaf_header(target.node.as_ptr(), ?right_parent, ?right_index) &*&
        owned_leaf_slots(t, edge.node.node.as_ptr(), ?old_len) &*&
        owned_leaf_slots(t, target.node.as_ptr(), 0) &*&
        0 <= edge.idx &*& edge.idx <= old_len &*&
        0 <= edge.node.height &*& edge.node.height <= usize::MAX &*& edge.node.height == target.height &*&
        balancing_child_padding(edge.node.node, edge.node.height) &*&
        balancing_child_padding(target.node, target.height) &*&
        balancing_child_edges(edge.node.node, edge.node.height, old_len, ?lc) &*&
        balancing_child_edges(target.node, target.height, 0, ?rc);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> edge &*& *right |-> target &*&
        leaf_header(edge.node.node.as_ptr(), left_parent, left_index) &*&
        leaf_header(target.node.as_ptr(), right_parent, right_index) &*&
        owned_leaf_slots(t, edge.node.node.as_ptr(), edge.idx) &*&
        owned_leaf_slots(t, target.node.as_ptr(), old_len - edge.idx) &*&
        balancing_child_padding(edge.node.node, edge.node.height) &*&
        balancing_child_padding(target.node, target.height) &*&
        balancing_child_edges(edge.node.node, edge.node.height, edge.idx, take(edge.idx + 1, lc)) &*&
        balancing_child_edges(target.node, target.height, old_len - edge.idx, append(rc, drop(edge.idx + 1, lc)));
    @*/
    //@ on_unwind_ens false;
    {
        unsafe {
            //@ let left_ptr = edge.node.node.as_ptr();
            //@ let right_ptr = target.node.as_ptr();
            //@ let height = edge.node.height;
            //@ open_points_to(self);
            let new_left_len = self.idx;
            //@ close_points_to(self);
            let mut left_node = self.reborrow_handle_mut/*@::<'a,K,V,marker::LeafOrInternal,marker::Edge,'short>@*/().into_node/*@::<NodeRef<marker::Mut<'short>,K,V,marker::LeafOrInternal>,marker::Edge>@*/();
            //@ close_points_to(&mut left_node);
            //@ let left_view = precreate_ref(&mut left_node);
            //@ init_ref_readonly(left_view, 1/2);
            //@ open owned_leaf_slots(t, left_ptr, old_len);
            //@ open leaf_slots(left_ptr, old_len, ?left_keys, ?left_vals);
            let old_left_len = left_node.merge_len/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'short>@*/();
            //@ end_ref_readonly(left_view);
            //@ merge_fractions points_to(&mut left_node, _);

            let new_right_len = old_left_len - new_left_len;
            let mut right_node = right.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'short>@*/();
            //@ close_points_to(&mut right_node);
            //@ let right_view = precreate_ref(&mut right_node);
            //@ init_ref_readonly(right_view, 1/2);
            //@ open owned_leaf_slots(t, right_ptr, 0);
            //@ open leaf_slots(right_ptr, 0, ?right_keys, ?right_vals);
            assert!(right_node.merge_len/*@::<marker::Mut<'a>,K,V,marker::LeafOrInternal,'short>@*/() == 0);
            //@ end_ref_readonly(right_view);
            //@ merge_fractions points_to(&mut right_node, _);
            //@ open_points_to(&mut left_node);
            //@ open_points_to(&mut right_node);
            assert!(left_node.height == right_node.height);
            //@ open balancing_child_edges(edge.node.node, height, old_len, lc);
            //@ open balancing_child_edges(target.node, height, 0, rc);

            if new_right_len > 0 {
                //@ close_points_to(&mut left_node);
                //@ close_points_to(&mut right_node);
                //@ open leaf_header(left_ptr, left_parent, left_index);
                //@ close leaf_without_len(left_ptr, left_parent, left_index, left_keys, left_vals);
                *left_node.len_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/() = new_left_len as u16;
                //@ assert len_loan(left_ptr, ?left_len_ref, left_parent, left_index, left_keys, left_vals);
                //@ end_len_loan(left_ptr, left_len_ref);
                //@ open leaf_without_len(left_ptr, left_parent, left_index, left_keys, left_vals);
                //@ open leaf_header(right_ptr, right_parent, right_index);
                //@ close leaf_without_len(right_ptr, right_parent, right_index, right_keys, right_vals);
                *right_node.len_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/() = new_right_len as u16;
                //@ assert len_loan(right_ptr, ?right_len_ref, right_parent, right_index, right_keys, right_vals);
                //@ end_len_loan(right_ptr, right_len_ref);
                //@ open leaf_without_len(right_ptr, right_parent, right_index, right_keys, right_vals);
                //@ close leaf_without_keys(left_ptr, left_parent, left_index, new_left_len as u16, left_vals);
                //@ close leaf_without_keys(right_ptr, right_parent, right_index, new_right_len as u16, right_vals);
                move_to_slice(
                    left_node.key_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(new_left_len..old_left_len),
                    right_node.key_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..new_right_len),
                );
                //@ assert keys_range_loan(left_ptr, ?keys_source, new_left_len, old_left_len, left_parent, left_index, new_left_len as u16, left_vals, _, _);
                //@ assert keys_range_loan(right_ptr, ?keys_dest, 0, new_right_len, right_parent, right_index, new_right_len as u16, right_vals, _, _);
                //@ end_keys_range(left_ptr, keys_source);
                //@ end_keys_range(right_ptr, keys_dest);
                //@ open leaf_without_keys(left_ptr, left_parent, left_index, new_left_len as u16, left_vals);
                //@ open leaf_without_keys(right_ptr, right_parent, right_index, new_right_len as u16, right_vals);
                //@ take_0(right_keys);
                //@ length_take(old_left_len, left_keys);
                //@ let active_keys = take(old_left_len, left_keys);
                //@ split_slot_owners(t, active_keys, new_left_len);
                //@ take_after_drop(left_keys, new_left_len, new_right_len);
                //@ take_twice(left_keys, new_left_len, old_left_len);
                //@ append_take_drop_n(active_keys, new_left_len);
                //@ append_assoc(take(new_left_len,left_keys), drop(new_left_len,active_keys), drop(old_left_len,left_keys));
                //@ append_take_drop_n(left_keys, old_left_len);
                //@ assert (*left_ptr).keys[..CAPACITY] |-> left_keys;
                //@ assert (*right_ptr).keys[..CAPACITY] |-> ?packed_keys;
                //@ length_drop(new_left_len, active_keys);
                //@ take_append_l(new_right_len, drop(new_left_len,active_keys), drop(new_right_len,right_keys));
                //@ take_length(drop(new_left_len,active_keys));
                //@ open slot_owners::<K>(t, nil);
                //@ close leaf_without_vals(left_ptr, left_parent, left_index, new_left_len as u16, left_keys);
                //@ close leaf_without_vals(right_ptr, right_parent, right_index, new_right_len as u16, packed_keys);
                move_to_slice(
                    left_node.val_area_range_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(new_left_len..old_left_len),
                    right_node.val_area_prefix_mut/*@::<'a,K,V,marker::LeafOrInternal,'short>@*/(..new_right_len),
                );
                //@ assert vals_range_loan(left_ptr, ?vals_source, new_left_len, old_left_len, left_parent, left_index, new_left_len as u16, left_keys, _, _);
                //@ assert vals_range_loan(right_ptr, ?vals_dest, 0, new_right_len, right_parent, right_index, new_right_len as u16, packed_keys, _, _);
                //@ end_vals_range(left_ptr, vals_source);
                //@ end_vals_range(right_ptr, vals_dest);
                //@ open leaf_without_vals(left_ptr, left_parent, left_index, new_left_len as u16, left_keys);
                //@ open leaf_without_vals(right_ptr, right_parent, right_index, new_right_len as u16, packed_keys);
                //@ take_0(right_vals);
                //@ length_take(old_left_len, left_vals);
                //@ let active_vals = take(old_left_len, left_vals);
                //@ split_slot_owners(t, active_vals, new_left_len);
                //@ take_after_drop(left_vals, new_left_len, new_right_len);
                //@ take_twice(left_vals, new_left_len, old_left_len);
                //@ append_take_drop_n(active_vals, new_left_len);
                //@ append_assoc(take(new_left_len,left_vals), drop(new_left_len,active_vals), drop(old_left_len,left_vals));
                //@ append_take_drop_n(left_vals, old_left_len);
                //@ assert (*left_ptr).vals[..CAPACITY] |-> left_vals;
                //@ assert (*right_ptr).vals[..CAPACITY] |-> ?packed_vals;
                //@ length_drop(new_left_len, active_vals);
                //@ take_append_l(new_right_len, drop(new_left_len,active_vals), drop(new_right_len,right_vals));
                //@ take_length(drop(new_left_len,active_vals));
                //@ open slot_owners::<V>(t, nil);
                //@ close leaf_header(left_ptr, left_parent, left_index);
                //@ close leaf_header(right_ptr, right_parent, right_index);
                //@ close leaf_slots(left_ptr, new_left_len, _, _);
                //@ close leaf_slots(right_ptr, new_right_len, _, _);
                //@ close owned_leaf_slots(t, left_ptr, new_left_len);
                //@ close owned_leaf_slots(t, right_ptr, new_right_len);
                match (
                    left_node.force/*@::<marker::Mut<'a>,K,V>@*/(),
                    right_node.force/*@::<marker::Mut<'a>,K,V>@*/(),
                ) {
                    (ForceResult::Internal(mut left), ForceResult::Internal(mut right_child)) => {
                        //@ let left_edges = NonNull::new(left_ptr as *InternalNode<K,V>);
                        //@ let right_edges = NonNull::new(right_ptr as *InternalNode<K,V>);
                        //@ std::ptr::NonNull_as_ptr_new(left_ptr as *InternalNode<K,V>);
                        //@ std::ptr::NonNull_as_ptr_new(right_ptr as *InternalNode<K,V>);
                        //@ std::ptr::NonNull_Sized_as_ptr(left_edges);
                        //@ std::ptr::NonNull_Sized_as_ptr(right_edges);
                        //@ open balancing_edges(left_edges, lc, ?left_slots);
                        //@ open balancing_edges(right_edges, rc, ?right_slots);
                        //@ let kept = take(new_left_len + 1, lc);
                        //@ let moved = drop(new_left_len + 1, lc);
                        //@ let joined = append(rc, moved);
                        //@ let first = take(1, right_slots);
                        //@ let tail = drop(new_right_len + 1, right_slots);
                        //@ initialized_edge_split(lc, new_left_len + 1);
                        //@ initialized_edge_count(kept);
                        //@ initialized_edge_count(moved);
                        //@ initialized_edge_count(rc);
                        //@ length_take(new_left_len + 1, lc);
                        //@ length_drop(new_left_len + 1, lc);
                        //@ split_linked_headers(lc, left_edges, 0, new_left_len + 1);
                        //@ forget_link_indices(moved, left_edges, new_left_len + 1);
                        //@ assert &(*left_edges.as_ptr()).data == left_ptr;
                        //@ open owned_leaf_slots(t, left_ptr, new_left_len);
                        //@ open leaf_slots(left_ptr, new_left_len, _, _);
                        //@ open leaf_header(left_ptr, left_parent, left_index);
                        //@ open balancing_child_padding(edge.node.node, height);
                        //@ close_points_to(left_ptr);
                        //@ close internal_without_edges(left_edges.as_ptr(), ?left_data);
                        //@ close_points_to(&mut left);
                        //@ assert &(*right_edges.as_ptr()).data == right_ptr;
                        //@ open owned_leaf_slots(t, right_ptr, new_right_len);
                        //@ open leaf_slots(right_ptr, new_right_len, _, _);
                        //@ open leaf_header(right_ptr, right_parent, right_index);
                        //@ open balancing_child_padding(target.node, height);
                        //@ close_points_to(right_ptr);
                        //@ close internal_without_edges(right_edges.as_ptr(), ?right_data);
                        //@ close_points_to(&mut right_child);
                        move_to_slice(
                            left.edge_area_range_mut/*@::<'a,K,V,'short>@*/(new_left_len + 1..old_left_len + 1),
                            right_child.edge_area_range_mut/*@::<'a,K,V,'short>@*/(1..new_right_len + 1),
                        );
                        //@ assert edges_range_loan(left_edges.as_ptr(), ?source, new_left_len + 1, old_left_len + 1, left_data, _, _);
                        //@ assert edges_range_loan(right_edges.as_ptr(), ?destination, 1, new_right_len + 1, right_data, _, _);
                        //@ end_edges_range(left_edges.as_ptr(), source);
                        //@ end_edges_range(right_edges.as_ptr(), destination);
                        //@ take_after_drop(left_slots, new_left_len + 1, new_right_len);
                        //@ take_twice(left_slots, new_left_len + 1, old_left_len + 1);
                        //@ append_take_drop_n(take(old_left_len + 1,left_slots), new_left_len + 1);
                        //@ append_take_drop_n(left_slots, old_left_len + 1);
                        //@ append_assoc(take(new_left_len + 1,left_slots), initialized_edges(moved), drop(old_left_len + 1,left_slots));
                        //@ length_take(1, right_slots);
                        //@ open internal_without_edges(right_edges.as_ptr(), right_data);
                        //@ open_points_to(&(*right_edges.as_ptr()).data);
                        //@ close exists(right_edges);
                        //@ close exists(pair(first, tail));
                        right_child.relink_range/*@::<'a,K,V,'short>@*/(1..new_right_len + 1);
                        //@ close_points_to(&(*right_edges.as_ptr()).data);
                        //@ close internal_without_edges(right_edges.as_ptr(), right_data);
                        //@ initialized_edges_append(rc, moved);
                        //@ append_assoc(first, initialized_edges(moved), tail);
                        //@ join_linked_headers(rc, moved, right_edges, 0);
                        //@ length_append(rc, moved);
                        //@ initialized_edge_count(joined);
                        //@ take_append_l(new_right_len + 1, initialized_edges(joined), tail);
                        //@ take_length(initialized_edges(joined));
                        //@ close balancing_edges(left_edges, kept, left_slots);
                        //@ close balancing_edges(right_edges, joined, _);
                        //@ open internal_without_edges(left_edges.as_ptr(), left_data);
                        //@ open_points_to(left_ptr);
                        //@ close leaf_header(left_ptr, left_parent, left_index);
                        //@ close leaf_slots(left_ptr, new_left_len, _, _);
                        //@ close owned_leaf_slots(t, left_ptr, new_left_len);
                        //@ close balancing_child_padding(edge.node.node, height);
                        //@ open_points_to(&mut left);
                        //@ open internal_without_edges(right_edges.as_ptr(), right_data);
                        //@ open_points_to(right_ptr);
                        //@ close leaf_header(right_ptr, right_parent, right_index);
                        //@ close leaf_slots(right_ptr, new_right_len, _, _);
                        //@ close owned_leaf_slots(t, right_ptr, new_right_len);
                        //@ close balancing_child_padding(target.node, height);
                        //@ open_points_to(&mut right_child);
                    }
                    (ForceResult::Leaf(_), ForceResult::Leaf(_)) => {}
                    _ => unreachable!(),
                }
                //@ close NodeRef_node_(&mut left_node, _);
                //@ close NodeRef_node_(&mut right_node, _);
            } else {
                /*@
                if height > 0 {
                    take_length(lc);
                    length_drop(new_left_len + 1, lc);
                    empty_list_if_zero(drop(new_left_len + 1, lc));
                }
                @*/
                //@ append_nil(rc);
                //@ close leaf_slots(left_ptr, old_len, left_keys, left_vals);
                //@ close leaf_slots(right_ptr, 0, right_keys, right_vals);
                //@ close owned_leaf_slots(t, left_ptr, old_len);
                //@ close owned_leaf_slots(t, right_ptr, 0);
                //@ close NodeRef_node_(&mut left_node, _);
                //@ close NodeRef_node_(&mut right_node, _);
            }
            //@ close balancing_child_edges(edge.node.node, height, new_left_len, take(new_left_len + 1, lc));
            //@ close balancing_child_edges(target.node, height, new_right_len, append(rc, drop(new_left_len + 1, lc)));
        }
    }
}



// The production cleanup edges are checked separately. A key unwind
// leaves its value pending. Its value guard completes that slot before
// the node guard resumes at the next pair.

impl<K, V, Type> NodeRef<marker::Dying, K, V, Type> {
    unsafe fn as_leaf_dying<'short>(&'short mut self) -> &'short mut LeafNode<K, V>
    //@ req *self |-> ?node &*& *node.node.as_ptr() |-> ?contents;
    //@ ens *self |-> node &*& *result |-> contents &*& ref_mut_end_token(result, node.node.as_ptr()) &*& ref_origin(result) == ref_origin(node.node.as_ptr());
    //@ on_unwind_ens false;
    {
        //@ let view = precreate_ref(self);
        //@ init_ref_readonly(view, 1/2);
        let ptr = unsafe { Self::as_leaf_ptr(self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(self, _);
        unsafe { &mut *ptr } //~track_ref_creation
    }
}

unsafe fn duplicate_dying<K,V>(
    node: *const NodeRef<marker::Dying,K,V,marker::LeafOrInternal>,
) -> NodeRef<marker::Dying,K,V,marker::LeafOrInternal>
/*@
req thread_token(?t) &*& [?q](*node |-> ?value);
@*/
//@ ens thread_token(t) &*& [q](*node |-> value) &*& result == value;
//@ on_unwind_ens false;
{
    //@ close NodeRef_own::<marker::Dying,K,V,marker::LeafOrInternal>(t, value);
    let duplicated = unsafe { std::ptr::read(node) };
    //@ open NodeRef_own::<marker::Dying,K,V,marker::LeafOrInternal>(t, duplicated);
    duplicated
}

/*@
pred drop_slot_loan<T,N>(
    field: *[MaybeUninit<T>; N], array: *[MaybeUninit<T>; N], slot: *MaybeUninit<T>, index: usize,
    prior: list<MaybeUninit<T>>, later: list<MaybeUninit<T>>
) =
    ref_mut_end_token(array, field) &*&
    ref_mut_end_token(slot, array as *MaybeUninit<T> + index) &*&
    (array as *MaybeUninit<T>)[..index] |-> prior &*&
    (array as *MaybeUninit<T>)[index+1..int_of_const(typeid(N))] |-> later;

lem close_drop_array<T, N>(p: *[T; N])
    req (p as *T)[..int_of_const(typeid(N))] |-> ?values;
    ens *p |-> ?value &*& Array_elems(value) == values;
{
    let base = p as *T;
    close_points_to(p, 1/2);
    assert [1/2](*p |-> ?value);
    Array_to_array(p);
    merge_fractions array(base, int_of_const(typeid(N)), _);
    assert Array_elems(value) == values;
    close_points_to(p);
}

lem end_drop_slot<T,N>(field: *[MaybeUninit<T>; N], slot: *MaybeUninit<T>, index: usize)
    req drop_slot_loan(field,?array,slot,index,?before,?after) &*& *slot |-> ?entry;
    ens *field |-> ?entries &*& Array_elems(entries) == append(before,cons(entry,after));
{
    open drop_slot_loan(field,array,slot,index,before,after);
    let base = array as *MaybeUninit<T>;
    end_ref_mut(slot);
    close array(base+index+1,0,[]);
    close array(base+index,1,[entry]);
    array_join(base+index);
    array_join(base);
    close_drop_array(array);
    end_ref_mut(array);
}
@*/

impl<K, V, NodeType> Handle<NodeRef<marker::Dying, K, V, NodeType>, marker::KV> {
    unsafe fn project_drop_slots<'short>(
        &'short mut self,
    ) -> (&'short mut MaybeUninit<K>, &'short mut MaybeUninit<V>)
    /*@
    req *self |-> ?incoming &*& leaf_header(incoming.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(incoming.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= incoming.idx &*& incoming.idx < len;
    @*/
    /*@
    ens *self |-> incoming &*&
        ref_mut_end_token(?leaf,incoming.node.node.as_ptr()) &*&
        leaf_header(leaf,parent,parent_idx) &*& (*leaf).len |-> len as u16 &*&
        drop_slot_loan(&(*leaf).keys,?key_array,result.0,incoming.idx,take(incoming.idx,keys),drop(incoming.idx+1,keys)) &*&
        drop_slot_loan(&(*leaf).vals,?val_array,result.1,incoming.idx,take(incoming.idx,vals),drop(incoming.idx+1,vals)) &*&
        *result.0 |-> nth(incoming.idx,keys) &*& *result.1 |-> nth(incoming.idx,vals);
    @*/
    //@ on_unwind_ens false;
    {
        //@ let node = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open leaf_slots(node,len,keys,vals);
        //@ open_points_to(self);
        //@ let view = precreate_ref(&(*self).node);
        //@ init_ref_readonly(view,1/2);
        debug_assert!(self.idx < self.node.merge_len());
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&(*self).node, _);
        //@ open leaf_header(node,parent,parent_idx);
        //@ close_points_to(node);
        let leaf = unsafe { self.node.as_leaf_dying/*@::<K,V,NodeType,'short>@*/() }; //~track_ref_creation
        //@ open_points_to(leaf);
        //@ close_points_to(&(*leaf).keys);
        let key_slot =
            <[MaybeUninit<K>]>::get_unchecked_mut(
                {
                    let key_array = &mut leaf.keys; //~track_ref_creation
                    let slice: &mut [MaybeUninit<K>] = key_array;
                    //@ open_points_to(key_array);
                    //@ let key_base = key_array as *MaybeUninit<K>;
                    //@ array_split(key_base,index);
                    //@ array_split(key_base+index,1);
                    //@ open array(key_base+index,1,_);
                    //@ open array(key_base+index+1,0,_);
                    //@ nth_drop(0,index,keys);
                    //@ drop_twice(1,index,keys);
                    slice
                },
                self.idx,
            );
        //@ close drop_slot_loan(&(*leaf).keys,key_array,key_slot,index,take(index,keys),drop(index+1,keys));
        //@ close_points_to(&(*leaf).vals);
        let val_slot =
            <[MaybeUninit<V>]>::get_unchecked_mut(
                {
                    let val_array = &mut leaf.vals; //~track_ref_creation
                    let slice: &mut [MaybeUninit<V>] = val_array;
                    //@ open_points_to(val_array);
                    //@ let val_base = val_array as *MaybeUninit<V>;
                    //@ array_split(val_base,index);
                    //@ array_split(val_base+index,1);
                    //@ open array(val_base+index,1,_);
                    //@ open array(val_base+index+1,0,_);
                    //@ nth_drop(0,index,vals);
                    //@ drop_twice(1,index,vals);
                    slice
                },
                self.idx,
            );
        //@ close drop_slot_loan(&(*leaf).vals,val_array,val_slot,index,take(index,vals),drop(index+1,vals));
        //@ close leaf_header(leaf,parent,parent_idx);
        //@ assert ref_mut_end_token(?receiver,&(*self).node);
        //@ end_ref_mut(receiver);
        //@ open_points_to(&(*self).node);
        //@ close_points_to(self);
        (key_slot, val_slot)
    }
}

/*@
pred drop_kv_frame<K,V>(
    node: *LeafNode<K,V>, leaf: *LeafNode<K,V>, key: *MaybeUninit<K>, value: *MaybeUninit<V>,
    index: usize, len: usize, keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>,
    parent: Option<NonNull<InternalNode<K,V>>>, parent_idx: MaybeUninit<u16>
) =
    ref_mut_end_token(leaf,node) &*&
    leaf_header(leaf,parent,parent_idx) &*& (*leaf).len |-> len as u16 &*&
    drop_slot_loan(&(*leaf).keys,?keys_ref,key,index,take(index,keys),drop(index+1,keys)) &*&
    drop_slot_loan(&(*leaf).vals,?vals_ref,value,index,take(index,vals),drop(index+1,vals));

lem take_after_replacing_cell<T>(entries: list<T>, len: usize, index: usize, cell: T)
    req 0 <= index &*& index < len &*& len <= length(entries);
    ens drop(index+1,take(len,replace_slot(index,cell,entries))) == drop(index+1,take(len,entries));
{
    let before = take(index,entries);
    let head = append(before,[cell]);
    let tail = drop(index+1,entries);
    length_take(index,entries);
    length_append(before,[cell]);
    append_assoc(before,[cell],tail);
    take_append(len,head,tail);
    drop_append(index+1,head,take(len-index-1,tail));
    drop_0(take(len-index-1,tail));
    take_after_drop(entries,index+1,len-index-1);
}

lem restore_dropped_kv<K,V>(
    node: *LeafNode<K,V>, leaf: *LeafNode<K,V>, key: *MaybeUninit<K>, value: *MaybeUninit<V>,
    index: usize, len: usize, keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>,
    parent: Option<NonNull<InternalNode<K,V>>>, parent_idx: MaybeUninit<u16>
)
    req drop_kv_frame(node,leaf,key,value,index,len,keys,vals,parent,parent_idx) &*&
        *(key as *K) |-> _ &*& *(value as *V) |-> _ &*&
        0 <= index &*& index < len &*& len <= CAPACITY &*& length(keys) == CAPACITY &*& length(vals) == CAPACITY;
    ens leaf_header(node,parent,parent_idx) &*& leaf_slots(node,len,?next_keys,?next_vals) &*&
        drop(index+1,take(len,next_keys)) == drop(index+1,take(len,keys)) &*&
        drop(index+1,take(len,next_vals)) == drop(index+1,take(len,vals));
{
    open drop_kv_frame(node,leaf,key,value,index,len,keys,vals,parent,parent_idx);
    std::mem::close_MaybeUninit_(key);
    std::mem::close_MaybeUninit_(value);
    assert *key |-> ?dead_key;
    assert *value |-> ?dead_val;
    end_drop_slot(&(*leaf).keys,key,index);
    end_drop_slot(&(*leaf).vals,value,index);
    assert *(&(*leaf).keys) |-> ?repacked_keys;
    assert *(&(*leaf).vals) |-> ?repacked_vals;
    assert Array_elems(repacked_keys) == replace_slot(index,dead_key,keys);
    assert Array_elems(repacked_vals) == replace_slot(index,dead_val,vals);
    Array_to_array(&(*leaf).keys);
    Array_to_array(&(*leaf).vals);
    assert (*leaf).keys[..CAPACITY] |-> replace_slot(index,dead_key,keys);
    assert (*leaf).vals[..CAPACITY] |-> replace_slot(index,dead_val,vals);
    open leaf_header(leaf,parent,parent_idx);
    close_points_to(leaf);
    end_ref_mut(leaf);
    open_points_to(node);
    assert (*node).keys[..CAPACITY] |-> replace_slot(index,dead_key,keys);
    assert (*node).vals[..CAPACITY] |-> replace_slot(index,dead_val,vals);
    close leaf_header(node,parent,parent_idx);
    close leaf_slots(node,len,_,_);
    take_after_replacing_cell(keys,len,index,dead_key);
    take_after_replacing_cell(vals,len,index,dead_val);
}
@*/

impl<K,V,NodeType> Handle<NodeRef<marker::Dying,K,V,NodeType>,marker::KV> {
    unsafe fn drop_key_val_step(mut self)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= self.idx &*& self.idx < len &*&
        slot_owners(t,drop(self.idx,take(len,keys))) &*& slot_owners(t,drop(self.idx,take(len,vals)));
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.node.node.as_ptr(),parent,parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),len,?final_keys,?final_vals) &*&
        slot_owners(t,drop(self.idx+1,take(len,final_keys))) &*& slot_owners(t,drop(self.idx+1,take(len,final_vals)));
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        drop_kv_frame(self.node.node.as_ptr(),?leaf,?key,?value,self.idx,len,keys,vals,parent,parent_idx) &*&
        length(keys) == CAPACITY &*& length(vals) == CAPACITY &*& len <= CAPACITY &*&
        *(key as *K) |-> _ &*& exists::<bool>(?pending) &*&
        (if pending {
            *value |-> ?contents &*& contents.inner() == some(?v) &*& <V>.own(t,v)
        } else {
            *(value as *V) |-> _
        }) &*& slot_owners(t,drop(self.idx+1,take(len,keys))) &*& slot_owners(t,drop(self.idx+1,take(len,vals)));
    @*/
    {
        //@ assert *(&mut self) |-> ?incoming;
        //@ let node = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open leaf_slots(node,len,keys,vals);
        //@ assert length(keys) == CAPACITY && length(vals) == CAPACITY;
        //@ close leaf_slots(node,len,keys,vals);
        let (key_slot,value_slot) = self.project_drop_slots/*@::<K,V,NodeType,'static>@*/();
        //@ assert ref_mut_end_token(?leaf,node);
        //@ close drop_kv_frame(node,leaf,key_slot,value_slot,index,len,keys,vals,parent,parent_idx);
        //@ length_take(len,keys);
        //@ length_take(len,vals);
        //@ drop_n_plus_one(index,take(len,keys));
        //@ drop_n_plus_one(index,take(len,vals));
        //@ open slot_owners(t,drop(index,take(len,keys)));
        //@ open slot_owners(t,drop(index,take(len,vals)));
        //@ nth_take_range(keys,len,index);
        //@ nth_take_range(vals,len,index);
        //@ drop_twice(1,index,take(len,keys));
        //@ drop_twice(1,index,take(len,vals));
        unsafe { drop_pair(key_slot,value_slot) };
        //@ restore_dropped_kv(node,leaf,key_slot,value_slot,index,len,keys,vals,parent,parent_idx);
    }
}

impl<K,V> Handle<NodeRef<marker::Dying,K,V,marker::LeafOrInternal>,marker::KV> {
    unsafe fn new_dying_kv(node: NodeRef<marker::Dying,K,V,marker::LeafOrInternal>, idx: usize) -> Self
    //@ req (*node.node.as_ptr()).len |-> ?len &*& 0 <= idx &*& idx < len;
    //@ ens (*node.node.as_ptr()).len |-> len &*& result.node == node &*& result.idx == idx;
    //@ on_unwind_ens false;
    {
        unsafe { debug_assert!(idx < node.len()) };
        let result = Handle { node, idx, _marker: PhantomData };
        //@ close_points_to(&node,1/2);
        result
    }
}

unsafe fn drop_at<K,V>(
    node: *const NodeRef<marker::Dying,K,V,marker::LeafOrInternal>,
    index: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    [?q](*node |-> ?incoming) &*&
    leaf_header(incoming.node.as_ptr(),?parent,?parent_idx) &*&
    leaf_slots(incoming.node.as_ptr(),?len,?keys,?vals) &*& 0 <= index &*& index < len &*&
    slot_owners(t,drop(index,take(len,keys))) &*& slot_owners(t,drop(index,take(len,vals)));
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    [q](*node |-> incoming) &*&
    leaf_header(incoming.node.as_ptr(),parent,parent_idx) &*& leaf_slots(incoming.node.as_ptr(),len,?next_keys,?next_vals) &*&
    slot_owners(t,drop(index+1,take(len,next_keys))) &*& slot_owners(t,drop(index+1,take(len,next_vals)));
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    [q](*node |-> incoming) &*&
    drop_kv_frame(incoming.node.as_ptr(),?leaf,?key,?value,index,len,keys,vals,parent,parent_idx) &*&
    length(keys) == CAPACITY &*& length(vals) == CAPACITY &*& len <= CAPACITY &*& 0 <= index &*& index < len &*&
    *(key as *K) |-> _ &*& exists::<bool>(?pending) &*&
    (if pending {
        *value |-> ?contents &*& contents.inner() == some(?v) &*& <V>.own(t,v)
    } else {
        *(value as *V) |-> _
    }) &*& slot_owners(t,drop(index+1,take(len,keys))) &*& slot_owners(t,drop(index+1,take(len,vals)));
@*/
{
    //@ let leaf = incoming.node.as_ptr();
    //@ open leaf_slots(leaf,len,keys,vals);
    let kv = unsafe { Handle::new_dying_kv(duplicate_dying(node), index) };
    //@ close leaf_slots(leaf,len,keys,vals);
    unsafe { kv.drop_key_val_step() };
}

unsafe fn drop_remaining<K,V>(
    node: *const NodeRef<marker::Dying,K,V,marker::LeafOrInternal>,
    start: usize,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    [?q](*node |-> ?incoming) &*&
    leaf_header(incoming.node.as_ptr(),?parent,?parent_idx) &*&
    leaf_slots(incoming.node.as_ptr(),?len,?keys,?vals) &*& 0 <= start &*& start <= len &*&
    slot_owners(t,drop(start,take(len,keys))) &*& slot_owners(t,drop(start,take(len,vals)));
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    [q](*node |-> incoming) &*&
    leaf_header(incoming.node.as_ptr(),parent,parent_idx) &*& leaf_slots(incoming.node.as_ptr(),len,_,_);
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
    [q](*node |-> incoming) &*&
    drop_kv_frame(incoming.node.as_ptr(),?leaf,?key,?value,?index,len,?ks,?vs,parent,parent_idx) &*&
    length(ks) == CAPACITY &*& length(vs) == CAPACITY &*& len <= CAPACITY &*& start <= index &*& index < len &*&
    *(key as *K) |-> _ &*& exists::<bool>(?pending) &*&
    (if pending {
        *value |-> ?contents &*& contents.inner() == some(?v) &*& <V>.own(t,v)
    } else {
        *(value as *V) |-> _
    }) &*& slot_owners(t,drop(index+1,take(len,ks))) &*& slot_owners(t,drop(index+1,take(len,vs)));
@*/
{
    //@ let leaf = incoming.node.as_ptr();
    //@ open leaf_slots(leaf,len,keys,vals);
    //@ let view = precreate_ref(node);
    //@ init_ref_readonly(view,1/2);
    let count = unsafe { (*node).len() };
    //@ end_ref_readonly(view);
    //@ merge_fractions points_to(node, _);
    //@ close leaf_slots(leaf,len,keys,vals);
    let mut iter = (start..count).into_iter();
    loop {
        /*@
        inv iter |-> ?state &*& state.end == len &*& start <= state.start &*& state.start <= len &*&
            thread_token(t) &*& lifetime_token(func_lft) &*& type_interp::<K>() &*& type_interp::<V>() &*&
            [q](*node |-> incoming) &*&
            leaf_header(leaf,parent,parent_idx) &*& leaf_slots(leaf,len,?active_keys,?active_vals) &*&
            slot_owners(t,drop(state.start,take(len,active_keys))) &*& slot_owners(t,drop(state.start,take(len,active_vals)));
        @*/
        let iter_ref = &mut iter;
        let next = iter_ref.next();
        match next {
            None => break,
            Some(i) => unsafe { drop_at(node, i) },
        }
    }
    //@ assert leaf_slots(leaf,len,?last_keys,?last_vals);
    //@ open leaf_slots(leaf,len,last_keys,last_vals);
    //@ length_take(len,last_keys);
    //@ length_take(len,last_vals);
    //@ drop_length(take(len,last_keys));
    //@ drop_length(take(len,last_vals));
    //@ open slot_owners::<K>(t,nil);
    //@ open slot_owners::<V>(t,nil);
    //@ close leaf_slots(leaf,len,last_keys,last_vals);
}

/*@ pred resume_phase(inside_value: bool) = true; @*/

unsafe fn finish_drop_value<V>(value: *mut MaybeUninit<V>, pending: bool)
/*@
req thread_token(?t) &*& type_interp::<V>() &*&
    (if pending {
        *value |-> ?contents &*& contents.inner() == some(?v) &*& <V>.own(t,v)
    } else {
        *(value as *V) |-> _
    });
@*/
//@ ens thread_token(t) &*& type_interp::<V>() &*& *(value as *V) |-> _;
//@ on_unwind_ens thread_token(t) &*& type_interp::<V>() &*& *(value as *V) |-> _;
{
    if pending {
        unsafe { drop_guarded_value(value) };
    }
}

unsafe fn resume_drop_remaining<K,V>(
    node: *const NodeRef<marker::Dying,K,V,marker::LeafOrInternal>,
    leaf: *mut LeafNode<K,V>,
    key: *mut MaybeUninit<K>,
    value: *mut MaybeUninit<V>,
    index: usize,
    len: usize,
    pending: bool,
)
/*@
req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& [?q](*node |-> ?incoming) &*&
    drop_kv_frame(incoming.node.as_ptr(),leaf,key,value,index,len,?keys,?vals,?parent,?parent_idx) &*&
    length(keys) == CAPACITY &*& length(vals) == CAPACITY &*& 0 <= index &*& index < len &*& len <= CAPACITY &*&
    *(key as *K) |-> _ &*&
    (if pending {
        *value |-> ?contents &*& contents.inner() == some(?v) &*& <V>.own(t,v)
    } else {
        *(value as *V) |-> _
    }) &*& slot_owners(t,drop(index+1,take(len,keys))) &*& slot_owners(t,drop(index+1,take(len,vals)));
@*/
/*@
ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& [q](*node |-> incoming) &*&
    leaf_header(incoming.node.as_ptr(),parent,parent_idx) &*& leaf_slots(incoming.node.as_ptr(),len,_,_);
@*/
/*@
on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& [q](*node |-> incoming) &*&
    resume_phase(?inside_value) &*&
    if inside_value {
        drop_kv_frame(incoming.node.as_ptr(),leaf,key,value,index,len,keys,vals,parent,parent_idx) &*&
        *(key as *K) |-> _ &*& *(value as *V) |-> _ &*&
        slot_owners(t,drop(index+1,take(len,keys))) &*& slot_owners(t,drop(index+1,take(len,vals)))
    } else {
        drop_kv_frame(incoming.node.as_ptr(),?rest_leaf,?rest_key,?rest_value,?remaining,len,?ks,?vs,parent,parent_idx) &*&
        length(ks) == CAPACITY &*& length(vs) == CAPACITY &*& index < remaining &*& remaining < len &*&
        *(rest_key as *K) |-> _ &*& exists::<bool>(?rest_pending) &*&
        (if rest_pending {
            *rest_value |-> ?bits &*& bits.inner() == some(?entry) &*& <V>.own(t,entry)
        } else {
            *(rest_value as *V) |-> _
        }) &*& slot_owners(t,drop(remaining+1,take(len,ks))) &*& slot_owners(t,drop(remaining+1,take(len,vs)))
    };
@*/
{
    //@ close resume_phase(true);
    unsafe { finish_drop_value(value, pending) };
    //@ open resume_phase(true);
    //@ restore_dropped_kv(incoming.node.as_ptr(),leaf,key,value,index,len,keys,vals,parent,parent_idx);
    //@ close resume_phase(false);
    unsafe { drop_remaining(node, index + 1) };
    //@ open resume_phase(false);
}


impl<'a, K: 'a, V: 'a, NodeType> Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV> {
    unsafe fn split_leaf_data<'short, 'dst>(&'short mut self, new_node: &'dst mut LeafNode<K, V>) -> (K, V)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> ?incoming &*& leaf_header(incoming.node.node.as_ptr(), ?parent, ?parent_idx) &*&
        leaf_slots(incoming.node.node.as_ptr(), ?len, ?keys, ?vals) &*& 0 <= incoming.idx &*& incoming.idx < len &*&
        nth(incoming.idx, keys).inner() == some(?key) &*& nth(incoming.idx, vals).inner() == some(?val) &*&
        <K>.own(t, key) &*& <V>.own(t, val) &*&
        leaf_header(new_node, ?right_parent, ?right_index) &*& leaf_slots(new_node, _, ?right_keys, ?right_vals);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        *self |-> incoming &*& leaf_header(incoming.node.node.as_ptr(), parent, parent_idx) &*&
        leaf_slots(incoming.node.node.as_ptr(), incoming.idx, keys, vals) &*&
        leaf_header(new_node, right_parent, right_index) &*&
        leaf_slots(new_node, len - incoming.idx - 1,
            append(take(len - incoming.idx - 1, drop(incoming.idx + 1, keys)), drop(len - incoming.idx - 1, right_keys)),
            append(take(len - incoming.idx - 1, drop(incoming.idx + 1, vals)), drop(len - incoming.idx - 1, right_vals))) &*&
        result.0 == key &*& result.1 == val &*& <K>.own(t, key) &*& <V>.own(t, val);
    @*/
    //@ on_unwind_ens false;
    {
        //@ let left = incoming.node.node.as_ptr();
        //@ std::ptr::NonNull_Sized_as_ptr(incoming.node.node);
        //@ open leaf_slots(left, len, keys, vals);
        //@ open leaf_slots(new_node, _, right_keys, right_vals);
        //@ open_points_to(self);
        //@ let check_view = precreate_ref(&(*self).node);
        //@ init_ref_readonly(check_view, 1/2);
        unsafe { debug_assert!(self.idx < self.node.merge_len()); }
        //@ end_ref_readonly(check_view);
        //@ merge_fractions points_to(&(*self).node, _);
        //@ let len_view = precreate_ref(&(*self).node);
        //@ init_ref_readonly(len_view, 1/2);
        let old_len = unsafe { self.node.merge_len() };
        //@ end_ref_readonly(len_view);
        //@ merge_fractions points_to(&(*self).node, _);
        let new_len = old_len - self.idx - 1;
        new_node.len = new_len as u16;
        unsafe {
            //@ close leaf_without_keys(left, parent, parent_idx, old_len as u16, vals);
            let keys_slot = self.node.key_area_slot_mut/*@::<'a,K,V,NodeType,'short>@*/(self.idx);
            //@ assert keys_slot_loan(left, keys_slot, incoming.idx, parent, parent_idx, old_len as u16, vals, _, _);
            //@ let keys_ref = precreate_ref(keys_slot);
            //@ init_ref_readonly(keys_ref, 1/2);
            let promoted_keys = keys_slot.assume_init_read();
            //@ end_ref_readonly(keys_ref);
            //@ merge_fractions points_to(keys_slot, _);
            //@ end_keys_slot(left, keys_slot);
            //@ append_take_drop_n(keys, incoming.idx);
            //@ drop_n_plus_one(incoming.idx, keys);
            //@ assert drop(incoming.idx, keys) == cons(nth(incoming.idx, keys), drop(incoming.idx + 1, keys));
            //@ open leaf_without_keys(left, parent, parent_idx, old_len as u16, vals);
            //@ close leaf_without_vals(left, parent, parent_idx, old_len as u16, keys);
            let vals_slot = self.node.val_area_slot_mut/*@::<'a,K,V,NodeType,'short>@*/(self.idx);
            //@ assert vals_slot_loan(left, vals_slot, incoming.idx, parent, parent_idx, old_len as u16, keys, _, _);
            //@ let vals_ref = precreate_ref(vals_slot);
            //@ init_ref_readonly(vals_ref, 1/2);
            let promoted_vals = vals_slot.assume_init_read();
            //@ end_ref_readonly(vals_ref);
            //@ merge_fractions points_to(vals_slot, _);
            //@ end_vals_slot(left, vals_slot);
            //@ append_take_drop_n(vals, incoming.idx);
            //@ drop_n_plus_one(incoming.idx, vals);
            //@ assert drop(incoming.idx, vals) == cons(nth(incoming.idx, vals), drop(incoming.idx + 1, vals));
            //@ open leaf_without_vals(left, parent, parent_idx, old_len as u16, keys);
            //@ close leaf_without_keys(left, parent, parent_idx, old_len as u16, vals);
            move_to_slice(
                self.node.key_area_range_mut/*@::<'a,K,V,NodeType,'short>@*/(self.idx + 1..old_len),
                {
                    //@ close_points_to(&(*new_node).keys);
                    let keys_array = &mut new_node.keys; //~track_ref_creation
                    //@ open_points_to(keys_array);
                    //@ let keys_base = keys_array as *MaybeUninit<K>;
                    //@ insertion_slot_limits(keys_base);
                    //@ move_slice_offset(keys_base, CAPACITY, new_len);
                    //@ array_split(keys_base, new_len);
                    let keys_target = &mut keys_array[..new_len];
                    //@ close move_slice(keys_target as *MaybeUninit<K>, new_len, _);
                    keys_target
                },
            );
            //@ assert keys_range_loan(left, ?keys_source, incoming.idx + 1, old_len, parent, parent_idx, old_len as u16, vals, _, _);
            //@ assert ref_mut_end_token(?keys_lent_array, &(*new_node).keys);
            //@ let keys_lent_base = keys_lent_array as *MaybeUninit<K>;
            //@ assert slice_ref_mut_end_token(?keys_lent_slice, keys_lent_base, new_len);
            //@ end_keys_range(left, keys_source);
            //@ let keys_copied = take(new_len, drop(incoming.idx + 1, keys));
            //@ open move_slice(keys_lent_slice as *MaybeUninit<K>, new_len, keys_copied);
            //@ end_slice_ref_mut(keys_lent_slice);
            //@ array_join(keys_lent_base);
            //@ close_points_to(keys_lent_array);
            //@ end_ref_mut(keys_lent_array);
            //@ open_points_to(&(*new_node).keys);
            //@ drop_twice(new_len, incoming.idx + 1, keys);
            //@ append_take_drop_n(drop(incoming.idx + 1, keys), new_len);
            //@ append_assoc(take(incoming.idx + 1, keys), keys_copied, drop(old_len, keys));
            //@ append_take_drop_n(keys, incoming.idx + 1);
            //@ open leaf_without_keys(left, parent, parent_idx, old_len as u16, vals);
            //@ close leaf_without_vals(left, parent, parent_idx, old_len as u16, keys);
            move_to_slice(
                self.node.val_area_range_mut/*@::<'a,K,V,NodeType,'short>@*/(self.idx + 1..old_len),
                {
                    //@ close_points_to(&(*new_node).vals);
                    let vals_array = &mut new_node.vals; //~track_ref_creation
                    //@ open_points_to(vals_array);
                    //@ let vals_base = vals_array as *MaybeUninit<V>;
                    //@ insertion_slot_limits(vals_base);
                    //@ move_slice_offset(vals_base, CAPACITY, new_len);
                    //@ array_split(vals_base, new_len);
                    let vals_target = &mut vals_array[..new_len];
                    //@ close move_slice(vals_target as *MaybeUninit<V>, new_len, _);
                    vals_target
                },
            );
            //@ assert vals_range_loan(left, ?vals_source, incoming.idx + 1, old_len, parent, parent_idx, old_len as u16, keys, _, _);
            //@ assert ref_mut_end_token(?vals_lent_array, &(*new_node).vals);
            //@ let vals_lent_base = vals_lent_array as *MaybeUninit<V>;
            //@ assert slice_ref_mut_end_token(?vals_lent_slice, vals_lent_base, new_len);
            //@ end_vals_range(left, vals_source);
            //@ let vals_copied = take(new_len, drop(incoming.idx + 1, vals));
            //@ open move_slice(vals_lent_slice as *MaybeUninit<V>, new_len, vals_copied);
            //@ end_slice_ref_mut(vals_lent_slice);
            //@ array_join(vals_lent_base);
            //@ close_points_to(vals_lent_array);
            //@ end_ref_mut(vals_lent_array);
            //@ open_points_to(&(*new_node).vals);
            //@ drop_twice(new_len, incoming.idx + 1, vals);
            //@ append_take_drop_n(drop(incoming.idx + 1, vals), new_len);
            //@ append_assoc(take(incoming.idx + 1, vals), vals_copied, drop(old_len, vals));
            //@ append_take_drop_n(vals, incoming.idx + 1);
            //@ open leaf_without_vals(left, parent, parent_idx, old_len as u16, keys);
            //@ close leaf_without_len(left, parent, parent_idx, keys, vals);
            *self.node.len_mut/*@::<'a,K,V,NodeType,'short>@*/() = self.idx as u16;
            //@ assert len_loan(left, ?length, parent, parent_idx, keys, vals);
            //@ end_len_loan(left, length);
            //@ open leaf_without_len(left, parent, parent_idx, keys, vals);
            //@ close leaf_header(left, parent, parent_idx);
            //@ close leaf_slots(left, incoming.idx, keys, vals);
            //@ close leaf_slots(new_node, new_len, _, _);
            //@ close_points_to(self);
            (promoted_keys, promoted_vals)
        }
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Leaf> {
    unsafe fn from_new_leaf<A: AllocatorClone>(leaf: Box<LeafNode<K, V>, A>) -> Self
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<A>() &*& Box_in(t, leaf, ?id, ?contents);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<A>() &*& result.height == 0 &*&
        points_to_at_lft(id.lft, result.node.as_ptr(), contents) &*&
        std::alloc::alloc_block_in(id, result.node.as_ptr() as *u8, std::alloc::Layout::new::<LeafNode<K,V>>()) &*&
        result.node.as_ptr() as usize != 0;
    @*/
    //@ on_unwind_ens false;
    {
        let (node, _alloc) = Box::into_non_null_with_allocator(leaf);
        //@ std::alloc::Allocator_to_own(_alloc);
        NodeRef { height: 0, node, _marker: PhantomData }
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV> {
    unsafe fn split_production_leaf<A: AllocatorClone>(
        mut self, alloc: A,
    ) -> SplitResult<'a, K, V, marker::Leaf>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t, alloc, ?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*&
        lifetime_inclusion(k, id.lft) == true &*&
        self.node.height == 0 &*& leaf_header(self.node.node.as_ptr(), ?parent, ?parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(), ?len, ?keys, ?vals) &*& 0 <= self.idx &*& self.idx < len &*&
        nth(self.idx, keys).inner() == some(?key) &*& nth(self.idx, vals).inner() == some(?val) &*&
        <K>.own(t, key) &*& <V>.own(t, val);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available/2]lifetime_token(k) &*& result.left == self.node &*& result.right.height == 0 &*&
        leaf_header(self.node.node.as_ptr(), parent, parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(), self.idx, keys, vals) &*&
        allocated_leaf(result.right.node.as_ptr(), id, k, available/2) &*&
        (*result.right.node.as_ptr()).parent |-> Option::None &*&
        (*result.right.node.as_ptr()).parent_idx |-> ?right_parent_idx &*&
        result.right.node.as_ptr() != self.node.node.as_ptr() &*&
        leaf_slots(result.right.node.as_ptr(), len - self.idx - 1, ?new_keys, ?new_vals) &*&
        take(len - self.idx - 1, new_keys) == take(len - self.idx - 1, drop(self.idx + 1, keys)) &*&
        take(len - self.idx - 1, new_vals) == take(len - self.idx - 1, drop(self.idx + 1, vals)) &*&
        result.kv.0 == key &*& result.kv.1 == val &*& <K>.own(t, key) &*& <V>.own(t, val);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available]lifetime_token(k) &*& leaf_header(self.node.node.as_ptr(), parent, parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(), len, keys, vals) &*& <K>.own(t, key) &*& <V>.own(t, val);
    @*/
    {
        //@ open exists(k);
        //@ assert *&self |-> ?incoming;
        //@ let suffix_len = len - incoming.idx - 1;
        //@ let left = incoming.node.node.as_ptr();
        //@ open leaf_slots(left, len, keys, vals);
        //@ assert length(keys) == CAPACITY && length(vals) == CAPACITY;
        //@ close leaf_slots(left, len, keys, vals);
        let mut new_node = unsafe { LeafNode::<K,V>::new(alloc) };
        let kv = unsafe {
            self.split_leaf_data/*@::<'a,K,V,marker::Leaf,'a,'a>@*/({ //~track_ref_creation
                let box_view = &mut new_node; //~track_ref_creation
                //@ let contents = std::boxed::Box_separate_contents(box_view);
                //@ let q_box = lifetime_token_trade(k, available, id.lft);
                //@ open_points_to_at_lft(contents, q_box);
                //@ points_to_limits(contents);
                //@ assert *contents |-> ?fresh;
                let destination: &mut LeafNode<K,V> = box_view; //~track_ref_creation
                //@ open_points_to(destination);
                //@ close leaf_header(destination, fresh.parent, fresh.parent_idx);
                //@ close leaf_slots(destination, 0, _, _);
                //@ assert leaf_slots(destination, 0, ?initial_keys, ?initial_vals);
                destination
            })
        };
        //@ assert ref_mut_end_token(?source_view, &mut self);
        //@ assert ref_mut_end_token(?box_ref, &mut new_node);
        //@ assert std::boxed::Box_minus_contents_in(_, t, _, box_ref, id, contents);
        //@ assert ref_mut_end_token(?right_view, contents);
        //@ assert leaf_slots(right_view, suffix_len, ?split_keys, ?split_vals);
        //@ length_drop(incoming.idx + 1, keys);
        //@ length_drop(incoming.idx + 1, vals);
        //@ length_take(suffix_len, drop(incoming.idx + 1, keys));
        //@ length_take(suffix_len, drop(incoming.idx + 1, vals));
        //@ take_append_l(suffix_len, take(suffix_len, drop(incoming.idx + 1, keys)), drop(suffix_len, initial_keys));
        //@ take_append_l(suffix_len, take(suffix_len, drop(incoming.idx + 1, vals)), drop(suffix_len, initial_vals));
        //@ close_points_to(right_view);
        //@ end_ref_mut(right_view);
        //@ assert close_points_to_at_lft_token(1, id.lft, contents, q_box);
        //@ close_points_to_at_lft(contents);
        //@ lifetime_token_trade_back(q_box, id.lft);
        //@ std::boxed::Box_unseparate_contents(box_ref);
        //@ end_ref_mut(box_ref);
        //@ end_ref_mut(source_view);
        let right = unsafe { NodeRef::<marker::Owned,K,V,marker::Leaf>::from_new_leaf(new_node) };
        //@ let ptr = right.node.as_ptr();
        //@ std::ptr::NonNull_Sized_as_ptr(right.node);
        //@ close reserve_allocation(k, available/2);
        //@ let q_alloc = lifetime_token_trade(k, available/2, id.lft);
        //@ open_points_to_at_lft(ptr, q_alloc);
        //@ points_to_limits(ptr);
        //@ open_points_to(ptr);
        //@ close allocated_leaf(ptr, id, k, available/2);
        //@ open reserve_allocation(k, available/2);
        //@ open_points_to(&self);
        //@ close leaf_slots(ptr, len - self.idx - 1, split_keys, split_vals);
        /*@ if ptr == left {
            open leaf_slots(left, incoming.idx, keys, vals);
            open leaf_slots(ptr, suffix_len, split_keys, split_vals);
            merge_fractions LeafNode_len_(left, _);
        } @*/
        let result = SplitResult { left: self.node, kv, right };
        //@ close_points_to(&self);
        result
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Internal> {
    unsafe fn from_new_internal<A: AllocatorClone>(
        internal: Box<InternalNode<K, V>, A>,
        height: NonZero<usize>,
    ) -> Self
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Box_in(t, internal, ?id, ?contents) &*& contents.data.parent == Option::None &*&
        exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k, id.lft) == true &*&
        child_headers(?children) &*& contents.data.len <= CAPACITY &*& length(children) == contents.data.len + 1 &*&
        exists::<list<MaybeUninit<BoxedNode<K,V>>>>(?tail) &*&
        Array_elems(contents.edges) == append(initialized_edges(children), tail);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available/2]lifetime_token(k) &*& result.height == height.get() &*& 0 < result.height &*&
        exists::<NonNull<InternalNode<K,V>>>(?node) &*& result.node.as_ptr() == &(*node.as_ptr()).data &*&
        allocated_internal(node.as_ptr(), id, k, available/2) &*&
        (*result.node.as_ptr()).parent |-> Option::None &*&
        (*result.node.as_ptr()).parent_idx |-> contents.data.parent_idx &*&
        internal_slots(node, contents.data.len, children, Array_elems(contents.data.keys), Array_elems(contents.data.vals));
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(k);
        //@ open exists(tail);
        let (node, _alloc) = Box::into_non_null_with_allocator(internal);
        //@ std::alloc::Allocator_to_own(_alloc);
        //@ let root = node.as_ptr();
        //@ std::ptr::NonNull_Sized_as_ptr(node);
        //@ close reserve_allocation(k, available/2);
        //@ let q_alloc = lifetime_token_trade(k, available/2, id.lft);
        //@ open_points_to_at_lft(root, q_alloc);
        //@ points_to_limits(root);
        //@ open_points_to(root);
        //@ close_points_to(&(*root).edges);
        //@ Array_to_array(&(*root).edges);
        //@ close_points_to(&(*root).data.keys);
        //@ Array_to_array(&(*root).data.keys);
        //@ close_points_to(&(*root).data.vals);
        //@ Array_to_array(&(*root).data.vals);
        //@ close allocated_internal(root, id, k, available/2);
        //@ open reserve_allocation(k, available/2);
        //@ std::num::NonZero_usize_limits(height);
        let mut this = NodeRef { height: height.into(), node: node.cast(), _marker: PhantomData };
        //@ std::ptr::NonNull_new_as_ptr(this.node);
        //@ close exists(node);
        //@ close exists(tail);
        unsafe { this.borrow_mut().correct_all_childrens_parent_links() };
        //@ close node_arrays(root, Array_elems(contents.data.keys), Array_elems(contents.data.vals), Array_elems(contents.edges));
        //@ initialized_edge_count(children);
        //@ take_append_l(length(children), initialized_edges(children), tail);
        //@ close internal_slots(node, contents.data.len, children, Array_elems(contents.data.keys), Array_elems(contents.data.vals));
        //@ close exists(node);
        this
    }
}

// The two half permissions describe the same cells. Their agreement
// carries the element list through the enclosing Box value.
/*@
lem close_known_array<T, N>(p: *[T; N])
    req (p as *T)[..int_of_const(typeid(N))] |-> ?values;
    ens *p |-> ?value &*& Array_elems(value) == values;
{
    let base = p as *T;
    close_points_to(p, 1/2);
    assert [1/2](*p |-> ?value);
    Array_to_array(p);
    merge_fractions array(base, int_of_const(typeid(N)), _);
    assert Array_elems(value) == values;
    close_points_to(p);
}
@*/

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::KV> {
    unsafe fn split_production_internal<A: AllocatorClone>(
        mut self, alloc: A,
    ) -> SplitResult<'a, K, V, marker::Internal>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t, alloc, ?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*&
        lifetime_inclusion(k, id.lft) == true &*& self.node.height > 0 &*&
        exists::<NonNull<InternalNode<K,V>>>(?left) &*& self.node.node.as_ptr() == &(*left.as_ptr()).data &*&
        leaf_header(self.node.node.as_ptr(), ?parent, ?parent_idx) &*& struct_InternalNode_padding(left.as_ptr()) &*&
        internal_slots(left, ?len, ?children, ?keys, ?vals) &*& 0 <= self.idx &*& self.idx < len &*&
        nth(self.idx, keys).inner() == some(?key) &*& nth(self.idx, vals).inner() == some(?val) &*&
        <K>.own(t, key) &*& <V>.own(t, val);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available/2]lifetime_token(k) &*& result.left == self.node &*& result.right.height == self.node.height &*&
        result.right.node.as_ptr() != self.node.node.as_ptr() &*&
        leaf_header(self.node.node.as_ptr(), parent, parent_idx) &*& struct_InternalNode_padding(left.as_ptr()) &*&
        internal_slots(left, self.idx, take(self.idx + 1, children), keys, vals) &*&
        exists::<NonNull<InternalNode<K,V>>>(?right) &*& result.right.node.as_ptr() == &(*right.as_ptr()).data &*&
        allocated_internal(right.as_ptr(), id, k, available/2) &*&
        (*result.right.node.as_ptr()).parent |-> Option::None &*&
        (*result.right.node.as_ptr()).parent_idx |-> ?right_parent_idx &*&
        internal_slots(right, len - self.idx - 1, drop(self.idx + 1, children), ?new_keys, ?new_vals) &*&
        take(len - self.idx - 1, new_keys) == take(len - self.idx - 1, drop(self.idx + 1, keys)) &*&
        take(len - self.idx - 1, new_vals) == take(len - self.idx - 1, drop(self.idx + 1, vals)) &*&
        result.kv.0 == key &*& result.kv.1 == val &*& <K>.own(t, key) &*& <V>.own(t, val);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available]lifetime_token(k) &*& leaf_header(self.node.node.as_ptr(), parent, parent_idx) &*&
        struct_InternalNode_padding(left.as_ptr()) &*& internal_slots(left, len, children, keys, vals) &*&
        <K>.own(t, key) &*& <V>.own(t, val);
    @*/
    {
        //@ open exists(k);
        //@ open exists(left);
        //@ assert *&self |-> ?incoming;
        //@ let source = incoming.node.node.as_ptr();
        //@ let left_ptr = left.as_ptr();
        //@ let first = incoming.idx + 1;
        //@ let suffix_len = len - first;
        //@ let moved_count = suffix_len + 1;
        //@ let kept = take(first, children);
        //@ let moved = drop(first, children);
        //@ std::ptr::NonNull_Sized_as_ptr(left);
        //@ std::ptr::NonNull_Sized_as_ptr(incoming.node.node);
        //@ open internal_slots(left, len, children, keys, vals);
        //@ open_points_to(&self);
        //@ let len_view = precreate_ref(&self.node);
        //@ init_ref_readonly(len_view, 1/2);
        let old_len = unsafe { self.node.merge_len() };
        //@ end_ref_readonly(len_view);
        //@ merge_fractions points_to(&self.node, _);
        //@ close_points_to(&self);
        //@ close internal_slots(left, len, children, keys, vals);
        let mut new_node = unsafe { InternalNode::<K,V>::new(alloc) };
        //@ open internal_slots(left, len, children, keys, vals);
        //@ open node_arrays(left_ptr, keys, vals, ?edges);
        //@ assert length(keys) == CAPACITY && length(vals) == CAPACITY;
        //@ close leaf_slots(source, len, keys, vals);
        //@ let contents = std::boxed::Box_separate_contents(&mut new_node);
        //@ let q_box = lifetime_token_trade(k, available, id.lft);
        //@ open_points_to_at_lft(contents, q_box);
        //@ points_to_limits(contents);
        //@ assert *contents |-> ?initial;
        //@ open_points_to(contents);
        //@ close_points_to(&(*contents).data);
        let kv = self.split_leaf_data/*@::<'a,K,V,marker::Internal,'a,'a>@*/({ //~track_ref_creation
            let destination = &mut new_node.data; //~track_ref_creation
            //@ open_points_to(destination);
            //@ close leaf_header(destination, Option::None, initial.data.parent_idx);
            //@ close leaf_slots(destination, 0, _, _);
            //@ assert leaf_slots(destination, 0, ?initial_keys, ?initial_vals);
            destination
        });
        //@ assert ref_mut_end_token(?source_view, &mut self);
        //@ assert ref_mut_end_token(?right_view, &(*contents).data);
        //@ assert leaf_slots(right_view, suffix_len, ?split_keys, ?split_vals);
        //@ close_points_to(right_view);
        //@ end_ref_mut(right_view);
        //@ end_ref_mut(source_view);
        //@ open_points_to(&(*contents).data);
        let new_len = usize::from(new_node.data.len);

        //@ open leaf_slots(source, incoming.idx, keys, vals);
        //@ open leaf_header(source, parent, parent_idx);
        //@ close_points_to(source);
        //@ close internal_without_edges(left_ptr, _);
        //@ assert (*contents).edges[..CAPACITY + 1] |-> ?fresh_edges;
        //@ open_points_to(&self);
        move_to_slice(
            self.node.edge_area_range_mut/*@::<'a,K,V,'a>@*/(self.idx + 1..old_len + 1), //~track_ref_creation
            {
                //@ close_points_to(&(*contents).edges);
                let right_array = &mut new_node.edges; //~track_ref_creation
                //@ open_points_to(right_array);
                //@ let right_base = right_array as *MaybeUninit<BoxedNode<K,V>>;
                //@ insertion_slot_limits(right_base);
                //@ move_slice_offset(right_base, CAPACITY + 1, moved_count);
                //@ array_split(right_base, moved_count);
                let right_edges = &mut right_array[..new_len + 1];
                //@ close move_slice(right_edges as *MaybeUninit<BoxedNode<K,V>>, moved_count, _);
                right_edges
            },
        );
        //@ assert ref_mut_end_token(?node_view, &(*&self).node);
        //@ assert edges_range_loan(left_ptr, ?left_edges, first, len + 1, ?left_data, _, _);
        //@ end_edges_range(left_ptr, left_edges);
        //@ end_ref_mut(node_view);
        //@ close_points_to(&self);

        //@ let copied = take(moved_count, drop(first, edges));
        //@ assert ref_mut_end_token(?right_lent, &(*contents).edges);
        //@ let right_lent_base = right_lent as *MaybeUninit<BoxedNode<K,V>>;
        //@ assert slice_ref_mut_end_token(?right_lent_slice, right_lent_base, moved_count);
        //@ open move_slice(right_lent_slice as *MaybeUninit<BoxedNode<K,V>>, moved_count, copied);
        //@ end_slice_ref_mut(right_lent_slice);
        //@ array_join(right_lent_base);
        //@ close_points_to(right_lent);
        //@ end_ref_mut(right_lent);
        //@ open_points_to(&(*contents).edges);

        //@ take_after_drop(edges, first, moved_count);
        //@ append_take_drop_n(children, first);
        //@ initialized_edges_append(kept, moved);
        //@ initialized_edge_count(kept);
        //@ initialized_edge_count(moved);
        //@ drop_append(first, initialized_edges(kept), initialized_edges(moved));
        //@ drop_0(initialized_edges(moved));
        //@ assert copied == initialized_edges(moved);
        //@ let tail = drop(moved_count, fresh_edges);
        //@ close_known_array(&(*contents).edges);
        //@ open_points_to(&(*contents).edges);
        //@ close_known_array(&(*contents).data.keys);
        //@ open_points_to(&(*contents).data.keys);
        //@ close_known_array(&(*contents).data.vals);
        //@ open_points_to(&(*contents).data.vals);
        //@ close_points_to(contents);
        //@ close_points_to_at_lft(contents);
        //@ lifetime_token_trade_back(q_box, id.lft);
        //@ std::boxed::Box_unseparate_contents(&mut new_node);
        //@ split_linked_headers(children, left, 0, first);
        //@ forget_link_indices(moved, left, first);
        //@ close exists(k);
        //@ close exists(tail);
        //@ open_points_to(&self);
        //@ open_points_to(&self.node);
        let height = NonZero::new_unchecked(self.node.height);
        //@ close_points_to(&self.node);
        let right = NodeRef::<marker::Owned,K,V,marker::Internal>::from_new_internal(new_node, height);

        //@ open internal_without_edges(left_ptr, left_data);
        //@ open_points_to(source);
        //@ close leaf_header(source, parent, parent_idx);
        //@ drop_twice(moved_count, first, edges);
        //@ append_take_drop_n(drop(first, edges), moved_count);
        //@ append_take_drop_n(edges, first);
        //@ close node_arrays(left_ptr, keys, vals, edges);
        //@ take_twice(edges, first, len + 1);
        //@ take_append_l(first, initialized_edges(kept), initialized_edges(moved));
        //@ close internal_slots(left, incoming.idx, kept, keys, vals);
        //@ length_drop(first, keys);
        //@ length_drop(first, vals);
        //@ length_take(suffix_len, drop(first, keys));
        //@ length_take(suffix_len, drop(first, vals));
        //@ take_append_l(suffix_len, take(suffix_len, drop(first, keys)), drop(suffix_len, initial_keys));
        //@ take_append_l(suffix_len, take(suffix_len, drop(first, vals)), drop(suffix_len, initial_vals));
        //@ assert exists::<NonNull<InternalNode<K,V>>>(?new_right);
        //@ open exists(new_right);
        // Both nodes own their length fields exclusively.
        /*@ if right.node.as_ptr() == source {
            open internal_slots(left, incoming.idx, kept, keys, vals);
            open internal_slots(new_right, suffix_len, moved, _, _);
            merge_fractions LeafNode_len_(source, _);
        } @*/
        //@ close exists(new_right);
        let result = SplitResult { left: self.node, kv, right };
        //@ close_points_to(&self);
        result
    }
}

// Production insertion into an internal B-tree node.

/*@
fix inserted_prefix<T>(slots: list<MaybeUninit<T>>, n: usize, index: usize, value: T) -> list<MaybeUninit<T>> {
    append(
        append(take(index, take(n, slots)), cons(MaybeUninit::new(value), take(n - index - 1, drop(index, take(n, slots))))),
        drop(n, slots))
}

lem nth_inserted_prefix<T>(slots: list<MaybeUninit<T>>, n: usize, index: usize, value: T)
    req 0 <= index &*& index < n &*& n <= length(slots);
    ens nth(index, inserted_prefix(slots, n, index, value)) == MaybeUninit::new(value);
{
    let before = take(index, take(n, slots));
    let rest = cons(MaybeUninit::new(value), take(n - index - 1, drop(index, take(n, slots))));
    length_take(n, slots);
    length_take(index, take(n, slots));
    length_append(before, rest);
    nth_append_r(before, rest, 0);
    nth_append(append(before, rest), drop(n, slots), index);
}
@*/

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    unsafe fn insert_fit_production<'short>(&'short mut self, key: K, val: V, edge: Root<K, V>)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        *self |-> ?incoming &*& incoming.node.height > 0 &*& edge.height == incoming.node.height - 1 &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& incoming.node.node.as_ptr() == &(*parent.as_ptr()).data &*&
        leaf_header(incoming.node.node.as_ptr(), ?ancestor, ?parent_idx) &*& struct_InternalNode_padding(parent.as_ptr()) &*&
        internal_slots(parent, ?len, ?children, ?keys, ?vals) &*& 0 <= incoming.idx &*& incoming.idx <= len &*& len < CAPACITY &*&
        detached_child(edge.node.as_ptr());
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,val) &*& *self |-> incoming &*&
        leaf_header(incoming.node.node.as_ptr(), ancestor, parent_idx) &*& struct_InternalNode_padding(parent.as_ptr()) &*&
        internal_slots(parent, len + 1, append(take(incoming.idx+1, children), cons(edge.node, drop(incoming.idx+1, children))),
            ?fitted_keys, ?fitted_vals) &*&
        fitted_keys == inserted_prefix(keys, len + 1, incoming.idx, key) &*&
        fitted_vals == inserted_prefix(vals, len + 1, incoming.idx, val) &*&
        nth(incoming.idx, fitted_keys).inner() == some(key) &*& nth(incoming.idx, fitted_vals).inner() == some(val);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(parent);
        //@ let node = incoming.node.node.as_ptr();
        //@ let parent_ptr = parent.as_ptr();
        //@ let right = edge.node;
        //@ let index = incoming.idx;
        //@ std::ptr::NonNull_Sized_as_ptr(parent);
        //@ std::ptr::NonNull_Sized_as_ptr(incoming.node.node);
        //@ open internal_slots(parent, len, children, keys, vals);
        //@ open node_arrays(parent_ptr, keys, vals, ?edges);
        //@ open_points_to(self);
        //@ let cap_view = precreate_ref(&(*self).node);
        //@ init_ref_readonly(cap_view, 1/2);
        debug_assert!(self.node.merge_len() < CAPACITY);
        //@ end_ref_readonly(cap_view);
        //@ merge_fractions points_to(&(*self).node, _);
        //@ open_points_to(&(*self).node);
        debug_assert!(edge.height == self.node.height - 1);
        //@ close_points_to(&(*self).node);
        //@ let len_view = precreate_ref(&(*self).node);
        //@ init_ref_readonly(len_view, 1/2);
        let new_len = self.node.merge_len() + 1;
        //@ end_ref_readonly(len_view);
        //@ merge_fractions points_to(&(*self).node, _);

        //@ open leaf_header(node, ancestor, parent_idx);
        //@ close leaf_without_keys(node, ancestor, parent_idx, len as u16, vals);
        slice_insert(
            {
                let keys_view = self.node.key_area_prefix_mut/*@::<'a,K,V,marker::Internal,'short>@*/(..new_len); //~track_ref_creation
                //@ open move_slice(keys_view as *MaybeUninit<K>, len + 1, _);
                keys_view
            },
            self.idx, key,
        );
        //@ assert ref_mut_end_token(?keys_receiver, &(*self).node);
        //@ assert keys_range_loan(node, ?keys_lent, 0, len + 1, ancestor, parent_idx, len as u16, vals, _, _);
        //@ close move_slice(keys_lent as *MaybeUninit<K>, len + 1, _);
        //@ end_keys_range(node, keys_lent);
        //@ end_ref_mut(keys_receiver);
        //@ open leaf_without_keys(node, ancestor, parent_idx, len as u16, vals);
        //@ assert (*node).keys[..CAPACITY] |-> ?fitted_keys;
        //@ take_0(keys);
        //@ drop_0(keys);
        //@ nth_inserted_prefix(keys, len + 1, index, key);
        //@ close leaf_without_vals(node, ancestor, parent_idx, len as u16, fitted_keys);
        slice_insert(
            {
                let vals_view = self.node.val_area_prefix_mut/*@::<'a,K,V,marker::Internal,'short>@*/(..new_len); //~track_ref_creation
                //@ open move_slice(vals_view as *MaybeUninit<V>, len + 1, _);
                vals_view
            },
            self.idx, val,
        );
        //@ assert ref_mut_end_token(?vals_receiver, &(*self).node);
        //@ assert vals_range_loan(node, ?vals_lent, 0, len + 1, ancestor, parent_idx, len as u16, fitted_keys, _, _);
        //@ close move_slice(vals_lent as *MaybeUninit<V>, len + 1, _);
        //@ end_vals_range(node, vals_lent);
        //@ end_ref_mut(vals_receiver);
        //@ open leaf_without_vals(node, ancestor, parent_idx, len as u16, fitted_keys);
        //@ assert (*node).vals[..CAPACITY] |-> ?fitted_vals;
        //@ take_0(vals);
        //@ drop_0(vals);
        //@ nth_inserted_prefix(vals, len + 1, index, val);

        //@ close_points_to(node);
        //@ close internal_without_edges(parent_ptr, _);
        //@ std::ptr::close_NonNull_own(t, right);
        //@ produce_type_interp::<NonNull<LeafNode<K,V>>>();
        slice_insert(
            {
                let edges_view = self.node.edge_area_prefix_mut/*@::<'a,K,V,'short>@*/(..new_len + 1); //~track_ref_creation
                //@ open move_slice(edges_view as *MaybeUninit<BoxedNode<K,V>>, len + 2, _);
                edges_view
            },
            self.idx + 1, edge.node,
        );
        //@ leak <NonNull<LeafNode<K,V>>>.own(t,right);
        //@ std::ptr::open_NonNull_own(t,right);
        //@ leak type_interp::<NonNull<LeafNode<K,V>>>();
        //@ assert ref_mut_end_token(?edges_receiver, &(*self).node);
        //@ assert edges_range_loan(parent_ptr, ?edges_lent, 0, len + 2, ?data, _, _);
        //@ close move_slice(edges_lent as *MaybeUninit<BoxedNode<K,V>>, len + 2, _);
        //@ end_edges_range(parent_ptr, edges_lent);
        //@ end_ref_mut(edges_receiver);
        //@ open internal_without_edges(parent_ptr, data);
        //@ open_points_to(node);

        //@ close leaf_without_len(node, ancestor, parent_idx, fitted_keys, fitted_vals);
        *self.node.len_mut/*@::<'a,K,V,marker::Internal,'short>@*/() = new_len as u16; //~track_ref_creation
        //@ assert ref_mut_end_token(?len_receiver, &(*self).node);
        //@ assert len_loan(node, ?new_length, ancestor, parent_idx, fitted_keys, fitted_vals);
        //@ end_len_loan(node, new_length);
        //@ end_ref_mut(len_receiver);
        //@ open leaf_without_len(node, ancestor, parent_idx, fitted_keys, fitted_vals);

        //@ let before = take(index + 1, children);
        //@ let after = drop(index + 1, children);
        //@ let inserted = cons(right, after);
        //@ let inactive = drop(len + 2, edges);
        //@ split_linked_headers(children, parent, 0, index + 1);
        //@ forget_link_indices(after, parent, index + 1);
        //@ open detached_child(right.as_ptr());
        //@ close child_headers(inserted);
        //@ length_take(index + 1, children);
        //@ length_drop(index + 1, children);
        //@ initialized_edge_split(children, index + 1);
        //@ initialized_edge_count(before);
        //@ initialized_edge_count(inserted);
        //@ take_after_drop(edges, index + 1, len - index);
        //@ take_after_drop(edges, index + 1, len + 1 - index);
        //@ take_twice(drop(index + 1, edges), len - index, len + 1 - index);
        //@ take_twice(edges, index + 1, len + 2);
        //@ take_twice(edges, index + 1, len + 1);
        //@ append_assoc(initialized_edges(before), initialized_edges(inserted), inactive);
        //@ close exists(parent);
        //@ close exists(pair(initialized_edges(before), inactive));
        self.node.relink_range/*@::<'a,K,V,'short>@*/(self.idx + 1..new_len + 1); //~track_ref_creation
        //@ assert ref_mut_end_token(?relink_receiver, &(*self).node);
        //@ end_ref_mut(relink_receiver);
        //@ join_linked_headers(before, inserted, parent, 0);
        //@ initialized_edges_append(before, inserted);
        //@ let active = initialized_edges(append(before, inserted));
        //@ take_append_l(len + 2, active, inactive);
        //@ take_length(active);
        //@ close node_arrays(parent_ptr, fitted_keys, fitted_vals, append(active, inactive));
        //@ close internal_slots(parent, len + 1, append(before, inserted), fitted_keys, fitted_vals);
        //@ close leaf_header(node, ancestor, parent_idx);
        //@ close_points_to(self);
    }
}

/*@
fix insert_item<T>(items: list<T>, at: usize, item: T) -> list<T> {
    append(take(at, items), cons(item, drop(at, items)))
}

lem insert_item_across_split<T>(items: list<T>, cut: usize, at: usize, item: T)
    req 0 <= cut &*& cut <= length(items) &*& 0 <= at &*& at <= length(items);
    ens insert_item(items, at, item) == if at <= cut {
        append(insert_item(take(cut, items), at, item), drop(cut, items))
    } else {
        append(take(cut, items), insert_item(drop(cut, items), at - cut, item))
    };
{
    if at <= cut {
        take_twice(items, at, cut);
        take_after_drop(items, at, cut - at);
        drop_twice(cut - at, at, items);
        append_take_drop_n(drop(at, items), cut - at);
        append_assoc(take(at, items), cons(item, drop(at, take(cut, items))), drop(cut, items));
    } else {
        length_take(cut, items);
        append_take_drop_n(items, cut);
        take_append(at, take(cut, items), drop(cut, items));
        drop_twice(at - cut, cut, items);
        append_assoc(take(cut, items), take(at - cut, drop(cut, items)), cons(item, drop(at, items)));
    }
}
@*/

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Internal>, marker::Edge> {
    unsafe fn insert_production<A: AllocatorClone>(
        mut self, key: K, val: V, edge: Root<K, V>, alloc: A,
    ) -> Option<SplitResult<'a, K, V, marker::Internal>>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t, alloc, ?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*&
        lifetime_inclusion(k, id.lft) == true &*& self.node.height > 0 &*& edge.height == self.node.height - 1 &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& self.node.node.as_ptr() == &(*parent.as_ptr()).data &*&
        leaf_header(self.node.node.as_ptr(), ?ancestor, ?parent_idx) &*& struct_InternalNode_padding(parent.as_ptr()) &*&
        internal_slots(parent, ?len, ?children, ?keys, ?vals) &*& 0 <= self.idx &*& self.idx <= len &*&
        pivot_owner(t, len, self.idx, keys, vals) &*& detached_child(edge.node.as_ptr()) &*& <K>.own(t, key) &*& <V>.own(t, val);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        <K>.own(t, key) &*& <V>.own(t, val) &*& leaf_header(self.node.node.as_ptr(), ancestor, parent_idx) &*&
        struct_InternalNode_padding(parent.as_ptr()) &*&
        match result {
            Option::None => len < CAPACITY &*& [available]lifetime_token(k) &*&
                internal_slots(parent, len + 1, insert_item(children, self.idx + 1, edge.node), ?fitted_keys, ?fitted_vals) &*&
                nth(self.idx, fitted_keys).inner() == some(key) &*& nth(self.idx, fitted_vals).inner() == some(val),
            Option::Some(split) => len == CAPACITY &*& [available/2]lifetime_token(k) &*& split.left == self.node &*&
                split.right.height == self.node.height &*& split.right.node.as_ptr() != self.node.node.as_ptr() &*&
                exists::<NonNull<InternalNode<K,V>>>(?sibling) &*& split.right.node.as_ptr() == &(*sibling.as_ptr()).data &*&
                allocated_internal(sibling.as_ptr(), id, k, available/2) &*&
                (*split.right.node.as_ptr()).parent |-> Option::None &*& (*split.right.node.as_ptr()).parent_idx |-> ?right_parent_idx &*&
                internal_slots(parent, ?left_len, ?left_children, ?left_keys, ?left_vals) &*&
                internal_slots(sibling, ?right_len, ?right_children, ?right_keys, ?right_vals) &*& left_len + right_len == len &*&
                append(left_children, right_children) == insert_item(children, self.idx + 1, edge.node) &*&
                nth(insertion_pivot(self.idx), keys).inner() == some(split.kv.0) &*&
                nth(insertion_pivot(self.idx), vals).inner() == some(split.kv.1) &*&
                <K>.own(t, split.kv.0) &*& <V>.own(t, split.kv.1) &*&
                if self.idx < left_len {
                    nth(self.idx, left_keys).inner() == some(key) &*& nth(self.idx, left_vals).inner() == some(val)
                } else {
                    nth(self.idx - left_len - 1, right_keys).inner() == some(key) &*&
                    nth(self.idx - left_len - 1, right_vals).inner() == some(val)
                }
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available]lifetime_token(k) &*& leaf_header(self.node.node.as_ptr(), ancestor, parent_idx) &*&
        struct_InternalNode_padding(parent.as_ptr()) &*&
        internal_slots(parent, len, children, keys, vals) &*& detached_child(edge.node.as_ptr()) &*&
        if len == CAPACITY {
            nth(insertion_pivot(self.idx), keys).inner() == some(?pivot_key) &*&
            nth(insertion_pivot(self.idx), vals).inner() == some(?pivot_val) &*&
            <K>.own(t, pivot_key) &*& <V>.own(t, pivot_val)
        } else { true };
    @*/
    {
        //@ open exists(k);
        //@ open exists(parent);
        //@ assert *&self |-> ?incoming;
        //@ let source = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ std::ptr::NonNull_Sized_as_ptr(parent);
        //@ std::ptr::NonNull_Sized_as_ptr(incoming.node.node);
        //@ open_points_to(&self);
        //@ open_points_to(&self.node);
        assert!(edge.height == self.node.height - 1);
        //@ close_points_to(&self.node);
        //@ open internal_slots(parent, len, children, keys, vals);
        //@ let len_view = precreate_ref(&self.node);
        //@ init_ref_readonly(len_view, 1/2);
        let fits = self.node.merge_len() < CAPACITY;
        //@ end_ref_readonly(len_view);
        //@ merge_fractions points_to(&self.node, _);
        //@ close internal_slots(parent, len, children, keys, vals);
        if fits {
            //@ open pivot_owner(t, len, index, keys, vals);
            //@ close_points_to(&self);
            //@ close exists(parent);
            self.insert_fit_production/*@::<'a,K,V,'a>@*/(key, val, edge); //~track_ref_creation
            //@ assert ref_mut_end_token(?this_view, &mut self);
            //@ end_ref_mut(this_view);
            //@ std::alloc::Allocator_to_own(alloc);
            None
        } else {
            let (middle_kv_idx, insertion) = splitpoint(self.idx);
            //@ open internal_slots(parent, len, children, keys, vals);
            let middle = unsafe { Handle::<NodeRef<marker::Mut<'_>,K,V,marker::Internal>,marker::KV>::new_kv/*@::<marker::Mut<'a>,K,V>@*/(self.node, middle_kv_idx) };
            //@ close_points_to(&self);
            //@ close internal_slots(parent, len, children, keys, vals);
            //@ open pivot_owner(t, len, index, keys, vals);
            //@ close exists(k);
            //@ close exists(parent);
            let mut result = middle.split_production_internal/*@::<'a,K,V,A>@*/(alloc);
            //@ open exists::<NonNull<InternalNode<K,V>>>(?sibling);
            //@ let right = sibling.as_ptr();
            //@ let inserted_edge_index = incoming.idx + 1;
            //@ let first_right_edge = middle_kv_idx + 1;
            //@ let right_count = len - first_right_edge;
            let mut insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    //@ open internal_slots(parent, middle_kv_idx, take(first_right_edge, children), keys, vals);
                    let selected = Handle::<NodeRef<marker::Mut<'_>,K,V,marker::Internal>,marker::Edge>::new_edge(
                        result.left.reborrow_mut(), insert_idx,
                    );
                    //@ close internal_slots(parent, middle_kv_idx, take(first_right_edge, children), keys, vals);
                    selected
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    //@ std::ptr::NonNull_Sized_as_ptr(sibling);
                    //@ open internal_slots(sibling, right_count, drop(first_right_edge, children), _, _);
                    let selected = Handle::<NodeRef<marker::Mut<'_>,K,V,marker::Internal>,marker::Edge>::new_edge(
                        result.right.borrow_mut(), insert_idx,
                    );
                    //@ close internal_slots(sibling, right_count, drop(first_right_edge, children), _, _);
                    selected
                },
            };
            /*@ match insertion {
                LeftOrRight::Left(at) => {
                    close exists(parent);
                }
                LeftOrRight::Right(at) => {
                    open allocated_internal(right, id, k, available/2);
                    close leaf_header(&(*right).data, Option::None, _);
                    close exists(sibling);
                }
            } @*/
            //@ close_points_to(&insertion_edge.node);
            insertion_edge.insert_fit_production/*@::<'a,K,V,'a>@*/(key, val, edge); //~track_ref_creation
            //@ assert ref_mut_end_token(?finished, &mut insertion_edge);
            //@ end_ref_mut(finished);
            //@ open_points_to(&insertion_edge);
            //@ open_points_to(&insertion_edge.node);
            //@ insert_item_across_split(children, first_right_edge, inserted_edge_index, edge.node);
            /*@ match insertion {
                LeftOrRight::Left(at) => {}
                LeftOrRight::Right(at) => {
                    open leaf_header(&(*right).data, Option::None, _);
                    close allocated_internal(right, id, k, available/2);
                }
            } @*/
            //@ close exists(sibling);
            Some(result)
        }
    }
}

/*@
pred ancestor_tail<K,V>(
    node: *LeafNode<K,V>, path: list<ParentStep<K,V>>, root: *LeafNode<K,V>, root_index: MaybeUninit<u16>;
    parent: Option<NonNull<InternalNode<K,V>>>, parent_idx: MaybeUninit<u16>
) =
    match path {
        nil => node == root &*& parent == Option::None &*& parent_idx == root_index,
        cons(step, remaining) =>
            match step {
                ParentStep(upper, idx, len, payload) =>
                    parent == Option::Some(NonNull::new(upper)) &*& parent_idx == MaybeUninit::new(idx) &*&
                    parent_payload(node, upper, idx, len, payload) &*&
                    ancestors(&(*upper).data, remaining, root) &*& (*root).parent_idx |-> root_index
            }
    };

lem open_ancestor_header<K,V>(node: *LeafNode<K,V>, path: list<ParentStep<K,V>>, root: *LeafNode<K,V>)
    req ancestors(node, path, root) &*& (*root).parent_idx |-> ?root_index &*& struct_LeafNode_padding(node);
    ens ancestor_tail(node, path, root, root_index, ?parent, ?idx) &*& leaf_header(node, parent, idx);
{
    open ancestors(node, path, root);
    match path {
        nil => {
            open link(node, Option::None, 0);
            close leaf_header(node, Option::None, root_index);
            close ancestor_tail(node, path, root, root_index, Option::None, root_index);
        }
        cons(step, remaining) => {
            match step {
                ParentStep(upper, idx, len, payload) => {
                    let parent = Option::Some(NonNull::new(upper));
                    open link(node, parent, idx);
                    close leaf_header(node, parent, MaybeUninit::new(idx));
                    close ancestor_tail(node, path, root, root_index, parent, MaybeUninit::new(idx));
                }
            }
        }
    }
}

lem close_ancestor_header<K,V>(node: *LeafNode<K,V>, path: list<ParentStep<K,V>>, root: *LeafNode<K,V>)
    req ancestor_tail(node, path, root, ?root_index, ?parent, ?parent_idx) &*& leaf_header(node, parent, parent_idx);
    ens ancestors(node, path, root) &*& (*root).parent_idx |-> root_index &*& struct_LeafNode_padding(node);
{
    open leaf_header(node, parent, parent_idx);
    open ancestor_tail(node, path, root, root_index, parent, parent_idx);
    match path {
        nil => { close link(node, Option::None, 0); }
        cons(step, remaining) => {
            match step {
                ParentStep(upper, idx, len, payload) => { close link(node, Option::Some(NonNull::new(upper)), idx); }
            }
        }
    }
    close ancestors(node, path, root);
}
@*/

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    unsafe fn insert_fit_leaf_production(mut self, key: K, val: V)
        -> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::KV>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        self.node.height == 0 &*& leaf_header(self.node.node.as_ptr(), ?ancestor, ?parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(), ?len, ?keys, ?vals) &*& 0 <= self.idx &*& self.idx <= len &*& len < CAPACITY;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        result.node == self.node &*& result.idx == self.idx &*&
        leaf_header(self.node.node.as_ptr(), ancestor, parent_idx) &*&
        dormant_pair(self.node.node.as_ptr(), self.idx, MaybeUninit::new(key), MaybeUninit::new(val)) &*&
        leaf_rest(self.node.node.as_ptr(),self.idx);
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert *&self |-> ?incoming;
        //@ let node = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ std::ptr::NonNull_Sized_as_ptr(incoming.node.node);
        //@ open leaf_slots(node, len, keys, vals);
        //@ open_points_to(&self);
        //@ let cap_view = precreate_ref(&self.node);
        //@ init_ref_readonly(cap_view, 1/2);
        debug_assert!(self.node.merge_len() < CAPACITY);
        //@ end_ref_readonly(cap_view);
        //@ merge_fractions points_to(&self.node, _);
        //@ let len_view = precreate_ref(&self.node);
        //@ init_ref_readonly(len_view, 1/2);
        let new_len = self.node.merge_len() + 1;
        //@ end_ref_readonly(len_view);
        //@ merge_fractions points_to(&self.node, _);
        //@ open leaf_header(node, ancestor, parent_idx);
        //@ close leaf_without_keys(node, ancestor, parent_idx, len as u16, vals);
        slice_insert(
            {
                let keys_view = self.node.key_area_prefix_mut/*@::<'a,K,V,marker::Leaf,'a>@*/(..new_len); //~track_ref_creation
                //@ open move_slice(keys_view as *MaybeUninit<K>, len + 1, _);
                keys_view
            },
            self.idx, key,
        );
        //@ assert ref_mut_end_token(?keys_receiver, &self.node);
        //@ assert keys_range_loan(node, ?keys_lent, 0, len + 1, ancestor, parent_idx, len as u16, vals, _, _);
        //@ close move_slice(keys_lent as *MaybeUninit<K>, len + 1, _);
        //@ end_keys_range(node, keys_lent);
        //@ end_ref_mut(keys_receiver);
        //@ open leaf_without_keys(node, ancestor, parent_idx, len as u16, vals);
        //@ assert (*node).keys[..CAPACITY] |-> ?fitted_keys;
        //@ take_0(keys);
        //@ drop_0(keys);
        //@ nth_inserted_prefix(keys, len + 1, index, key);
        //@ close leaf_without_vals(node, ancestor, parent_idx, len as u16, fitted_keys);
        slice_insert(
            {
                let vals_view = self.node.val_area_prefix_mut/*@::<'a,K,V,marker::Leaf,'a>@*/(..new_len); //~track_ref_creation
                //@ open move_slice(vals_view as *MaybeUninit<V>, len + 1, _);
                vals_view
            },
            self.idx, val,
        );
        //@ assert ref_mut_end_token(?vals_receiver, &self.node);
        //@ assert vals_range_loan(node, ?vals_lent, 0, len + 1, ancestor, parent_idx, len as u16, fitted_keys, _, _);
        //@ close move_slice(vals_lent as *MaybeUninit<V>, len + 1, _);
        //@ end_vals_range(node, vals_lent);
        //@ end_ref_mut(vals_receiver);
        //@ open leaf_without_vals(node, ancestor, parent_idx, len as u16, fitted_keys);
        //@ assert (*node).vals[..CAPACITY] |-> ?fitted_vals;
        //@ take_0(vals);
        //@ drop_0(vals);
        //@ nth_inserted_prefix(vals, len + 1, index, val);

        //@ close leaf_without_len(node, ancestor, parent_idx, fitted_keys, fitted_vals);
        *self.node.len_mut/*@::<'a,K,V,marker::Leaf,'a>@*/() = new_len as u16; //~track_ref_creation
        //@ assert ref_mut_end_token(?len_receiver, &self.node);
        //@ assert len_loan(node, ?new_length, ancestor, parent_idx, fitted_keys, fitted_vals);
        //@ end_len_loan(node, new_length);
        //@ end_ref_mut(len_receiver);
        //@ open leaf_without_len(node, ancestor, parent_idx, fitted_keys, fitted_vals);
        let handle = Handle::<NodeRef<marker::Mut<'_>, K, V, marker::Leaf>, marker::KV>::new_kv/*@::<marker::Mut<'a>,K,V>@*/(self.node, self.idx);
        //@ close_points_to(&self);
        //@ close leaf_header(node, ancestor, parent_idx);
        //@ let key_base = &(*node).keys as *MaybeUninit<K>;
        //@ let val_base = &(*node).vals as *MaybeUninit<V>;
        //@ array_split(key_base,index);
        //@ array_split(val_base,index);
        //@ array_split(key_base+index,1);
        //@ array_split(val_base+index,1);
        //@ nth_drop(0,index,fitted_keys);
        //@ nth_drop(0,index,fitted_vals);
        //@ open array(key_base+index,1,_);
        //@ open array(val_base+index,1,_);
        //@ close dormant_pair(node,index,MaybeUninit::new(key),MaybeUninit::new(val));
        //@ close leaf_rest(node,index);
        handle
    }
}

impl<'a, K: 'a, V: 'a> Handle<NodeRef<marker::Mut<'a>, K, V, marker::Leaf>, marker::Edge> {
    unsafe fn insert_leaf_production<A: AllocatorClone>(mut self, key: K, val: V, alloc: A) -> (
        Option<SplitResult<'a, K, V, marker::Leaf>>,
        Handle<NodeRef<marker::DormantMut, K, V, marker::Leaf>, marker::KV>,
    )
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t,alloc,?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k,id.lft) == true &*&
        self.node.height == 0 &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        leaf_header(self.node.node.as_ptr(),?ancestor,?parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= self.idx &*& self.idx <= len &*& pivot_owner(t,len,self.idx,keys,vals);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [?remaining]lifetime_token(k) &*& <K>.own(t,key) &*& <V>.own(t,val) &*& result.1.node.height == 0 &*&
        leaf_header(self.node.node.as_ptr(),ancestor,parent_idx) &*&
        dormant_pair(result.1.node.node.as_ptr(),result.1.idx,MaybeUninit::new(key),MaybeUninit::new(val)) &*&
        match result.0 {
            Option::None => len < CAPACITY &*& result.1.node.node == self.node.node &*& result.1.idx == self.idx &*&
                insertion_leaves(self.node.node,self.node.node,self.idx,Option::None,id,k),
            Option::Some(split) => len == CAPACITY &*& split.left == self.node &*& split.right.height == 0 &*&
                split.right.node.as_ptr() != self.node.node.as_ptr() &*&
                detached_child(split.right.node.as_ptr()) &*&
                insertion_leaves(self.node.node,result.1.node.node,result.1.idx,Option::Some(split.right.node),id,k) &*&
                nth(insertion_pivot(self.idx),keys).inner() == some(split.kv.0) &*&
                nth(insertion_pivot(self.idx),vals).inner() == some(split.kv.1) &*&
                <K>.own(t,split.kv.0) &*& <V>.own(t,split.kv.1)
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [?remaining]lifetime_token(k) &*& len == CAPACITY &*&
        leaf_header(self.node.node.as_ptr(),ancestor,parent_idx) &*& leaf_slots(self.node.node.as_ptr(),len,keys,vals) &*&
        nth(insertion_pivot(self.idx),keys).inner() == some(?promoted_key) &*&
        nth(insertion_pivot(self.idx),vals).inner() == some(?promoted_val) &*&
        <K>.own(t,promoted_key) &*& <V>.own(t,promoted_val);
    @*/
    {
        //@ open exists(k);
        //@ assert *&self |-> ?entry;
        //@ let left = entry.node.node;
        //@ let index = entry.idx;
        //@ std::ptr::NonNull_Sized_as_ptr(left);
        //@ open leaf_slots(left.as_ptr(),len,keys,vals);
        //@ open_points_to(&self);
        //@ let len_view = precreate_ref(&self.node);
        //@ init_ref_readonly(len_view,1/2);
        let fits = unsafe { self.node.merge_len() < CAPACITY };
        //@ end_ref_readonly(len_view);
        //@ merge_fractions points_to(&self.node,_);
        //@ close leaf_slots(left.as_ptr(),len,keys,vals);
        if fits {
            //@ open pivot_owner(t,len,index,keys,vals);
            //@ open_points_to(&self.node);
            let kv_handle = unsafe { self.insert_fit_leaf_production(key,val) };
            //@ close_points_to(&self.node);
            //@ close_points_to(&kv_handle.node,1/2);
            let dormant = unsafe { kv_handle.dormant/*@::<'a,K,V,marker::Leaf,marker::KV,'a>@*/() };
            //@ open_points_to(&kv_handle);
            //@ open_points_to(&kv_handle.node);
            //@ close Handle_node_(&self, some(entry.node));
            //@ std::alloc::Allocator_to_own(alloc);
            //@ close insertion_leaves(left,left,index,Option::None,id,k);
            (None, dormant)
        } else {
            let (middle_kv_idx, insertion) = unsafe { splitpoint(self.idx) };
            //@ open leaf_slots(left.as_ptr(),len,keys,vals);
            //@ open_points_to(&self.node);
            let middle = unsafe {
                Handle::<NodeRef<marker::Mut<'_>, K, V, marker::Leaf>, marker::KV>::new_kv/*@::<marker::Mut<'a>,K,V>@*/(
                    self.node, middle_kv_idx
                )
            };
            //@ close_points_to(&self.node);
            //@ close Handle_node_(&self, some(entry.node));
            //@ close leaf_slots(left.as_ptr(),len,keys,vals);
            //@ open pivot_owner(t,len,index,keys,vals);
            //@ close exists(k);
            let mut result = unsafe { middle.split_production_leaf/*@::<'a,K,V,A>@*/(alloc) };
            //@ let right = result.right.node;
            //@ std::ptr::NonNull_Sized_as_ptr(right);
            let insertion_edge = match insertion {
                LeftOrRight::Left(insert_idx) => unsafe {
                    //@ open leaf_slots(left.as_ptr(),middle_kv_idx,_,_);
                    let edge = Handle::<NodeRef<marker::Mut<'_>, K, V, marker::Leaf>, marker::Edge>::new_edge(
                        result.left.reborrow_mut(), insert_idx,
                    );
                    //@ close leaf_slots(left.as_ptr(),middle_kv_idx,_,_);
                    edge
                },
                LeftOrRight::Right(insert_idx) => unsafe {
                    //@ open leaf_slots(right.as_ptr(),CAPACITY-middle_kv_idx-1,_,_);
                    let edge = Handle::<NodeRef<marker::Mut<'_>, K, V, marker::Leaf>, marker::Edge>::new_edge(
                        result.right.borrow_mut(), insert_idx,
                    );
                    //@ close leaf_slots(right.as_ptr(),CAPACITY-middle_kv_idx-1,_,_);
                    edge
                },
            };
            /*@ match insertion {
                LeftOrRight::Left(at) => {}
                LeftOrRight::Right(at) => {
                    open allocated_leaf(right.as_ptr(),id,k,available/2);
                    close leaf_header(right.as_ptr(), Option::None, _);
                }
            } @*/
            let fitted = unsafe { insertion_edge.insert_fit_leaf_production(key,val) };
            //@ close_points_to(&fitted.node,1/2);
            let dormant = unsafe { fitted.dormant/*@::<'a,K,V,marker::Leaf,marker::KV,'a>@*/() };
            //@ open_points_to(&fitted);
            //@ open_points_to(&fitted.node);
            /*@ match insertion {
                LeftOrRight::Left(at) => {
                    close exists(right);
                    close insertion_leaves(left,left,at,Option::Some(right),id,k);
                }
                LeftOrRight::Right(at) => {
                    open leaf_header(right.as_ptr(), Option::None, _);
                    close allocated_leaf(right.as_ptr(),id,k,available/2);
                    close exists(left);
                    close insertion_leaves(left,right,at,Option::Some(right),id,k);
                }
            } @*/
            //@ close detached_child(right.as_ptr());
            (Some(result), dormant)
        }
    }
}

/*@
pred leaf_insert_sibling<'a,K,V>(
    result: (Option<SplitResult<'a,K,V,marker::Leaf>>, Handle<NodeRef<marker::DormantMut,K,V,marker::Leaf>,marker::KV>),
    entry: Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,marker::Edge>,
    t: thread_id_t, len: usize, id: std::alloc::alloc_id_t, k: lifetime_t
) =
    match result.0 {
        Option::None => len < CAPACITY &*& result.1.node.node == entry.node.node &*& result.1.idx == entry.idx &*&
            insertion_leaves(entry.node.node,entry.node.node,entry.idx,Option::None,id,k),
        Option::Some(split) => len == CAPACITY &*& split.left == entry.node &*& split.right.height == 0 &*&
            split.right.node.as_ptr() != entry.node.node.as_ptr() &*& detached_child(split.right.node.as_ptr()) &*&
            insertion_leaves(entry.node.node,result.1.node.node,result.1.idx,Option::Some(split.right.node),id,k) &*&
            <K>.own(t,split.kv.0) &*& <V>.own(t,split.kv.1)
    };
@*/

impl<'tree, K: 'tree, V: 'tree> Handle<NodeRef<marker::Mut<'tree>, K, V, marker::Leaf>, marker::Edge> {
    unsafe fn insert_recursing_for_root<'alloc, 'slot, A: AllocatorClone>(
        self, key: K, val: V, alloc: &'alloc A,
        root_slot: &'slot mut DormantMutRef<'tree, Option<Root<K,V>>>,
        root_allocator: &'slot mut A,
    ) -> Handle<NodeRef<marker::Mut<'tree>,K,V,marker::Leaf>,marker::KV>
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [_]allocator_clone_bound::<A>() &*&
        [_]std::alloc::Allocator_share::<A>(?alloc_lifetime,t,alloc,?alloc_id) &*&
        [_]frac_borrow(alloc_lifetime, ref_initialized_(alloc)) &*& [?qa]lifetime_token(alloc_lifetime) &*&
        exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*& lifetime_inclusion(k,alloc_id.lft) == true &*&
        ancestors(self.node.node.as_ptr(),?path,?root) &*& route_frames(t,path) &*& (*root).parent_idx |-> ?root_index &*&
        *root_allocator |-> ?root_alloc &*& Allocator::<A>(t,root_alloc,alloc_id) &*&
        *root_slot |-> ?sleeper &*& *sleeper.ptr.as_ptr() |-> Option::Some(?old_root) &*&
        old_root.node.as_ptr() == root &*& old_root.height == length(path) &*&
        length(path) < usize::MAX &*& self.node.height == 0 &*&
        struct_LeafNode_padding(self.node.node.as_ptr()) &*&
        leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= self.idx &*& self.idx <= len &*& pivot_owner(t,len,self.idx,keys,vals) &*&
        <K>.own(t,key) &*& <V>.own(t,val);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [qa]lifetime_token(alloc_lifetime) &*& [?remaining_fraction]lifetime_token(k) &*&
        *root_allocator |-> ?after &*& Allocator::<A>(t,after,alloc_id) &*& *root_slot |-> sleeper &*&
        struct_LeafNode_padding(self.node.node.as_ptr()) &*& result.node.height == 0 &*&
        <K>.own(t,key) &*& <V>.own(t,val) &*&
        dormant_pair(result.node.node.as_ptr(),result.idx,MaybeUninit::new(key),MaybeUninit::new(val)) &*&
        exists::<Option<NonNull<LeafNode<K,V>>>>(?initial_sibling) &*&
        insertion_leaves(self.node.node,result.node.node,result.idx,initial_sibling,alloc_id,k) &*&
        match initial_sibling {
            Option::None =>
                *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& (*root).parent_idx |-> root_index &*&
                ancestors(self.node.node.as_ptr(),path,root) &*& route_frames(t,path),
            Option::Some(sibling) => completed_levels::<K,V>(t,alloc_id,k,?completed) &*&
                if length(completed) == length(path) {
                    *sleeper.ptr.as_ptr() |-> Option::Some(?installed) &*& installed.height == old_root.height + 1 &*&
                    exists::<NonNull<InternalNode<K,V>>>(?new_root) &*& installed.node.as_ptr() == &(*new_root.as_ptr()).data &*&
                    allocated_internal(new_root.as_ptr(),alloc_id,k,_) &*& (*new_root.as_ptr()).data.parent_idx |-> _ &*&
                    ancestors(installed.node.as_ptr(),[],installed.node.as_ptr()) &*&
                    internal_slots(new_root,1,cons(old_root.node,cons(?right,nil)),_,_) &*& <K>.own(t,_) &*& <V>.own(t,_)
                } else {
                    *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& (*root).parent_idx |-> root_index &*&
                    exists::<NonNull<InternalNode<K,V>>>(?receiving) &*& ancestors(&(*receiving.as_ptr()).data,?remaining,root) &*&
                    route_frames(t,remaining) &*& internal_slots(receiving,_,_,_,_) &*& struct_LeafNode_padding(&(*receiving.as_ptr()).data) &*& struct_InternalNode_padding(receiving.as_ptr()) &*& <K>.own(t,_) &*& <V>.own(t,_) &*&
                    length(completed) + length(remaining) + 1 == length(path)
                }
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [qa]lifetime_token(alloc_lifetime) &*& [?remaining_fraction]lifetime_token(k) &*&
        *root_allocator |-> ?after &*& Allocator::<A>(t,after,alloc_id) &*& *root_slot |-> sleeper &*&
        exists::<bool>(?after_leaf) &*&
        if after_leaf {
            struct_LeafNode_padding(self.node.node.as_ptr()) &*&
            exists::<(Option<SplitResult<'tree,K,V,marker::Leaf>>, Handle<NodeRef<marker::DormantMut,K,V,marker::Leaf>,marker::KV>)>(?initial) &*&
            <K>.own(t,key) &*& <V>.own(t,val) &*&
            dormant_pair(initial.1.node.node.as_ptr(),initial.1.idx,MaybeUninit::new(key),MaybeUninit::new(val)) &*&
            match initial.0 {
                Option::None => *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& (*root).parent_idx |-> root_index &*&
                    ancestors(self.node.node.as_ptr(),path,root) &*& route_frames(t,path) &*&
                    insertion_leaves(self.node.node,initial.1.node.node,initial.1.idx,Option::None,alloc_id,k),
                Option::Some(split_leaf) =>
                    insertion_leaves(self.node.node,initial.1.node.node,initial.1.idx,Option::Some(split_leaf.right.node),alloc_id,k) &*&
                    completed_levels::<K,V>(t,alloc_id,k,?completed) &*&
                    if length(completed) == length(path) {
                        *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& detached_child::<K,V>(?pending_sibling) &*&
                        exists::<Option<NonNull<InternalNode<K,V>>>>(?partial_root) &*&
                        interrupted_root_change(old_root.node,root_index,alloc_id,k,partial_root)
                    } else {
                        *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& exists::<NonNull<InternalNode<K,V>>>(?receiving) &*&
                        ancestor_tail(&(*receiving.as_ptr()).data,?remaining,root,root_index,?ancestor,?ancestor_idx) &*&
                        leaf_header(&(*receiving.as_ptr()).data,ancestor,ancestor_idx) &*& struct_InternalNode_padding(receiving.as_ptr()) &*&
                        route_frames(t,remaining) &*& length(completed) + length(remaining) + 1 == length(path) &*&
                        internal_slots(receiving,?receiving_len,_,_,_) &*& detached_child::<K,V>(?detached) &*&
                        if receiving_len == CAPACITY { <K>.own(t,_) &*& <V>.own(t,_) } else { true }
                    }
            }
        } else {
            len == CAPACITY &*& *sleeper.ptr.as_ptr() |-> Option::Some(old_root) &*& route_frames(t,path) &*&
            ancestor_tail(self.node.node.as_ptr(),path,root,root_index,?parent,?idx) &*&
            leaf_header(self.node.node.as_ptr(),parent,idx) &*& leaf_slots(self.node.node.as_ptr(),len,keys,vals) &*&
            nth(insertion_pivot(self.idx),keys).inner() == some(?promoted_key) &*&
            nth(insertion_pivot(self.idx),vals).inner() == some(?promoted_val) &*&
            <K>.own(t,promoted_key) &*& <V>.own(t,promoted_val)
        };
    @*/
    {
        //@ let entry = self;
        //@ let first = self.node.node;
        //@ close exists(false);
        let initial = unsafe { self.clone_and_insert/*@::<'tree,K,V,A,'alloc>@*/(key,val,alloc) };
        //@ open leaf_insert_sibling(initial,entry,t,len,alloc_id,k);
        //@ open exists(false);
        //@ close exists(initial);
        //@ close exists(true);
        //@ close exists(first);
        let result = unsafe { resume_after_leaf_insert_for_root/*@::<'tree,K,V,A,'alloc,'slot>@*/(initial,alloc,root_slot,root_allocator) };
        //@ open exists(true);
        //@ open exists(initial);
        result
    }
}

impl<K, V> NodeRef<marker::Owned, K, V, marker::Internal> {
    unsafe fn new_internal_production<A: AllocatorClone>(child: Root<K,V>, alloc: A) -> Self
    /*@
    req thread_token(?t) &*& std::ptr::drop_may_unwind::<A>() == false &*&
        type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t,alloc,?id) &*& exists::<lifetime_t>(?k) &*& [?available]lifetime_token(k) &*&
        lifetime_inclusion(k,id.lft) == true &*& 0 <= child.height &*& child.height < usize::MAX &*&
        ancestors(child.node.as_ptr(),[],child.node.as_ptr()) &*& (*child.node.as_ptr()).parent_idx |-> ?old_index;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available/2]lifetime_token(k) &*& result.height == child.height + 1 &*&
        exists::<NonNull<InternalNode<K,V>>>(?root) &*& result.node.as_ptr() == &(*root.as_ptr()).data &*&
        allocated_internal(root.as_ptr(),id,k,available/2) &*&
        ancestors(result.node.as_ptr(),[],result.node.as_ptr()) &*& (*result.node.as_ptr()).parent_idx |-> ?created_index &*&
        internal_slots(root,0,[child.node],_,_);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        [available]lifetime_token(k) &*& exists::<Option<NonNull<InternalNode<K,V>>>>(?partial) &*&
        interrupted_root_change(child.node,old_index,id,k,partial);
    @*/
    {
        //@ open exists(k);
        //@ close interrupted_root_change(child.node,old_index,id,k,Option::None);
        //@ close exists::<Option<NonNull<InternalNode<K,V>>>>(Option::None);
        let mut new_node = unsafe { InternalNode::new(alloc) };
        //@ open exists::<Option<NonNull<InternalNode<K,V>>>>(Option::None);
        //@ open interrupted_root_change(child.node,old_index,id,k,Option::None);
        //@ let contents = std::boxed::Box_separate_contents(&mut new_node);
        //@ let q_box = lifetime_token_trade(k,available,id.lft);
        //@ open_points_to_at_lft(contents,q_box);
        //@ points_to_limits(contents);
        //@ assert *contents |-> ?initial;
        //@ open_points_to(contents);
        //@ let first_edge = &(*contents).edges as *MaybeUninit<BoxedNode<K,V>>;
        //@ array_split(first_edge,1);
        //@ assert array(first_edge+1,CAPACITY,?tail);
        //@ open array(first_edge,1,_);
        new_node.edges[0].write(child.node);
        //@ close array(first_edge,1,[MaybeUninit::new(child.node)]);
        //@ array_join(first_edge);
        //@ close_known_array(&(*contents).edges);
        //@ open_points_to(&(*contents).edges);
        //@ close_points_to(contents);
        //@ assert *contents |-> ?new_contents;
        //@ assert new_contents.data == initial.data;
        //@ assert Array_elems(new_contents.edges) == append(initialized_edges([child.node]),tail);
        //@ close_points_to_at_lft(contents);
        //@ lifetime_token_trade_back(q_box,id.lft);
        //@ std::boxed::Box_unseparate_contents(&mut new_node);
        //@ open ancestors(child.node.as_ptr(),[],child.node.as_ptr());
        //@ open link(child.node.as_ptr(),Option::None,0);
        //@ close child_headers::<K,V>([]);
        //@ close child_headers([child.node]);
        //@ close exists(tail);
        //@ close exists(k);
        let root = unsafe { NodeRef::from_new_internal(new_node, NonZero::new(child.height + 1).unwrap()) };
        //@ open exists::<NonNull<InternalNode<K,V>>>(?ptr);
        //@ close link(root.node.as_ptr(),Option::None,0);
        //@ close ancestors(root.node.as_ptr(),[],root.node.as_ptr());
        //@ close exists(ptr);
        root
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Mut<'a>, K, V, marker::Internal> {
    unsafe fn push_production<'short>(&'short mut self, key: K, val: V, edge: Root<K, V>)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        *self |-> ?incoming &*& incoming.height > 0 &*& edge.height == incoming.height - 1 &*&
        exists::<NonNull<InternalNode<K,V>>>(?parent) &*& incoming.node.as_ptr() == &(*parent.as_ptr()).data &*&
        leaf_header(incoming.node.as_ptr(),?ancestor,?parent_idx) &*& struct_InternalNode_padding(parent.as_ptr()) &*&
        internal_slots(parent,?count,?children,?keys,?vals) &*& count < CAPACITY &*& detached_child(edge.node.as_ptr());
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        *self |-> incoming &*& leaf_header(incoming.node.as_ptr(),ancestor,parent_idx) &*& struct_InternalNode_padding(parent.as_ptr()) &*&
        internal_slots(parent,count+1,append(children,[edge.node]),?fitted_keys,?fitted_vals) &*&
        nth(count,fitted_keys).inner() == some(key) &*& nth(count,fitted_vals).inner() == some(val);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(parent);
        //@ let node = incoming.node.as_ptr();
        //@ let parent_ptr = parent.as_ptr();
        //@ let right = edge.node;
        //@ std::ptr::NonNull_Sized_as_ptr(parent);
        //@ std::ptr::NonNull_Sized_as_ptr(incoming.node);
        //@ std::ptr::NonNull_Sized_as_ptr(right);
        //@ open_points_to(self);
        assert!(edge.height == self.height - 1);
        //@ close_points_to(self);
        //@ open internal_slots(parent,count,children,keys,vals);
        //@ open node_arrays(parent_ptr,keys,vals,?edges);
        //@ open leaf_header(node,ancestor,parent_idx);
        //@ close leaf_without_len(node,ancestor,parent_idx,keys,vals);
        let len = unsafe { self.len_mut/*@::<'a,K,V,marker::Internal,'short>@*/() }; //~track_ref_creation
        let idx = usize::from(*len);
        assert!(idx < CAPACITY);
        *len += 1;
        //@ end_len_loan(node,len);
        //@ open leaf_without_len(node,ancestor,parent_idx,keys,vals);
        //@ close leaf_header(node,ancestor,parent_idx);
        unsafe {
            //@ close leaf_without_keys(node,ancestor,parent_idx,(count+1) as u16,vals);
            self.key_area_slot_mut/*@::<'a,K,V,marker::Internal,'short>@*/(idx).write(key); //~track_ref_creation
            //@ assert keys_slot_loan(node,?key_slot,count,ancestor,parent_idx,(count+1) as u16,vals,_,_);
            //@ end_keys_slot(node,key_slot);
            //@ open leaf_without_keys(node,ancestor,parent_idx,(count+1) as u16,vals);
            //@ assert (*node).keys[..CAPACITY] |-> ?fitted_keys;

            //@ close leaf_without_vals(node,ancestor,parent_idx,(count+1) as u16,fitted_keys);
            self.val_area_slot_mut/*@::<'a,K,V,marker::Internal,'short>@*/(idx).write(val); //~track_ref_creation
            //@ assert vals_slot_loan(node,?val_slot,count,ancestor,parent_idx,(count+1) as u16,fitted_keys,_,_);
            //@ end_vals_slot(node,val_slot);
            //@ open leaf_without_vals(node,ancestor,parent_idx,(count+1) as u16,fitted_keys);
            //@ assert (*node).vals[..CAPACITY] |-> ?fitted_vals;

            //@ open leaf_header(node,ancestor,parent_idx);
            //@ close_points_to(node);
            //@ close internal_without_edges(parent_ptr,_);
            self.edge_area_slot_mut/*@::<'a,K,V,'short>@*/(idx + 1).write(edge.node); //~track_ref_creation
            //@ assert edges_slot_loan(parent_ptr,?edge_slot,count+1,?data,_,_);
            //@ end_edges_slot(parent_ptr,edge_slot);
            //@ open internal_without_edges(parent_ptr,data);
            //@ open_points_to(node);
            //@ assert (*parent_ptr).edges[..CAPACITY+1] |-> ?fitted_edges;

            //@ let head = take(count+1, edges);
            //@ let tail = drop(count+2, edges);
            //@ length_take(count+1,edges);
            //@ nth_append_r(head,cons(MaybeUninit::new(right),tail),0);
            //@ close exists(parent);
            //@ close exists(right);
            //@ open detached_child(right.as_ptr());
            Handle::<NodeRef<marker::Mut<'_>,K,V,marker::Internal>,marker::Edge>::new_edge(
                self.reborrow_mut/*@::<marker::Mut<'a>,K,V,marker::Internal,'short>@*/(), idx + 1
            ).correct_parent_link/*@::<'short,K,V>@*/();
            //@ append_linked_header(children,right,parent,0);
            //@ initialized_edges_append(children,[right]);
            //@ initialized_edge_count(children);
            //@ append_assoc(head,[MaybeUninit::new(right)],tail);
            //@ take_append_l(count+2,append(head,[MaybeUninit::new(right)]),tail);
            //@ take_length(append(head,[MaybeUninit::new(right)]));

            //@ length_take(count,keys);
            //@ length_take(count,vals);
            //@ nth_append_r(take(count,keys),cons(MaybeUninit::new(key),drop(count+1,keys)),0);
            //@ nth_append_r(take(count,vals),cons(MaybeUninit::new(val),drop(count+1,vals)),0);
            //@ close node_arrays(parent_ptr,fitted_keys,fitted_vals,fitted_edges);
            //@ close internal_slots(parent,count+1,append(children,[right]),fitted_keys,fitted_vals);
            //@ close leaf_header(node,ancestor,parent_idx);
        }
    }
}

impl<'a, K: 'a, V: 'a, Type> Copy for NodeRef<marker::Immut<'a>, K, V, Type> {}
impl<'a, K: 'a, V: 'a, Type> Clone for NodeRef<marker::Immut<'a>, K, V, Type> {
    fn clone(&self) -> Self {
        *self
    }
}

/*@
lem slots_are_initialized<T>(t: thread_id_t, slots: list<MaybeUninit<T>>)
    req slot_owners(t, slots);
    ens slot_owners(t, slots) &*& std::mem::initialized_slots(slots) == true;
{
    open slot_owners(t, slots);
    match slots {
        nil => {}
        cons(slot, tail) => {
            slots_are_initialized(t, tail);
        }
    }
    close slot_owners(t, slots);
}

pred shared_key_view<K,V>(
    root: *LeafNode<K,V>, slice: *[K], store: real,
    parent: Option<NonNull<InternalNode<K,V>>>, pidx: MaybeUninit<u16>, len: usize,
    keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>
) =
    ref_readonly_end_token(?leaf,root,store/2) &*& ref_initialized(leaf) &*&
    [store/2]leaf_header(leaf,parent,pidx) &*& [store/2](*leaf).len |-> (len as u16) &*&
    [store/2](*leaf).vals[..CAPACITY] |-> vals &*&
    [store/4](*leaf).keys[..CAPACITY] |-> keys &*&
    ref_readonly_end_token(?array,&(*leaf).keys,store/4) &*&
    [store/4](array as *MaybeUninit<K>)[..CAPACITY] |-> keys &*&
    ref_initialized(array) &*& [_]ref_initialized(slice) &*&
    strip_pointer_metadata(slice as pointer) == array as pointer &*& slice.len() == len;
@*/
impl<'a, K: 'a, V: 'a, Type> NodeRef<marker::Immut<'a>, K, V, Type> {
    unsafe fn into_leaf(mut self) -> &'a LeafNode<K, V>
    //@ req ref_precreated_token(self.node.as_ptr(), ?leaf) &*& [?f]ref_initialized(leaf);
    //@ ens [f]ref_initialized(leaf) &*& result == leaf;
    //@ on_unwind_ens false;
    {
        //@ let view = precreate_ref(&self);
        //@ init_ref_readonly(view, 1/2);
        let ptr = unsafe { Self::as_leaf_ptr(&self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self, _);
        unsafe { &*ptr }
    }

    unsafe fn keys<'short>(&'short self) -> &'short [K]
    /*@
    req [?f](*self |-> ?node) &*& ref_initialized(self) &*& [?q]lifetime_token('short) &*&
        [?store]leaf_header(node.node.as_ptr(),?parent,?pidx) &*&
        [store]leaf_slots(node.node.as_ptr(),?len,?key_slots,?vals) &*&
        slot_owners(?t,take(len,key_slots)) &*&
        ((&(*node.node.as_ptr()).keys) as pointer).address != 0 &*&
        ((&(*node.node.as_ptr()).keys) as pointer).address % std::mem::align_of::<K>() == 0;
    @*/
    /*@
    ens [f](*self |-> node) &*& ref_initialized(self) &*& [q]lifetime_token('short) &*&
        [store/2]leaf_header(node.node.as_ptr(),parent,pidx) &*&
        [store/2]leaf_slots(node.node.as_ptr(),len,key_slots,vals) &*&
        slot_owners(t,take(len,key_slots)) &*&
        shared_key_view(node.node.as_ptr(),result,store,parent,pidx,len,key_slots,vals);
    @*/
    //@ on_unwind_ens false;
    {
        //@ let root = node.node.as_ptr();
        //@ open [store]leaf_header(root,parent,pidx);
        //@ open [store]leaf_slots(root,len,key_slots,vals);
        //@ close_points_to(root,store);
        //@ let view = precreate_ref(root);
        //@ init_ref_readonly(view,1/2);
        //@ open_points_to(self);
        let leaf = unsafe { self.into_leaf() };
        //@ close_points_to(self, f);
        //@ open_points_to(root);
        //@ close [store/2]leaf_header(root,parent,pidx);
        //@ close [store/2]leaf_slots(root,len,key_slots,vals);
        //@ open_points_to(leaf);
        //@ let keys_addr = &(*leaf).keys;
        //@ close_points_to(keys_addr,store/2);
        //@ let array = precreate_ref(keys_addr);
        //@ init_ref_readonly(array,1/2);
        let keys = &leaf.keys;
        // Rust reborrows the array reference before attaching slice metadata.
        //@ let local = begin_lifetime();
        //@ close ref_initialized_::<[MaybeUninit<K>; 11]>(keys)();
        //@ borrow(local, ref_initialized_::<[MaybeUninit<K>; 11]>(keys));
        //@ full_borrow_into_frac(local, ref_initialized_::<[MaybeUninit<K>; 11]>(keys));
        //@ let half = open_frac_borrow(local, ref_initialized_::<[MaybeUninit<K>; 11]>(keys), 1/2);
        //@ open [half]ref_initialized_::<[MaybeUninit<K>; 11]>(keys)();
        let key_slice: &[MaybeUninit<K>] = keys;
        //@ close [half]ref_initialized_::<[MaybeUninit<K>; 11]>(keys)();
        //@ close_frac_borrow(half, ref_initialized_::<[MaybeUninit<K>; 11]>(keys));
        //@ end_lifetime(local);
        //@ borrow_end(local, ref_initialized_::<[MaybeUninit<K>; 11]>(keys));
        //@ open ref_initialized_::<[MaybeUninit<K>; 11]>(keys)();
        //@ open_points_to(keys);
        //@ let base = keys as *MaybeUninit<K>;
        //@ array_inv::<MaybeUninit<K>>();
        //@ move_slice_offset(base,CAPACITY,len);
        //@ assert (base as pointer).address != 0;
        //@ assert (base as *u8 + len * std::mem::size_of::<K>()) as pointer == (base + len) as pointer;
        //@ slots_are_initialized(t,take(len,key_slots));
        let prefix = unsafe { <[MaybeUninit<K>]>::get_unchecked(key_slice, ..usize::from(leaf.len)) };
        //@ array_split(base,len);
        let result = unsafe { <[MaybeUninit<K>]>::assume_init_ref/*@::<K,'short>@*/(prefix) };
        //@ array_join(base);
        //@ open_points_to(keys_addr);
        //@ close [store/2]leaf_header(leaf,parent,pidx);
        //@ close shared_key_view(root,result,store,parent,pidx,len,key_slots,vals);
        result
    }
}

impl<'a, K, V, Type> NodeRef<marker::Mut<'a>, K, V, Type> {
    unsafe fn into_leaf_mut(mut self) -> &'a mut LeafNode<K, V>
    //@ req *self.node.as_ptr() |-> ?contents;
    //@ ens *result |-> contents &*& ref_mut_end_token(result, self.node.as_ptr()) &*& ref_origin(result) == ref_origin(self.node.as_ptr());
    //@ on_unwind_ens false;
    {
        //@ let view = precreate_ref(&self);
        //@ init_ref_readonly(view, 1/2);
        let ptr = unsafe { Self::as_leaf_ptr(&mut self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self, _);
        unsafe { &mut *ptr } //~track_ref_creation
    }
}

/*@
pred kv_loan<'a,K,V,NodeType>(owner: *Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV>,
    view: *LeafNode<K,V>, key: *K, val: *V,
    contents: Handle<NodeRef<marker::Mut<'a>, K, V, NodeType>, marker::KV>, len: u16,
    parent: Option<NonNull<InternalNode<K,V>>>, parent_idx: MaybeUninit<u16>, keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>) =
    (*owner).idx |-> contents.idx &*& struct_Handle_padding(owner) &*&
    ref_mut_end_token(?receiver,&(*owner).node) &*& *receiver |-> contents.node &*&
    ref_mut_end_token(view,contents.node.node.as_ptr()) &*&
    leaf_header(view,parent,parent_idx) &*& (*view).len |-> len &*&
    ref_mut_end_token(?key_array,&(*view).keys) &*& ref_mut_end_token(?val_array,&(*view).vals) &*&
    initialized_array_slot(key_array as *MaybeUninit<K>,contents.idx,key,take(contents.idx,keys),drop(contents.idx+1,keys)) &*&
    initialized_array_slot(val_array as *MaybeUninit<V>,contents.idx,val,take(contents.idx,vals),drop(contents.idx+1,vals));
@*/

impl<'a, K:'a, V:'a, NodeType> Handle<NodeRef<marker::Mut<'a>,K,V,NodeType>,marker::KV> {
    unsafe fn kv_mut<'short>(&'short mut self) -> (&'short mut K, &'short mut V)
    /*@
    req *self |-> ?incoming &*& leaf_header(incoming.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(incoming.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= incoming.idx &*& incoming.idx < len &*&
        nth(incoming.idx,keys).inner() == some(?old_key) &*& nth(incoming.idx,vals).inner() == some(?old_val);
    @*/
    /*@
    ens kv_loan(self, ?leaf, result.0, result.1, incoming, len, parent, parent_idx, keys, vals) &*&
        *result.0 |-> old_key &*& *result.1 |-> old_val;
    @*/
    //@ on_unwind_ens false;
    {
        //@ let node = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open leaf_slots(node,len,keys,vals);
        //@ open_points_to(self);
        //@ let view = precreate_ref(&(*self).node);
        //@ init_ref_readonly(view,1/2);
        debug_assert!(self.idx < self.node.merge_len());
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&(*self).node, _);
        //@ open leaf_header(node,parent,parent_idx);
        //@ close_points_to(node);
        unsafe {
            let leaf = self.node.as_leaf_mut/*@::<'a,K,V,NodeType,'short>@*/(); //~track_ref_creation
            //@ open_points_to(leaf);
            //@ close_points_to(&(*leaf).keys);
            let key_slot = {
                <[MaybeUninit<K>]>::get_unchecked_mut(
                    {
                        let key_array = &mut leaf.keys; //~track_ref_creation
                        let slice: &mut [MaybeUninit<K>] = key_array;
                        //@ open_points_to(key_array);
                        //@ let key_base = key_array as *MaybeUninit<K>;
                        //@ array_split(key_base,index);
                        //@ array_split(key_base+index,1);
                        //@ open array(key_base+index,1,_);
                        //@ open array(key_base+index+1,0,_);
                        //@ nth_drop(0,index,keys);
                        //@ drop_twice(1,index,keys);
                        slice
                    },
                    self.idx,
                )
            };
            let key = key_slot.assume_init_mut();
            //@ close exists::<*MaybeUninit<K>>(key_slot);
            //@ close initialized_array_slot(key_base,index,key,take(index,keys),drop(index+1,keys));
            //@ close_points_to(&(*leaf).vals);
            let val_slot = {
                <[MaybeUninit<V>]>::get_unchecked_mut(
                    {
                        let val_array = &mut leaf.vals; //~track_ref_creation
                        let slice: &mut [MaybeUninit<V>] = val_array;
                        //@ open_points_to(val_array);
                        //@ let val_base = val_array as *MaybeUninit<V>;
                        //@ array_split(val_base,index);
                        //@ array_split(val_base+index,1);
                        //@ open array(val_base+index,1,_);
                        //@ open array(val_base+index+1,0,_);
                        //@ nth_drop(0,index,vals);
                        //@ drop_twice(1,index,vals);
                        slice
                    },
                    self.idx,
                )
            };
            let val = val_slot.assume_init_mut();
            //@ close exists::<*MaybeUninit<V>>(val_slot);
            //@ close initialized_array_slot(val_base,index,val,take(index,vals),drop(index+1,vals));
            //@ close leaf_header(leaf,parent,parent_idx);
            //@ close kv_loan(self,leaf,key,val,incoming,len,parent,parent_idx,keys,vals);
            (key, val)
        }
    }
}

impl<BorrowType, K, V, Type> Handle<NodeRef<BorrowType, K, V, Type>, marker::KV> {
    unsafe fn new_navigation_kv(node: NodeRef<BorrowType, K, V, Type>, idx: usize) -> Self
    //@ req (*node.node.as_ptr()).len |-> ?len &*& idx < len;
    //@ ens result.node == node &*& result.idx == idx &*& (*node.node.as_ptr()).len |-> len;
    //@ on_unwind_ens false;
    {
        unsafe { debug_assert!(idx < node.relink_len()) };
        let kv = Handle { node, idx, _marker: PhantomData };
        //@ close_points_to(&node, 1/2);
        kv
    }
}

impl<BorrowType, K, V, Type> NodeRef<BorrowType, K, V, Type> {
    unsafe fn first_edge(self) -> Handle<Self, marker::Edge>
    //@ req (*self.node.as_ptr()).len |-> ?len;
    //@ ens (*self.node.as_ptr()).len |-> len &*& result.node == self &*& result.idx == 0;
    //@ on_unwind_ens false;
    {
        unsafe { Handle::new_relink_edge(self, 0) }
    }

    unsafe fn last_edge(self) -> Handle<Self, marker::Edge>
    //@ req (*self.node.as_ptr()).len |-> ?count;
    //@ ens (*self.node.as_ptr()).len |-> count &*& result.node == self &*& result.idx == count;
    //@ on_unwind_ens false;
    {
        let len = unsafe { self.relink_len() };
        let edge = unsafe { Handle::new_relink_edge(self, len) };
        //@ close_points_to(&self, 1/2);
        edge
    }

    unsafe fn first_kv(self) -> Handle<Self, marker::KV>
    //@ req (*self.node.as_ptr()).len |-> ?count &*& count > 0;
    //@ ens (*self.node.as_ptr()).len |-> count &*& result.node == self &*& result.idx == 0;
    //@ on_unwind_ens false;
    {
        let len = unsafe { self.relink_len() };
        assert!(len > 0);
        let kv = unsafe { Handle::new_navigation_kv(self, 0) };
        //@ close_points_to(&self, 1/2);
        kv
    }

    unsafe fn last_kv(self) -> Handle<Self, marker::KV>
    //@ req (*self.node.as_ptr()).len |-> ?count &*& count > 0;
    //@ ens (*self.node.as_ptr()).len |-> count &*& result.node == self &*& result.idx == count - 1;
    //@ on_unwind_ens false;
    {
        let len = unsafe { self.relink_len() };
        assert!(len > 0);
        let kv = unsafe { Handle::new_navigation_kv(self, len - 1) };
        //@ close_points_to(&self, 1/2);
        kv
    }
}

impl<BorrowType, K, V, Type> Handle<NodeRef<BorrowType, K, V, Type>, marker::KV> {
    unsafe fn left_edge(self) -> Handle<NodeRef<BorrowType, K, V, Type>, marker::Edge>
    //@ req (*self.node.node.as_ptr()).len |-> ?len &*& self.idx <= len;
    //@ ens (*self.node.node.as_ptr()).len |-> len &*& result.node == self.node &*& result.idx == self.idx;
    //@ on_unwind_ens false;
    {
        unsafe { Handle::new_relink_edge(self.node, self.idx) }
    }

    unsafe fn right_edge(self) -> Handle<NodeRef<BorrowType, K, V, Type>, marker::Edge>
    //@ req (*self.node.node.as_ptr()).len |-> ?len &*& 0 <= self.idx &*& self.idx < len;
    //@ ens (*self.node.node.as_ptr()).len |-> len &*& result.node == self.node &*& result.idx == self.idx + 1;
    //@ on_unwind_ens false;
    {
        unsafe { Handle::new_relink_edge(self.node, self.idx + 1) }
    }
}

impl<BorrowType, K, V, Type> Handle<NodeRef<BorrowType, K, V, Type>, marker::Edge> {
    unsafe fn left_kv(self) -> Result<Handle<NodeRef<BorrowType, K, V, Type>, marker::KV>, Self>
    //@ req (*self.node.node.as_ptr()).len |-> ?len &*& self.idx <= len;
    /*@
    ens (*self.node.node.as_ptr()).len |-> len &*&
        match result { Result::Ok(kv) => self.idx > 0 && kv.node == self.node && kv.idx == self.idx - 1,
                          Result::Err(edge) => self.idx == 0 && edge == self };
    @*/
    //@ on_unwind_ens false;
    {
        if self.idx > 0 {
            Ok(unsafe { Handle::new_navigation_kv(self.node, self.idx - 1) })
        } else {
            Err(self)
        }
    }

}
impl<BorrowType: marker::BorrowType, K, V> Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge> {
    unsafe fn descend(mut self) -> NodeRef<BorrowType, K, V, marker::LeafOrInternal>
    /*@
    req 0 < self.node.height &*& 0 <= self.idx &*& self.idx <= CAPACITY &*&
        pointer_within_limits(&(*(self.node.node.as_ptr() as *InternalNode<K,V>)).edges) == true &*&
        [?f](*(self.node.node.as_ptr() as *InternalNode<K,V>)).edges[..CAPACITY+1] |-> ?edges &*&
        exists::<BoxedNode<K,V>>(?child) &*& nth(self.idx,edges) == MaybeUninit::new(child);
    @*/
    /*@
    ens exists::<BoxedNode<K,V>>(child) &*& [f](*(self.node.node.as_ptr() as *InternalNode<K,V>)).edges[..CAPACITY+1] |-> edges &*&
        result.node == child &*& result.height == self.node.height - 1;
    @*/
    //@ on_unwind_ens false;
    {
        const { assert!(BorrowType::TRAVERSAL_PERMIT); }
        //@ open exists(child);
        //@ open_points_to(&self);
        //@ let receiver = precreate_ref(&self.node);
        //@ init_ref_readonly(receiver, 1/2);
        let parent_ptr = unsafe { NodeRef::as_internal_ptr(&self.node) };
        //@ end_ref_readonly(receiver);
        //@ merge_fractions points_to(&self.node, _);
        // BEGIN_RAW_EDGE_READ
        //@ let array = &(*parent_ptr).edges;
        //@ close_points_to(array, f);
        //@ let view = precreate_ref(array);
        //@ init_ref_readonly(view, 1/2);
        //@ open_points_to(view);
        //@ let base = view as *MaybeUninit<BoxedNode<K,V>>;
        //@ array_inv::<MaybeUninit<BoxedNode<K,V>>>();
        //@ array_split(base, self.idx);
        //@ array_split(base + self.idx, 1);
        //@ nth_drop(0, self.idx, edges);
        //@ open [f/2]array(base + self.idx, 1, _);
        //@ open [f/2]array(base + self.idx + 1, 0, _);
        //@ let slot = precreate_ref(base + self.idx);
        //@ init_ref_readonly(slot, 1/2);
        let edge = unsafe { (*parent_ptr).edges.get_unchecked(self.idx).assume_init_read() };
        //@ end_ref_readonly(slot);
        //@ merge_fractions points_to(base + self.idx, _);
        //@ close [f/2]array(base + self.idx, 1, [MaybeUninit::new(child)]);
        //@ array_join(base + self.idx);
        //@ array_join(base);
        //@ close_points_to(view, f/2);
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(array, _);
        //@ open_points_to(array);
        // END_RAW_EDGE_READ
        let descended = NodeRef { node: edge, height: self.node.height - 1, _marker: PhantomData };
        //@ close_points_to(&self);
        //@ close exists(child);
        descended
    }
}

/*@
pred handle_key_loan<'a,K,V,NodeType>(
    owner: *Handle<NodeRef<marker::Mut<'a>,K,V,NodeType>,marker::KV>, key: *K,
    contents: Handle<NodeRef<marker::Mut<'a>,K,V,NodeType>,marker::KV>,
    parent: Option<NonNull<InternalNode<K,V>>>, parent_idx: MaybeUninit<u16>, len: u16,
    keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>
) =
    (*owner).idx |-> contents.idx &*& struct_Handle_padding(owner) &*&
    ref_mut_end_token(?receiver,&(*owner).node) &*& *receiver |-> contents.node &*&
    keys_slot_loan(contents.node.node.as_ptr(),?slot,contents.idx,parent,parent_idx,len,vals,
        take(contents.idx,keys),drop(contents.idx+1,keys)) &*&
    ref_mut_end_token(key,slot as *K);
@*/

impl<'a, K:'a, V:'a, NodeType> Handle<NodeRef<marker::Mut<'a>,K,V,NodeType>,marker::KV> {
    unsafe fn key_mut<'short>(&'short mut self) -> &'short mut K
    /*@
    req *self |-> ?incoming &*& leaf_header(incoming.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(incoming.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= incoming.idx &*& incoming.idx < len &*&
        nth(incoming.idx,keys).inner() == some(?entry);
    @*/
    //@ ens handle_key_loan(self,result,incoming,parent,parent_idx,len as u16,keys,vals) &*& *result |-> entry;
    //@ on_unwind_ens false;
    {
        //@ let raw = incoming.node.node.as_ptr();
        //@ open leaf_slots(raw,len,keys,vals);
        //@ close leaf_without_keys(raw,parent,parent_idx,len as u16,vals);
        //@ open_points_to(self);
        unsafe {
            let slot = self.node.key_area_slot_mut/*@::<'a,K,V,NodeType,'short>@*/(self.idx); //~track_ref_creation
            let key = slot.assume_init_mut();
            //@ close handle_key_loan(self,key,incoming,parent,parent_idx,len as u16,keys,vals);
            key
        }
    }
}

/*@
fix array_address_ok<T>(base: *MaybeUninit<T>) -> bool {
    base != 0 &&
    object_pointer_within_limits(base as *u8, CAPACITY * std::mem::size_of::<T>()) &&
    (base as pointer).address % std::mem::align_of::<T>() == 0 &&
    CAPACITY * std::mem::size_of::<T>() <= isize::MAX
}

pred valmut_input<K,V>(leaf: *LeafNode<K,V>, index: usize, f: real; bits: MaybeUninit<K>, value_bits: MaybeUninit<V>) =
    0 <= index &*& index < CAPACITY &*&
    array_address_ok(&(*leaf).keys as *MaybeUninit<K>) == true &*&
    array_address_ok(&(*leaf).vals as *MaybeUninit<V>) == true &*&
    [f](*((&(*leaf).keys as *MaybeUninit<K>) + index) |-> bits) &*&
    *((&(*leaf).vals as *MaybeUninit<V>) + index) |-> value_bits;

pred valmut_loan<K,V>(
    leaf: *LeafNode<K,V>, index: usize, key: *K, val: *V, bits: MaybeUninit<K>, f: real
) =
    [f/2](*((&(*leaf).keys as *MaybeUninit<K>) + index) |-> bits) &*&
    ref_readonly_end_token(?key_view, ((&(*leaf).keys as *MaybeUninit<K>) + index), f/2) &*& [f/2](*key_view |-> bits) &*& ref_initialized(key_view) &*&
    key as pointer == key_view as pointer &*&
    ref_mut_end_token(?val_view,((&(*leaf).vals as *MaybeUninit<V>) + index)) &*& ref_mut_end_token(val,val_view as *V);
@*/

impl<'a, K, V, Type> NodeRef<marker::ValMut<'a>, K, V, Type> {
    unsafe fn into_key_val_mut_at(mut self, idx: usize) -> (&'a K, &'a mut V)
    //@ req valmut_input(self.node.as_ptr(), idx, ?f, ?bits, ?value_bits) &*& bits.inner() == some(?entry_key) &*& value_bits.inner() == some(?entry_val) &*& [?q]lifetime_token('a);
    //@ ens valmut_loan(self.node.as_ptr(), idx, result.0, result.1, bits, f) &*& *result.1 |-> entry_val &*& [q]lifetime_token('a) &*& [_]frac_borrow('a, ref_initialized_(result.0));
    //@ on_unwind_ens false;
    {
        //@ assert *(&self) |-> ?original;
        //@ let storage = original.node.as_ptr();
        //@ open valmut_input(storage, idx, f, bits, value_bits);
        //@ let view = precreate_ref(&self);
        //@ init_ref_readonly(view,1/2);
        let leaf = unsafe { Self::as_leaf_ptr(&mut self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self, _);
        let keys = unsafe { &raw const (*leaf).keys };
        let vals = unsafe { &raw mut (*leaf).vals };
        let keys: *const [_] = keys;
        let vals: *mut [_] = vals;
        //@ let key_view = precreate_ref((&(*leaf).keys as *MaybeUninit<K>) + idx);
        //@ init_ref_readonly(key_view,1/2);
        let key = unsafe { (&*keys.get_unchecked(idx)).assume_init_ref/*@::<K,'a>@*/() };
        let val = unsafe { (&mut *vals.get_unchecked_mut(idx)).assume_init_mut() }; //~track_ref_creation
        //@ close valmut_loan(storage,idx,key,val,bits,f);
        (key, val)
    }
}

impl<'a, K, V, NodeType> Handle<NodeRef<marker::ValMut<'a>, K, V, NodeType>, marker::KV> {
    unsafe fn into_kv_valmut(self) -> (&'a K, &'a mut V)
    //@ req valmut_input(self.node.node.as_ptr(), self.idx, ?f, ?bits, ?value_bits) &*& bits.inner() == some(?key) &*& value_bits.inner() == some(?val) &*& [?q]lifetime_token('a);
    //@ ens valmut_loan(self.node.node.as_ptr(), self.idx, result.0, result.1, bits, f) &*& *result.1 |-> val &*& [q]lifetime_token('a) &*& [_]frac_borrow('a, ref_initialized_(result.0));
    //@ on_unwind_ens false;
    {
        unsafe { self.node.into_key_val_mut_at/*@::<'a,K,V,NodeType>@*/(self.idx) }
    }
}

/*@
lem split_node_slot<T>(base: *MaybeUninit<T>, index: usize)
    req [?f]base[..CAPACITY] |-> ?slots &*& 0 <= index &*& index < CAPACITY;
    ens [f]base[..index] |-> take(index,slots) &*& [f](*(base+index) |-> nth(index,slots)) &*&
        [f]base[index+1..CAPACITY] |-> drop(index+1,slots);
{
    array_split(base,index);
    array_split(base+index,1);
    open [f]array(base+index,1,_);
    open [f]array(base+index+1,0,_);
    nth_drop(0,index,slots);
    drop_twice(1,index,slots);
}

pred consumed_val_loan<K,V>(
    root: *LeafNode<K,V>, index: usize, val: *V, len: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, parent_idx: MaybeUninit<u16>,
    keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>
) =
    ref_mut_end_token(?leaf,root) &*& leaf_header(leaf,parent,parent_idx) &*& (*leaf).len |-> (len as u16) &*&
    (*leaf).keys[..CAPACITY] |-> keys &*&
    ref_mut_end_token(?val_array,&(*leaf).vals) &*&
    initialized_array_slot(val_array as *MaybeUninit<V>,index,val,take(index,vals),drop(index+1,vals));

pred consumed_kv_loan<K,V>(
    root: *LeafNode<K,V>, index: usize, key: *K, val: *V, len: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, parent_idx: MaybeUninit<u16>,
    keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>
) =
    ref_mut_end_token(?leaf,root) &*& leaf_header(leaf,parent,parent_idx) &*& (*leaf).len |-> (len as u16) &*&
    ref_mut_end_token(?key_array,&(*leaf).keys) &*& ref_mut_end_token(?val_array,&(*leaf).vals) &*&
    initialized_array_slot(key_array as *MaybeUninit<K>,index,key,take(index,keys),drop(index+1,keys)) &*&
    initialized_array_slot(val_array as *MaybeUninit<V>,index,val,take(index,vals),drop(index+1,vals));
@*/

impl<'a, K:'a, V:'a, NodeType> Handle<NodeRef<marker::Mut<'a>,K,V,NodeType>,marker::KV> {
    unsafe fn into_val_mut(mut self) -> &'a mut V
    /*@
    req leaf_header(self.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= self.idx &*& self.idx < len &*&
        nth(self.idx,vals).inner() == some(?entry);
    @*/
    /*@
    ens consumed_val_loan(self.node.node.as_ptr(),self.idx,result,len,parent,parent_idx,keys,vals) &*& *result |-> entry;
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert *(&self) |-> ?incoming;
        //@ let node = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open leaf_slots(node,len,keys,vals);
        //@ open_points_to(&self);
        //@ let view = precreate_ref(&self.node);
        //@ init_ref_readonly(view,1/2);
        debug_assert!(self.idx < self.node.merge_len());
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self.node, _);
        //@ open leaf_header(node,parent,parent_idx);
        //@ close_points_to(node);
        let leaf = self.node.into_leaf_mut/*@::<'a,K,V,NodeType>@*/();
        //@ open_points_to(leaf);
        //@ close_points_to(&(*leaf).vals);
        unsafe {
            let slot = <[MaybeUninit<V>]>::get_unchecked_mut(
                {
                    let val_array = &mut leaf.vals; //~track_ref_creation
                    let slice: &mut [MaybeUninit<V>] = val_array;
                    //@ open_points_to(val_array);
                    //@ let base = val_array as *MaybeUninit<V>;
                    //@ split_node_slot(base,index);
                    slice
                },
                self.idx,
            );
            let val = slot.assume_init_mut();
            //@ close exists::<*MaybeUninit<V>>(slot);
            //@ close initialized_array_slot(base,index,val,take(index,vals),drop(index+1,vals));
            //@ close leaf_header(leaf,parent,parent_idx);
            //@ close consumed_val_loan(node,index,val,len,parent,parent_idx,keys,vals);
            //@ close_points_to(&self);
            val
        }
    }

    unsafe fn into_kv_mut(mut self) -> (&'a mut K, &'a mut V)
    /*@
    req leaf_header(self.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= self.idx &*& self.idx < len &*&
        nth(self.idx,keys).inner() == some(?old_key) &*& nth(self.idx,vals).inner() == some(?old_val);
    @*/
    /*@
    ens consumed_kv_loan(self.node.node.as_ptr(),self.idx,result.0,result.1,len,parent,parent_idx,keys,vals) &*&
        *result.0 |-> old_key &*& *result.1 |-> old_val;
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert *(&self) |-> ?incoming;
        //@ let node = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open leaf_slots(node,len,keys,vals);
        //@ open_points_to(&self);
        //@ let view = precreate_ref(&self.node);
        //@ init_ref_readonly(view,1/2);
        debug_assert!(self.idx < self.node.merge_len());
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self.node, _);
        //@ open leaf_header(node,parent,parent_idx);
        //@ close_points_to(node);
        let leaf = self.node.into_leaf_mut/*@::<'a,K,V,NodeType>@*/();
        //@ open_points_to(leaf);
        //@ close_points_to(&(*leaf).keys);
        let key = unsafe {
            let key_slot = {
                <[MaybeUninit<K>]>::get_unchecked_mut(
                    {
                        let key_array = &mut leaf.keys; //~track_ref_creation
                        let slice: &mut [MaybeUninit<K>] = key_array;
                        //@ open_points_to(key_array);
                        //@ let key_base = key_array as *MaybeUninit<K>;
                        //@ array_split(key_base,index);
                        //@ array_split(key_base+index,1);
                        //@ open array(key_base+index,1,_);
                        //@ open array(key_base+index+1,0,_);
                        //@ nth_drop(0,index,keys);
                        //@ drop_twice(1,index,keys);
                        slice
                    },
                    self.idx,
                )
            };
            let lent_key = key_slot.assume_init_mut();
            //@ close exists::<*MaybeUninit<K>>(key_slot);
            //@ close initialized_array_slot(key_base,index,lent_key,take(index,keys),drop(index+1,keys));
            lent_key
        };
        //@ close_points_to(&(*leaf).vals);
        let val = unsafe {
            let val_slot = {
                <[MaybeUninit<V>]>::get_unchecked_mut(
                    {
                        let val_array = &mut leaf.vals; //~track_ref_creation
                        let slice: &mut [MaybeUninit<V>] = val_array;
                        //@ open_points_to(val_array);
                        //@ let val_base = val_array as *MaybeUninit<V>;
                        //@ array_split(val_base,index);
                        //@ array_split(val_base+index,1);
                        //@ open array(val_base+index,1,_);
                        //@ open array(val_base+index+1,0,_);
                        //@ nth_drop(0,index,vals);
                        //@ drop_twice(1,index,vals);
                        slice
                    },
                    self.idx,
                )
            };
            let lent_val = val_slot.assume_init_mut();
            //@ close exists::<*MaybeUninit<V>>(val_slot);
            //@ close initialized_array_slot(val_base,index,lent_val,take(index,vals),drop(index+1,vals));
            lent_val
        };
        //@ close leaf_header(leaf,parent,parent_idx);
        //@ close consumed_kv_loan(node,index,key,val,len,parent,parent_idx,keys,vals);
        //@ close_points_to(&self);
        (key, val)
    }
}


/*@
lem initialized_entry<T>(slots: list<MaybeUninit<T>>, index: usize)
    req std::mem::initialized_slots(slots) == true &*& 0 <= index &*& index < length(slots);
    ens nth(index,slots).inner() != none;
{
    match slots {
        nil => {}
        cons(slot, tail) => {
            if index != 0 {
                initialized_entry(tail,index-1);
            }
        }
    }
}

pred shared_slot_backing<T>(
    array: *[MaybeUninit<T>; 11], view: *[MaybeUninit<T>; 11], slot: *MaybeUninit<T>,
    share: real, index: usize, slots: list<MaybeUninit<T>>
) =
    ref_readonly_end_token(view,array,share/2) &*&
    [share/2](array as *MaybeUninit<T>)[..CAPACITY] |-> slots &*&
    [share/2](view as *MaybeUninit<T>)[..index] |-> take(index,slots) &*&
    [share/2](view as *MaybeUninit<T>)[index+1..CAPACITY] |-> drop(index+1,slots) &*&
    ref_readonly_end_token(slot,(view as *MaybeUninit<T>) + index,share/4) &*&
    [share/4](*((view as *MaybeUninit<T>) + index) |-> nth(index,slots));

pred shared_slot_loan<T>(
    array: *[MaybeUninit<T>; 11], result: *T, share: real, index: usize, slots: list<MaybeUninit<T>>
) =
    shared_slot_backing(array,?view,?slot,share,index,slots) &*& ref_initialized(view) &*&
    [share/4](*slot |-> nth(index,slots)) &*& ref_initialized(slot) &*& result as pointer == slot as pointer;

lem prepare_shared_slot<T>(array: *[MaybeUninit<T>; 11], index: usize)
    req [?f](array as *MaybeUninit<T>)[..CAPACITY] |-> ?slots &*& 0 <= index &*& index < CAPACITY;
    ens ref_precreated_token(array,?view) &*& ref_precreated_token((view as *MaybeUninit<T>) + index,?slot) &*&
        shared_slot_backing(array,view,slot,f,index,slots) &*& ref_initialized(view) &*& ref_initialized(slot) &*&
        [f/4](*slot |-> nth(index,slots));
{
    close_points_to(array,f);
    let view = precreate_ref(array);
    init_ref_readonly(view,1/2);
    open_points_to(array);
    open_points_to(view);
    let base = view as *MaybeUninit<T>;
    split_node_slot(base,index);
    let slot = precreate_ref(base+index);
    init_ref_readonly(slot,1/2);
    // Keep the array marker outside the backing predicate for native unsizing.
    close shared_slot_backing(array,view,slot,f,index,slots);
}

pred shared_kv_loan<K,V>(
    root: *LeafNode<K,V>, key: *K, val: *V, store: real, index: usize,
    parent: Option<NonNull<InternalNode<K,V>>>, parent_idx: MaybeUninit<u16>, len: usize,
    keys: list<MaybeUninit<K>>, vals: list<MaybeUninit<V>>
) =
    ref_readonly_end_token(?leaf,root,store/2) &*& ref_initialized(leaf) &*&
    [store/2]leaf_header(leaf,parent,parent_idx) &*& [store/2](*leaf).len |-> (len as u16) &*&
    shared_slot_loan(&(*leaf).keys,key,store/2,index,keys) &*&
    shared_slot_loan(&(*leaf).vals,val,store/2,index,vals);
@*/

impl<'a, K:'a, V:'a, NodeType> Handle<NodeRef<marker::Immut<'a>,K,V,NodeType>,marker::KV> {
    unsafe fn into_kv(mut self) -> (&'a K, &'a V)
    /*@
    req [?store]leaf_header(self.node.node.as_ptr(),?parent,?parent_idx) &*&
        [store]leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*&
        0 <= self.idx &*& self.idx < len &*&
        slot_owners(?t,take(len,keys)) &*& slot_owners(t,take(len,vals)) &*& [?q]lifetime_token('a);
    @*/
    /*@
    ens [store/2]leaf_header(self.node.node.as_ptr(),parent,parent_idx) &*&
        [store/2]leaf_slots(self.node.node.as_ptr(),len,keys,vals) &*&
        slot_owners(t,take(len,keys)) &*& slot_owners(t,take(len,vals)) &*& [q]lifetime_token('a) &*&
        shared_kv_loan(self.node.node.as_ptr(),result.0,result.1,store,self.idx,parent,parent_idx,len,keys,vals) &*&
        [_]frac_borrow('a,ref_initialized_(result.0)) &*& [_]frac_borrow('a,ref_initialized_(result.1));
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert *(&self) |-> ?incoming;
        //@ let root = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open [store]leaf_slots(root,len,keys,vals);
        //@ open_points_to(&self);
        //@ let receiver = precreate_ref(&self.node);
        //@ init_ref_readonly(receiver,1/2);
        debug_assert!(self.idx < self.node.merge_len());
        //@ end_ref_readonly(receiver);
        //@ merge_fractions points_to(&self.node, _);
        //@ open [store]leaf_header(root,parent,parent_idx);
        //@ close_points_to(root,store);
        //@ let view = precreate_ref(root);
        //@ init_ref_readonly(view,1/2);
        let leaf = unsafe { self.node.into_leaf() };
        //@ open_points_to(root);
        //@ close [store/2]leaf_header(root,parent,parent_idx);
        //@ close [store/2]leaf_slots(root,len,keys,vals);
        //@ open_points_to(leaf);
        //@ slots_are_initialized(t,take(len,keys));
        //@ initialized_entry(take(len,keys),index);
        //@ nth_take(index,len,keys);
        //@ prepare_shared_slot(&(*leaf).keys,index);
        let key = unsafe { leaf.keys.get_unchecked(self.idx).assume_init_ref/*@::<K,'a>@*/() };
        //@ close shared_slot_loan(&(*leaf).keys,key,store/2,index,keys);
        //@ slots_are_initialized(t,take(len,vals));
        //@ initialized_entry(take(len,vals),index);
        //@ nth_take(index,len,vals);
        //@ prepare_shared_slot(&(*leaf).vals,index);
        let val = unsafe { leaf.vals.get_unchecked(self.idx).assume_init_ref/*@::<V,'a>@*/() };
        //@ close shared_slot_loan(&(*leaf).vals,val,store/2,index,vals);
        //@ close [store/2]leaf_header(leaf,parent,parent_idx);
        //@ close shared_kv_loan(root,key,val,store,index,parent,parent_idx,len,keys,vals);
        //@ close_points_to(&self);
        (key, val)
    }
}

impl<'a,K:'a,V:'a> NodeRef<marker::Mut<'a>,K,V,marker::Leaf> {
    unsafe fn push_with_handle<'b,'short>(&'short mut self, key: K, val: V) -> Handle<NodeRef<marker::Mut<'b>,K,V,marker::Leaf>,marker::KV>
    /*@
    req *self |-> ?node &*& leaf_header(node.node.as_ptr(),?parent,?pidx) &*&
        leaf_slots(node.node.as_ptr(),?count,?keys,?vals) &*& count < CAPACITY;
    @*/
    /*@
    ens *self |-> node &*& result.node.node == node.node &*& result.node.height == node.height &*& result.idx == count &*&
        leaf_header(node.node.as_ptr(),parent,pidx) &*&
        leaf_slots(node.node.as_ptr(),count+1,replace_slot(count,MaybeUninit::new(key),keys),
            replace_slot(count,MaybeUninit::new(val),vals));
    @*/
    //@ on_unwind_ens false;
    {
        //@ let raw = node.node.as_ptr();
        //@ open leaf_header(raw,parent,pidx);
        //@ open leaf_slots(raw,count,keys,vals);
        //@ close leaf_without_len(raw,parent,pidx,keys,vals);
        let len = self.len_mut/*@::<'a,K,V,marker::Leaf,'short>@*/(); //~track_ref_creation
        let idx = usize::from(*len);
        assert!(idx < CAPACITY);
        *len += 1;
        //@ end_len_loan(raw,len);
        //@ open leaf_without_len(raw,parent,pidx,keys,vals);
        //@ close leaf_header(raw,parent,pidx);
        unsafe {
            //@ close leaf_without_keys(raw,parent,pidx,(count+1) as u16,vals);
            self.key_area_slot_mut/*@::<'a,K,V,marker::Leaf,'short>@*/(idx).write(key); //~track_ref_creation
            //@ assert keys_slot_loan(raw,?key_slot,count,parent,pidx,(count+1) as u16,vals,_,_);
            //@ end_keys_slot(raw,key_slot);
            //@ open leaf_without_keys(raw,parent,pidx,(count+1) as u16,vals);
            //@ let fitted_keys = replace_slot(count,MaybeUninit::new(key),keys);
            //@ close leaf_without_vals(raw,parent,pidx,(count+1) as u16,fitted_keys);
            self.val_area_slot_mut/*@::<'a,K,V,marker::Leaf,'short>@*/(idx).write(val); //~track_ref_creation
            //@ assert vals_slot_loan(raw,?val_slot,count,parent,pidx,(count+1) as u16,fitted_keys,_,_);
            //@ end_vals_slot(raw,val_slot);
            //@ open leaf_without_vals(raw,parent,pidx,(count+1) as u16,fitted_keys);
            //@ open_points_to(self);
            let handle = Handle::<NodeRef<marker::Mut<'b>,K,V,marker::Leaf>,marker::KV>::new_kv(
                NodeRef { height: self.height, node: self.node, _marker: PhantomData },
                idx,
            );
            //@ close_points_to(self);
            //@ close leaf_slots(raw,count+1,fitted_keys,replace_slot(count,MaybeUninit::new(val),vals));
            handle
        }
    }

    unsafe fn push_leaf<'short>(&'short mut self, key: K, val: V) -> *mut V
    /*@
    req *self |-> ?node &*& leaf_header(node.node.as_ptr(),?parent,?pidx) &*&
        leaf_slots(node.node.as_ptr(),?count,?keys,?vals) &*& count < CAPACITY;
    @*/
    /*@
    ens *self |-> node &*&
        consumed_val_loan(node.node.as_ptr(),count,result,count+1,parent,pidx,
            replace_slot(count,MaybeUninit::new(key),keys),replace_slot(count,MaybeUninit::new(val),vals)) &*& *result |-> val;
    @*/
    //@ on_unwind_ens false;
    {
        //@ open leaf_slots(node.node.as_ptr(),count,keys,vals);
        //@ array_inv::<MaybeUninit<V>>();
        //@ close leaf_slots(node.node.as_ptr(),count,keys,vals);
        //@ length_take(count,vals);
        //@ nth_append_r(take(count,vals),cons(MaybeUninit::new(val),drop(count+1,vals)),0);
        unsafe {
            self.push_with_handle/*@::<'a,K,V,'short,'short>@*/(key,val).into_val_mut/*@::<'short,K,V,marker::Leaf>@*/()
        }
    }
}

impl<BorrowType,K,V,Type> Handle<NodeRef<BorrowType,K,V,Type>,marker::Edge> {
    unsafe fn right_kv(mut self) -> Result<Handle<NodeRef<BorrowType,K,V,Type>,marker::KV>,Self>
    //@ req (*self.node.node.as_ptr()).len |-> ?len &*& self.idx <= len;
    /*@
    ens (*self.node.node.as_ptr()).len |-> len &*&
        match result { Result::Ok(kv) => self.idx < len && kv.node == self.node && kv.idx == self.idx,
                       Result::Err(edge) => self.idx == len && edge == self };
    @*/
    //@ on_unwind_ens false;
    {
        //@ open_points_to(&self);
        //@ let receiver = precreate_ref(&self.node);
        //@ init_ref_readonly(receiver,1/2);
        let has_right = self.idx < unsafe { self.node.merge_len() };
        //@ end_ref_readonly(receiver);
        //@ merge_fractions points_to(&self.node,_);
        if has_right {
            let kv = unsafe { Handle::new_navigation_kv(self.node,self.idx) };
            //@ close_points_to(&self);
            Ok(kv)
        } else {
            //@ open_points_to(&self.node);
            let out = Err(self);
            //@ close_points_to(&self.node);
            //@ close_points_to(&self);
            out
        }
    }
}

impl<K,V> NodeRef<marker::Owned,K,V,marker::LeafOrInternal> {
    unsafe fn clear_parent_link<'short>(&'short mut self)
    /*@
    req *self |-> ?node &*& leaf_header(node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(node.node.as_ptr(),?len,?keys,?vals);
    @*/
    /*@
    ens *self |-> node &*& leaf_header(node.node.as_ptr(),Option::None,parent_idx) &*&
        leaf_slots(node.node.as_ptr(),len,keys,vals);
    @*/
    //@ on_unwind_ens false;
    {
        let mut root_node = self.borrow_mut/*@::<K,V,marker::LeafOrInternal,'short>@*/();
        //@ let raw = node.node.as_ptr();
        //@ open leaf_header(raw,parent,parent_idx);
        //@ open leaf_slots(raw,len,keys,vals);
        //@ close_points_to(raw);
        let leaf = root_node.as_leaf_mut/*@::<'short,K,V,marker::LeafOrInternal,'short>@*/();
        //@ open_points_to(leaf);
        leaf.parent = None;
        //@ close_points_to(leaf);
        //@ end_ref_mut(leaf);
        //@ open_points_to(raw);
        //@ close leaf_header(raw,Option::None,parent_idx);
        //@ close leaf_slots(raw,len,keys,vals);
    }

    unsafe fn pop_internal_level<'short,A: AllocatorClone>(&'short mut self, /*@~mut@*/ alloc: A)
    /*@
    req *self |-> ?old &*& std::ptr::drop_may_unwind::<A>() == false &*&
        thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        Allocator::<A>(t,alloc,?id) &*& exists::<lifetime_t>(?k) &*& exists::<real>(?fraction) &*&
        exists::<BoxedNode<K,V>>(?child) &*&
        leaf_header(child.as_ptr(),?parent,?parent_idx) &*& leaf_slots(child.as_ptr(),?len,?keys,?vals) &*&
        if old.height == 0 {
            child == old.node
        } else {
            allocated_internal(old.node.as_ptr() as *InternalNode<K,V>,id,k,fraction) &*&
            (*(old.node.as_ptr() as *InternalNode<K,V>)).data.parent |-> Option::None &*&
            (*(old.node.as_ptr() as *InternalNode<K,V>)).data.parent_idx |-> _ &*&
            leaf_slots(&(*(old.node.as_ptr() as *InternalNode<K,V>)).data,0,_,_) &*&
            (*(old.node.as_ptr() as *InternalNode<K,V>)).edges[..CAPACITY+1] |-> ?edges &*&
            nth(0,edges) == MaybeUninit::new(child)
        };
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        *self |-> ?root &*& root.node == child &*& root.height == old.height - 1 &*&
        leaf_header(child.as_ptr(),Option::None,parent_idx) &*& leaf_slots(child.as_ptr(),len,keys,vals) &*&
        [fraction]lifetime_token(k);
    @*/
    /*@
    on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        old.height == 0 &*& *self |-> old &*&
        leaf_header(child.as_ptr(),parent,parent_idx) &*& leaf_slots(child.as_ptr(),len,keys,vals);
    @*/
    {
        //@ open exists(k);
        //@ open exists(fraction);
        //@ open exists(child);
        /*@
        if old.height == 0 {
            std::alloc::Allocator_to_own::<A>(alloc);
        }
        @*/
        //@ open_points_to(self);
        assert!(self.height > 0);
        let top = self.node;
        //@ close_points_to(self);
        let mut internal_self = unsafe { self.borrow_mut/*@::<K,V,marker::LeafOrInternal,'short>@*/().cast_to_internal_unchecked() };
        //@ let target = old.node.as_ptr() as *InternalNode<K,V>;
        //@ let old_root = &(*target).data;
        //@ open allocated_internal(target,id,k,fraction);
        //@ std::ptr::NonNull_Sized_as_ptr(old.node);
        //@ open leaf_slots(old_root,0,_,_);
        //@ std::mem::MaybeUninit__to_MaybeUninit(&(*old_root).parent_idx);
        //@ close_points_to(target);
        let internal_node = internal_self.as_internal_mut/*@::<'short,K,V,'short>@*/();
        //@ open_points_to(internal_node);
        //@ let base = &(*internal_node).edges as *MaybeUninit<BoxedNode<K,V>>;
        //@ array_split(base,1);
        //@ open array(base,1,_);
        //@ open array(base+1,0,_);
        //@ let slot = precreate_ref(base);
        //@ init_ref_readonly(slot,1/2);
        //@ open_points_to(self);
        self.node = unsafe { internal_node.edges[0].assume_init_read() };
        //@ end_ref_readonly(slot);
        //@ merge_fractions points_to(base,_);
        //@ close array(base,1,[MaybeUninit::new(child)]);
        //@ array_join(base);
        //@ close_points_to(internal_node);
        //@ end_ref_mut(internal_node);
        self.height -= 1;
        //@ close_points_to(self);
        self.clear_parent_link/*@::<K,V,'short>@*/();

        //@ points_to__limits(target);
        //@ assert close_points_to_at_lft_token(1,id.lft,target,?allocation_fraction);
        //@ to_u8s_(target);
        //@ close_points_to_at_lft_token_to_close_u8s_at_lft_token(target);
        //@ close_array_at_lft_(target as *u8);
        //@ lifetime_token_trade_back(allocation_fraction,id.lft);
        //@ let view = precreate_ref(&alloc);
        //@ let call_lifetime = begin_lifetime();
        unsafe {
            //@ let_lft 'call = call_lifetime;
            //@ std::alloc::init_ref_Allocator_at_lifetime::<'call,A>(view);
            //@ std::ptr::NonNull_as_ptr_new(top.as_ptr() as *u8);
            alloc.deallocate/*@::<A,'call>@*/(top.cast(),std::alloc::Layout::new::<InternalNode<K,V>>());
            //@ leak Allocator::<&'call A>(t,view,id);
        }
        //@ end_lifetime(call_lifetime);
        //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
        //@ std::alloc::Allocator_to_own::<A>(alloc);
    }
}

impl<K,V,NodeType> Handle<NodeRef<marker::Dying,K,V,NodeType>,marker::KV> {
    unsafe fn into_key_val(mut self) -> (K,V)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),?len,?keys,?vals) &*& 0 <= self.idx &*& self.idx < len &*&
        nth(self.idx,keys).inner() == some(?former_key) &*& nth(self.idx,vals).inner() == some(?former_val) &*&
        <K>.own(t,former_key) &*& <V>.own(t,former_val);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.node.node.as_ptr(),parent,parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),len,keys,vals) &*&
        result.0 == former_key &*& result.1 == former_val &*& <K>.own(t,result.0) &*& <V>.own(t,result.1);
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert *(&self) |-> ?incoming;
        //@ let node = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open leaf_slots(node,len,keys,vals);
        //@ open_points_to(&self);
        //@ let view = precreate_ref(&self.node);
        //@ init_ref_readonly(view,1/2);
        debug_assert!(self.idx < self.node.merge_len());
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self.node,_);
        //@ open leaf_header(node,parent,parent_idx);
        //@ close_points_to(node);
        let leaf = self.node.as_leaf_dying/*@::<K,V,NodeType,'static>@*/(); //~track_ref_creation
        //@ open_points_to(leaf);
        //@ close_points_to(&(*leaf).keys);
        unsafe {
            let key_slot = <[MaybeUninit<K>]>::get_unchecked_mut(
                {
                    let key_array = &mut leaf.keys; //~track_ref_creation
                    let slice: &mut [MaybeUninit<K>] = key_array;
                    //@ open_points_to(key_array);
                    //@ split_node_slot(key_array as *MaybeUninit<K>,index);
                    slice
                },
                self.idx,
            );
            //@ let key_view = precreate_ref(key_slot);
            //@ init_ref_readonly(key_view,1/2);
            let key = key_slot.assume_init_read();
            //@ end_ref_readonly(key_view);
            //@ merge_fractions points_to(key_slot,_);
            //@ close drop_slot_loan(&(*leaf).keys,key_array,key_slot,index,take(index,keys),drop(index+1,keys));
            //@ end_drop_slot(&(*leaf).keys,key_slot,index);

            //@ close_points_to(&(*leaf).vals);
            let val_slot = <[MaybeUninit<V>]>::get_unchecked_mut(
                {
                    let val_array = &mut leaf.vals; //~track_ref_creation
                    let slice: &mut [MaybeUninit<V>] = val_array;
                    //@ open_points_to(val_array);
                    //@ split_node_slot(val_array as *MaybeUninit<V>,index);
                    slice
                },
                self.idx,
            );
            //@ let val_view = precreate_ref(val_slot);
            //@ init_ref_readonly(val_view,1/2);
            let val = val_slot.assume_init_read();
            //@ end_ref_readonly(val_view);
            //@ merge_fractions points_to(val_slot,_);
            //@ close drop_slot_loan(&(*leaf).vals,val_array,val_slot,index,take(index,vals),drop(index+1,vals));
            //@ end_drop_slot(&(*leaf).vals,val_slot,index);
            //@ nth_at_partition(keys,index);
            //@ nth_at_partition(vals,index);
            //@ Array_to_array(&(*leaf).keys);
            //@ Array_to_array(&(*leaf).vals);
            //@ close_points_to(leaf);
            //@ end_ref_mut(leaf);
            //@ assert ref_mut_end_token(?receiver,&self.node);
            //@ end_ref_mut(receiver);
            //@ close_points_to(&self);
            //@ open_points_to(node);
            //@ close leaf_header(node,parent,parent_idx);
            //@ close leaf_slots(node,len,keys,vals);
            (key,val)
        }
    }
}

unsafe fn read_parent_link<K,V>(child: *const LeafNode<K,V>) -> Option<(NonNull<InternalNode<K,V>>,u16)>
/*@
req [?f]link(child,?expected_parent,?idx);
@*/
/*@
ens [f]link(child,expected_parent,idx) &*&
    match expected_parent {
        Option::None => result == Option::None,
        Option::Some(p) => result == Option::Some(std_tuple_2_::<NonNull<InternalNode<K,V>>,u16> { 0: p, 1: idx })
    };
@*/
//@ on_unwind_ens false;
{
    //@ open [f]link(child,expected_parent,idx);
    let backlink = unsafe { (*child).parent };
    match backlink {
        None => {
            //@ close [f]link(child,Option::None,idx);
            None
        }
        Some(parent) => {
            //@ open_MaybeUninit(&(*child).parent_idx);
            //@ points_to_limits(&(*child).parent_idx as *u16);
            let observed_index = unsafe { *((&raw const (*child).parent_idx) as *const u16) };
            //@ close_MaybeUninit(&(*child).parent_idx);
            //@ close [f]link(child,Option::Some(parent),idx);
            Some((parent, observed_index))
        }
    }
}

impl<BorrowType: marker::BorrowType,K,V,Type> NodeRef<BorrowType,K,V,Type> {
    unsafe fn ascend_from_link(mut self) -> Result<Handle<NodeRef<BorrowType,K,V,marker::Internal>,marker::Edge>, Self>
    /*@
    req [?f]link(self.node.as_ptr(),?expected_parent,?index) &*&
        (if expected_parent != Option::None { self.height < usize::MAX } else { true });
    @*/
    /*@
    ens [f]link(self.node.as_ptr(),expected_parent,index) &*&
        match expected_parent {
            Option::None => match result {
                Result::Err(original) => original == self,
                Result::Ok(edge) => false
            },
            Option::Some(p) => match result {
                Result::Err(original) => false,
                Result::Ok(edge) => edge.node.node.as_ptr() == p.as_ptr() as *LeafNode<K,V> &*&
                    edge.node.height == self.height+1 &*& edge.idx == index
            }
        };
    @*/
    //@ on_unwind_ens false;
    {
        const { assert!(BorrowType::TRAVERSAL_PERMIT); }
        //@ assert [?q]points_to(&self, ?original);
        //@ let view = precreate_ref(&self);
        //@ init_ref_readonly(view, 1/2);
        let leaf_ptr: *const _ = unsafe { Self::as_leaf_ptr(&self) };
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self, _);
        //@ open_points_to(&self);
        let height = self.height;
        let node = self.node;
        //@ close_points_to(&self, q);
        let successor = unsafe { read_parent_link(leaf_ptr) };
        let result = match successor {
            None => None,
            Some((parent, observed_index)) => {
                let parent_height = height + 1;
                Some(Handle {
                    node: unsafe { NodeRef::from_internal(parent, parent_height) },
                    idx: observed_index as usize,
                    _marker: PhantomData,
                })
            }
        };
        result.ok_or(NodeRef { height, node, _marker: PhantomData })
    }
}

type DyingParent<K,V> = Handle<NodeRef<marker::Dying,K,V,marker::Internal>,marker::Edge>;
type DyingNode<K,V> = NodeRef<marker::Dying,K,V,marker::LeafOrInternal>;

unsafe fn dying_result_ok<K,V>(value: Result<DyingParent<K,V>,DyingNode<K,V>>) -> Option<DyingParent<K,V>>
//@ req true;
//@ ens match value { Result::Ok(v) => result == Option::Some(v), Result::Err(original) => result == Option::None };
//@ on_unwind_ens false;
{
    match value {
        Ok(x) => Some(x),
        Err(_) => None,
    }
}

impl<K,V> NodeRef<marker::Dying,K,V,marker::LeafOrInternal> {
    unsafe fn deallocate_and_ascend<A: AllocatorClone>(
        self, /*@~mut@*/ alloc: A,
    ) -> Option<DyingParent<K,V>>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*&
        std::ptr::drop_may_unwind::<A>() == false &*& Allocator::<A>(t,alloc,?id) &*&
        0 <= self.height &*&
        balancing_child_allocation(self.node,self.height,id,?k,?fraction) &*&
        (*self.node.as_ptr()).parent |-> ?parent &*& (*self.node.as_ptr()).parent_idx |-> ?pidx &*&
        leaf_slots(self.node.as_ptr(),_,_,_) &*&
        exists::<u16>(?index) &*&
        (if parent == Option::None {
            index == 0
        } else {
            self.height < usize::MAX &*& pidx == MaybeUninit::new(index)
        }) &*&
        (if self.height > 0 {
            (*(self.node.as_ptr() as *InternalNode<K,V>)).edges[..CAPACITY+1] |-> ?edge_storage
        } else {
            true
        });
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& type_interp::<A>() &*& [fraction]lifetime_token(k) &*&
        match parent {
            Option::None => result == Option::None,
            Option::Some(p) => match result {
                Option::None => false,
                Option::Some(edge) => edge.node.node.as_ptr() == p.as_ptr() as *LeafNode<K,V> &*&
                    edge.node.height == self.height+1 &*& edge.idx == index
            }
        };
    @*/
    //@ on_unwind_ens false;
    {
        let height = self.height;
        let node = self.node;
        //@ let root = node.as_ptr();
        //@ open exists(index);
        //@ close link(root,parent,index);
        let ret = unsafe { dying_result_ok(self.ascend_from_link()) };
        //@ open link(root,parent,index);
        //@ open balancing_child_allocation(node,height,id,k,fraction);
        //@ open leaf_slots(root,_,_,_);
        //@ std::ptr::NonNull_Sized_as_ptr(node);
        /*@
        if height > 0 {
            let internal = root as *InternalNode<K,V>;
            open allocated_internal(internal,id,k,fraction);
            assert &(*internal).data == root;
            close_points_to(internal);
            points_to__limits(internal);
            assert close_points_to_at_lft_token(1,id.lft,internal,?allocation_fraction);
            to_u8s_(internal);
            close_points_to_at_lft_token_to_close_u8s_at_lft_token(internal);
            close_array_at_lft_(internal as *u8);
            lifetime_token_trade_back(allocation_fraction,id.lft);
        } else {
            open allocated_leaf(root,id,k,fraction);
            close_points_to(root);
            points_to__limits(root);
            assert close_points_to_at_lft_token(1,id.lft,root,?allocation_fraction);
            to_u8s_(root);
            close_points_to_at_lft_token_to_close_u8s_at_lft_token(root);
            close_array_at_lft_(root as *u8);
            lifetime_token_trade_back(allocation_fraction,id.lft);
        }
        @*/
        //@ let view = precreate_ref(&alloc);
        //@ let call_lifetime = begin_lifetime();
        unsafe {
            //@ let_lft 'call = call_lifetime;
            //@ std::alloc::init_ref_Allocator_at_lifetime::<'call,A>(view);
            //@ std::ptr::NonNull_as_ptr_new(node.as_ptr() as *u8);
            alloc.deallocate/*@::<A,'call>@*/(
                node.cast(),
                if height > 0 {
                    std::alloc::Layout::new::<InternalNode<K,V>>()
                } else {
                    std::alloc::Layout::new::<LeafNode<K,V>>()
                },
            );
            //@ leak Allocator::<&'call A>(t,view,id);
        }
        //@ end_lifetime(call_lifetime);
        //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
        //@ std::alloc::Allocator_to_own::<A>(alloc);
        ret
    }
}

/*@
fix removed_prefix<T>(entries: list<T>, count: usize, index: usize) -> list<T> {
    append(take(index, take(count,entries)), append(drop(index+1,take(count,entries)),
        append(drop(count-1,take(count,entries)), drop(count,entries))))
}

lem expand_removed_prefix<T>(entries: list<T>, count: usize, index: usize)
    req true;
    ens append(append(take(index,take(count,entries)),append(drop(index+1,take(count,entries)),
        drop(count-1,take(count,entries)))),drop(count,entries)) == removed_prefix(entries,count,index);
{
    append_assoc(drop(index+1,take(count,entries)),drop(count-1,take(count,entries)),drop(count,entries));
    append_assoc(take(index,take(count,entries)),append(drop(index+1,take(count,entries)),
        drop(count-1,take(count,entries))),drop(count,entries));
}
@*/

impl<'a,K:'a,V:'a> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,marker::KV> {
    unsafe fn remove<'short>(mut self)
        -> ((K,V), Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,marker::Edge>)
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.node.node.as_ptr(),?parent,?parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),?size,?keys,?vals) &*& 0 <= self.idx &*& self.idx < size &*&
        nth(self.idx,keys).inner() == some(?key) &*& nth(self.idx,keys) == MaybeUninit::new(key) &*&
        nth(self.idx,vals).inner() == some(?val) &*& nth(self.idx,vals) == MaybeUninit::new(val) &*&
        <K>.own(t,key) &*& <V>.own(t,val);
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        leaf_header(self.node.node.as_ptr(),parent,parent_idx) &*&
        leaf_slots(self.node.node.as_ptr(),size-1,removed_prefix(keys,size,self.idx),removed_prefix(vals,size,self.idx)) &*&
        (result.0).0 == key &*& (result.0).1 == val &*& <K>.own(t,key) &*& <V>.own(t,val) &*&
        result.1.node == self.node &*& result.1.idx == self.idx;
    @*/
    //@ on_unwind_ens false;
    {
        //@ assert *(&self) |-> ?incoming;
        //@ let raw = incoming.node.node.as_ptr();
        //@ let index = incoming.idx;
        //@ open leaf_slots(raw,size,keys,vals);
        //@ open_points_to(&self);
        //@ let meta = precreate_ref(&self.node);
        //@ init_ref_readonly(meta,1/2);
        let old_len = self.node.merge_len();
        //@ end_ref_readonly(meta);
        //@ merge_fractions points_to(&self.node,_);
        unsafe {
            //@ close leaf_without_keys(raw,parent,parent_idx,size as u16,vals);
            //@ nth_take_range(keys,size,index);
            let k = slice_remove(self.node.key_area_prefix_mut/*@::<'a,K,V,marker::Leaf,'short>@*/(..old_len),self.idx); //~track_ref_creation
            //@ assert keys_range_loan(raw,?key_slice,0,size,parent,parent_idx,size as u16,vals,_,_);
            //@ end_keys_range(raw,key_slice);
            //@ open leaf_without_keys(raw,parent,parent_idx,size as u16,vals);
            //@ assert ref_mut_end_token(?after_key,&self.node);
            //@ end_ref_mut(after_key);
            //@ expand_removed_prefix(keys,size,index);

            //@ close leaf_without_vals(raw,parent,parent_idx,size as u16,removed_prefix(keys,size,index));
            //@ nth_take_range(vals,size,index);
            let v = slice_remove(self.node.val_area_prefix_mut/*@::<'a,K,V,marker::Leaf,'short>@*/(..old_len),self.idx); //~track_ref_creation
            //@ assert vals_range_loan(raw,?val_slice,0,size,parent,parent_idx,size as u16,_,_,_);
            //@ end_vals_range(raw,val_slice);
            //@ open leaf_without_vals(raw,parent,parent_idx,size as u16,removed_prefix(keys,size,index));
            //@ assert ref_mut_end_token(?after_val,&self.node);
            //@ end_ref_mut(after_val);
            //@ expand_removed_prefix(vals,size,index);

            //@ open leaf_header(raw,parent,parent_idx);
            //@ close leaf_without_len(raw,parent,parent_idx,removed_prefix(keys,size,index),removed_prefix(vals,size,index));
            *self.node.len_mut/*@::<'a,K,V,marker::Leaf,'short>@*/() = (old_len-1) as u16; //~track_ref_creation
            //@ assert len_loan(raw,?len,parent,parent_idx,_,_);
            //@ end_len_loan(raw,len);
            //@ open leaf_without_len(raw,parent,parent_idx,removed_prefix(keys,size,index),removed_prefix(vals,size,index));
            //@ assert ref_mut_end_token(?after_len,&self.node);
            //@ end_ref_mut(after_len);

            let result = ((k,v),self.left_edge());
            //@ close leaf_header(raw,parent,parent_idx);
            //@ close leaf_slots(raw,size-1,removed_prefix(keys,size,index),removed_prefix(vals,size,index));
            //@ close_points_to(&self);
            result
        }
    }
}

impl<'a,K,V> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Internal>,marker::KV> {
    unsafe fn consider_for_balancing(mut self) -> BalancingContext<'a,K,V>
    /*@
    req thread_token(?t) &*& 0 < self.node.height &*&
        0 <= self.idx &*& (*self.node.node.as_ptr()).len |-> ?len &*& self.idx < len &*& len <= CAPACITY &*&
        pointer_within_limits(&(*(self.node.node.as_ptr() as *InternalNode<K,V>)).edges) == true &*&
        [?f](*(self.node.node.as_ptr() as *InternalNode<K,V>)).edges[..CAPACITY+1] |-> ?edges &*&
        exists::<pair<BoxedNode<K,V>,BoxedNode<K,V>>>(pair(?left,?right)) &*&
        nth(self.idx,edges) == MaybeUninit::new(left) &*& nth(self.idx+1,edges) == MaybeUninit::new(right);
    @*/
    /*@
    ens thread_token(t) &*& (*self.node.node.as_ptr()).len |-> len &*&
        [f](*(self.node.node.as_ptr() as *InternalNode<K,V>)).edges[..CAPACITY+1] |-> edges &*&
        exists::<pair<BoxedNode<K,V>,BoxedNode<K,V>>>(pair(left,right)) &*&
        result.parent == self &*& result.left_child.node == left &*& result.right_child.node == right &*&
        result.left_child.height == self.node.height-1 &*& result.right_child.height == self.node.height-1;
    @*/
    //@ on_unwind_ens false;
    {
        //@ open exists(pair(left,right));
        //@ assert *(&self) |-> ?incoming;
        //@ let view = precreate_ref(&self);
        //@ init_ref_readonly(view,1/2);
        //@ open_points_to(view);
        //@ open_points_to(&(*view).node);
        let self1 = unsafe { std::ptr::read(&self) };
        //@ close_points_to(&(*view).node,1/2);
        //@ close_points_to(view,1/2);
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self,_);
        //@ let view2 = precreate_ref(&self);
        //@ init_ref_readonly(view2,1/2);
        //@ open_points_to(view2);
        //@ open_points_to(&(*view2).node);
        let self2 = unsafe { std::ptr::read(&self) };
        //@ close_points_to(&(*view2).node,1/2);
        //@ close_points_to(view2,1/2);
        //@ end_ref_readonly(view2);
        //@ merge_fractions points_to(&self,_);
        //@ open_points_to(&self);
        //@ open_points_to(&self.node);
        let context = BalancingContext {
            parent: self,
            left_child: {
                //@ close exists(left);
                let child = unsafe { self1.left_edge().descend() };
                //@ open exists(left);
                child
            },
            right_child: {
                //@ close exists(right);
                let child = unsafe { self2.right_edge().descend() };
                //@ open exists(right);
                child
            },
        };
        //@ close_points_to(&self.node);
        //@ close_points_to(&self);
        //@ close exists(pair(left,right));
        context
    }
}


impl<'a,K,V> NodeRef<marker::Mut<'a>,K,V,marker::LeafOrInternal> {
    unsafe fn cast_node_to_leaf(self) -> NodeRef<marker::Mut<'a>,K,V,marker::Leaf>
    //@ req self.height == 0;
    //@ ens result.node == self.node &*& result.height == 0;
    //@ on_unwind_ens false;
    {
        debug_assert!(self.height == 0);
        NodeRef { height: self.height, node: self.node, _marker: PhantomData }
    }
}

impl<'a,K,V,Type> Handle<NodeRef<marker::Mut<'a>,K,V,marker::LeafOrInternal>,Type> {
    unsafe fn cast_handle_to_leaf(self) -> Handle<NodeRef<marker::Mut<'a>,K,V,marker::Leaf>,Type>
    //@ req self.node.height == 0;
    //@ ens result.node.node == self.node.node &*& result.node.height == 0 &*& result.idx == self.idx;
    //@ on_unwind_ens false;
    {
        let node = unsafe { self.node.cast_node_to_leaf() };
        Handle { node, idx: self.idx, _marker: PhantomData }
    }
}


impl<BorrowType,K,V> Handle<NodeRef<BorrowType,K,V,marker::Leaf>,marker::Edge> {
    unsafe fn forget_leaf_edge(self) -> Handle<NodeRef<BorrowType,K,V,marker::LeafOrInternal>,marker::Edge>
    //@ req (*self.node.node.as_ptr()).len |-> ?len &*& self.idx <= len;
    //@ ens (*self.node.node.as_ptr()).len |-> len &*& result.node.node == self.node.node &*& result.node.height == self.node.height &*& result.idx == self.idx;
    //@ on_unwind_ens false;
    {
        unsafe { Handle::new_relink_edge(self.node.forget_type(),self.idx) }
    }
}

impl<BorrowType,K,V> Handle<NodeRef<BorrowType,K,V,marker::Internal>,marker::Edge> {
    unsafe fn forget_internal_edge(self) -> Handle<NodeRef<BorrowType,K,V,marker::LeafOrInternal>,marker::Edge>
    //@ req (*self.node.node.as_ptr()).len |-> ?len &*& self.idx <= len;
    //@ ens (*self.node.node.as_ptr()).len |-> len &*& result.node.node == self.node.node &*& result.node.height == self.node.height &*& result.idx == self.idx;
    //@ on_unwind_ens false;
    {
        unsafe { Handle::new_relink_edge(self.node.forget_type(),self.idx) }
    }
}

impl<BorrowType,K,V> Handle<NodeRef<BorrowType,K,V,marker::Leaf>,marker::KV> {
    unsafe fn forget_leaf_kv(self) -> Handle<NodeRef<BorrowType,K,V,marker::LeafOrInternal>,marker::KV>
    //@ req (*self.node.node.as_ptr()).len |-> ?len &*& self.idx < len;
    //@ ens (*self.node.node.as_ptr()).len |-> len &*& result.node.node == self.node.node &*& result.node.height == self.node.height &*& result.idx == self.idx;
    //@ on_unwind_ens false;
    {
        unsafe { Handle::new_navigation_kv(self.node.forget_type(),self.idx) }
    }
}


/*@
lem prepare_neighbor<K,V>(children: list<BoxedNode<K,V>>, edges: list<MaybeUninit<BoxedNode<K,V>>>, index: usize)
    req take(length(children),edges) == initialized_edges(children) &*& length(children) <= length(edges) &*&
        0 <= index &*& index < length(children);
    ens exists::<BoxedNode<K,V>>(nth(index,children)) &*& nth(index,edges) == MaybeUninit::new(nth(index,children));
{
    nth_take_range(edges,length(children),index);
    nth_initialized_edge(children,index);
    close exists(nth(index,children));
}

pred chosen_parent<K,V>(
    t: thread_id_t, path: list<ParentStep<K,V>>, origin: *LeafNode<K,V>, root: *LeafNode<K,V>
) =
    path == cons(ParentStep(?address,?idx,?count,ParentPayload(?keys,?vals,?edges)),?rest) &*&
    exists::<NonNull<InternalNode<K,V>>>(?parent) &*& parent.as_ptr() == address &*&
    ancestors(&(*address).data,rest,root) &*& route_frames(t,rest) &*&
    ready_parent(t,parent,count,idx,?children,keys,vals) &*& nth(idx,children) == NonNull::new(origin) &*&
    struct_LeafNode_padding(&(*address).data) &*& struct_InternalNode_padding(address);
@*/

impl<'a,K,V> NodeRef<marker::Mut<'a>,K,V,marker::LeafOrInternal> {
    unsafe fn choose_parent_kv(mut self) -> Result<LeftOrRight<BalancingContext<'a,K,V>>,Self>
    /*@
    req thread_token(?t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        ancestors(self.node.as_ptr(),?path,?root) &*& route_frames(t,path) &*&
        0 <= self.height &*& self.height + length(path) < usize::MAX;
    @*/
    /*@
    ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*&
        match result {
            Result::Err(top) => top == self &*& path == nil &*& ancestors(self.node.as_ptr(),path,root) &*& route_frames(t,path),
            Result::Ok(choice) => chosen_parent(t,path,self.node.as_ptr(),root) &*&
                match choice {
                    LeftOrRight::Left(context) => context.right_child == self,
                    LeftOrRight::Right(context) => context.left_child == self
                }
        };
    @*/
    //@ on_unwind_ens thread_token(t) &*& type_interp::<K>() &*& type_interp::<V>() &*& chosen_parent(t,path,self.node.as_ptr(),root);
    {
        //@ assert *(&self) |-> ?incoming;
        //@ let raw = incoming.node.as_ptr();
        //@ let view = precreate_ref(&self);
        //@ init_ref_readonly(view,1/2);
        //@ std::ptr::NonNull_new_as_ptr(incoming.node);
        //@ close NodeRef_own::<marker::Mut<'a>,K,V,marker::LeafOrInternal>(t,incoming);
        let original = unsafe { std::ptr::read(&self) };
        //@ open NodeRef_own::<marker::Mut<'a>,K,V,marker::LeafOrInternal>(t,original);
        //@ end_ref_readonly(view);
        //@ merge_fractions points_to(&self,_);
        match unsafe { original.ascend/*@::<'a,K,V>@*/() } {
            Ok(parent_edge) => {
                //@ open exists::<NonNull<InternalNode<K,V>>>(?parent);
                //@ assert path == cons(ParentStep(parent.as_ptr(),?index,?count,ParentPayload(?keys,?vals,?original_edges)),?rest);
                //@ std::ptr::NonNull_new_as_ptr(parent);
                //@ std::ptr::NonNull_Sized_as_ptr(parent);
                //@ open ready_parent(t,parent,count,index,?children,keys,vals);
                //@ open internal_slots(parent,count,children,keys,vals);
                //@ open node_arrays(parent.as_ptr(),keys,vals,?edges);
                //@ assert parent_edge.node.node.as_ptr() == parent.as_ptr() as *LeafNode<K,V>;
                //@ assert &(*parent.as_ptr()).data == parent.as_ptr() as *LeafNode<K,V>;
                //@ array_inv::<MaybeUninit<BoxedNode<K,V>>>();
                match parent_edge.left_kv() {
                    Ok(/*@~mut@*/ left_parent_kv) => {
                        //@ close_points_to(&left_parent_kv);
                        //@ let meta = precreate_ref(&left_parent_kv);
                        //@ init_ref_readonly(meta,1/2);
                        //@ open_points_to(meta);
                        //@ open_points_to(&(*meta).node);
                        let parent_handle = unsafe { std::ptr::read(&left_parent_kv) };
                        //@ close_points_to(&(*meta).node,1/2);
                        //@ close_points_to(meta,1/2);
                        //@ end_ref_readonly(meta);
                        //@ merge_fractions points_to(&left_parent_kv,_);
                        //@ prepare_neighbor(children,edges,index-1);
                        //@ open_points_to(&left_parent_kv);
                        //@ open_points_to(&left_parent_kv.node);
                        let left_child = unsafe { left_parent_kv.left_edge().descend() };
                        //@ open exists(nth(index-1,children));
                        //@ close node_arrays(parent.as_ptr(),keys,vals,edges);
                        //@ close internal_slots(parent,count,children,keys,vals);
                        //@ close ready_parent(t,parent,count,index,children,keys,vals);
                        //@ close exists(parent);
                        //@ close chosen_parent(t,path,raw,root);
                        //@ open_points_to(&self);
                        let answer = Ok(LeftOrRight::Left(BalancingContext {
                            parent: parent_handle, left_child, right_child: self,
                        }));
                        //@ close_points_to(&self);
                        answer
                    }
                    Err(parent_edge) => match parent_edge.right_kv() {
                        Ok(/*@~mut@*/ right_parent_kv) => {
                            //@ close_points_to(&right_parent_kv);
                            //@ let meta = precreate_ref(&right_parent_kv);
                            //@ init_ref_readonly(meta,1/2);
                            //@ open_points_to(meta);
                            //@ open_points_to(&(*meta).node);
                            let parent_handle = unsafe { std::ptr::read(&right_parent_kv) };
                            //@ close_points_to(&(*meta).node,1/2);
                            //@ close_points_to(meta,1/2);
                            //@ end_ref_readonly(meta);
                            //@ merge_fractions points_to(&right_parent_kv,_);
                            //@ open_points_to(&self);
                            let left_child = self;
                            //@ prepare_neighbor(children,edges,index+1);
                            //@ open_points_to(&right_parent_kv);
                            //@ open_points_to(&right_parent_kv.node);
                            let right_child = unsafe { right_parent_kv.right_edge().descend() };
                            //@ open exists(nth(index+1,children));
                            //@ close node_arrays(parent.as_ptr(),keys,vals,edges);
                            //@ close internal_slots(parent,count,children,keys,vals);
                            //@ close ready_parent(t,parent,count,index,children,keys,vals);
                            //@ close exists(parent);
                            //@ close chosen_parent(t,path,raw,root);
                            let answer = Ok(LeftOrRight::Right(BalancingContext {
                                parent: parent_handle, left_child, right_child,
                            }));
                            //@ close_points_to(&self);
                            answer
                        }
                        Err(_) => {
                            //@ close node_arrays(parent.as_ptr(),keys,vals,edges);
                            //@ close internal_slots(parent,count,children,keys,vals);
                            //@ close ready_parent(t,parent,count,index,children,keys,vals);
                            //@ close exists(parent);
                            //@ close chosen_parent(t,path,raw,root);
                            panic!("internal error: entered unreachable code: empty internal node")
                        },
                    },
                }
            }
            Err(top) => Err(top),
        }
    }
}

fn main() {}
