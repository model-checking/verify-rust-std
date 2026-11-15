//! This module contains a variety of sort implementations that are optimized for small lengths.

use crate::mem::{self, ManuallyDrop, MaybeUninit};
use crate::slice::sort::shared::FreezeMarker;
use crate::{hint, intrinsics, ptr, slice};

/*@

// ===== Ghost vocabulary for the Challenge 8 target specifications =====

// `x` occurs in `xs`.
fix contains<T>(xs: list<T>, x: T) -> bool {
    match xs {
        nil => false,
        cons(x0, xs0) => x0 == x || contains(xs0, x)
    }
}

// `xs` is a permutation of `ys` (same elements, same multiplicities).
fix is_perm<T>(xs: list<T>, ys: list<T>) -> bool {
    match xs {
        nil => ys == nil,
        cons(x, xs0) => contains(ys, x) && is_perm(xs0, remove(x, ys))
    }
}

// No element of `xs` is less than its predecessor according to `lt`.
// (Clause-by-clause equivalent to the nested form `cons(x, xs0) => match xs0 { nil => true,
// cons(y, xs1) => !lt(y, x) && sorted_by(lt, xs0) }`, which VeriFast 26.10 cannot unfold: any proof step
// that unfolds a fixpoint with a nested `match` on a pattern variable aborts with
// `Fatal error: exception Not_found`.)
fix sorted_by<T>(lt: fix(T, T, bool), xs: list<T>) -> bool {
    match xs {
        nil => true,
        cons(x, xs0) => (xs0 == nil || !lt(head(xs0), x)) && sorted_by(lt, xs0)
    }
}

// `xs` with the element at index `i` replaced by `x`.
fix update_nth<T>(i: i32, x: T, xs: list<T>) -> list<T> {
    match xs {
        nil => nil,
        cons(x0, xs0) => if i == 0 { cons(x, xs0) } else { cons(x0, update_nth(i - 1, x, xs0)) }
    }
}

// ===== BEGIN TRUSTED COMPARATOR MODEL =====
//
// The only trusted part of the specifications. Everything in this block is assumed, not proven.
// Every target crate contains this block verbatim (checked by verify.sh); `assume` may appear
// nowhere else.
//
// `is_less_models::<T, F>(f)`: the comparator value `f` is well-behaved. A call `f(&a, &b)`
// terminates without panicking, leaves `f`, `a` and `b` unchanged, and returns
// `is_less_model_of::<T, F>(f)(a, b)`.
// `is_less_model_of::<T, F>(f)`: the order `f` computes. It is left uninterpreted so that the
// specifications hold for every such order; the lemmas below only fix it to be a strict weak order.
// The link between a real call `is_less(&x, &y)` and the model is the trusted wrapper
// `is_less__VeriFast_wrapper` (block TRUSTED COMPARATOR CALL WRAPPER at the end of smallsort.rs), which
// every such call goes through; there is no free-argument lemma for it, so each use of the link is
// tied to one real call.
fix is_less_models<T, F>(f: F) -> bool;
fix is_less_model_of<T, F>(f: F) -> fix(T, T, bool);

// `lt(a, b)`.
fix apply_lt<T>(lt: fix(T, T, bool), a: T, b: T) -> bool { lt(a, b) }

// Axiom (strict weak order, 1/3): irreflexive.
lem is_less_irreflexive<T, F>(f: F, a: T)
    req is_less_models::<T, F>(f) == true;
    ens !apply_lt(is_less_model_of::<T, F>(f), a, a);
{
    assume(false);
}

// Axiom (strict weak order, 2/3): transitive.
lem is_less_transitive<T, F>(f: F, a: T, b: T, c: T)
    req is_less_models::<T, F>(f) == true &*&
        apply_lt(is_less_model_of::<T, F>(f), a, b) && apply_lt(is_less_model_of::<T, F>(f), b, c);
    ens apply_lt(is_less_model_of::<T, F>(f), a, c) == true;
{
    assume(false);
}

// Axiom (strict weak order, 3/3): incomparability is transitive.
lem is_less_incomparable_transitive<T, F>(f: F, a: T, b: T, c: T)
    req is_less_models::<T, F>(f) == true &*&
        !apply_lt(is_less_model_of::<T, F>(f), a, b) && !apply_lt(is_less_model_of::<T, F>(f), b, a) &*&
        !apply_lt(is_less_model_of::<T, F>(f), b, c) && !apply_lt(is_less_model_of::<T, F>(f), c, b);
    ens !apply_lt(is_less_model_of::<T, F>(f), a, c) && !apply_lt(is_less_model_of::<T, F>(f), c, a);
{
    assume(false);
}

// ===== END TRUSTED COMPARATOR MODEL =====

@*/

// ===== BEGIN TRUSTED MODEL AXIOMS =====
//
// Trusted: facts about Rust that VeriFast 26.10 does not model. Each is assumed, not proven. Every crate
// contains this block verbatim (checked by verify.sh).
/*@

// `MaybeUninit<T>` owns no resources (it may hold any bytes, and dropping it does nothing). VeriFast 26.10
// leaves `<MaybeUninit<T>>.own` undefined.
lem MaybeUninit_own_trivial<T>(t: thread_id_t, v: std::mem::MaybeUninit<T>)
    req true;
    ens own::<std::mem::MaybeUninit<T>>(t)(v);
{
    assume(false);
}

// Layout of the stack arrays `MaybeUninit<[T; N]>` of `small_sort_general` (N = 48) and
// `small_sort_network` (N = 32): an array of `N` elements, aligned as `T` (Rust reference, "Type
// layout": arrays). VeriFast 26.10 has no `size_of`/`align_of` facts for array types.
lem MaybeUninit_array_48_layout<T>()
    req true;
    ens std::mem::size_of::<std::mem::MaybeUninit<[T; 48]>>() == 48 * std::mem::size_of::<T>() &*&
        std::mem::align_of::<std::mem::MaybeUninit<[T; 48]>>() == std::mem::align_of::<T>();
{
    assume(false);
}

lem MaybeUninit_array_32_layout<T>()
    req true;
    ens std::mem::size_of::<std::mem::MaybeUninit<[T; 32]>>() == 32 * std::mem::size_of::<T>() &*&
        std::mem::align_of::<std::mem::MaybeUninit<[T; 32]>>() == std::mem::align_of::<T>();
{
    assume(false);
}

// For every `T` that the trait impls of `UnstableSmallSortFreezeTypeImpl` are instantiated with, the
// array types `[T; 48]` (in `small_sort_general`, which both impls call) and `[T; 32]` (in
// `small_sort_network`, called by the `CopyMarker` impl) exist; rustc rejects types larger than
// `isize::MAX` bytes. So `size_of::<T>() * 48` (and `* 32`) does not overflow.
lem small_sort_general_instantiated<T>()
    req true;
    ens 0 <= std::mem::size_of::<T>() &*& 48 * std::mem::size_of::<T>() <= isize::MAX;
{
    assume(false);
}

@*/
// ===== END TRUSTED MODEL AXIOMS =====

/*@

// ===== Proof library (not trusted: every lemma below is proven) =====

// Splits a points-to chunk into two chunks of different predicate symbols, so that VeriFast does not
// merge them again (needed when two shared references to the same place are passed to one call).
lem points_to_split_half<T>(p: *T)
    req [?f](*p |-> ?v);
    ens [f/2](*p |-> v) &*& [f/2]points_to_(p, some(v));
{
    open points_to(p, v);
    close [f/2]points_to(p, v);
}

// A fraction of a points-to chunk kept out of reach of a call (so that the call sees only the rest).
pred hidden_pt<T>(p: *T, v: T) = *p |-> v;

lem pt_hide_half<T>(p: *T)
    req [?f](*p |-> ?v);
    ens [f/2](*p |-> v) &*& [f/2]hidden_pt(p, v);
{
    close [f/2]hidden_pt(p, v);
}

lem pt_unhide<T>(p: *T)
    req [?f1](*p |-> ?v1) &*& [?f2]hidden_pt(p, ?v2);
    ens [f1 + f2](*p |-> v2) &*& v1 == v2;
{
    open [f2]hidden_pt(p, v2);
}

// ----- lists -----

lem nth_take_lt<T>(i: i32, n: i32, xs: list<T>)
    req 0 <= i &*& i < n;
    ens nth(i, take(n, xs)) == nth(i, xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { nth_take_lt(i - 1, n - 1, xs0); } }
    }
}

lem update_nth_length<T>(i: i32, x: T, xs: list<T>)
    req true;
    ens length(update_nth(i, x, xs)) == length(xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { update_nth_length(i - 1, x, xs0); } }
    }
}

lem update_nth_def<T>(i: i32, x: T, xs: list<T>)
    req 0 <= i &*& i < length(xs);
    ens update_nth(i, x, xs) == append(take(i, xs), cons(x, drop(i + 1, xs)));
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { update_nth_def(i - 1, x, xs0); } }
    }
}

lem nth_update_nth_same<T>(i: i32, x: T, xs: list<T>)
    req 0 <= i &*& i < length(xs);
    ens nth(i, update_nth(i, x, xs)) == x;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { nth_update_nth_same(i - 1, x, xs0); } }
    }
}

lem nth_update_nth_other<T>(i: i32, j: i32, x: T, xs: list<T>)
    req i != j;
    ens nth(j, update_nth(i, x, xs)) == nth(j, xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 && j != 0 { nth_update_nth_other(i - 1, j - 1, x, xs0); } }
    }
}

lem update_nth_nth<T>(i: i32, xs: list<T>)
    req true;
    ens update_nth(i, nth(i, xs), xs) == xs;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { update_nth_nth(i - 1, xs0); } }
    }
}

lem update_nth_update_nth_same<T>(i: i32, x: T, y: T, xs: list<T>)
    req true;
    ens update_nth(i, x, update_nth(i, y, xs)) == update_nth(i, x, xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if i != 0 { update_nth_update_nth_same(i - 1, x, y, xs0); } }
    }
}

// ----- arrays -----

lem array_join_n0<T>(p: *T, c1: i32, c2: i32)
    req [?f]array::<T>(p, c1, ?vs1) &*& [f]array::<T>(p + c1, c2, ?vs2);
    ens [f]array::<T>(p, c1 + c2, append(vs1, vs2));
{
    open array::<T>(p, c1, vs1);
    if c1 == 0 {
    } else {
        array_join_n0(p + 1, c1 - 1, c2);
        close [f]array::<T>(p, c1 + c2, append(vs1, vs2));
    }
}

pred array_hole<T>(p: *T, n: i32, vs: list<T>, i: i32) =
    0 <= i &*& i < n &*& length(vs) == n &*&
    array::<T>(p, i, take(i, vs)) &*& array::<T>(p + i + 1, n - i - 1, drop(i + 1, vs));

lem array_open_at<T>(p: *T, i: i32)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 <= i &*& i < n;
    ens [f](*(p + i) |-> nth(i, vs)) &*& [f]array_hole::<T>(p, n, vs, i);
{
    array_split(p, i);
    drop_n_plus_one(i, vs);
    open array::<T>(p + i, n - i, drop(i, vs));
    close [f]array_hole::<T>(p, n, vs, i);
}

lem array_close_at<T>(p: *T, i: i32, x: T)
    req [?f](*(p + i) |-> x) &*& [f]array_hole::<T>(p, ?n, ?vs, i);
    ens [f]array::<T>(p, n, update_nth(i, x, vs));
{
    open array_hole::<T>(p, n, vs, i);
    close [f]array::<T>(p + i, n - i, cons(x, drop(i + 1, vs)));
    array_join_n0(p, i, n - i);
    update_nth_def(i, x, vs);
}

lem take_update_nth<T>(n: i32, j: i32, y: T, xs: list<T>)
    req 0 <= n &*& 0 <= j;
    ens take(n, update_nth(j, y, xs)) == if j < n { update_nth(j, y, take(n, xs)) } else { take(n, xs) };
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if n != 0 && j != 0 { take_update_nth(n - 1, j - 1, y, xs0); } }
    }
}

lem drop_update_nth<T>(n: i32, j: i32, y: T, xs: list<T>)
    req 0 <= n &*& 0 <= j;
    ens drop(n, update_nth(j, y, xs)) == if j < n { drop(n, xs) } else { update_nth(j - n, y, drop(n, xs)) };
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if n != 0 { if j != 0 { drop_update_nth(n - 1, j - 1, y, xs0); } else { } } }
    }
}

pred array_hole2<T>(p: *T, n: i32, vs: list<T>, i: i32, j: i32) =
    0 <= i &*& i < n &*& 0 <= j &*& j < n &*& i != j &*& length(vs) == n &*&
    if j < i {
        array_hole::<T>(p, i, take(i, vs), j) &*& array::<T>(p + i + 1, n - i - 1, drop(i + 1, vs))
    } else {
        array::<T>(p, i, take(i, vs)) &*& array_hole::<T>(p + i + 1, n - i - 1, drop(i + 1, vs), j - i - 1)
    };

lem array_open_at2<T>(p: *T, i: i32, j: i32)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 <= i &*& i < n &*& 0 <= j &*& j < n &*& i != j;
    ens [f](*(p + i) |-> nth(i, vs)) &*& [f](*(p + j) |-> nth(j, vs)) &*& [f]array_hole2::<T>(p, n, vs, i, j);
{
    array_open_at(p, i);
    open array_hole::<T>(p, n, vs, i);
    if j < i {
        array_open_at(p, j);
    } else {
        array_open_at(p + i + 1, j - i - 1);
        nth_drop(j - i - 1, i + 1, vs);
    }
    close [f]array_hole2::<T>(p, n, vs, i, j);
}

lem array_close_at2<T>(p: *T, i: i32, j: i32, x: T, y: T)
    req [?f](*(p + i) |-> x) &*& [f](*(p + j) |-> y) &*& [f]array_hole2::<T>(p, ?n, ?vs, i, j);
    ens [f]array::<T>(p, n, update_nth(i, x, update_nth(j, y, vs)));
{
    open array_hole2::<T>(p, n, vs, i, j);
    let ws = update_nth(j, y, vs);
    update_nth_length(j, y, vs);
    take_update_nth(i, j, y, vs);
    drop_update_nth(i + 1, j, y, vs);
    if j < i {
        array_close_at(p, j, y);
    } else {
        array_close_at(p + i + 1, j - i - 1, y);
    }
    close [f]array_hole::<T>(p, n, ws, i);
    array_close_at(p, i, x);
}

// Reading two elements leaves the array unchanged.
lem array_close_at2_same<T>(p: *T, i: i32, j: i32)
    req [?f](*(p + i) |-> ?x) &*& [f](*(p + j) |-> ?y) &*& [f]array_hole2::<T>(p, ?n, ?vs, i, j) &*& x == nth(i, vs) &*& y == nth(j, vs);
    ens [f]array::<T>(p, n, vs);
{
    array_close_at2(p, i, j, x, y);
    update_nth_nth(j, vs);
    update_nth_nth(i, vs);
}

lem array_close_at_same<T>(p: *T, i: i32)
    req [?f](*(p + i) |-> ?x) &*& [f]array_hole::<T>(p, ?n, ?vs, i) &*& x == nth(i, vs);
    ens [f]array::<T>(p, n, vs);
{
    array_close_at(p, i, x);
    update_nth_nth(i, vs);
}

// ----- permutations -----

lem contains_remove<T>(x: T, y: T, xs: list<T>)
    req contains(xs, x) == true &*& x != y;
    ens contains(remove(y, xs), x) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != x && x0 != y { contains_remove(x, y, xs0); } }
    }
}

lem contains_remove_inv<T>(x: T, y: T, xs: list<T>)
    req contains(remove(y, xs), x) == true;
    ens contains(xs, x) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != y && x0 != x { contains_remove_inv(x, y, xs0); } }
    }
}

lem remove_remove_comm<T>(x: T, y: T, xs: list<T>)
    req true;
    ens remove(x, remove(y, xs)) == remove(y, remove(x, xs));
{
    match xs {
        nil => {}
        cons(x0, xs0) => { remove_remove_comm(x, y, xs0); }
    }
}

lem is_perm_refl<T>(xs: list<T>)
    req true;
    ens is_perm(xs, xs) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { is_perm_refl(xs0); }
    }
}

lem length_remove<T>(x: T, xs: list<T>)
    req contains(xs, x) == true;
    ens length(remove(x, xs)) == length(xs) - 1;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != x { length_remove(x, xs0); } }
    }
}

lem is_perm_length<T>(xs: list<T>, ys: list<T>)
    req is_perm(xs, ys) == true;
    ens length(xs) == length(ys);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { is_perm_length(xs0, remove(x0, ys)); length_remove(x0, ys); }
    }
}

lem is_perm_contains<T>(xs: list<T>, ys: list<T>, z: T)
    req is_perm(xs, ys) == true &*& contains(xs, z) == true;
    ens contains(ys, z) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if x0 != z {
                is_perm_contains(xs0, remove(x0, ys), z);
                contains_remove_inv(z, x0, ys);
            }
        }
    }
}

lem is_perm_remove<T>(xs: list<T>, ys: list<T>, z: T)
    req is_perm(xs, ys) == true &*& contains(xs, z) == true;
    ens contains(ys, z) == true &*& is_perm(remove(z, xs), remove(z, ys)) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if x0 == z {
            } else {
                is_perm_remove(xs0, remove(x0, ys), z);
                contains_remove_inv(z, x0, ys);
                contains_remove(x0, z, ys);
                remove_remove_comm(x0, z, ys);
            }
        }
    }
}

lem is_perm_trans<T>(xs: list<T>, ys: list<T>, zs: list<T>)
    req is_perm(xs, ys) == true &*& is_perm(ys, zs) == true;
    ens is_perm(xs, zs) == true;
{
    match xs {
        nil => { is_perm_length(ys, zs); match zs { nil => {} cons(z0, zs0) => {} } }
        cons(x0, xs0) => {
            is_perm_remove(ys, zs, x0);
            is_perm_trans(xs0, remove(x0, ys), remove(x0, zs));
        }
    }
}

lem is_perm_cons_r<T>(ys: list<T>, x: T, ws: list<T>)
    req is_perm(remove(x, ys), ws) == true &*& contains(ys, x) == true;
    ens is_perm(ys, cons(x, ws)) == true;
{
    match ys {
        nil => {}
        cons(y0, ys0) => {
            if y0 == x {
            } else {
                is_perm_cons_r(ys0, x, remove(y0, ws));
            }
        }
    }
}

lem is_perm_sym<T>(xs: list<T>, ys: list<T>)
    req is_perm(xs, ys) == true;
    ens is_perm(ys, xs) == true;
{
    match xs {
        nil => { match ys { nil => {} cons(y0, ys0) => {} } }
        cons(x0, xs0) => {
            is_perm_sym(xs0, remove(x0, ys));
            is_perm_cons_r(ys, x0, xs0);
        }
    }
}

lem is_perm_cons<T>(x: T, xs: list<T>, ys: list<T>)
    req is_perm(xs, ys) == true;
    ens is_perm(cons(x, xs), cons(x, ys)) == true;
{
}

lem is_perm_swap_head<T>(a: T, b: T, l: list<T>)
    req true;
    ens is_perm(cons(a, cons(b, l)), cons(b, cons(a, l))) == true;
{
    is_perm_refl(cons(b, l));
    is_perm_refl(l);
}

lem is_perm_update_nth<T>(i: i32, x: T, ws: list<T>)
    req 0 <= i &*& i < length(ws);
    ens is_perm(cons(nth(i, ws), update_nth(i, x, ws)), cons(x, ws)) == true;
{
    match ws {
        nil => {}
        cons(w, ws0) => {
            if i == 0 {
                is_perm_swap_head(w, x, ws0);
            } else {
                is_perm_update_nth(i - 1, x, ws0);
                let a = nth(i - 1, ws0);
                let u = update_nth(i - 1, x, ws0);
                is_perm_swap_head(a, w, u);
                is_perm_cons(w, cons(a, u), cons(x, ws0));
                is_perm_trans(cons(a, cons(w, u)), cons(w, cons(a, u)), cons(w, cons(x, ws0)));
                is_perm_swap_head(w, x, ws0);
                is_perm_trans(cons(a, cons(w, u)), cons(w, cons(x, ws0)), cons(x, cons(w, ws0)));
            }
        }
    }
}

// Swapping two positions is a permutation.
lem is_perm_swap<T>(i: i32, j: i32, vs: list<T>)
    req 0 <= i &*& i < length(vs) &*& 0 <= j &*& j < length(vs);
    ens is_perm(update_nth(i, nth(j, vs), update_nth(j, nth(i, vs), vs)), vs) == true;
{
    if i == j {
        update_nth_nth(i, vs);
        update_nth_update_nth_same(i, nth(i, vs), nth(i, vs), vs);
        is_perm_refl(vs);
    } else {
        let ws = update_nth(j, nth(i, vs), vs);
        update_nth_length(j, nth(i, vs), vs);
        nth_update_nth_other(j, i, nth(i, vs), vs);
        is_perm_update_nth(i, nth(j, vs), ws);
        // cons(vi, final) ~ cons(vj, ws)
        is_perm_update_nth(j, nth(i, vs), vs);
        // cons(vj, ws) ~ cons(vi, vs)
        is_perm_trans(cons(nth(i, vs), update_nth(i, nth(j, vs), ws)), cons(nth(j, vs), ws), cons(nth(i, vs), vs));
    }
}

// One more swap on top of a permutation of `vs0`.
lem perm_step<T>(i: i32, j: i32, l: list<T>, vs0: list<T>)
    req is_perm(l, vs0) == true &*& 0 <= i &*& i < length(l) &*& 0 <= j &*& j < length(l);
    ens is_perm(update_nth(i, nth(j, l), update_nth(j, nth(i, l), l)), vs0) == true;
{
    is_perm_swap(i, j, l);
    is_perm_trans(update_nth(i, nth(j, l), update_nth(j, nth(i, l), l)), l, vs0);
}

lem foreach_unremove<T>(x: T, xs: list<T>, p: pred(T))
    req foreach(remove(x, xs), p) &*& p(x) &*& contains(xs, x) == true;
    ens foreach(xs, p);
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if x0 == x {
                close foreach(xs, p);
            } else {
                open foreach(remove(x, xs), p);
                foreach_unremove(x, xs0, p);
                close foreach(xs, p);
            }
        }
    }
}

lem foreach_perm<T>(xs: list<T>, ys: list<T>)
    req foreach(xs, ?p) &*& is_perm(xs, ys) == true;
    ens foreach(ys, p);
{
    match xs {
        nil => { open foreach(xs, p); match ys { nil => { close foreach(ys, p); } cons(y0, ys0) => {} } }
        cons(x0, xs0) => {
            open foreach(xs, p);
            foreach_perm(xs0, remove(x0, ys));
            foreach_unremove(x0, ys, p);
        }
    }
}

// ----- arithmetic -----

lem mul_pos(a: i32, b: i32)
    req 0 < a &*& 0 < b;
    ens 0 < a * b &*& b <= a * b;
{
    mul_mono_l(1, a, b);
}

// `p + i == p` (as element pointers) with `i != 0`: the element type is zero-sized.
lem ptr_add_eq_zst<T>(p: *T, i: i32, q: *T)
    req p + i == p &*& i != 0 &*& [?f](*q |-> ?v);
    ens std::mem::size_of::<T>() == 0 &*& [f](*q |-> v);
{
    points_to_limits(q);
    let s = std::mem::size_of::<T>();
    if s != 0 {
        assert (p as pointer).address + i * s == (p as pointer).address;
        if i > 0 { mul_pos(i, s); } else { mul_pos(-i, s); }
    }
}

lem array_size_nonneg<T>(p: *T)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 < n;
    ens [f]array::<T>(p, n, vs) &*& 0 <= std::mem::size_of::<T>();
{
    open array::<T>(p, n, vs);
    points_to_limits(p);
    close [f]array::<T>(p, n, vs);
}

lem ptr_add_inj<T>(p: *T, i: i32, j: i32)
    req p + i == p + j &*& std::mem::size_of::<T>() > 0;
    ens i == j;
{
    let s = std::mem::size_of::<T>();
    if i != j {
        assert (p as pointer).address + i * s == (p as pointer).address + j * s;
        if i > j { mul_pos(i - j, s); } else { mul_pos(j - i, s); }
    }
}

// ----- small arrays -----

lem array4_open<T>(p: *T)
    req [?f]array::<T>(p, 4, ?vs);
    ens [f](*p |-> nth(0, vs)) &*& [f](*(p + 1) |-> nth(1, vs)) &*& [f](*(p + 2) |-> nth(2, vs)) &*& [f](*(p + 3) |-> nth(3, vs)) &*&
        [f]array::<T>(p + 4, 0, nil) &*& vs == [nth(0, vs), nth(1, vs), nth(2, vs), nth(3, vs)];
{
    open array::<T>(p, 4, vs);
    open array::<T>(p + 1, 3, _);
    open array::<T>(p + 2, 2, _);
    open array::<T>(p + 3, 1, _);
    open array::<T>(p + 4, 0, _);
    close [f]array::<T>(p + 4, 0, nil);
}

lem array4_close<T>(p: *T)
    req [?f](*p |-> ?v0) &*& [f](*(p + 1) |-> ?v1) &*& [f](*(p + 2) |-> ?v2) &*& [f](*(p + 3) |-> ?v3) &*& [f]array::<T>(p + 4, 0, nil);
    ens [f]array::<T>(p, 4, [v0, v1, v2, v3]);
{
    points_to_limits(p);
    points_to_limits(p + 1);
    points_to_limits(p + 2);
    points_to_limits(p + 3);
    close [f]array::<T>(p + 3, 1, [v3]);
    close [f]array::<T>(p + 2, 2, [v2, v3]);
    close [f]array::<T>(p + 1, 3, [v1, v2, v3]);
    close [f]array::<T>(p, 4, [v0, v1, v2, v3]);
}

lem array__4_open<T>(p: *T)
    req array_::<T>(p, 4, ?vs);
    ens (*p |-> _) &*& (*(p + 1) |-> _) &*& (*(p + 2) |-> _) &*& (*(p + 3) |-> _) &*& array_::<T>(p + 4, 0, nil);
{
    open array_::<T>(p, 4, vs);
    open array_::<T>(p + 1, 3, _);
    open array_::<T>(p + 2, 2, _);
    open array_::<T>(p + 3, 1, _);
    open array_::<T>(p + 4, 0, _);
    close array_::<T>(p + 4, 0, nil);
}

// A one-element array at `p` from its points-to chunk, and back.
lem array1_close<T>(p: *T)
    req [?f](*p |-> ?v);
    ens [f]array::<T>(p, 1, [v]);
{
    points_to_limits(p);
    close [f]array::<T>(p + 1, 0, nil);
    close [f]array::<T>(p, 1, [v]);
}

lem array1_open<T>(p: *T)
    req [?f]array::<T>(p, 1, ?vs);
    ens [f](*p |-> head(vs)) &*& vs == [head(vs)];
{
    open array::<T>(p, 1, vs);
    open array::<T>(p + 1, 0, _);
}

lem array_1_close<T>(p: *T)
    req *p |-> _;
    ens array_::<T>(p, 1, _);
{
    points_to__limits(p);
    close array_::<T>(p + 1, 0, nil);
    close array_::<T>(p, 1, _);
}

// ----- zero-sized types -----

// Any two values of a zero-sized type are equal (both are `of_u8s_` of the empty byte list).
lem zst_values_equal<T>(p: *T, q: *T)
    req [?f1](*p |-> ?v1) &*& [?f2](*q |-> ?v2) &*& std::mem::size_of::<T>() == 0;
    ens [f1](*p |-> v1) &*& [f2](*q |-> v2) &*& v1 == v2;
{
    to_u8s_(p);
    to_u8s_(q);
    assert [f1](p as *u8)[..0] |-?-> ?bs1;
    assert [f2](q as *u8)[..0] |-?-> ?bs2;
    match bs1 { nil => {} cons(b1, bs10) => {} }
    match bs2 { nil => {} cons(b2, bs20) => {} }
    from_u8s_(p);
    from_u8s_(q);
    close [f1]points_to::<T>(p, v1);
    close [f2]points_to::<T>(q, v2);
}

// ----- array helpers, part 2 -----

// `array_join` with explicit counts (so that the right chunks are picked when `T` is zero-sized and
// several arrays start at the same address).
lem array_join_n<T>(p: *T, c1: i32, c2: i32)
    req [?f]array::<T>(p, c1, ?vs1) &*& [f]array::<T>(p + c1, c2, ?vs2);
    ens [f]array::<T>(p, c1 + c2, append(vs1, vs2));
{
    open array::<T>(p, c1, vs1);
    if c1 == 0 {
    } else {
        array_join_n(p + 1, c1 - 1, c2);
        close [f]array::<T>(p, c1 + c2, append(vs1, vs2));
    }
}

lem take_take<T>(m: i32, n: i32, xs: list<T>)
    req 0 <= m &*& m <= n;
    ens take(m, take(n, xs)) == take(m, xs);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if m != 0 { take_take(m - 1, n - 1, xs0); } }
    }
}

lem array_split_last<T>(p: *T, m: i32)
    req [?f]array::<T>(p, m + 1, ?vs) &*& 0 <= m;
    ens [f]array::<T>(p, m, take(m, vs)) &*& [f](*(p + m) |-> nth(m, vs)) &*& [f]array::<T>(p + m + 1, 0, nil) &*& vs == append(take(m, vs), [nth(m, vs)]);
{
    array_split(p, m);
    drop_n_plus_one(m, vs);
    open array::<T>(p + m, 1, _);
}

lem array_join_last<T>(p: *T, m: i32)
    req [?f]array::<T>(p, m, ?xs) &*& [f](*(p + m) |-> ?x) &*& [f]array::<T>(p + m + 1, 0, nil);
    ens [f]array::<T>(p, m + 1, append(xs, [x]));
{
    close [f]array::<T>(p + m, 1, [x]);
    array_join(p);
}
// ----- pointer limits inside arrays -----

lem array_ptr_within_limits<T>(p: *T, k: i32)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 <= k &*& k <= n;
    ens [f]array::<T>(p, n, vs) &*& pointer_within_limits(p + k) == true;
{
    array_split(p, k);
    array_join_n(p, k, n - k);
}

lem array__split_n<T>(p: *T, k: i32)
    req [?f]array_::<T>(p, ?n, ?vs) &*& 0 <= k &*& k <= n;
    ens [f]array_::<T>(p, k, take(k, vs)) &*& [f]array_::<T>(p + k, n - k, drop(k, vs));
{
    array__split(p, k);
}

lem array__join_n<T>(p: *T, c1: i32, c2: i32)
    req [?f]array_::<T>(p, c1, ?vs1) &*& [f]array_::<T>(p + c1, c2, ?vs2);
    ens [f]array_::<T>(p, c1 + c2, append(vs1, vs2));
{
    open array_::<T>(p, c1, vs1);
    if c1 == 0 {
    } else {
        array__join_n(p + 1, c1 - 1, c2);
        close [f]array_::<T>(p, c1 + c2, append(vs1, vs2));
    }
}

lem array__ptr_within_limits<T>(p: *T, k: i32)
    req [?f]array_::<T>(p, ?n, ?vs) &*& 0 <= k &*& k <= n;
    ens [f]array_::<T>(p, n, vs) &*& pointer_within_limits(p + k) == true;
{
    array__split(p, k);
    array__join_n(p, k, n - k);
}

// `p + i < p + j` (by address): the element type is not zero-sized and `i < j`.
lem ptr_lt_index<T>(p: *T, i: i32, j: i32)
    req (p + i) < (p + j) &*& 0 <= std::mem::size_of::<T>();
    ens 0 < std::mem::size_of::<T>() &*& i < j;
{
    let s = std::mem::size_of::<T>();
    if s == 0 {
    } else if i >= j {
        mul_mono_l(j, i, s);
    }
}

// ----- wrapping pointer arithmetic (see `ptr_wrapping_offset` in the STD WRAPPERS block) -----

lem pwo_no_wrap<T>(p: *T, n: i32)
    req 0 <= (p as pointer).address + n * std::mem::size_of::<T>() &*& (p as pointer).address + n * std::mem::size_of::<T>() <= usize::MAX;
    ens ptr_wrapping_offset(p, n) == p + n;
{
}

lem pwo_roundtrip<T>(p: *T)
    req 0 <= (p as pointer).address &*& (p as pointer).address <= usize::MAX &*&
        0 <= std::mem::size_of::<T>() &*& std::mem::size_of::<T>() <= isize::MAX;
    ens ptr_wrapping_offset(ptr_wrapping_offset(p, -1), 1) == p;
{
}

@*/

/*@

// ===== Proof library: sorting (not trusted: every lemma below is proven) =====

// Facts about the insertion position `j` of `x` into `xs` found by `insert_tail` (under a well-behaved comparator).
pred ins_facts<T>(m: bool, order: fix(T, T, bool), x: T, xs: list<T>, j: i32) =
    0 <= j &*& j < length(xs) &*&
    (!m || ((j == 0 || !apply_lt(order, x, nth(j - 1, xs))) && apply_lt(order, x, nth(j, xs)))) == true;

// ----- derived order facts (from the three comparator-model axioms) -----

lem lt_asym<T, F>(f0: F, a: T, b: T)
    req is_less_models::<T, F>(f0) == true &*& apply_lt(is_less_model_of::<T, F>(f0), a, b) == true;
    ens !apply_lt(is_less_model_of::<T, F>(f0), b, a);
{
    if apply_lt(is_less_model_of::<T, F>(f0), b, a) {
        is_less_transitive::<T, F>(f0, a, b, a);
        is_less_irreflexive::<T, F>(f0, a);
    }
}

// Negative transitivity: `x <= y` and `y <= z` (as `!lt(y, x)`, `!lt(z, y)`) give `x <= z`.
lem lt_neg_trans<T, F>(f0: F, x: T, y: T, z: T)
    req is_less_models::<T, F>(f0) == true &*&
        !apply_lt(is_less_model_of::<T, F>(f0), y, x) && !apply_lt(is_less_model_of::<T, F>(f0), z, y);
    ens !apply_lt(is_less_model_of::<T, F>(f0), z, x);
{
    let lt = is_less_model_of::<T, F>(f0);
    if apply_lt(lt, z, x) {
        if apply_lt(lt, y, z) {
            is_less_transitive::<T, F>(f0, y, z, x);
        } else if apply_lt(lt, x, y) {
            is_less_transitive::<T, F>(f0, z, x, y);
        } else {
            is_less_incomparable_transitive::<T, F>(f0, x, y, z);
        }
    }
}

fix all_eq<T>(xs: list<T>, v: T) -> bool {
    match xs { nil => true, cons(x, xs0) => x == v && all_eq(xs0, v) }
}

lem zst_array_all_eq<T>(p: *T, n: i32, w: *T)
    req [?q]array::<T>(p, n, ?vs) &*& [?r](*w |-> ?v) &*& std::mem::size_of::<T>() == 0;
    ens [q]array::<T>(p, n, vs) &*& [r](*w |-> v) &*& all_eq(vs, v) == true;
{
    open array::<T>(p, n, vs);
    if n != 0 {
        zst_values_equal(p, w);
        zst_array_all_eq(p + 1, n - 1, w);
    }
    close [q]array::<T>(p, n, vs);
}

lem all_eq_sorted<T, F>(f0: F, xs: list<T>, v: T)
    req all_eq(xs, v) == true &*& is_less_models::<T, F>(f0) == true;
    ens sorted_by(is_less_model_of::<T, F>(f0), xs) == true;
{
    match xs {
        nil => {}
        cons(x, xs0) => {
            is_less_irreflexive::<T, F>(f0, v);
            all_eq_sorted::<T, F>(f0, xs0, v);
            match xs0 { nil => {} cons(y, ys) => {} }
        }
    }
}

// Under a well-behaved comparator, any list of values of a zero-sized type is sorted (all its values are
// equal, and the order is irreflexive).
lem zst_array_sorted<T, F>(f0: F, p: *T, n: i32)
    req [?q]array::<T>(p, n, ?vs) &*& std::mem::size_of::<T>() == 0 &*& is_less_models::<T, F>(f0) == true;
    ens [q]array::<T>(p, n, vs) &*& sorted_by(is_less_model_of::<T, F>(f0), vs) == true;
{
    open array::<T>(p, n, vs);
    if n != 0 {
        zst_array_all_eq(p + 1, n - 1, p);
        all_eq_sorted::<T, F>(f0, vs, head(vs));
    }
    close [q]array::<T>(p, n, vs);
}

fix insert_at<T>(j: i32, x: T, xs: list<T>) -> list<T> { append(take(j, xs), cons(x, drop(j, xs))) }

lem insert_at_length<T>(j: i32, x: T, xs: list<T>)
    req 0 <= j &*& j <= length(xs);
    ens length(insert_at(j, x, xs)) == length(xs) + 1;
{
}

lem is_perm_insert_at_cons<T>(j: i32, x: T, xs: list<T>)
    req 0 <= j &*& j <= length(xs);
    ens is_perm(insert_at(j, x, xs), cons(x, xs)) == true;
{
    match xs {
        nil => { is_perm_refl(cons(x, xs)); }
        cons(x0, xs0) => {
            if j == 0 {
                is_perm_refl(cons(x, xs));
            } else {
                is_perm_insert_at_cons(j - 1, x, xs0);
                // insert_at(j, x, xs) == cons(x0, insert_at(j - 1, x, xs0))
                is_perm_cons(x0, insert_at(j - 1, x, xs0), cons(x, xs0));
                is_perm_swap_head(x0, x, xs0);
                is_perm_trans(cons(x0, insert_at(j - 1, x, xs0)), cons(x0, cons(x, xs0)), cons(x, xs));
            }
        }
    }
}

lem is_perm_cons_snoc<T>(x: T, xs: list<T>)
    req true;
    ens is_perm(cons(x, xs), append(xs, [x])) == true;
{
    match xs {
        nil => { is_perm_refl([x]); }
        cons(x0, xs0) => {
            is_perm_cons_snoc(x, xs0);
            is_perm_swap_head(x, x0, xs0);
            is_perm_cons(x0, cons(x, xs0), append(xs0, [x]));
            is_perm_trans(cons(x, xs), cons(x0, cons(x, xs0)), append(xs, [x]));
        }
    }
}

lem contains_append_l<T>(x: T, xs: list<T>, ys: list<T>)
    req contains(xs, x) == true;
    ens contains(append(xs, ys), x) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != x { contains_append_l(x, xs0, ys); } }
    }
}

lem remove_append_l<T>(x: T, xs: list<T>, ys: list<T>)
    req contains(xs, x) == true;
    ens remove(x, append(xs, ys)) == append(remove(x, xs), ys);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if x0 != x { remove_append_l(x, xs0, ys); } }
    }
}

lem is_perm_append_l<T>(xs: list<T>, xs1: list<T>, ys: list<T>)
    req is_perm(xs1, xs) == true;
    ens is_perm(append(xs1, ys), append(xs, ys)) == true;
{
    match xs1 {
        nil => { match xs { nil => {} cons(x0, xs0) => {} } is_perm_refl(ys); }
        cons(x0, xs10) => {
            // contains(xs, x0), is_perm(xs10, remove(x0, xs))
            is_perm_append_l(remove(x0, xs), xs10, ys);
            contains_append_l(x0, xs, ys);
            remove_append_l(x0, xs, ys);
        }
    }
}

lem sorted_insert_at<T>(order: fix(T, T, bool), j: i32, x: T, xs: list<T>)
    req sorted_by(order, xs) == true &*& 0 <= j &*& j <= length(xs) &*&
        (j == 0 || !apply_lt(order, x, nth(j - 1, xs))) &*& (j == length(xs) || !apply_lt(order, nth(j, xs), x));
    ens sorted_by(order, insert_at(j, x, xs)) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if j == 0 {
            } else {
                sorted_insert_at(order, j - 1, x, xs0);
                if j == 1 {
                } else {
                    match xs0 { nil => {} cons(x1, xs1) => {} }
                }
            }
        }
    }
}

@*/

/*@

// ===== Proof library: merging (not trusted: every lemma below is proven) =====

// ----- order facts on sorted lists -----

lem le_lt_trans<T, F>(f0: F, a: T, b: T, c: T)
    req is_less_models::<T, F>(f0) == true &*&
        !apply_lt(is_less_model_of::<T, F>(f0), b, a) && apply_lt(is_less_model_of::<T, F>(f0), b, c);
    ens apply_lt(is_less_model_of::<T, F>(f0), a, c) == true;
{
    if !apply_lt(is_less_model_of::<T, F>(f0), a, c) {
        lt_neg_trans::<T, F>(f0, c, a, b);
    }
}

lem lt_le_trans<T, F>(f0: F, a: T, b: T, c: T)
    req is_less_models::<T, F>(f0) == true &*&
        apply_lt(is_less_model_of::<T, F>(f0), a, b) && !apply_lt(is_less_model_of::<T, F>(f0), c, b);
    ens apply_lt(is_less_model_of::<T, F>(f0), a, c) == true;
{
    if !apply_lt(is_less_model_of::<T, F>(f0), a, c) {
        lt_neg_trans::<T, F>(f0, b, c, a);
    }
}

lem sorted_tail<T>(order: fix(T, T, bool), x: T, xs: list<T>)
    req sorted_by(order, cons(x, xs)) == true;
    ens sorted_by(order, xs) == true;
{
}

lem sorted_adj<T>(order: fix(T, T, bool), xs: list<T>, k: i32)
    req sorted_by(order, xs) == true &*& 0 <= k &*& k + 1 < length(xs);
    ens !apply_lt(order, nth(k + 1, xs), nth(k, xs));
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            match xs0 { nil => {} cons(x1, xs1) => {} }
            if k != 0 { sorted_adj(order, xs0, k - 1); }
        }
    }
}

// In a sorted list, a later element is not less than an earlier one.
lem sorted_nth_le<T, F>(f0: F, xs: list<T>, a: i32, b: i32)
    req is_less_models::<T, F>(f0) == true &*& sorted_by(is_less_model_of::<T, F>(f0), xs) == true &*&
        0 <= a &*& a <= b &*& b < length(xs);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(b, xs), nth(a, xs));
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            if a == 0 {
                if b == 0 {
                    is_less_irreflexive::<T, F>(f0, x0);
                } else {
                    sorted_nth_le::<T, F>(f0, xs0, 0, b - 1);
                    match xs0 { nil => {} cons(x1, xs1) => {} }
                    lt_neg_trans::<T, F>(f0, x0, nth(0, xs0), nth(b - 1, xs0));
                }
            } else {
                sorted_nth_le::<T, F>(f0, xs0, a - 1, b - 1);
            }
        }
    }
}

// ----- cuts of a stable merge of `l` and `r` -----

// `(i, j)`: the first `i` elements of `l` and the first `j` of `r` are exactly the first `i + j` elements
// of the stable merge of `l` and `r` (ties: elements of `l` first).
fix valid_cut<T>(order: fix(T, T, bool), l: list<T>, r: list<T>, i: i32, j: i32) -> bool {
    0 <= i && i <= length(l) && 0 <= j && j <= length(r) &&
    (i == 0 || j == length(r) || !apply_lt(order, nth(j, r), nth(i - 1, l))) &&
    (j == 0 || i == length(l) || apply_lt(order, nth(j - 1, r), nth(i, l)))
}

// A forward step (`merge_up`) from a valid cut gives a valid cut.
lem cut_step_fwd<T, F>(f0: F, l: list<T>, r: list<T>, i: i32, j: i32)
    req is_less_models::<T, F>(f0) == true &*& sorted_by(is_less_model_of::<T, F>(f0), l) == true &*&
        sorted_by(is_less_model_of::<T, F>(f0), r) == true &*&
        valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j) == true &*& i < length(l) &*& j < length(r);
    ens if !apply_lt(is_less_model_of::<T, F>(f0), nth(j, r), nth(i, l)) {
            valid_cut(is_less_model_of::<T, F>(f0), l, r, i + 1, j) == true
        } else {
            valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j + 1) == true
        };
{
    let lt = is_less_model_of::<T, F>(f0);
    if !apply_lt(lt, nth(j, r), nth(i, l)) {
        if j != 0 && i + 1 != length(l) {
            sorted_adj(lt, l, i);
            lt_le_trans::<T, F>(f0, nth(j - 1, r), nth(i, l), nth(i + 1, l));
        }
    } else {
        if i != 0 && j + 1 != length(r) {
            sorted_adj(lt, r, j);
            lt_neg_trans::<T, F>(f0, nth(i - 1, l), nth(j, r), nth(j + 1, r));
        }
    }
}

// A backward step (`merge_down`) from a valid cut with both sides nonempty gives a valid cut.
lem cut_step_bwd<T, F>(f0: F, l: list<T>, r: list<T>, i: i32, j: i32)
    req is_less_models::<T, F>(f0) == true &*& sorted_by(is_less_model_of::<T, F>(f0), l) == true &*&
        sorted_by(is_less_model_of::<T, F>(f0), r) == true &*&
        valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j) == true &*& 1 <= i &*& 1 <= j;
    ens if !apply_lt(is_less_model_of::<T, F>(f0), nth(j - 1, r), nth(i - 1, l)) {
            valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j - 1) == true
        } else {
            valid_cut(is_less_model_of::<T, F>(f0), l, r, i - 1, j) == true
        };
{
    let lt = is_less_model_of::<T, F>(f0);
    if !apply_lt(lt, nth(j - 1, r), nth(i - 1, l)) {
        if j - 1 != 0 && i != length(l) {
            sorted_adj(lt, r, j - 2);
            le_lt_trans::<T, F>(f0, nth(j - 2, r), nth(j - 1, r), nth(i, l));
        }
    } else {
        if i - 1 != 0 && j != length(r) {
            sorted_adj(lt, l, i - 2);
            lt_neg_trans::<T, F>(f0, nth(i - 2, l), nth(i - 1, l), nth(j, r));
        }
    }
}

// Valid cuts are ordered by their sizes.
lem cut_mono<T, F>(f0: F, l: list<T>, r: list<T>, i: i32, j: i32, i2: i32, j2: i32)
    req is_less_models::<T, F>(f0) == true &*& sorted_by(is_less_model_of::<T, F>(f0), l) == true &*&
        sorted_by(is_less_model_of::<T, F>(f0), r) == true &*&
        valid_cut(is_less_model_of::<T, F>(f0), l, r, i, j) == true &*&
        valid_cut(is_less_model_of::<T, F>(f0), l, r, i2, j2) == true &*& i + j <= i2 + j2;
    ens i <= i2 &*& j <= j2;
{
    let lt = is_less_model_of::<T, F>(f0);
    if i > i2 {
        // j < j2: R[j2-1] < L[i2] <= L[i-1] <= R[j] <= R[j2-1]
        sorted_nth_le::<T, F>(f0, l, i2, i - 1);
        sorted_nth_le::<T, F>(f0, r, j, j2 - 1);
        lt_le_trans::<T, F>(f0, nth(j2 - 1, r), nth(i2, l), nth(i - 1, l));
        lt_le_trans::<T, F>(f0, nth(j2 - 1, r), nth(i - 1, l), nth(j, r));
        lt_le_trans::<T, F>(f0, nth(j2 - 1, r), nth(j, r), nth(j2 - 1, r));
        is_less_irreflexive::<T, F>(f0, nth(j2 - 1, r));
    } else if j > j2 {
        // i < i2: R[j-1] < L[i] <= L[i2-1] <= R[j2] <= R[j-1]
        sorted_nth_le::<T, F>(f0, l, i, i2 - 1);
        sorted_nth_le::<T, F>(f0, r, j2, j - 1);
        lt_le_trans::<T, F>(f0, nth(j - 1, r), nth(i, l), nth(i2 - 1, l));
        lt_le_trans::<T, F>(f0, nth(j - 1, r), nth(i2 - 1, l), nth(j2, r));
        lt_le_trans::<T, F>(f0, nth(j - 1, r), nth(j2, r), nth(j - 1, r));
        is_less_irreflexive::<T, F>(f0, nth(j - 1, r));
    }
}

// ----- runs written by the merge -----

fix last<T>(xs: list<T>) -> T {
    match xs { nil => default_value, cons(x, xs0) => if xs0 == nil { x } else { last(xs0) } }
}

lem last_snoc<T>(xs: list<T>, x: T)
    req true;
    ens last(append(xs, [x])) == x;
{
    match xs { nil => {} cons(x0, xs0) => { last_snoc(xs0, x); match xs0 { nil => {} cons(y, ys) => {} } } }
}

lem sorted_snoc<T>(order: fix(T, T, bool), xs: list<T>, x: T)
    req sorted_by(order, xs) == true &*& (xs == nil || !apply_lt(order, x, last(xs)));
    ens sorted_by(order, append(xs, [x])) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            sorted_snoc(order, xs0, x);
            match xs0 { nil => {} cons(x1, xs1) => {} }
        }
    }
}

lem sorted_append<T>(order: fix(T, T, bool), xs: list<T>, ys: list<T>)
    req sorted_by(order, xs) == true &*& sorted_by(order, ys) == true &*&
        (xs == nil || ys == nil || !apply_lt(order, head(ys), last(xs)));
    ens sorted_by(order, append(xs, ys)) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            sorted_append(order, xs0, ys);
            match xs0 { nil => { match ys { nil => {} cons(y0, ys0) => {} } } cons(x1, xs1) => {} }
        }
    }
}

// ----- permutation algebra -----

lem is_perm_cons_middle<T>(y: T, c: list<T>, d: list<T>)
    req true;
    ens is_perm(cons(y, append(c, d)), append(c, cons(y, d))) == true;
{
    match c {
        nil => { is_perm_refl(cons(y, d)); }
        cons(c0, c1) => {
            is_perm_cons_middle(y, c1, d);
            is_perm_swap_head(y, c0, append(c1, d));
            is_perm_cons(c0, cons(y, append(c1, d)), append(c1, cons(y, d)));
            is_perm_trans(cons(y, append(c, d)), cons(c0, cons(y, append(c1, d))), append(c, cons(y, d)));
        }
    }
}

lem is_perm_append_r<T>(xs: list<T>, ys: list<T>, ys1: list<T>)
    req is_perm(ys1, ys) == true;
    ens is_perm(append(xs, ys1), append(xs, ys)) == true;
{
    match xs {
        nil => {}
        cons(x0, xs0) => {
            is_perm_append_r(xs0, ys, ys1);
            is_perm_cons(x0, append(xs0, ys1), append(xs0, ys));
        }
    }
}

lem is_perm_append_both<T>(a1: list<T>, a: list<T>, b1: list<T>, b: list<T>)
    req is_perm(a1, a) == true &*& is_perm(b1, b) == true;
    ens is_perm(append(a1, b1), append(a, b)) == true;
{
    is_perm_append_l(a, a1, b1);
    is_perm_append_r(a, b, b1);
    is_perm_trans(append(a1, b1), append(a, b1), append(a, b));
}

lem is_perm_append_comm<T>(xs: list<T>, ys: list<T>)
    req true;
    ens is_perm(append(xs, ys), append(ys, xs)) == true;
{
    match xs {
        nil => { is_perm_refl(ys); }
        cons(x0, xs0) => {
            is_perm_append_comm(xs0, ys);
            is_perm_cons(x0, append(xs0, ys), append(ys, xs0));
            is_perm_cons_middle(x0, ys, xs0);
            is_perm_trans(append(xs, ys), cons(x0, append(ys, xs0)), append(ys, xs));
        }
    }
}

// (a ++ b) ++ (c ++ d)  ~  (a ++ c) ++ (b ++ d)
lem is_perm_middle_swap<T>(a: list<T>, b: list<T>, c: list<T>, d: list<T>)
    req true;
    ens is_perm(append(append(a, b), append(c, d)), append(append(a, c), append(b, d))) == true;
{
    append_assoc(a, b, append(c, d));
    append_assoc(b, c, d);
    is_perm_append_comm(b, c);
    is_perm_refl(d);
    is_perm_append_both(append(b, c), append(c, b), d, d);
    append_assoc(c, b, d);
    is_perm_append_r(a, append(c, append(b, d)), append(b, append(c, d)));
    append_assoc(a, c, append(b, d));
}

lem is_perm_snoc_middle<T>(f: list<T>, a: list<T>, b: list<T>, x: T)
    req is_perm(f, append(a, b)) == true;
    ens is_perm(append(f, [x]), append(append(a, [x]), b)) == true;
{
    is_perm_refl([x]);
    is_perm_append_both(f, append(a, b), [x], [x]);
    append_assoc(a, b, [x]);
    is_perm_append_comm(b, [x]);
    is_perm_append_r(a, cons(x, b), append(b, [x]));
    is_perm_trans(append(f, [x]), append(a, append(b, [x])), append(a, cons(x, b)));
    append_assoc(a, [x], b);
}

lem is_perm_snoc_right<T>(f: list<T>, a: list<T>, b: list<T>, y: T)
    req is_perm(f, append(a, b)) == true;
    ens is_perm(append(f, [y]), append(a, append(b, [y]))) == true;
{
    is_perm_refl([y]);
    is_perm_append_both(f, append(a, b), [y], [y]);
    append_assoc(a, b, [y]);
}

lem is_perm_cons_right<T>(bw: list<T>, c: list<T>, d: list<T>, y: T)
    req is_perm(bw, append(c, d)) == true;
    ens is_perm(cons(y, bw), append(c, cons(y, d))) == true;
{
    is_perm_cons(y, bw, append(c, d));
    is_perm_cons_middle(y, c, d);
    is_perm_trans(cons(y, bw), cons(y, append(c, d)), append(c, cons(y, d)));
}

lem take_plus_one<T>(n: i32, xs: list<T>)
    req 0 <= n &*& n < length(xs);
    ens take(n + 1, xs) == append(take(n, xs), [nth(n, xs)]);
{
    match xs {
        nil => {}
        cons(x0, xs0) => { if n != 0 { take_plus_one(n - 1, xs0); } }
    }
}

lem all_eq_perm<T>(xs: list<T>, ys: list<T>, v: T)
    req all_eq(xs, v) == true &*& all_eq(ys, v) == true &*& length(xs) == length(ys);
    ens is_perm(xs, ys) == true;
{
    match xs {
        nil => { match ys { nil => {} cons(y0, ys0) => {} } }
        cons(x0, xs0) => {
            match ys { nil => {} cons(y0, ys0) => { all_eq_perm(xs0, ys0, v); } }
        }
    }
}

lem all_eq_append<T>(xs: list<T>, ys: list<T>, v: T)
    req all_eq(xs, v) == true &*& all_eq(ys, v) == true;
    ens all_eq(append(xs, ys), v) == true;
{
    match xs { nil => {} cons(x0, xs0) => { all_eq_append(xs0, ys, v); } }
}

// With a zero-sized `T`, the elements of `p[..n]` all equal the first element of `w[..m]`.
lem zst_arrays_all_eq<T>(p: *T, w: *T)
    req [?q]array::<T>(p, ?n, ?xs) &*& [?r]array::<T>(w, ?m, ?ys) &*& 0 < m &*& std::mem::size_of::<T>() == 0;
    ens [q]array::<T>(p, n, xs) &*& [r]array::<T>(w, m, ys) &*& all_eq(xs, head(ys)) == true;
{
    open array::<T>(w, m, ys);
    zst_array_all_eq(p, n, w);
    close [r]array::<T>(w, m, ys);
}

lem zst_array_all_eq_self<T>(p: *T)
    req [?q]array::<T>(p, ?n, ?xs) &*& 0 < n &*& std::mem::size_of::<T>() == 0;
    ens [q]array::<T>(p, n, xs) &*& all_eq(xs, head(xs)) == true;
{
    open array::<T>(p, n, xs);
    zst_array_all_eq(p + 1, n - 1, p);
    close [q]array::<T>(p, n, xs);
}

lem array_nonnull_aligned<T>(p: *T)
    req [?f]array::<T>(p, ?n, ?vs) &*& 0 < n;
    ens [f]array::<T>(p, n, vs) &*& p != 0 &*& p as usize % std::mem::align_of::<T>() == 0;
{
    open array::<T>(p, n, vs);
    points_to_limits(p);
    to_u8s_(p);
    from_u8s_(p);
    close [f]points_to::<T>(p, head(vs));
    close [f]array::<T>(p, n, vs);
}

lem sorted_take1<T>(order: fix(T, T, bool), xs: list<T>)
    req true;
    ens sorted_by(order, take(1, xs)) == true;
{
    match xs { nil => {} cons(x0, xs0) => {} }
}

// ----- the scratch regions of `small_sort_general_with_scratch` -----

// `p[..d]`: the first `n` elements are initialized with a permutation `ss` of `take(n, xs)` (sorted if
// `srt`), the rest is uninitialized.
pred sregion<T>(p: *T, d: i32, n: i32, xs: list<T>, srt: bool, order: fix(T, T, bool); ss: list<T>) =
    0 <= n &*& n <= d &*& array::<T>(p, n, ss) &*& array_::<T>(p + n, d - n, _) &*&
    is_perm(ss, take(n, xs)) == true &*& (!srt || sorted_by(order, ss));

lem foreach_MaybeUninit_own<T>(t: thread_id_t, xs: list<std::mem::MaybeUninit<T>>)
    req true;
    ens foreach(xs, own::<std::mem::MaybeUninit<T>>(t));
{
    match xs {
        nil => { close foreach(xs, own::<std::mem::MaybeUninit<T>>(t)); }
        cons(x0, xs0) => {
            foreach_MaybeUninit_own(t, xs0);
            MaybeUninit_own_trivial(t, x0);
            close foreach(xs, own::<std::mem::MaybeUninit<T>>(t));
        }
    }
}

lem array_MaybeUninit_to_array_<T>(p: *std::mem::MaybeUninit<T>)
    req array::<std::mem::MaybeUninit<T>>(p, ?n, ?ms);
    ens array_::<T>(p as *T, n, _);
{
    open array::<std::mem::MaybeUninit<T>>(p, n, ms);
    if n != 0 {
        std::mem::open_MaybeUninit(p);
        array_MaybeUninit_to_array_(p + 1);
        assert (p + 1) as *T == (p as *T) + 1;
        close array_::<T>(p as *T, n, _);
    } else {
        close array_::<T>(p as *T, 0, nil);
    }
}
@*/

/*@

// ===== Proof library: sorting networks (not trusted: every lemma below is proven) =====
//
// 0-1 principle, per compare-exchange step: a threshold `x |-> c < x` maps the smaller and the larger
// of two values to the minimum and maximum of their bits; and the networks sort every 0/1 input
// (checked exhaustively, with every intermediate bit a parameter so that terms stay small).

// One compare-exchange step of a sorting network, as `swap_if_less` performs it.
fix net_step<T>(order: fix(T, T, bool), a: i32, b: i32, vs: list<T>) -> list<T> {
    if apply_lt(order, nth(b, vs), nth(a, vs)) { update_nth(a, nth(b, vs), update_nth(b, nth(a, vs), vs)) } else { vs }
}

inductive bit = bit0 | bit1;
fix bit_of(b: bool) -> bit { if b { bit1 } else { bit0 } }
fix min01(x: bit, y: bit) -> bit { match x { bit0 => bit0, bit1 => y } }
fix max01(x: bit, y: bit) -> bit { match x { bit0 => y, bit1 => bit1 } }

lem net_step_nth<T>(order: fix(T, T, bool), a: i32, b: i32, vs: list<T>, i: i32)
    req 0 <= a &*& a < length(vs) &*& 0 <= b &*& b < length(vs) &*& a != b &*& 0 <= i &*& i < length(vs);
    ens nth(i, net_step(order, a, b, vs)) ==
        if i == a { if apply_lt(order, nth(b, vs), nth(a, vs)) { nth(b, vs) } else { nth(a, vs) } }
        else if i == b { if apply_lt(order, nth(b, vs), nth(a, vs)) { nth(a, vs) } else { nth(b, vs) } }
        else { nth(i, vs) };
{
    if apply_lt(order, nth(b, vs), nth(a, vs)) {
        update_nth_length(b, nth(a, vs), vs);
        if i == a {
            nth_update_nth_same(a, nth(b, vs), update_nth(b, nth(a, vs), vs));
        } else {
            nth_update_nth_other(a, i, nth(b, vs), update_nth(b, nth(a, vs), vs));
            if i == b { nth_update_nth_same(b, nth(a, vs), vs); } else { nth_update_nth_other(b, i, nth(a, vs), vs); }
        }
    }
}

// `ws` is the result of one step on `vs` (held as a dummy fraction `[_]`). A predicate, so that callers
// do not see the list equation (VeriFast
// 26.10's prover blows up on chains of such equations); `step_done_nth` gives one element at a time.
pred step_done<T>(order: fix(T, T, bool), a: i32, b: i32, vs: list<T>, ws: list<T>) = ws == net_step(order, a, b, vs);

lem step_done_nth<T>(order: fix(T, T, bool), a: i32, b: i32, vs: list<T>, ws: list<T>, i: i32)
    req [_]step_done(order, a, b, vs, ws) &*&
        0 <= a &*& a < length(vs) &*& 0 <= b &*& b < length(vs) &*& a != b &*& 0 <= i &*& i < length(vs);
    ens nth(i, ws) ==
        if i == a { if apply_lt(order, nth(b, vs), nth(a, vs)) { nth(b, vs) } else { nth(a, vs) } }
        else if i == b { if apply_lt(order, nth(b, vs), nth(a, vs)) { nth(a, vs) } else { nth(b, vs) } }
        else { nth(i, vs) };
{
    open [_]step_done(order, a, b, vs, ws);
    net_step_nth(order, a, b, vs, i);
}

lem net_step_length<T>(order: fix(T, T, bool), a: i32, b: i32, vs: list<T>)
    req true;
    ens length(net_step(order, a, b, vs)) == length(vs);
{
    update_nth_length(b, nth(a, vs), vs);
    update_nth_length(a, nth(b, vs), update_nth(b, nth(a, vs), vs));
}

// The threshold bits of the smaller and the larger of `x` and `y`.
lem step_bits<T, F>(f0: F, c: T, x: T, y: T)
    req is_less_models::<T, F>(f0) == true;
    ens bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, if apply_lt(is_less_model_of::<T, F>(f0), y, x) { y } else { x })) ==
            min01(bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, x)), bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, y))) &*&
        bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, if apply_lt(is_less_model_of::<T, F>(f0), y, x) { x } else { y })) ==
            max01(bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, x)), bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, y)));
{
    let lt = is_less_model_of::<T, F>(f0);
    if apply_lt(lt, y, x) {
        if apply_lt(lt, c, y) { is_less_transitive::<T, F>(f0, c, y, x); }
    } else {
        if apply_lt(lt, c, x) { lt_le_trans::<T, F>(f0, c, x, y); }
    }
}

lem step_done_length<T>(order: fix(T, T, bool), a: i32, b: i32, vs: list<T>, ws: list<T>)
    req [_]step_done(order, a, b, vs, ws);
    ens length(ws) == length(vs);
{
    open [_]step_done(order, a, b, vs, ws);
    net_step_length(order, a, b, vs);
}

// From a sorted 0/1 output pair `(o_k, o_k+1)` with `o_k+1 = bit_of(b2)`, `!b2`, conclude `!b1` where
// `o_k = bit_of(b1)`.
lem bit_adj(b1: bool, b2: bool)
    req (bit_of(b2) == bit1 || bit_of(b1) == bit0) &*& !b2;
    ens !b1;
{
    if b1 {} else {}
}

// Positions a step does not touch keep their element.
lem step_done_same<T>(order: fix(T, T, bool), a: i32, b: i32, vs: list<T>, ws: list<T>, i: i32)
    req [_]step_done(order, a, b, vs, ws) &*&
        0 <= a &*& a < length(vs) &*& 0 <= b &*& b < length(vs) &*& a != b &*& 0 <= i &*& i < length(vs) &*& i != a &*& i != b;
    ens nth(i, ws) == nth(i, vs);
{
    step_done_nth(order, a, b, vs, ws, i);
}

// The threshold bits at the two positions a step touches (no `if` terms in the postcondition, so that the
// caller's prover does not split cases).
lem step_done_bits<T, F>(f0: F, c: T, a: i32, b: i32, vs: list<T>, ws: list<T>)
    req is_less_models::<T, F>(f0) == true &*& [_]step_done(is_less_model_of::<T, F>(f0), a, b, vs, ws) &*&
        0 <= a &*& a < length(vs) &*& 0 <= b &*& b < length(vs) &*& a != b;
    ens bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, nth(a, ws))) ==
            min01(bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, nth(a, vs))), bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, nth(b, vs)))) &*&
        bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, nth(b, ws))) ==
            max01(bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, nth(a, vs))), bit_of(apply_lt(is_less_model_of::<T, F>(f0), c, nth(b, vs))));
{
    step_done_nth(is_less_model_of::<T, F>(f0), a, b, vs, ws, a);
    step_done_nth(is_less_model_of::<T, F>(f0), a, b, vs, ws, b);
    step_bits::<T, F>(f0, c, nth(a, vs), nth(b, vs));
}

// Network of `sort9_optimal`: every 0/1 input comes out sorted (outputs: the last bit of each position).
lem net9_01(x0: bit, x1: bit, x2: bit, x3: bit, x4: bit, x5: bit, x6: bit, x7: bit, x8: bit, y1_0: bit, y1_3: bit, y2_1: bit, y2_7: bit, y3_2: bit, y3_5: bit, y4_4: bit, y4_8: bit, y5_0: bit, y5_7: bit, y6_2: bit, y6_4: bit, y7_3: bit, y7_8: bit, y8_5: bit, y8_6: bit, y9_0: bit, y9_2: bit, y10_1: bit, y10_3: bit, y11_4: bit, y11_5: bit, y12_7: bit, y12_8: bit, y13_1: bit, y13_4: bit, y14_3: bit, y14_6: bit, y15_5: bit, y15_7: bit, y16_0: bit, y16_1: bit, y17_2: bit, y17_4: bit, y18_3: bit, y18_5: bit, y19_6: bit, y19_8: bit, y20_2: bit, y20_3: bit, y21_4: bit, y21_5: bit, y22_6: bit, y22_7: bit, y23_1: bit, y23_2: bit, y24_3: bit, y24_4: bit, y25_5: bit, y25_6: bit)
    req y1_0 == min01(x0, x3) &*& y1_3 == max01(x0, x3) &*&
        y2_1 == min01(x1, x7) &*& y2_7 == max01(x1, x7) &*&
        y3_2 == min01(x2, x5) &*& y3_5 == max01(x2, x5) &*&
        y4_4 == min01(x4, x8) &*& y4_8 == max01(x4, x8) &*&
        y5_0 == min01(y1_0, y2_7) &*& y5_7 == max01(y1_0, y2_7) &*&
        y6_2 == min01(y3_2, y4_4) &*& y6_4 == max01(y3_2, y4_4) &*&
        y7_3 == min01(y1_3, y4_8) &*& y7_8 == max01(y1_3, y4_8) &*&
        y8_5 == min01(y3_5, x6) &*& y8_6 == max01(y3_5, x6) &*&
        y9_0 == min01(y5_0, y6_2) &*& y9_2 == max01(y5_0, y6_2) &*&
        y10_1 == min01(y2_1, y7_3) &*& y10_3 == max01(y2_1, y7_3) &*&
        y11_4 == min01(y6_4, y8_5) &*& y11_5 == max01(y6_4, y8_5) &*&
        y12_7 == min01(y5_7, y7_8) &*& y12_8 == max01(y5_7, y7_8) &*&
        y13_1 == min01(y10_1, y11_4) &*& y13_4 == max01(y10_1, y11_4) &*&
        y14_3 == min01(y10_3, y8_6) &*& y14_6 == max01(y10_3, y8_6) &*&
        y15_5 == min01(y11_5, y12_7) &*& y15_7 == max01(y11_5, y12_7) &*&
        y16_0 == min01(y9_0, y13_1) &*& y16_1 == max01(y9_0, y13_1) &*&
        y17_2 == min01(y9_2, y13_4) &*& y17_4 == max01(y9_2, y13_4) &*&
        y18_3 == min01(y14_3, y15_5) &*& y18_5 == max01(y14_3, y15_5) &*&
        y19_6 == min01(y14_6, y12_8) &*& y19_8 == max01(y14_6, y12_8) &*&
        y20_2 == min01(y17_2, y18_3) &*& y20_3 == max01(y17_2, y18_3) &*&
        y21_4 == min01(y17_4, y18_5) &*& y21_5 == max01(y17_4, y18_5) &*&
        y22_6 == min01(y19_6, y15_7) &*& y22_7 == max01(y19_6, y15_7) &*&
        y23_1 == min01(y16_1, y20_2) &*& y23_2 == max01(y16_1, y20_2) &*&
        y24_3 == min01(y20_3, y21_4) &*& y24_4 == max01(y20_3, y21_4) &*&
        y25_5 == min01(y21_5, y22_6) &*& y25_6 == max01(y21_5, y22_6);
    ens (y23_1 == bit1 || y16_0 == bit0) &*& (y23_2 == bit1 || y23_1 == bit0) &*& (y24_3 == bit1 || y23_2 == bit0) &*& (y24_4 == bit1 || y24_3 == bit0) &*& (y25_5 == bit1 || y24_4 == bit0) &*& (y25_6 == bit1 || y25_5 == bit0) &*& (y22_7 == bit1 || y25_6 == bit0) &*& (y19_8 == bit1 || y22_7 == bit0);
{
    match x0 { bit0 => {} bit1 => {} }
    match x1 { bit0 => {} bit1 => {} }
    match x2 { bit0 => {} bit1 => {} }
    match x3 { bit0 => {} bit1 => {} }
    match x4 { bit0 => {} bit1 => {} }
    match x5 { bit0 => {} bit1 => {} }
    match x6 { bit0 => {} bit1 => {} }
    match x7 { bit0 => {} bit1 => {} }
    match x8 { bit0 => {} bit1 => {} }
}

lem take9_explicit<T>(xs: list<T>)
    req 9 <= length(xs);
    ens take(9, xs) == [nth(0, xs), nth(1, xs), nth(2, xs), nth(3, xs), nth(4, xs), nth(5, xs), nth(6, xs), nth(7, xs), nth(8, xs)];
{
    drop_n_plus_one(0, xs);
    drop_n_plus_one(1, xs);
    drop_n_plus_one(2, xs);
    drop_n_plus_one(3, xs);
    drop_n_plus_one(4, xs);
    drop_n_plus_one(5, xs);
    drop_n_plus_one(6, xs);
    drop_n_plus_one(7, xs);
    drop_n_plus_one(8, xs);
}

lem sorted9_from_adj<T>(order: fix(T, T, bool), xs: list<T>)
    req 9 <= length(xs) &*& !apply_lt(order, nth(1, xs), nth(0, xs)) &*& !apply_lt(order, nth(2, xs), nth(1, xs)) &*& !apply_lt(order, nth(3, xs), nth(2, xs)) &*& !apply_lt(order, nth(4, xs), nth(3, xs)) &*& !apply_lt(order, nth(5, xs), nth(4, xs)) &*& !apply_lt(order, nth(6, xs), nth(5, xs)) &*& !apply_lt(order, nth(7, xs), nth(6, xs)) &*& !apply_lt(order, nth(8, xs), nth(7, xs));
    ens sorted_by(order, take(9, xs)) == true;
{
    take9_explicit(xs);
}

lem net9_frame<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25);
    ens length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& true &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
{
    let lt = is_less_model_of::<T, F>(f0);
    step_done_length(lt, 0, 3, w0, w1);
    step_done_length(lt, 1, 7, w1, w2);
    step_done_length(lt, 2, 5, w2, w3);
    step_done_length(lt, 4, 8, w3, w4);
    step_done_length(lt, 0, 7, w4, w5);
    step_done_length(lt, 2, 4, w5, w6);
    step_done_length(lt, 3, 8, w6, w7);
    step_done_length(lt, 5, 6, w7, w8);
    step_done_length(lt, 0, 2, w8, w9);
    step_done_length(lt, 1, 3, w9, w10);
    step_done_length(lt, 4, 5, w10, w11);
    step_done_length(lt, 7, 8, w11, w12);
    step_done_length(lt, 1, 4, w12, w13);
    step_done_length(lt, 3, 6, w13, w14);
    step_done_length(lt, 5, 7, w14, w15);
    step_done_length(lt, 0, 1, w15, w16);
    step_done_length(lt, 2, 4, w16, w17);
    step_done_length(lt, 3, 5, w17, w18);
    step_done_length(lt, 6, 8, w18, w19);
    step_done_length(lt, 2, 3, w19, w20);
    step_done_length(lt, 4, 5, w20, w21);
    step_done_length(lt, 6, 7, w21, w22);
    step_done_length(lt, 1, 2, w22, w23);
    step_done_length(lt, 3, 4, w23, w24);
    step_done_length(lt, 5, 6, w24, w25);
    step_done_same(lt, 0, 3, w0, w1, 1);
    step_done_same(lt, 0, 3, w0, w1, 2);
    step_done_same(lt, 0, 3, w0, w1, 4);
    step_done_same(lt, 0, 3, w0, w1, 5);
    step_done_same(lt, 0, 3, w0, w1, 6);
    step_done_same(lt, 0, 3, w0, w1, 7);
    step_done_same(lt, 0, 3, w0, w1, 8);
    step_done_same(lt, 1, 7, w1, w2, 0);
    step_done_same(lt, 1, 7, w1, w2, 2);
    step_done_same(lt, 1, 7, w1, w2, 3);
    step_done_same(lt, 1, 7, w1, w2, 4);
    step_done_same(lt, 1, 7, w1, w2, 5);
    step_done_same(lt, 1, 7, w1, w2, 6);
    step_done_same(lt, 1, 7, w1, w2, 8);
    step_done_same(lt, 2, 5, w2, w3, 0);
    step_done_same(lt, 2, 5, w2, w3, 1);
    step_done_same(lt, 2, 5, w2, w3, 3);
    step_done_same(lt, 2, 5, w2, w3, 4);
    step_done_same(lt, 2, 5, w2, w3, 6);
    step_done_same(lt, 2, 5, w2, w3, 7);
    step_done_same(lt, 2, 5, w2, w3, 8);
    step_done_same(lt, 4, 8, w3, w4, 0);
    step_done_same(lt, 4, 8, w3, w4, 1);
    step_done_same(lt, 4, 8, w3, w4, 2);
    step_done_same(lt, 4, 8, w3, w4, 3);
    step_done_same(lt, 4, 8, w3, w4, 5);
    step_done_same(lt, 4, 8, w3, w4, 6);
    step_done_same(lt, 4, 8, w3, w4, 7);
    step_done_same(lt, 0, 7, w4, w5, 1);
    step_done_same(lt, 0, 7, w4, w5, 2);
    step_done_same(lt, 0, 7, w4, w5, 3);
    step_done_same(lt, 0, 7, w4, w5, 4);
    step_done_same(lt, 0, 7, w4, w5, 5);
    step_done_same(lt, 0, 7, w4, w5, 6);
    step_done_same(lt, 0, 7, w4, w5, 8);
    step_done_same(lt, 2, 4, w5, w6, 0);
    step_done_same(lt, 2, 4, w5, w6, 1);
    step_done_same(lt, 2, 4, w5, w6, 3);
    step_done_same(lt, 2, 4, w5, w6, 5);
    step_done_same(lt, 2, 4, w5, w6, 6);
    step_done_same(lt, 2, 4, w5, w6, 7);
    step_done_same(lt, 2, 4, w5, w6, 8);
    step_done_same(lt, 3, 8, w6, w7, 0);
    step_done_same(lt, 3, 8, w6, w7, 1);
    step_done_same(lt, 3, 8, w6, w7, 2);
    step_done_same(lt, 3, 8, w6, w7, 4);
    step_done_same(lt, 3, 8, w6, w7, 5);
    step_done_same(lt, 3, 8, w6, w7, 6);
    step_done_same(lt, 3, 8, w6, w7, 7);
    step_done_same(lt, 5, 6, w7, w8, 0);
    step_done_same(lt, 5, 6, w7, w8, 1);
    step_done_same(lt, 5, 6, w7, w8, 2);
    step_done_same(lt, 5, 6, w7, w8, 3);
    step_done_same(lt, 5, 6, w7, w8, 4);
    step_done_same(lt, 5, 6, w7, w8, 7);
    step_done_same(lt, 5, 6, w7, w8, 8);
    step_done_same(lt, 0, 2, w8, w9, 1);
    step_done_same(lt, 0, 2, w8, w9, 3);
    step_done_same(lt, 0, 2, w8, w9, 4);
    step_done_same(lt, 0, 2, w8, w9, 5);
    step_done_same(lt, 0, 2, w8, w9, 6);
    step_done_same(lt, 0, 2, w8, w9, 7);
    step_done_same(lt, 0, 2, w8, w9, 8);
    step_done_same(lt, 1, 3, w9, w10, 0);
    step_done_same(lt, 1, 3, w9, w10, 2);
    step_done_same(lt, 1, 3, w9, w10, 4);
    step_done_same(lt, 1, 3, w9, w10, 5);
    step_done_same(lt, 1, 3, w9, w10, 6);
    step_done_same(lt, 1, 3, w9, w10, 7);
    step_done_same(lt, 1, 3, w9, w10, 8);
    step_done_same(lt, 4, 5, w10, w11, 0);
    step_done_same(lt, 4, 5, w10, w11, 1);
    step_done_same(lt, 4, 5, w10, w11, 2);
    step_done_same(lt, 4, 5, w10, w11, 3);
    step_done_same(lt, 4, 5, w10, w11, 6);
    step_done_same(lt, 4, 5, w10, w11, 7);
    step_done_same(lt, 4, 5, w10, w11, 8);
    step_done_same(lt, 7, 8, w11, w12, 0);
    step_done_same(lt, 7, 8, w11, w12, 1);
    step_done_same(lt, 7, 8, w11, w12, 2);
    step_done_same(lt, 7, 8, w11, w12, 3);
    step_done_same(lt, 7, 8, w11, w12, 4);
    step_done_same(lt, 7, 8, w11, w12, 5);
    step_done_same(lt, 7, 8, w11, w12, 6);
    step_done_same(lt, 1, 4, w12, w13, 0);
    step_done_same(lt, 1, 4, w12, w13, 2);
    step_done_same(lt, 1, 4, w12, w13, 3);
    step_done_same(lt, 1, 4, w12, w13, 5);
    step_done_same(lt, 1, 4, w12, w13, 6);
    step_done_same(lt, 1, 4, w12, w13, 7);
    step_done_same(lt, 1, 4, w12, w13, 8);
    step_done_same(lt, 3, 6, w13, w14, 0);
    step_done_same(lt, 3, 6, w13, w14, 1);
    step_done_same(lt, 3, 6, w13, w14, 2);
    step_done_same(lt, 3, 6, w13, w14, 4);
    step_done_same(lt, 3, 6, w13, w14, 5);
    step_done_same(lt, 3, 6, w13, w14, 7);
    step_done_same(lt, 3, 6, w13, w14, 8);
    step_done_same(lt, 5, 7, w14, w15, 0);
    step_done_same(lt, 5, 7, w14, w15, 1);
    step_done_same(lt, 5, 7, w14, w15, 2);
    step_done_same(lt, 5, 7, w14, w15, 3);
    step_done_same(lt, 5, 7, w14, w15, 4);
    step_done_same(lt, 5, 7, w14, w15, 6);
    step_done_same(lt, 5, 7, w14, w15, 8);
    step_done_same(lt, 0, 1, w15, w16, 2);
    step_done_same(lt, 0, 1, w15, w16, 3);
    step_done_same(lt, 0, 1, w15, w16, 4);
    step_done_same(lt, 0, 1, w15, w16, 5);
    step_done_same(lt, 0, 1, w15, w16, 6);
    step_done_same(lt, 0, 1, w15, w16, 7);
    step_done_same(lt, 0, 1, w15, w16, 8);
    step_done_same(lt, 2, 4, w16, w17, 0);
    step_done_same(lt, 2, 4, w16, w17, 1);
    step_done_same(lt, 2, 4, w16, w17, 3);
    step_done_same(lt, 2, 4, w16, w17, 5);
    step_done_same(lt, 2, 4, w16, w17, 6);
    step_done_same(lt, 2, 4, w16, w17, 7);
    step_done_same(lt, 2, 4, w16, w17, 8);
    step_done_same(lt, 3, 5, w17, w18, 0);
    step_done_same(lt, 3, 5, w17, w18, 1);
    step_done_same(lt, 3, 5, w17, w18, 2);
    step_done_same(lt, 3, 5, w17, w18, 4);
    step_done_same(lt, 3, 5, w17, w18, 6);
    step_done_same(lt, 3, 5, w17, w18, 7);
    step_done_same(lt, 3, 5, w17, w18, 8);
    step_done_same(lt, 6, 8, w18, w19, 0);
    step_done_same(lt, 6, 8, w18, w19, 1);
    step_done_same(lt, 6, 8, w18, w19, 2);
    step_done_same(lt, 6, 8, w18, w19, 3);
    step_done_same(lt, 6, 8, w18, w19, 4);
    step_done_same(lt, 6, 8, w18, w19, 5);
    step_done_same(lt, 6, 8, w18, w19, 7);
    step_done_same(lt, 2, 3, w19, w20, 0);
    step_done_same(lt, 2, 3, w19, w20, 1);
    step_done_same(lt, 2, 3, w19, w20, 4);
    step_done_same(lt, 2, 3, w19, w20, 5);
    step_done_same(lt, 2, 3, w19, w20, 6);
    step_done_same(lt, 2, 3, w19, w20, 7);
    step_done_same(lt, 2, 3, w19, w20, 8);
    step_done_same(lt, 4, 5, w20, w21, 0);
    step_done_same(lt, 4, 5, w20, w21, 1);
    step_done_same(lt, 4, 5, w20, w21, 2);
    step_done_same(lt, 4, 5, w20, w21, 3);
    step_done_same(lt, 4, 5, w20, w21, 6);
    step_done_same(lt, 4, 5, w20, w21, 7);
    step_done_same(lt, 4, 5, w20, w21, 8);
    step_done_same(lt, 6, 7, w21, w22, 0);
    step_done_same(lt, 6, 7, w21, w22, 1);
    step_done_same(lt, 6, 7, w21, w22, 2);
    step_done_same(lt, 6, 7, w21, w22, 3);
    step_done_same(lt, 6, 7, w21, w22, 4);
    step_done_same(lt, 6, 7, w21, w22, 5);
    step_done_same(lt, 6, 7, w21, w22, 8);
    step_done_same(lt, 1, 2, w22, w23, 0);
    step_done_same(lt, 1, 2, w22, w23, 3);
    step_done_same(lt, 1, 2, w22, w23, 4);
    step_done_same(lt, 1, 2, w22, w23, 5);
    step_done_same(lt, 1, 2, w22, w23, 6);
    step_done_same(lt, 1, 2, w22, w23, 7);
    step_done_same(lt, 1, 2, w22, w23, 8);
    step_done_same(lt, 3, 4, w23, w24, 0);
    step_done_same(lt, 3, 4, w23, w24, 1);
    step_done_same(lt, 3, 4, w23, w24, 2);
    step_done_same(lt, 3, 4, w23, w24, 5);
    step_done_same(lt, 3, 4, w23, w24, 6);
    step_done_same(lt, 3, 4, w23, w24, 7);
    step_done_same(lt, 3, 4, w23, w24, 8);
    step_done_same(lt, 5, 6, w24, w25, 0);
    step_done_same(lt, 5, 6, w24, w25, 1);
    step_done_same(lt, 5, 6, w24, w25, 2);
    step_done_same(lt, 5, 6, w24, w25, 3);
    step_done_same(lt, 5, 6, w24, w25, 4);
    step_done_same(lt, 5, 6, w24, w25, 7);
    step_done_same(lt, 5, 6, w24, w25, 8);
}

lem net9_adj0<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(1, w25), nth(0, w25));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(1, w25);
    step_done_bits::<T, F>(f0, c, 0, 3, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 7, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 5, w2, w3);
    step_done_bits::<T, F>(f0, c, 4, 8, w3, w4);
    step_done_bits::<T, F>(f0, c, 0, 7, w4, w5);
    step_done_bits::<T, F>(f0, c, 2, 4, w5, w6);
    step_done_bits::<T, F>(f0, c, 3, 8, w6, w7);
    step_done_bits::<T, F>(f0, c, 5, 6, w7, w8);
    step_done_bits::<T, F>(f0, c, 0, 2, w8, w9);
    step_done_bits::<T, F>(f0, c, 1, 3, w9, w10);
    step_done_bits::<T, F>(f0, c, 4, 5, w10, w11);
    step_done_bits::<T, F>(f0, c, 7, 8, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 4, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 5, 7, w14, w15);
    step_done_bits::<T, F>(f0, c, 0, 1, w15, w16);
    step_done_bits::<T, F>(f0, c, 2, 4, w16, w17);
    step_done_bits::<T, F>(f0, c, 3, 5, w17, w18);
    step_done_bits::<T, F>(f0, c, 6, 8, w18, w19);
    step_done_bits::<T, F>(f0, c, 2, 3, w19, w20);
    step_done_bits::<T, F>(f0, c, 4, 5, w20, w21);
    step_done_bits::<T, F>(f0, c, 6, 7, w21, w22);
    step_done_bits::<T, F>(f0, c, 1, 2, w22, w23);
    step_done_bits::<T, F>(f0, c, 3, 4, w23, w24);
    step_done_bits::<T, F>(f0, c, 5, 6, w24, w25);
    net9_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(3, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(7, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(5, w3))), bit_of(apply_lt(lt, c, nth(4, w4))), bit_of(apply_lt(lt, c, nth(8, w4))), bit_of(apply_lt(lt, c, nth(0, w5))), bit_of(apply_lt(lt, c, nth(7, w5))), bit_of(apply_lt(lt, c, nth(2, w6))), bit_of(apply_lt(lt, c, nth(4, w6))), bit_of(apply_lt(lt, c, nth(3, w7))), bit_of(apply_lt(lt, c, nth(8, w7))), bit_of(apply_lt(lt, c, nth(5, w8))), bit_of(apply_lt(lt, c, nth(6, w8))), bit_of(apply_lt(lt, c, nth(0, w9))), bit_of(apply_lt(lt, c, nth(2, w9))), bit_of(apply_lt(lt, c, nth(1, w10))), bit_of(apply_lt(lt, c, nth(3, w10))), bit_of(apply_lt(lt, c, nth(4, w11))), bit_of(apply_lt(lt, c, nth(5, w11))), bit_of(apply_lt(lt, c, nth(7, w12))), bit_of(apply_lt(lt, c, nth(8, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(4, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(5, w15))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(0, w16))), bit_of(apply_lt(lt, c, nth(1, w16))), bit_of(apply_lt(lt, c, nth(2, w17))), bit_of(apply_lt(lt, c, nth(4, w17))), bit_of(apply_lt(lt, c, nth(3, w18))), bit_of(apply_lt(lt, c, nth(5, w18))), bit_of(apply_lt(lt, c, nth(6, w19))), bit_of(apply_lt(lt, c, nth(8, w19))), bit_of(apply_lt(lt, c, nth(2, w20))), bit_of(apply_lt(lt, c, nth(3, w20))), bit_of(apply_lt(lt, c, nth(4, w21))), bit_of(apply_lt(lt, c, nth(5, w21))), bit_of(apply_lt(lt, c, nth(6, w22))), bit_of(apply_lt(lt, c, nth(7, w22))), bit_of(apply_lt(lt, c, nth(1, w23))), bit_of(apply_lt(lt, c, nth(2, w23))), bit_of(apply_lt(lt, c, nth(3, w24))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(5, w25))), bit_of(apply_lt(lt, c, nth(6, w25))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(0, w25)), apply_lt(lt, c, c));
}

lem net9_adj1<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(2, w25), nth(1, w25));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(2, w25);
    step_done_bits::<T, F>(f0, c, 0, 3, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 7, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 5, w2, w3);
    step_done_bits::<T, F>(f0, c, 4, 8, w3, w4);
    step_done_bits::<T, F>(f0, c, 0, 7, w4, w5);
    step_done_bits::<T, F>(f0, c, 2, 4, w5, w6);
    step_done_bits::<T, F>(f0, c, 3, 8, w6, w7);
    step_done_bits::<T, F>(f0, c, 5, 6, w7, w8);
    step_done_bits::<T, F>(f0, c, 0, 2, w8, w9);
    step_done_bits::<T, F>(f0, c, 1, 3, w9, w10);
    step_done_bits::<T, F>(f0, c, 4, 5, w10, w11);
    step_done_bits::<T, F>(f0, c, 7, 8, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 4, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 5, 7, w14, w15);
    step_done_bits::<T, F>(f0, c, 0, 1, w15, w16);
    step_done_bits::<T, F>(f0, c, 2, 4, w16, w17);
    step_done_bits::<T, F>(f0, c, 3, 5, w17, w18);
    step_done_bits::<T, F>(f0, c, 6, 8, w18, w19);
    step_done_bits::<T, F>(f0, c, 2, 3, w19, w20);
    step_done_bits::<T, F>(f0, c, 4, 5, w20, w21);
    step_done_bits::<T, F>(f0, c, 6, 7, w21, w22);
    step_done_bits::<T, F>(f0, c, 1, 2, w22, w23);
    step_done_bits::<T, F>(f0, c, 3, 4, w23, w24);
    step_done_bits::<T, F>(f0, c, 5, 6, w24, w25);
    net9_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(3, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(7, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(5, w3))), bit_of(apply_lt(lt, c, nth(4, w4))), bit_of(apply_lt(lt, c, nth(8, w4))), bit_of(apply_lt(lt, c, nth(0, w5))), bit_of(apply_lt(lt, c, nth(7, w5))), bit_of(apply_lt(lt, c, nth(2, w6))), bit_of(apply_lt(lt, c, nth(4, w6))), bit_of(apply_lt(lt, c, nth(3, w7))), bit_of(apply_lt(lt, c, nth(8, w7))), bit_of(apply_lt(lt, c, nth(5, w8))), bit_of(apply_lt(lt, c, nth(6, w8))), bit_of(apply_lt(lt, c, nth(0, w9))), bit_of(apply_lt(lt, c, nth(2, w9))), bit_of(apply_lt(lt, c, nth(1, w10))), bit_of(apply_lt(lt, c, nth(3, w10))), bit_of(apply_lt(lt, c, nth(4, w11))), bit_of(apply_lt(lt, c, nth(5, w11))), bit_of(apply_lt(lt, c, nth(7, w12))), bit_of(apply_lt(lt, c, nth(8, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(4, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(5, w15))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(0, w16))), bit_of(apply_lt(lt, c, nth(1, w16))), bit_of(apply_lt(lt, c, nth(2, w17))), bit_of(apply_lt(lt, c, nth(4, w17))), bit_of(apply_lt(lt, c, nth(3, w18))), bit_of(apply_lt(lt, c, nth(5, w18))), bit_of(apply_lt(lt, c, nth(6, w19))), bit_of(apply_lt(lt, c, nth(8, w19))), bit_of(apply_lt(lt, c, nth(2, w20))), bit_of(apply_lt(lt, c, nth(3, w20))), bit_of(apply_lt(lt, c, nth(4, w21))), bit_of(apply_lt(lt, c, nth(5, w21))), bit_of(apply_lt(lt, c, nth(6, w22))), bit_of(apply_lt(lt, c, nth(7, w22))), bit_of(apply_lt(lt, c, nth(1, w23))), bit_of(apply_lt(lt, c, nth(2, w23))), bit_of(apply_lt(lt, c, nth(3, w24))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(5, w25))), bit_of(apply_lt(lt, c, nth(6, w25))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(1, w25)), apply_lt(lt, c, c));
}

lem net9_adj2<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(3, w25), nth(2, w25));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(3, w25);
    step_done_bits::<T, F>(f0, c, 0, 3, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 7, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 5, w2, w3);
    step_done_bits::<T, F>(f0, c, 4, 8, w3, w4);
    step_done_bits::<T, F>(f0, c, 0, 7, w4, w5);
    step_done_bits::<T, F>(f0, c, 2, 4, w5, w6);
    step_done_bits::<T, F>(f0, c, 3, 8, w6, w7);
    step_done_bits::<T, F>(f0, c, 5, 6, w7, w8);
    step_done_bits::<T, F>(f0, c, 0, 2, w8, w9);
    step_done_bits::<T, F>(f0, c, 1, 3, w9, w10);
    step_done_bits::<T, F>(f0, c, 4, 5, w10, w11);
    step_done_bits::<T, F>(f0, c, 7, 8, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 4, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 5, 7, w14, w15);
    step_done_bits::<T, F>(f0, c, 0, 1, w15, w16);
    step_done_bits::<T, F>(f0, c, 2, 4, w16, w17);
    step_done_bits::<T, F>(f0, c, 3, 5, w17, w18);
    step_done_bits::<T, F>(f0, c, 6, 8, w18, w19);
    step_done_bits::<T, F>(f0, c, 2, 3, w19, w20);
    step_done_bits::<T, F>(f0, c, 4, 5, w20, w21);
    step_done_bits::<T, F>(f0, c, 6, 7, w21, w22);
    step_done_bits::<T, F>(f0, c, 1, 2, w22, w23);
    step_done_bits::<T, F>(f0, c, 3, 4, w23, w24);
    step_done_bits::<T, F>(f0, c, 5, 6, w24, w25);
    net9_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(3, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(7, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(5, w3))), bit_of(apply_lt(lt, c, nth(4, w4))), bit_of(apply_lt(lt, c, nth(8, w4))), bit_of(apply_lt(lt, c, nth(0, w5))), bit_of(apply_lt(lt, c, nth(7, w5))), bit_of(apply_lt(lt, c, nth(2, w6))), bit_of(apply_lt(lt, c, nth(4, w6))), bit_of(apply_lt(lt, c, nth(3, w7))), bit_of(apply_lt(lt, c, nth(8, w7))), bit_of(apply_lt(lt, c, nth(5, w8))), bit_of(apply_lt(lt, c, nth(6, w8))), bit_of(apply_lt(lt, c, nth(0, w9))), bit_of(apply_lt(lt, c, nth(2, w9))), bit_of(apply_lt(lt, c, nth(1, w10))), bit_of(apply_lt(lt, c, nth(3, w10))), bit_of(apply_lt(lt, c, nth(4, w11))), bit_of(apply_lt(lt, c, nth(5, w11))), bit_of(apply_lt(lt, c, nth(7, w12))), bit_of(apply_lt(lt, c, nth(8, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(4, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(5, w15))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(0, w16))), bit_of(apply_lt(lt, c, nth(1, w16))), bit_of(apply_lt(lt, c, nth(2, w17))), bit_of(apply_lt(lt, c, nth(4, w17))), bit_of(apply_lt(lt, c, nth(3, w18))), bit_of(apply_lt(lt, c, nth(5, w18))), bit_of(apply_lt(lt, c, nth(6, w19))), bit_of(apply_lt(lt, c, nth(8, w19))), bit_of(apply_lt(lt, c, nth(2, w20))), bit_of(apply_lt(lt, c, nth(3, w20))), bit_of(apply_lt(lt, c, nth(4, w21))), bit_of(apply_lt(lt, c, nth(5, w21))), bit_of(apply_lt(lt, c, nth(6, w22))), bit_of(apply_lt(lt, c, nth(7, w22))), bit_of(apply_lt(lt, c, nth(1, w23))), bit_of(apply_lt(lt, c, nth(2, w23))), bit_of(apply_lt(lt, c, nth(3, w24))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(5, w25))), bit_of(apply_lt(lt, c, nth(6, w25))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(2, w25)), apply_lt(lt, c, c));
}

lem net9_adj3<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(4, w25), nth(3, w25));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(4, w25);
    step_done_bits::<T, F>(f0, c, 0, 3, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 7, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 5, w2, w3);
    step_done_bits::<T, F>(f0, c, 4, 8, w3, w4);
    step_done_bits::<T, F>(f0, c, 0, 7, w4, w5);
    step_done_bits::<T, F>(f0, c, 2, 4, w5, w6);
    step_done_bits::<T, F>(f0, c, 3, 8, w6, w7);
    step_done_bits::<T, F>(f0, c, 5, 6, w7, w8);
    step_done_bits::<T, F>(f0, c, 0, 2, w8, w9);
    step_done_bits::<T, F>(f0, c, 1, 3, w9, w10);
    step_done_bits::<T, F>(f0, c, 4, 5, w10, w11);
    step_done_bits::<T, F>(f0, c, 7, 8, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 4, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 5, 7, w14, w15);
    step_done_bits::<T, F>(f0, c, 0, 1, w15, w16);
    step_done_bits::<T, F>(f0, c, 2, 4, w16, w17);
    step_done_bits::<T, F>(f0, c, 3, 5, w17, w18);
    step_done_bits::<T, F>(f0, c, 6, 8, w18, w19);
    step_done_bits::<T, F>(f0, c, 2, 3, w19, w20);
    step_done_bits::<T, F>(f0, c, 4, 5, w20, w21);
    step_done_bits::<T, F>(f0, c, 6, 7, w21, w22);
    step_done_bits::<T, F>(f0, c, 1, 2, w22, w23);
    step_done_bits::<T, F>(f0, c, 3, 4, w23, w24);
    step_done_bits::<T, F>(f0, c, 5, 6, w24, w25);
    net9_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(3, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(7, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(5, w3))), bit_of(apply_lt(lt, c, nth(4, w4))), bit_of(apply_lt(lt, c, nth(8, w4))), bit_of(apply_lt(lt, c, nth(0, w5))), bit_of(apply_lt(lt, c, nth(7, w5))), bit_of(apply_lt(lt, c, nth(2, w6))), bit_of(apply_lt(lt, c, nth(4, w6))), bit_of(apply_lt(lt, c, nth(3, w7))), bit_of(apply_lt(lt, c, nth(8, w7))), bit_of(apply_lt(lt, c, nth(5, w8))), bit_of(apply_lt(lt, c, nth(6, w8))), bit_of(apply_lt(lt, c, nth(0, w9))), bit_of(apply_lt(lt, c, nth(2, w9))), bit_of(apply_lt(lt, c, nth(1, w10))), bit_of(apply_lt(lt, c, nth(3, w10))), bit_of(apply_lt(lt, c, nth(4, w11))), bit_of(apply_lt(lt, c, nth(5, w11))), bit_of(apply_lt(lt, c, nth(7, w12))), bit_of(apply_lt(lt, c, nth(8, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(4, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(5, w15))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(0, w16))), bit_of(apply_lt(lt, c, nth(1, w16))), bit_of(apply_lt(lt, c, nth(2, w17))), bit_of(apply_lt(lt, c, nth(4, w17))), bit_of(apply_lt(lt, c, nth(3, w18))), bit_of(apply_lt(lt, c, nth(5, w18))), bit_of(apply_lt(lt, c, nth(6, w19))), bit_of(apply_lt(lt, c, nth(8, w19))), bit_of(apply_lt(lt, c, nth(2, w20))), bit_of(apply_lt(lt, c, nth(3, w20))), bit_of(apply_lt(lt, c, nth(4, w21))), bit_of(apply_lt(lt, c, nth(5, w21))), bit_of(apply_lt(lt, c, nth(6, w22))), bit_of(apply_lt(lt, c, nth(7, w22))), bit_of(apply_lt(lt, c, nth(1, w23))), bit_of(apply_lt(lt, c, nth(2, w23))), bit_of(apply_lt(lt, c, nth(3, w24))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(5, w25))), bit_of(apply_lt(lt, c, nth(6, w25))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(3, w25)), apply_lt(lt, c, c));
}

lem net9_adj4<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(5, w25), nth(4, w25));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(5, w25);
    step_done_bits::<T, F>(f0, c, 0, 3, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 7, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 5, w2, w3);
    step_done_bits::<T, F>(f0, c, 4, 8, w3, w4);
    step_done_bits::<T, F>(f0, c, 0, 7, w4, w5);
    step_done_bits::<T, F>(f0, c, 2, 4, w5, w6);
    step_done_bits::<T, F>(f0, c, 3, 8, w6, w7);
    step_done_bits::<T, F>(f0, c, 5, 6, w7, w8);
    step_done_bits::<T, F>(f0, c, 0, 2, w8, w9);
    step_done_bits::<T, F>(f0, c, 1, 3, w9, w10);
    step_done_bits::<T, F>(f0, c, 4, 5, w10, w11);
    step_done_bits::<T, F>(f0, c, 7, 8, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 4, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 5, 7, w14, w15);
    step_done_bits::<T, F>(f0, c, 0, 1, w15, w16);
    step_done_bits::<T, F>(f0, c, 2, 4, w16, w17);
    step_done_bits::<T, F>(f0, c, 3, 5, w17, w18);
    step_done_bits::<T, F>(f0, c, 6, 8, w18, w19);
    step_done_bits::<T, F>(f0, c, 2, 3, w19, w20);
    step_done_bits::<T, F>(f0, c, 4, 5, w20, w21);
    step_done_bits::<T, F>(f0, c, 6, 7, w21, w22);
    step_done_bits::<T, F>(f0, c, 1, 2, w22, w23);
    step_done_bits::<T, F>(f0, c, 3, 4, w23, w24);
    step_done_bits::<T, F>(f0, c, 5, 6, w24, w25);
    net9_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(3, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(7, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(5, w3))), bit_of(apply_lt(lt, c, nth(4, w4))), bit_of(apply_lt(lt, c, nth(8, w4))), bit_of(apply_lt(lt, c, nth(0, w5))), bit_of(apply_lt(lt, c, nth(7, w5))), bit_of(apply_lt(lt, c, nth(2, w6))), bit_of(apply_lt(lt, c, nth(4, w6))), bit_of(apply_lt(lt, c, nth(3, w7))), bit_of(apply_lt(lt, c, nth(8, w7))), bit_of(apply_lt(lt, c, nth(5, w8))), bit_of(apply_lt(lt, c, nth(6, w8))), bit_of(apply_lt(lt, c, nth(0, w9))), bit_of(apply_lt(lt, c, nth(2, w9))), bit_of(apply_lt(lt, c, nth(1, w10))), bit_of(apply_lt(lt, c, nth(3, w10))), bit_of(apply_lt(lt, c, nth(4, w11))), bit_of(apply_lt(lt, c, nth(5, w11))), bit_of(apply_lt(lt, c, nth(7, w12))), bit_of(apply_lt(lt, c, nth(8, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(4, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(5, w15))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(0, w16))), bit_of(apply_lt(lt, c, nth(1, w16))), bit_of(apply_lt(lt, c, nth(2, w17))), bit_of(apply_lt(lt, c, nth(4, w17))), bit_of(apply_lt(lt, c, nth(3, w18))), bit_of(apply_lt(lt, c, nth(5, w18))), bit_of(apply_lt(lt, c, nth(6, w19))), bit_of(apply_lt(lt, c, nth(8, w19))), bit_of(apply_lt(lt, c, nth(2, w20))), bit_of(apply_lt(lt, c, nth(3, w20))), bit_of(apply_lt(lt, c, nth(4, w21))), bit_of(apply_lt(lt, c, nth(5, w21))), bit_of(apply_lt(lt, c, nth(6, w22))), bit_of(apply_lt(lt, c, nth(7, w22))), bit_of(apply_lt(lt, c, nth(1, w23))), bit_of(apply_lt(lt, c, nth(2, w23))), bit_of(apply_lt(lt, c, nth(3, w24))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(5, w25))), bit_of(apply_lt(lt, c, nth(6, w25))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(4, w25)), apply_lt(lt, c, c));
}

lem net9_adj5<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(6, w25), nth(5, w25));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(6, w25);
    step_done_bits::<T, F>(f0, c, 0, 3, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 7, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 5, w2, w3);
    step_done_bits::<T, F>(f0, c, 4, 8, w3, w4);
    step_done_bits::<T, F>(f0, c, 0, 7, w4, w5);
    step_done_bits::<T, F>(f0, c, 2, 4, w5, w6);
    step_done_bits::<T, F>(f0, c, 3, 8, w6, w7);
    step_done_bits::<T, F>(f0, c, 5, 6, w7, w8);
    step_done_bits::<T, F>(f0, c, 0, 2, w8, w9);
    step_done_bits::<T, F>(f0, c, 1, 3, w9, w10);
    step_done_bits::<T, F>(f0, c, 4, 5, w10, w11);
    step_done_bits::<T, F>(f0, c, 7, 8, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 4, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 5, 7, w14, w15);
    step_done_bits::<T, F>(f0, c, 0, 1, w15, w16);
    step_done_bits::<T, F>(f0, c, 2, 4, w16, w17);
    step_done_bits::<T, F>(f0, c, 3, 5, w17, w18);
    step_done_bits::<T, F>(f0, c, 6, 8, w18, w19);
    step_done_bits::<T, F>(f0, c, 2, 3, w19, w20);
    step_done_bits::<T, F>(f0, c, 4, 5, w20, w21);
    step_done_bits::<T, F>(f0, c, 6, 7, w21, w22);
    step_done_bits::<T, F>(f0, c, 1, 2, w22, w23);
    step_done_bits::<T, F>(f0, c, 3, 4, w23, w24);
    step_done_bits::<T, F>(f0, c, 5, 6, w24, w25);
    net9_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(3, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(7, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(5, w3))), bit_of(apply_lt(lt, c, nth(4, w4))), bit_of(apply_lt(lt, c, nth(8, w4))), bit_of(apply_lt(lt, c, nth(0, w5))), bit_of(apply_lt(lt, c, nth(7, w5))), bit_of(apply_lt(lt, c, nth(2, w6))), bit_of(apply_lt(lt, c, nth(4, w6))), bit_of(apply_lt(lt, c, nth(3, w7))), bit_of(apply_lt(lt, c, nth(8, w7))), bit_of(apply_lt(lt, c, nth(5, w8))), bit_of(apply_lt(lt, c, nth(6, w8))), bit_of(apply_lt(lt, c, nth(0, w9))), bit_of(apply_lt(lt, c, nth(2, w9))), bit_of(apply_lt(lt, c, nth(1, w10))), bit_of(apply_lt(lt, c, nth(3, w10))), bit_of(apply_lt(lt, c, nth(4, w11))), bit_of(apply_lt(lt, c, nth(5, w11))), bit_of(apply_lt(lt, c, nth(7, w12))), bit_of(apply_lt(lt, c, nth(8, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(4, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(5, w15))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(0, w16))), bit_of(apply_lt(lt, c, nth(1, w16))), bit_of(apply_lt(lt, c, nth(2, w17))), bit_of(apply_lt(lt, c, nth(4, w17))), bit_of(apply_lt(lt, c, nth(3, w18))), bit_of(apply_lt(lt, c, nth(5, w18))), bit_of(apply_lt(lt, c, nth(6, w19))), bit_of(apply_lt(lt, c, nth(8, w19))), bit_of(apply_lt(lt, c, nth(2, w20))), bit_of(apply_lt(lt, c, nth(3, w20))), bit_of(apply_lt(lt, c, nth(4, w21))), bit_of(apply_lt(lt, c, nth(5, w21))), bit_of(apply_lt(lt, c, nth(6, w22))), bit_of(apply_lt(lt, c, nth(7, w22))), bit_of(apply_lt(lt, c, nth(1, w23))), bit_of(apply_lt(lt, c, nth(2, w23))), bit_of(apply_lt(lt, c, nth(3, w24))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(5, w25))), bit_of(apply_lt(lt, c, nth(6, w25))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(5, w25)), apply_lt(lt, c, c));
}

lem net9_adj6<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(7, w25), nth(6, w25));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(7, w25);
    step_done_bits::<T, F>(f0, c, 0, 3, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 7, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 5, w2, w3);
    step_done_bits::<T, F>(f0, c, 4, 8, w3, w4);
    step_done_bits::<T, F>(f0, c, 0, 7, w4, w5);
    step_done_bits::<T, F>(f0, c, 2, 4, w5, w6);
    step_done_bits::<T, F>(f0, c, 3, 8, w6, w7);
    step_done_bits::<T, F>(f0, c, 5, 6, w7, w8);
    step_done_bits::<T, F>(f0, c, 0, 2, w8, w9);
    step_done_bits::<T, F>(f0, c, 1, 3, w9, w10);
    step_done_bits::<T, F>(f0, c, 4, 5, w10, w11);
    step_done_bits::<T, F>(f0, c, 7, 8, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 4, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 5, 7, w14, w15);
    step_done_bits::<T, F>(f0, c, 0, 1, w15, w16);
    step_done_bits::<T, F>(f0, c, 2, 4, w16, w17);
    step_done_bits::<T, F>(f0, c, 3, 5, w17, w18);
    step_done_bits::<T, F>(f0, c, 6, 8, w18, w19);
    step_done_bits::<T, F>(f0, c, 2, 3, w19, w20);
    step_done_bits::<T, F>(f0, c, 4, 5, w20, w21);
    step_done_bits::<T, F>(f0, c, 6, 7, w21, w22);
    step_done_bits::<T, F>(f0, c, 1, 2, w22, w23);
    step_done_bits::<T, F>(f0, c, 3, 4, w23, w24);
    step_done_bits::<T, F>(f0, c, 5, 6, w24, w25);
    net9_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(3, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(7, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(5, w3))), bit_of(apply_lt(lt, c, nth(4, w4))), bit_of(apply_lt(lt, c, nth(8, w4))), bit_of(apply_lt(lt, c, nth(0, w5))), bit_of(apply_lt(lt, c, nth(7, w5))), bit_of(apply_lt(lt, c, nth(2, w6))), bit_of(apply_lt(lt, c, nth(4, w6))), bit_of(apply_lt(lt, c, nth(3, w7))), bit_of(apply_lt(lt, c, nth(8, w7))), bit_of(apply_lt(lt, c, nth(5, w8))), bit_of(apply_lt(lt, c, nth(6, w8))), bit_of(apply_lt(lt, c, nth(0, w9))), bit_of(apply_lt(lt, c, nth(2, w9))), bit_of(apply_lt(lt, c, nth(1, w10))), bit_of(apply_lt(lt, c, nth(3, w10))), bit_of(apply_lt(lt, c, nth(4, w11))), bit_of(apply_lt(lt, c, nth(5, w11))), bit_of(apply_lt(lt, c, nth(7, w12))), bit_of(apply_lt(lt, c, nth(8, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(4, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(5, w15))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(0, w16))), bit_of(apply_lt(lt, c, nth(1, w16))), bit_of(apply_lt(lt, c, nth(2, w17))), bit_of(apply_lt(lt, c, nth(4, w17))), bit_of(apply_lt(lt, c, nth(3, w18))), bit_of(apply_lt(lt, c, nth(5, w18))), bit_of(apply_lt(lt, c, nth(6, w19))), bit_of(apply_lt(lt, c, nth(8, w19))), bit_of(apply_lt(lt, c, nth(2, w20))), bit_of(apply_lt(lt, c, nth(3, w20))), bit_of(apply_lt(lt, c, nth(4, w21))), bit_of(apply_lt(lt, c, nth(5, w21))), bit_of(apply_lt(lt, c, nth(6, w22))), bit_of(apply_lt(lt, c, nth(7, w22))), bit_of(apply_lt(lt, c, nth(1, w23))), bit_of(apply_lt(lt, c, nth(2, w23))), bit_of(apply_lt(lt, c, nth(3, w24))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(5, w25))), bit_of(apply_lt(lt, c, nth(6, w25))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(6, w25)), apply_lt(lt, c, c));
}

lem net9_adj7<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(3, w4) == nth(3, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(7, w4) == nth(7, w3) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(5, w5) == nth(5, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(6, w6) == nth(6, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(8, w6) == nth(8, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(1, w7) == nth(1, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(6, w7) == nth(6, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(2, w8) == nth(2, w7) &*&
        nth(3, w8) == nth(3, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(4, w9) == nth(4, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(7, w10) == nth(7, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(8, w11) == nth(8, w10) &*&
        nth(0, w12) == nth(0, w11) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(4, w12) == nth(4, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(2, w13) == nth(2, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(8, w15) == nth(8, w14) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(4, w18) == nth(4, w17) &*&
        nth(6, w18) == nth(6, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(5, w19) == nth(5, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(8, w20) == nth(8, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(0, w22) == nth(0, w21) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(5, w22) == nth(5, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(3, w23) == nth(3, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(8, w23) == nth(8, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(7, w24) == nth(7, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(8, w25), nth(7, w25));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(8, w25);
    step_done_bits::<T, F>(f0, c, 0, 3, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 7, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 5, w2, w3);
    step_done_bits::<T, F>(f0, c, 4, 8, w3, w4);
    step_done_bits::<T, F>(f0, c, 0, 7, w4, w5);
    step_done_bits::<T, F>(f0, c, 2, 4, w5, w6);
    step_done_bits::<T, F>(f0, c, 3, 8, w6, w7);
    step_done_bits::<T, F>(f0, c, 5, 6, w7, w8);
    step_done_bits::<T, F>(f0, c, 0, 2, w8, w9);
    step_done_bits::<T, F>(f0, c, 1, 3, w9, w10);
    step_done_bits::<T, F>(f0, c, 4, 5, w10, w11);
    step_done_bits::<T, F>(f0, c, 7, 8, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 4, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 5, 7, w14, w15);
    step_done_bits::<T, F>(f0, c, 0, 1, w15, w16);
    step_done_bits::<T, F>(f0, c, 2, 4, w16, w17);
    step_done_bits::<T, F>(f0, c, 3, 5, w17, w18);
    step_done_bits::<T, F>(f0, c, 6, 8, w18, w19);
    step_done_bits::<T, F>(f0, c, 2, 3, w19, w20);
    step_done_bits::<T, F>(f0, c, 4, 5, w20, w21);
    step_done_bits::<T, F>(f0, c, 6, 7, w21, w22);
    step_done_bits::<T, F>(f0, c, 1, 2, w22, w23);
    step_done_bits::<T, F>(f0, c, 3, 4, w23, w24);
    step_done_bits::<T, F>(f0, c, 5, 6, w24, w25);
    net9_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(3, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(7, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(5, w3))), bit_of(apply_lt(lt, c, nth(4, w4))), bit_of(apply_lt(lt, c, nth(8, w4))), bit_of(apply_lt(lt, c, nth(0, w5))), bit_of(apply_lt(lt, c, nth(7, w5))), bit_of(apply_lt(lt, c, nth(2, w6))), bit_of(apply_lt(lt, c, nth(4, w6))), bit_of(apply_lt(lt, c, nth(3, w7))), bit_of(apply_lt(lt, c, nth(8, w7))), bit_of(apply_lt(lt, c, nth(5, w8))), bit_of(apply_lt(lt, c, nth(6, w8))), bit_of(apply_lt(lt, c, nth(0, w9))), bit_of(apply_lt(lt, c, nth(2, w9))), bit_of(apply_lt(lt, c, nth(1, w10))), bit_of(apply_lt(lt, c, nth(3, w10))), bit_of(apply_lt(lt, c, nth(4, w11))), bit_of(apply_lt(lt, c, nth(5, w11))), bit_of(apply_lt(lt, c, nth(7, w12))), bit_of(apply_lt(lt, c, nth(8, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(4, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(5, w15))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(0, w16))), bit_of(apply_lt(lt, c, nth(1, w16))), bit_of(apply_lt(lt, c, nth(2, w17))), bit_of(apply_lt(lt, c, nth(4, w17))), bit_of(apply_lt(lt, c, nth(3, w18))), bit_of(apply_lt(lt, c, nth(5, w18))), bit_of(apply_lt(lt, c, nth(6, w19))), bit_of(apply_lt(lt, c, nth(8, w19))), bit_of(apply_lt(lt, c, nth(2, w20))), bit_of(apply_lt(lt, c, nth(3, w20))), bit_of(apply_lt(lt, c, nth(4, w21))), bit_of(apply_lt(lt, c, nth(5, w21))), bit_of(apply_lt(lt, c, nth(6, w22))), bit_of(apply_lt(lt, c, nth(7, w22))), bit_of(apply_lt(lt, c, nth(1, w23))), bit_of(apply_lt(lt, c, nth(2, w23))), bit_of(apply_lt(lt, c, nth(3, w24))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(5, w25))), bit_of(apply_lt(lt, c, nth(6, w25))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(7, w25)), apply_lt(lt, c, c));
}

// The network of `sort9_optimal` sorts the first 9 elements (0-1 principle, see above).
lem net9_sorted<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 9 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 3, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 7, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 8, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 7, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 2, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 4, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 5, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w24, w25);
    ens sorted_by(is_less_model_of::<T, F>(f0), take(9, w25)) == true;
{
    let lt = is_less_model_of::<T, F>(f0);
    net9_frame::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    net9_adj0::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    net9_adj1::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    net9_adj2::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    net9_adj3::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    net9_adj4::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    net9_adj5::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    net9_adj6::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    net9_adj7::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
    sorted9_from_adj(lt, w25);
}

// Network of `sort13_optimal`: every 0/1 input comes out sorted (outputs: the last bit of each position).
lem net13_01(x0: bit, x1: bit, x2: bit, x3: bit, x4: bit, x5: bit, x6: bit, x7: bit, x8: bit, x9: bit, x10: bit, x11: bit, x12: bit, y1_0: bit, y1_12: bit, y2_1: bit, y2_10: bit, y3_2: bit, y3_9: bit, y4_3: bit, y4_7: bit, y5_5: bit, y5_11: bit, y6_6: bit, y6_8: bit, y7_1: bit, y7_6: bit, y8_2: bit, y8_3: bit, y9_4: bit, y9_11: bit, y10_7: bit, y10_9: bit, y11_8: bit, y11_10: bit, y12_0: bit, y12_4: bit, y13_1: bit, y13_2: bit, y14_3: bit, y14_6: bit, y15_7: bit, y15_8: bit, y16_9: bit, y16_10: bit, y17_11: bit, y17_12: bit, y18_4: bit, y18_6: bit, y19_5: bit, y19_9: bit, y20_8: bit, y20_11: bit, y21_10: bit, y21_12: bit, y22_0: bit, y22_5: bit, y23_3: bit, y23_8: bit, y24_4: bit, y24_7: bit, y25_6: bit, y25_11: bit, y26_9: bit, y26_10: bit, y27_0: bit, y27_1: bit, y28_2: bit, y28_5: bit, y29_6: bit, y29_9: bit, y30_7: bit, y30_8: bit, y31_10: bit, y31_11: bit, y32_1: bit, y32_3: bit, y33_2: bit, y33_4: bit, y34_5: bit, y34_6: bit, y35_9: bit, y35_10: bit, y36_1: bit, y36_2: bit, y37_3: bit, y37_4: bit, y38_5: bit, y38_7: bit, y39_6: bit, y39_8: bit, y40_2: bit, y40_3: bit, y41_4: bit, y41_5: bit, y42_6: bit, y42_7: bit, y43_8: bit, y43_9: bit, y44_3: bit, y44_4: bit, y45_5: bit, y45_6: bit)
    req y1_0 == min01(x0, x12) &*& y1_12 == max01(x0, x12) &*&
        y2_1 == min01(x1, x10) &*& y2_10 == max01(x1, x10) &*&
        y3_2 == min01(x2, x9) &*& y3_9 == max01(x2, x9) &*&
        y4_3 == min01(x3, x7) &*& y4_7 == max01(x3, x7) &*&
        y5_5 == min01(x5, x11) &*& y5_11 == max01(x5, x11) &*&
        y6_6 == min01(x6, x8) &*& y6_8 == max01(x6, x8) &*&
        y7_1 == min01(y2_1, y6_6) &*& y7_6 == max01(y2_1, y6_6) &*&
        y8_2 == min01(y3_2, y4_3) &*& y8_3 == max01(y3_2, y4_3) &*&
        y9_4 == min01(x4, y5_11) &*& y9_11 == max01(x4, y5_11) &*&
        y10_7 == min01(y4_7, y3_9) &*& y10_9 == max01(y4_7, y3_9) &*&
        y11_8 == min01(y6_8, y2_10) &*& y11_10 == max01(y6_8, y2_10) &*&
        y12_0 == min01(y1_0, y9_4) &*& y12_4 == max01(y1_0, y9_4) &*&
        y13_1 == min01(y7_1, y8_2) &*& y13_2 == max01(y7_1, y8_2) &*&
        y14_3 == min01(y8_3, y7_6) &*& y14_6 == max01(y8_3, y7_6) &*&
        y15_7 == min01(y10_7, y11_8) &*& y15_8 == max01(y10_7, y11_8) &*&
        y16_9 == min01(y10_9, y11_10) &*& y16_10 == max01(y10_9, y11_10) &*&
        y17_11 == min01(y9_11, y1_12) &*& y17_12 == max01(y9_11, y1_12) &*&
        y18_4 == min01(y12_4, y14_6) &*& y18_6 == max01(y12_4, y14_6) &*&
        y19_5 == min01(y5_5, y16_9) &*& y19_9 == max01(y5_5, y16_9) &*&
        y20_8 == min01(y15_8, y17_11) &*& y20_11 == max01(y15_8, y17_11) &*&
        y21_10 == min01(y16_10, y17_12) &*& y21_12 == max01(y16_10, y17_12) &*&
        y22_0 == min01(y12_0, y19_5) &*& y22_5 == max01(y12_0, y19_5) &*&
        y23_3 == min01(y14_3, y20_8) &*& y23_8 == max01(y14_3, y20_8) &*&
        y24_4 == min01(y18_4, y15_7) &*& y24_7 == max01(y18_4, y15_7) &*&
        y25_6 == min01(y18_6, y20_11) &*& y25_11 == max01(y18_6, y20_11) &*&
        y26_9 == min01(y19_9, y21_10) &*& y26_10 == max01(y19_9, y21_10) &*&
        y27_0 == min01(y22_0, y13_1) &*& y27_1 == max01(y22_0, y13_1) &*&
        y28_2 == min01(y13_2, y22_5) &*& y28_5 == max01(y13_2, y22_5) &*&
        y29_6 == min01(y25_6, y26_9) &*& y29_9 == max01(y25_6, y26_9) &*&
        y30_7 == min01(y24_7, y23_8) &*& y30_8 == max01(y24_7, y23_8) &*&
        y31_10 == min01(y26_10, y25_11) &*& y31_11 == max01(y26_10, y25_11) &*&
        y32_1 == min01(y27_1, y23_3) &*& y32_3 == max01(y27_1, y23_3) &*&
        y33_2 == min01(y28_2, y24_4) &*& y33_4 == max01(y28_2, y24_4) &*&
        y34_5 == min01(y28_5, y29_6) &*& y34_6 == max01(y28_5, y29_6) &*&
        y35_9 == min01(y29_9, y31_10) &*& y35_10 == max01(y29_9, y31_10) &*&
        y36_1 == min01(y32_1, y33_2) &*& y36_2 == max01(y32_1, y33_2) &*&
        y37_3 == min01(y32_3, y33_4) &*& y37_4 == max01(y32_3, y33_4) &*&
        y38_5 == min01(y34_5, y30_7) &*& y38_7 == max01(y34_5, y30_7) &*&
        y39_6 == min01(y34_6, y30_8) &*& y39_8 == max01(y34_6, y30_8) &*&
        y40_2 == min01(y36_2, y37_3) &*& y40_3 == max01(y36_2, y37_3) &*&
        y41_4 == min01(y37_4, y38_5) &*& y41_5 == max01(y37_4, y38_5) &*&
        y42_6 == min01(y39_6, y38_7) &*& y42_7 == max01(y39_6, y38_7) &*&
        y43_8 == min01(y39_8, y35_9) &*& y43_9 == max01(y39_8, y35_9) &*&
        y44_3 == min01(y40_3, y41_4) &*& y44_4 == max01(y40_3, y41_4) &*&
        y45_5 == min01(y41_5, y42_6) &*& y45_6 == max01(y41_5, y42_6);
    ens (y36_1 == bit1 || y27_0 == bit0) &*& (y40_2 == bit1 || y36_1 == bit0) &*& (y44_3 == bit1 || y40_2 == bit0) &*& (y44_4 == bit1 || y44_3 == bit0) &*& (y45_5 == bit1 || y44_4 == bit0) &*& (y45_6 == bit1 || y45_5 == bit0) &*& (y42_7 == bit1 || y45_6 == bit0) &*& (y43_8 == bit1 || y42_7 == bit0) &*& (y43_9 == bit1 || y43_8 == bit0) &*& (y35_10 == bit1 || y43_9 == bit0) &*& (y31_11 == bit1 || y35_10 == bit0) &*& (y21_12 == bit1 || y31_11 == bit0);
{
    match x0 { bit0 => {} bit1 => {} }
    match x1 { bit0 => {} bit1 => {} }
    match x2 { bit0 => {} bit1 => {} }
    match x3 { bit0 => {} bit1 => {} }
    match x4 { bit0 => {} bit1 => {} }
    match x5 { bit0 => {} bit1 => {} }
    match x6 { bit0 => {} bit1 => {} }
    match x7 { bit0 => {} bit1 => {} }
    match x8 { bit0 => {} bit1 => {} }
    match x9 { bit0 => {} bit1 => {} }
    match x10 { bit0 => {} bit1 => {} }
    match x11 { bit0 => {} bit1 => {} }
    match x12 { bit0 => {} bit1 => {} }
}

lem take13_explicit<T>(xs: list<T>)
    req 13 <= length(xs);
    ens take(13, xs) == [nth(0, xs), nth(1, xs), nth(2, xs), nth(3, xs), nth(4, xs), nth(5, xs), nth(6, xs), nth(7, xs), nth(8, xs), nth(9, xs), nth(10, xs), nth(11, xs), nth(12, xs)];
{
    drop_n_plus_one(0, xs);
    drop_n_plus_one(1, xs);
    drop_n_plus_one(2, xs);
    drop_n_plus_one(3, xs);
    drop_n_plus_one(4, xs);
    drop_n_plus_one(5, xs);
    drop_n_plus_one(6, xs);
    drop_n_plus_one(7, xs);
    drop_n_plus_one(8, xs);
    drop_n_plus_one(9, xs);
    drop_n_plus_one(10, xs);
    drop_n_plus_one(11, xs);
    drop_n_plus_one(12, xs);
}

lem sorted13_from_adj<T>(order: fix(T, T, bool), xs: list<T>)
    req 13 <= length(xs) &*& !apply_lt(order, nth(1, xs), nth(0, xs)) &*& !apply_lt(order, nth(2, xs), nth(1, xs)) &*& !apply_lt(order, nth(3, xs), nth(2, xs)) &*& !apply_lt(order, nth(4, xs), nth(3, xs)) &*& !apply_lt(order, nth(5, xs), nth(4, xs)) &*& !apply_lt(order, nth(6, xs), nth(5, xs)) &*& !apply_lt(order, nth(7, xs), nth(6, xs)) &*& !apply_lt(order, nth(8, xs), nth(7, xs)) &*& !apply_lt(order, nth(9, xs), nth(8, xs)) &*& !apply_lt(order, nth(10, xs), nth(9, xs)) &*& !apply_lt(order, nth(11, xs), nth(10, xs)) &*& !apply_lt(order, nth(12, xs), nth(11, xs));
    ens sorted_by(order, take(13, xs)) == true;
{
    take13_explicit(xs);
}

lem net13_frame<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45);
    ens length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*& true &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
{
    let lt = is_less_model_of::<T, F>(f0);
    step_done_length(lt, 0, 12, w0, w1);
    step_done_length(lt, 1, 10, w1, w2);
    step_done_length(lt, 2, 9, w2, w3);
    step_done_length(lt, 3, 7, w3, w4);
    step_done_length(lt, 5, 11, w4, w5);
    step_done_length(lt, 6, 8, w5, w6);
    step_done_length(lt, 1, 6, w6, w7);
    step_done_length(lt, 2, 3, w7, w8);
    step_done_length(lt, 4, 11, w8, w9);
    step_done_length(lt, 7, 9, w9, w10);
    step_done_length(lt, 8, 10, w10, w11);
    step_done_length(lt, 0, 4, w11, w12);
    step_done_length(lt, 1, 2, w12, w13);
    step_done_length(lt, 3, 6, w13, w14);
    step_done_length(lt, 7, 8, w14, w15);
    step_done_length(lt, 9, 10, w15, w16);
    step_done_length(lt, 11, 12, w16, w17);
    step_done_length(lt, 4, 6, w17, w18);
    step_done_length(lt, 5, 9, w18, w19);
    step_done_length(lt, 8, 11, w19, w20);
    step_done_length(lt, 10, 12, w20, w21);
    step_done_length(lt, 0, 5, w21, w22);
    step_done_length(lt, 3, 8, w22, w23);
    step_done_length(lt, 4, 7, w23, w24);
    step_done_length(lt, 6, 11, w24, w25);
    step_done_length(lt, 9, 10, w25, w26);
    step_done_length(lt, 0, 1, w26, w27);
    step_done_length(lt, 2, 5, w27, w28);
    step_done_length(lt, 6, 9, w28, w29);
    step_done_length(lt, 7, 8, w29, w30);
    step_done_length(lt, 10, 11, w30, w31);
    step_done_length(lt, 1, 3, w31, w32);
    step_done_length(lt, 2, 4, w32, w33);
    step_done_length(lt, 5, 6, w33, w34);
    step_done_length(lt, 9, 10, w34, w35);
    step_done_length(lt, 1, 2, w35, w36);
    step_done_length(lt, 3, 4, w36, w37);
    step_done_length(lt, 5, 7, w37, w38);
    step_done_length(lt, 6, 8, w38, w39);
    step_done_length(lt, 2, 3, w39, w40);
    step_done_length(lt, 4, 5, w40, w41);
    step_done_length(lt, 6, 7, w41, w42);
    step_done_length(lt, 8, 9, w42, w43);
    step_done_length(lt, 3, 4, w43, w44);
    step_done_length(lt, 5, 6, w44, w45);
    step_done_same(lt, 0, 12, w0, w1, 1);
    step_done_same(lt, 0, 12, w0, w1, 2);
    step_done_same(lt, 0, 12, w0, w1, 3);
    step_done_same(lt, 0, 12, w0, w1, 4);
    step_done_same(lt, 0, 12, w0, w1, 5);
    step_done_same(lt, 0, 12, w0, w1, 6);
    step_done_same(lt, 0, 12, w0, w1, 7);
    step_done_same(lt, 0, 12, w0, w1, 8);
    step_done_same(lt, 0, 12, w0, w1, 9);
    step_done_same(lt, 0, 12, w0, w1, 10);
    step_done_same(lt, 0, 12, w0, w1, 11);
    step_done_same(lt, 1, 10, w1, w2, 0);
    step_done_same(lt, 1, 10, w1, w2, 2);
    step_done_same(lt, 1, 10, w1, w2, 3);
    step_done_same(lt, 1, 10, w1, w2, 4);
    step_done_same(lt, 1, 10, w1, w2, 5);
    step_done_same(lt, 1, 10, w1, w2, 6);
    step_done_same(lt, 1, 10, w1, w2, 7);
    step_done_same(lt, 1, 10, w1, w2, 8);
    step_done_same(lt, 1, 10, w1, w2, 9);
    step_done_same(lt, 1, 10, w1, w2, 11);
    step_done_same(lt, 1, 10, w1, w2, 12);
    step_done_same(lt, 2, 9, w2, w3, 0);
    step_done_same(lt, 2, 9, w2, w3, 1);
    step_done_same(lt, 2, 9, w2, w3, 3);
    step_done_same(lt, 2, 9, w2, w3, 4);
    step_done_same(lt, 2, 9, w2, w3, 5);
    step_done_same(lt, 2, 9, w2, w3, 6);
    step_done_same(lt, 2, 9, w2, w3, 7);
    step_done_same(lt, 2, 9, w2, w3, 8);
    step_done_same(lt, 2, 9, w2, w3, 10);
    step_done_same(lt, 2, 9, w2, w3, 11);
    step_done_same(lt, 2, 9, w2, w3, 12);
    step_done_same(lt, 3, 7, w3, w4, 0);
    step_done_same(lt, 3, 7, w3, w4, 1);
    step_done_same(lt, 3, 7, w3, w4, 2);
    step_done_same(lt, 3, 7, w3, w4, 4);
    step_done_same(lt, 3, 7, w3, w4, 5);
    step_done_same(lt, 3, 7, w3, w4, 6);
    step_done_same(lt, 3, 7, w3, w4, 8);
    step_done_same(lt, 3, 7, w3, w4, 9);
    step_done_same(lt, 3, 7, w3, w4, 10);
    step_done_same(lt, 3, 7, w3, w4, 11);
    step_done_same(lt, 3, 7, w3, w4, 12);
    step_done_same(lt, 5, 11, w4, w5, 0);
    step_done_same(lt, 5, 11, w4, w5, 1);
    step_done_same(lt, 5, 11, w4, w5, 2);
    step_done_same(lt, 5, 11, w4, w5, 3);
    step_done_same(lt, 5, 11, w4, w5, 4);
    step_done_same(lt, 5, 11, w4, w5, 6);
    step_done_same(lt, 5, 11, w4, w5, 7);
    step_done_same(lt, 5, 11, w4, w5, 8);
    step_done_same(lt, 5, 11, w4, w5, 9);
    step_done_same(lt, 5, 11, w4, w5, 10);
    step_done_same(lt, 5, 11, w4, w5, 12);
    step_done_same(lt, 6, 8, w5, w6, 0);
    step_done_same(lt, 6, 8, w5, w6, 1);
    step_done_same(lt, 6, 8, w5, w6, 2);
    step_done_same(lt, 6, 8, w5, w6, 3);
    step_done_same(lt, 6, 8, w5, w6, 4);
    step_done_same(lt, 6, 8, w5, w6, 5);
    step_done_same(lt, 6, 8, w5, w6, 7);
    step_done_same(lt, 6, 8, w5, w6, 9);
    step_done_same(lt, 6, 8, w5, w6, 10);
    step_done_same(lt, 6, 8, w5, w6, 11);
    step_done_same(lt, 6, 8, w5, w6, 12);
    step_done_same(lt, 1, 6, w6, w7, 0);
    step_done_same(lt, 1, 6, w6, w7, 2);
    step_done_same(lt, 1, 6, w6, w7, 3);
    step_done_same(lt, 1, 6, w6, w7, 4);
    step_done_same(lt, 1, 6, w6, w7, 5);
    step_done_same(lt, 1, 6, w6, w7, 7);
    step_done_same(lt, 1, 6, w6, w7, 8);
    step_done_same(lt, 1, 6, w6, w7, 9);
    step_done_same(lt, 1, 6, w6, w7, 10);
    step_done_same(lt, 1, 6, w6, w7, 11);
    step_done_same(lt, 1, 6, w6, w7, 12);
    step_done_same(lt, 2, 3, w7, w8, 0);
    step_done_same(lt, 2, 3, w7, w8, 1);
    step_done_same(lt, 2, 3, w7, w8, 4);
    step_done_same(lt, 2, 3, w7, w8, 5);
    step_done_same(lt, 2, 3, w7, w8, 6);
    step_done_same(lt, 2, 3, w7, w8, 7);
    step_done_same(lt, 2, 3, w7, w8, 8);
    step_done_same(lt, 2, 3, w7, w8, 9);
    step_done_same(lt, 2, 3, w7, w8, 10);
    step_done_same(lt, 2, 3, w7, w8, 11);
    step_done_same(lt, 2, 3, w7, w8, 12);
    step_done_same(lt, 4, 11, w8, w9, 0);
    step_done_same(lt, 4, 11, w8, w9, 1);
    step_done_same(lt, 4, 11, w8, w9, 2);
    step_done_same(lt, 4, 11, w8, w9, 3);
    step_done_same(lt, 4, 11, w8, w9, 5);
    step_done_same(lt, 4, 11, w8, w9, 6);
    step_done_same(lt, 4, 11, w8, w9, 7);
    step_done_same(lt, 4, 11, w8, w9, 8);
    step_done_same(lt, 4, 11, w8, w9, 9);
    step_done_same(lt, 4, 11, w8, w9, 10);
    step_done_same(lt, 4, 11, w8, w9, 12);
    step_done_same(lt, 7, 9, w9, w10, 0);
    step_done_same(lt, 7, 9, w9, w10, 1);
    step_done_same(lt, 7, 9, w9, w10, 2);
    step_done_same(lt, 7, 9, w9, w10, 3);
    step_done_same(lt, 7, 9, w9, w10, 4);
    step_done_same(lt, 7, 9, w9, w10, 5);
    step_done_same(lt, 7, 9, w9, w10, 6);
    step_done_same(lt, 7, 9, w9, w10, 8);
    step_done_same(lt, 7, 9, w9, w10, 10);
    step_done_same(lt, 7, 9, w9, w10, 11);
    step_done_same(lt, 7, 9, w9, w10, 12);
    step_done_same(lt, 8, 10, w10, w11, 0);
    step_done_same(lt, 8, 10, w10, w11, 1);
    step_done_same(lt, 8, 10, w10, w11, 2);
    step_done_same(lt, 8, 10, w10, w11, 3);
    step_done_same(lt, 8, 10, w10, w11, 4);
    step_done_same(lt, 8, 10, w10, w11, 5);
    step_done_same(lt, 8, 10, w10, w11, 6);
    step_done_same(lt, 8, 10, w10, w11, 7);
    step_done_same(lt, 8, 10, w10, w11, 9);
    step_done_same(lt, 8, 10, w10, w11, 11);
    step_done_same(lt, 8, 10, w10, w11, 12);
    step_done_same(lt, 0, 4, w11, w12, 1);
    step_done_same(lt, 0, 4, w11, w12, 2);
    step_done_same(lt, 0, 4, w11, w12, 3);
    step_done_same(lt, 0, 4, w11, w12, 5);
    step_done_same(lt, 0, 4, w11, w12, 6);
    step_done_same(lt, 0, 4, w11, w12, 7);
    step_done_same(lt, 0, 4, w11, w12, 8);
    step_done_same(lt, 0, 4, w11, w12, 9);
    step_done_same(lt, 0, 4, w11, w12, 10);
    step_done_same(lt, 0, 4, w11, w12, 11);
    step_done_same(lt, 0, 4, w11, w12, 12);
    step_done_same(lt, 1, 2, w12, w13, 0);
    step_done_same(lt, 1, 2, w12, w13, 3);
    step_done_same(lt, 1, 2, w12, w13, 4);
    step_done_same(lt, 1, 2, w12, w13, 5);
    step_done_same(lt, 1, 2, w12, w13, 6);
    step_done_same(lt, 1, 2, w12, w13, 7);
    step_done_same(lt, 1, 2, w12, w13, 8);
    step_done_same(lt, 1, 2, w12, w13, 9);
    step_done_same(lt, 1, 2, w12, w13, 10);
    step_done_same(lt, 1, 2, w12, w13, 11);
    step_done_same(lt, 1, 2, w12, w13, 12);
    step_done_same(lt, 3, 6, w13, w14, 0);
    step_done_same(lt, 3, 6, w13, w14, 1);
    step_done_same(lt, 3, 6, w13, w14, 2);
    step_done_same(lt, 3, 6, w13, w14, 4);
    step_done_same(lt, 3, 6, w13, w14, 5);
    step_done_same(lt, 3, 6, w13, w14, 7);
    step_done_same(lt, 3, 6, w13, w14, 8);
    step_done_same(lt, 3, 6, w13, w14, 9);
    step_done_same(lt, 3, 6, w13, w14, 10);
    step_done_same(lt, 3, 6, w13, w14, 11);
    step_done_same(lt, 3, 6, w13, w14, 12);
    step_done_same(lt, 7, 8, w14, w15, 0);
    step_done_same(lt, 7, 8, w14, w15, 1);
    step_done_same(lt, 7, 8, w14, w15, 2);
    step_done_same(lt, 7, 8, w14, w15, 3);
    step_done_same(lt, 7, 8, w14, w15, 4);
    step_done_same(lt, 7, 8, w14, w15, 5);
    step_done_same(lt, 7, 8, w14, w15, 6);
    step_done_same(lt, 7, 8, w14, w15, 9);
    step_done_same(lt, 7, 8, w14, w15, 10);
    step_done_same(lt, 7, 8, w14, w15, 11);
    step_done_same(lt, 7, 8, w14, w15, 12);
    step_done_same(lt, 9, 10, w15, w16, 0);
    step_done_same(lt, 9, 10, w15, w16, 1);
    step_done_same(lt, 9, 10, w15, w16, 2);
    step_done_same(lt, 9, 10, w15, w16, 3);
    step_done_same(lt, 9, 10, w15, w16, 4);
    step_done_same(lt, 9, 10, w15, w16, 5);
    step_done_same(lt, 9, 10, w15, w16, 6);
    step_done_same(lt, 9, 10, w15, w16, 7);
    step_done_same(lt, 9, 10, w15, w16, 8);
    step_done_same(lt, 9, 10, w15, w16, 11);
    step_done_same(lt, 9, 10, w15, w16, 12);
    step_done_same(lt, 11, 12, w16, w17, 0);
    step_done_same(lt, 11, 12, w16, w17, 1);
    step_done_same(lt, 11, 12, w16, w17, 2);
    step_done_same(lt, 11, 12, w16, w17, 3);
    step_done_same(lt, 11, 12, w16, w17, 4);
    step_done_same(lt, 11, 12, w16, w17, 5);
    step_done_same(lt, 11, 12, w16, w17, 6);
    step_done_same(lt, 11, 12, w16, w17, 7);
    step_done_same(lt, 11, 12, w16, w17, 8);
    step_done_same(lt, 11, 12, w16, w17, 9);
    step_done_same(lt, 11, 12, w16, w17, 10);
    step_done_same(lt, 4, 6, w17, w18, 0);
    step_done_same(lt, 4, 6, w17, w18, 1);
    step_done_same(lt, 4, 6, w17, w18, 2);
    step_done_same(lt, 4, 6, w17, w18, 3);
    step_done_same(lt, 4, 6, w17, w18, 5);
    step_done_same(lt, 4, 6, w17, w18, 7);
    step_done_same(lt, 4, 6, w17, w18, 8);
    step_done_same(lt, 4, 6, w17, w18, 9);
    step_done_same(lt, 4, 6, w17, w18, 10);
    step_done_same(lt, 4, 6, w17, w18, 11);
    step_done_same(lt, 4, 6, w17, w18, 12);
    step_done_same(lt, 5, 9, w18, w19, 0);
    step_done_same(lt, 5, 9, w18, w19, 1);
    step_done_same(lt, 5, 9, w18, w19, 2);
    step_done_same(lt, 5, 9, w18, w19, 3);
    step_done_same(lt, 5, 9, w18, w19, 4);
    step_done_same(lt, 5, 9, w18, w19, 6);
    step_done_same(lt, 5, 9, w18, w19, 7);
    step_done_same(lt, 5, 9, w18, w19, 8);
    step_done_same(lt, 5, 9, w18, w19, 10);
    step_done_same(lt, 5, 9, w18, w19, 11);
    step_done_same(lt, 5, 9, w18, w19, 12);
    step_done_same(lt, 8, 11, w19, w20, 0);
    step_done_same(lt, 8, 11, w19, w20, 1);
    step_done_same(lt, 8, 11, w19, w20, 2);
    step_done_same(lt, 8, 11, w19, w20, 3);
    step_done_same(lt, 8, 11, w19, w20, 4);
    step_done_same(lt, 8, 11, w19, w20, 5);
    step_done_same(lt, 8, 11, w19, w20, 6);
    step_done_same(lt, 8, 11, w19, w20, 7);
    step_done_same(lt, 8, 11, w19, w20, 9);
    step_done_same(lt, 8, 11, w19, w20, 10);
    step_done_same(lt, 8, 11, w19, w20, 12);
    step_done_same(lt, 10, 12, w20, w21, 0);
    step_done_same(lt, 10, 12, w20, w21, 1);
    step_done_same(lt, 10, 12, w20, w21, 2);
    step_done_same(lt, 10, 12, w20, w21, 3);
    step_done_same(lt, 10, 12, w20, w21, 4);
    step_done_same(lt, 10, 12, w20, w21, 5);
    step_done_same(lt, 10, 12, w20, w21, 6);
    step_done_same(lt, 10, 12, w20, w21, 7);
    step_done_same(lt, 10, 12, w20, w21, 8);
    step_done_same(lt, 10, 12, w20, w21, 9);
    step_done_same(lt, 10, 12, w20, w21, 11);
    step_done_same(lt, 0, 5, w21, w22, 1);
    step_done_same(lt, 0, 5, w21, w22, 2);
    step_done_same(lt, 0, 5, w21, w22, 3);
    step_done_same(lt, 0, 5, w21, w22, 4);
    step_done_same(lt, 0, 5, w21, w22, 6);
    step_done_same(lt, 0, 5, w21, w22, 7);
    step_done_same(lt, 0, 5, w21, w22, 8);
    step_done_same(lt, 0, 5, w21, w22, 9);
    step_done_same(lt, 0, 5, w21, w22, 10);
    step_done_same(lt, 0, 5, w21, w22, 11);
    step_done_same(lt, 0, 5, w21, w22, 12);
    step_done_same(lt, 3, 8, w22, w23, 0);
    step_done_same(lt, 3, 8, w22, w23, 1);
    step_done_same(lt, 3, 8, w22, w23, 2);
    step_done_same(lt, 3, 8, w22, w23, 4);
    step_done_same(lt, 3, 8, w22, w23, 5);
    step_done_same(lt, 3, 8, w22, w23, 6);
    step_done_same(lt, 3, 8, w22, w23, 7);
    step_done_same(lt, 3, 8, w22, w23, 9);
    step_done_same(lt, 3, 8, w22, w23, 10);
    step_done_same(lt, 3, 8, w22, w23, 11);
    step_done_same(lt, 3, 8, w22, w23, 12);
    step_done_same(lt, 4, 7, w23, w24, 0);
    step_done_same(lt, 4, 7, w23, w24, 1);
    step_done_same(lt, 4, 7, w23, w24, 2);
    step_done_same(lt, 4, 7, w23, w24, 3);
    step_done_same(lt, 4, 7, w23, w24, 5);
    step_done_same(lt, 4, 7, w23, w24, 6);
    step_done_same(lt, 4, 7, w23, w24, 8);
    step_done_same(lt, 4, 7, w23, w24, 9);
    step_done_same(lt, 4, 7, w23, w24, 10);
    step_done_same(lt, 4, 7, w23, w24, 11);
    step_done_same(lt, 4, 7, w23, w24, 12);
    step_done_same(lt, 6, 11, w24, w25, 0);
    step_done_same(lt, 6, 11, w24, w25, 1);
    step_done_same(lt, 6, 11, w24, w25, 2);
    step_done_same(lt, 6, 11, w24, w25, 3);
    step_done_same(lt, 6, 11, w24, w25, 4);
    step_done_same(lt, 6, 11, w24, w25, 5);
    step_done_same(lt, 6, 11, w24, w25, 7);
    step_done_same(lt, 6, 11, w24, w25, 8);
    step_done_same(lt, 6, 11, w24, w25, 9);
    step_done_same(lt, 6, 11, w24, w25, 10);
    step_done_same(lt, 6, 11, w24, w25, 12);
    step_done_same(lt, 9, 10, w25, w26, 0);
    step_done_same(lt, 9, 10, w25, w26, 1);
    step_done_same(lt, 9, 10, w25, w26, 2);
    step_done_same(lt, 9, 10, w25, w26, 3);
    step_done_same(lt, 9, 10, w25, w26, 4);
    step_done_same(lt, 9, 10, w25, w26, 5);
    step_done_same(lt, 9, 10, w25, w26, 6);
    step_done_same(lt, 9, 10, w25, w26, 7);
    step_done_same(lt, 9, 10, w25, w26, 8);
    step_done_same(lt, 9, 10, w25, w26, 11);
    step_done_same(lt, 9, 10, w25, w26, 12);
    step_done_same(lt, 0, 1, w26, w27, 2);
    step_done_same(lt, 0, 1, w26, w27, 3);
    step_done_same(lt, 0, 1, w26, w27, 4);
    step_done_same(lt, 0, 1, w26, w27, 5);
    step_done_same(lt, 0, 1, w26, w27, 6);
    step_done_same(lt, 0, 1, w26, w27, 7);
    step_done_same(lt, 0, 1, w26, w27, 8);
    step_done_same(lt, 0, 1, w26, w27, 9);
    step_done_same(lt, 0, 1, w26, w27, 10);
    step_done_same(lt, 0, 1, w26, w27, 11);
    step_done_same(lt, 0, 1, w26, w27, 12);
    step_done_same(lt, 2, 5, w27, w28, 0);
    step_done_same(lt, 2, 5, w27, w28, 1);
    step_done_same(lt, 2, 5, w27, w28, 3);
    step_done_same(lt, 2, 5, w27, w28, 4);
    step_done_same(lt, 2, 5, w27, w28, 6);
    step_done_same(lt, 2, 5, w27, w28, 7);
    step_done_same(lt, 2, 5, w27, w28, 8);
    step_done_same(lt, 2, 5, w27, w28, 9);
    step_done_same(lt, 2, 5, w27, w28, 10);
    step_done_same(lt, 2, 5, w27, w28, 11);
    step_done_same(lt, 2, 5, w27, w28, 12);
    step_done_same(lt, 6, 9, w28, w29, 0);
    step_done_same(lt, 6, 9, w28, w29, 1);
    step_done_same(lt, 6, 9, w28, w29, 2);
    step_done_same(lt, 6, 9, w28, w29, 3);
    step_done_same(lt, 6, 9, w28, w29, 4);
    step_done_same(lt, 6, 9, w28, w29, 5);
    step_done_same(lt, 6, 9, w28, w29, 7);
    step_done_same(lt, 6, 9, w28, w29, 8);
    step_done_same(lt, 6, 9, w28, w29, 10);
    step_done_same(lt, 6, 9, w28, w29, 11);
    step_done_same(lt, 6, 9, w28, w29, 12);
    step_done_same(lt, 7, 8, w29, w30, 0);
    step_done_same(lt, 7, 8, w29, w30, 1);
    step_done_same(lt, 7, 8, w29, w30, 2);
    step_done_same(lt, 7, 8, w29, w30, 3);
    step_done_same(lt, 7, 8, w29, w30, 4);
    step_done_same(lt, 7, 8, w29, w30, 5);
    step_done_same(lt, 7, 8, w29, w30, 6);
    step_done_same(lt, 7, 8, w29, w30, 9);
    step_done_same(lt, 7, 8, w29, w30, 10);
    step_done_same(lt, 7, 8, w29, w30, 11);
    step_done_same(lt, 7, 8, w29, w30, 12);
    step_done_same(lt, 10, 11, w30, w31, 0);
    step_done_same(lt, 10, 11, w30, w31, 1);
    step_done_same(lt, 10, 11, w30, w31, 2);
    step_done_same(lt, 10, 11, w30, w31, 3);
    step_done_same(lt, 10, 11, w30, w31, 4);
    step_done_same(lt, 10, 11, w30, w31, 5);
    step_done_same(lt, 10, 11, w30, w31, 6);
    step_done_same(lt, 10, 11, w30, w31, 7);
    step_done_same(lt, 10, 11, w30, w31, 8);
    step_done_same(lt, 10, 11, w30, w31, 9);
    step_done_same(lt, 10, 11, w30, w31, 12);
    step_done_same(lt, 1, 3, w31, w32, 0);
    step_done_same(lt, 1, 3, w31, w32, 2);
    step_done_same(lt, 1, 3, w31, w32, 4);
    step_done_same(lt, 1, 3, w31, w32, 5);
    step_done_same(lt, 1, 3, w31, w32, 6);
    step_done_same(lt, 1, 3, w31, w32, 7);
    step_done_same(lt, 1, 3, w31, w32, 8);
    step_done_same(lt, 1, 3, w31, w32, 9);
    step_done_same(lt, 1, 3, w31, w32, 10);
    step_done_same(lt, 1, 3, w31, w32, 11);
    step_done_same(lt, 1, 3, w31, w32, 12);
    step_done_same(lt, 2, 4, w32, w33, 0);
    step_done_same(lt, 2, 4, w32, w33, 1);
    step_done_same(lt, 2, 4, w32, w33, 3);
    step_done_same(lt, 2, 4, w32, w33, 5);
    step_done_same(lt, 2, 4, w32, w33, 6);
    step_done_same(lt, 2, 4, w32, w33, 7);
    step_done_same(lt, 2, 4, w32, w33, 8);
    step_done_same(lt, 2, 4, w32, w33, 9);
    step_done_same(lt, 2, 4, w32, w33, 10);
    step_done_same(lt, 2, 4, w32, w33, 11);
    step_done_same(lt, 2, 4, w32, w33, 12);
    step_done_same(lt, 5, 6, w33, w34, 0);
    step_done_same(lt, 5, 6, w33, w34, 1);
    step_done_same(lt, 5, 6, w33, w34, 2);
    step_done_same(lt, 5, 6, w33, w34, 3);
    step_done_same(lt, 5, 6, w33, w34, 4);
    step_done_same(lt, 5, 6, w33, w34, 7);
    step_done_same(lt, 5, 6, w33, w34, 8);
    step_done_same(lt, 5, 6, w33, w34, 9);
    step_done_same(lt, 5, 6, w33, w34, 10);
    step_done_same(lt, 5, 6, w33, w34, 11);
    step_done_same(lt, 5, 6, w33, w34, 12);
    step_done_same(lt, 9, 10, w34, w35, 0);
    step_done_same(lt, 9, 10, w34, w35, 1);
    step_done_same(lt, 9, 10, w34, w35, 2);
    step_done_same(lt, 9, 10, w34, w35, 3);
    step_done_same(lt, 9, 10, w34, w35, 4);
    step_done_same(lt, 9, 10, w34, w35, 5);
    step_done_same(lt, 9, 10, w34, w35, 6);
    step_done_same(lt, 9, 10, w34, w35, 7);
    step_done_same(lt, 9, 10, w34, w35, 8);
    step_done_same(lt, 9, 10, w34, w35, 11);
    step_done_same(lt, 9, 10, w34, w35, 12);
    step_done_same(lt, 1, 2, w35, w36, 0);
    step_done_same(lt, 1, 2, w35, w36, 3);
    step_done_same(lt, 1, 2, w35, w36, 4);
    step_done_same(lt, 1, 2, w35, w36, 5);
    step_done_same(lt, 1, 2, w35, w36, 6);
    step_done_same(lt, 1, 2, w35, w36, 7);
    step_done_same(lt, 1, 2, w35, w36, 8);
    step_done_same(lt, 1, 2, w35, w36, 9);
    step_done_same(lt, 1, 2, w35, w36, 10);
    step_done_same(lt, 1, 2, w35, w36, 11);
    step_done_same(lt, 1, 2, w35, w36, 12);
    step_done_same(lt, 3, 4, w36, w37, 0);
    step_done_same(lt, 3, 4, w36, w37, 1);
    step_done_same(lt, 3, 4, w36, w37, 2);
    step_done_same(lt, 3, 4, w36, w37, 5);
    step_done_same(lt, 3, 4, w36, w37, 6);
    step_done_same(lt, 3, 4, w36, w37, 7);
    step_done_same(lt, 3, 4, w36, w37, 8);
    step_done_same(lt, 3, 4, w36, w37, 9);
    step_done_same(lt, 3, 4, w36, w37, 10);
    step_done_same(lt, 3, 4, w36, w37, 11);
    step_done_same(lt, 3, 4, w36, w37, 12);
    step_done_same(lt, 5, 7, w37, w38, 0);
    step_done_same(lt, 5, 7, w37, w38, 1);
    step_done_same(lt, 5, 7, w37, w38, 2);
    step_done_same(lt, 5, 7, w37, w38, 3);
    step_done_same(lt, 5, 7, w37, w38, 4);
    step_done_same(lt, 5, 7, w37, w38, 6);
    step_done_same(lt, 5, 7, w37, w38, 8);
    step_done_same(lt, 5, 7, w37, w38, 9);
    step_done_same(lt, 5, 7, w37, w38, 10);
    step_done_same(lt, 5, 7, w37, w38, 11);
    step_done_same(lt, 5, 7, w37, w38, 12);
    step_done_same(lt, 6, 8, w38, w39, 0);
    step_done_same(lt, 6, 8, w38, w39, 1);
    step_done_same(lt, 6, 8, w38, w39, 2);
    step_done_same(lt, 6, 8, w38, w39, 3);
    step_done_same(lt, 6, 8, w38, w39, 4);
    step_done_same(lt, 6, 8, w38, w39, 5);
    step_done_same(lt, 6, 8, w38, w39, 7);
    step_done_same(lt, 6, 8, w38, w39, 9);
    step_done_same(lt, 6, 8, w38, w39, 10);
    step_done_same(lt, 6, 8, w38, w39, 11);
    step_done_same(lt, 6, 8, w38, w39, 12);
    step_done_same(lt, 2, 3, w39, w40, 0);
    step_done_same(lt, 2, 3, w39, w40, 1);
    step_done_same(lt, 2, 3, w39, w40, 4);
    step_done_same(lt, 2, 3, w39, w40, 5);
    step_done_same(lt, 2, 3, w39, w40, 6);
    step_done_same(lt, 2, 3, w39, w40, 7);
    step_done_same(lt, 2, 3, w39, w40, 8);
    step_done_same(lt, 2, 3, w39, w40, 9);
    step_done_same(lt, 2, 3, w39, w40, 10);
    step_done_same(lt, 2, 3, w39, w40, 11);
    step_done_same(lt, 2, 3, w39, w40, 12);
    step_done_same(lt, 4, 5, w40, w41, 0);
    step_done_same(lt, 4, 5, w40, w41, 1);
    step_done_same(lt, 4, 5, w40, w41, 2);
    step_done_same(lt, 4, 5, w40, w41, 3);
    step_done_same(lt, 4, 5, w40, w41, 6);
    step_done_same(lt, 4, 5, w40, w41, 7);
    step_done_same(lt, 4, 5, w40, w41, 8);
    step_done_same(lt, 4, 5, w40, w41, 9);
    step_done_same(lt, 4, 5, w40, w41, 10);
    step_done_same(lt, 4, 5, w40, w41, 11);
    step_done_same(lt, 4, 5, w40, w41, 12);
    step_done_same(lt, 6, 7, w41, w42, 0);
    step_done_same(lt, 6, 7, w41, w42, 1);
    step_done_same(lt, 6, 7, w41, w42, 2);
    step_done_same(lt, 6, 7, w41, w42, 3);
    step_done_same(lt, 6, 7, w41, w42, 4);
    step_done_same(lt, 6, 7, w41, w42, 5);
    step_done_same(lt, 6, 7, w41, w42, 8);
    step_done_same(lt, 6, 7, w41, w42, 9);
    step_done_same(lt, 6, 7, w41, w42, 10);
    step_done_same(lt, 6, 7, w41, w42, 11);
    step_done_same(lt, 6, 7, w41, w42, 12);
    step_done_same(lt, 8, 9, w42, w43, 0);
    step_done_same(lt, 8, 9, w42, w43, 1);
    step_done_same(lt, 8, 9, w42, w43, 2);
    step_done_same(lt, 8, 9, w42, w43, 3);
    step_done_same(lt, 8, 9, w42, w43, 4);
    step_done_same(lt, 8, 9, w42, w43, 5);
    step_done_same(lt, 8, 9, w42, w43, 6);
    step_done_same(lt, 8, 9, w42, w43, 7);
    step_done_same(lt, 8, 9, w42, w43, 10);
    step_done_same(lt, 8, 9, w42, w43, 11);
    step_done_same(lt, 8, 9, w42, w43, 12);
    step_done_same(lt, 3, 4, w43, w44, 0);
    step_done_same(lt, 3, 4, w43, w44, 1);
    step_done_same(lt, 3, 4, w43, w44, 2);
    step_done_same(lt, 3, 4, w43, w44, 5);
    step_done_same(lt, 3, 4, w43, w44, 6);
    step_done_same(lt, 3, 4, w43, w44, 7);
    step_done_same(lt, 3, 4, w43, w44, 8);
    step_done_same(lt, 3, 4, w43, w44, 9);
    step_done_same(lt, 3, 4, w43, w44, 10);
    step_done_same(lt, 3, 4, w43, w44, 11);
    step_done_same(lt, 3, 4, w43, w44, 12);
    step_done_same(lt, 5, 6, w44, w45, 0);
    step_done_same(lt, 5, 6, w44, w45, 1);
    step_done_same(lt, 5, 6, w44, w45, 2);
    step_done_same(lt, 5, 6, w44, w45, 3);
    step_done_same(lt, 5, 6, w44, w45, 4);
    step_done_same(lt, 5, 6, w44, w45, 7);
    step_done_same(lt, 5, 6, w44, w45, 8);
    step_done_same(lt, 5, 6, w44, w45, 9);
    step_done_same(lt, 5, 6, w44, w45, 10);
    step_done_same(lt, 5, 6, w44, w45, 11);
    step_done_same(lt, 5, 6, w44, w45, 12);
}

lem net13_adj0<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(1, w45), nth(0, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(1, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(0, w45)), apply_lt(lt, c, c));
}

lem net13_adj1<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(2, w45), nth(1, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(2, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(1, w45)), apply_lt(lt, c, c));
}

lem net13_adj2<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(3, w45), nth(2, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(3, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(2, w45)), apply_lt(lt, c, c));
}

lem net13_adj3<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(4, w45), nth(3, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(4, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(3, w45)), apply_lt(lt, c, c));
}

lem net13_adj4<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(5, w45), nth(4, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(5, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(4, w45)), apply_lt(lt, c, c));
}

lem net13_adj5<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(6, w45), nth(5, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(6, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(5, w45)), apply_lt(lt, c, c));
}

lem net13_adj6<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(7, w45), nth(6, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(7, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(6, w45)), apply_lt(lt, c, c));
}

lem net13_adj7<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(8, w45), nth(7, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(8, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(7, w45)), apply_lt(lt, c, c));
}

lem net13_adj8<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(9, w45), nth(8, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(9, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(8, w45)), apply_lt(lt, c, c));
}

lem net13_adj9<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(10, w45), nth(9, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(10, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(9, w45)), apply_lt(lt, c, c));
}

lem net13_adj10<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(11, w45), nth(10, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(11, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(10, w45)), apply_lt(lt, c, c));
}

lem net13_adj11<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45) &*& length(w1) == length(w0) &*& length(w2) == length(w0) &*& length(w3) == length(w0) &*& length(w4) == length(w0) &*& length(w5) == length(w0) &*& length(w6) == length(w0) &*& length(w7) == length(w0) &*& length(w8) == length(w0) &*& length(w9) == length(w0) &*& length(w10) == length(w0) &*& length(w11) == length(w0) &*& length(w12) == length(w0) &*& length(w13) == length(w0) &*& length(w14) == length(w0) &*& length(w15) == length(w0) &*& length(w16) == length(w0) &*& length(w17) == length(w0) &*& length(w18) == length(w0) &*& length(w19) == length(w0) &*& length(w20) == length(w0) &*& length(w21) == length(w0) &*& length(w22) == length(w0) &*& length(w23) == length(w0) &*& length(w24) == length(w0) &*& length(w25) == length(w0) &*& length(w26) == length(w0) &*& length(w27) == length(w0) &*& length(w28) == length(w0) &*& length(w29) == length(w0) &*& length(w30) == length(w0) &*& length(w31) == length(w0) &*& length(w32) == length(w0) &*& length(w33) == length(w0) &*& length(w34) == length(w0) &*& length(w35) == length(w0) &*& length(w36) == length(w0) &*& length(w37) == length(w0) &*& length(w38) == length(w0) &*& length(w39) == length(w0) &*& length(w40) == length(w0) &*& length(w41) == length(w0) &*& length(w42) == length(w0) &*& length(w43) == length(w0) &*& length(w44) == length(w0) &*& length(w45) == length(w0) &*&
        nth(1, w1) == nth(1, w0) &*&
        nth(2, w1) == nth(2, w0) &*&
        nth(3, w1) == nth(3, w0) &*&
        nth(4, w1) == nth(4, w0) &*&
        nth(5, w1) == nth(5, w0) &*&
        nth(6, w1) == nth(6, w0) &*&
        nth(7, w1) == nth(7, w0) &*&
        nth(8, w1) == nth(8, w0) &*&
        nth(9, w1) == nth(9, w0) &*&
        nth(10, w1) == nth(10, w0) &*&
        nth(11, w1) == nth(11, w0) &*&
        nth(0, w2) == nth(0, w1) &*&
        nth(2, w2) == nth(2, w1) &*&
        nth(3, w2) == nth(3, w1) &*&
        nth(4, w2) == nth(4, w1) &*&
        nth(5, w2) == nth(5, w1) &*&
        nth(6, w2) == nth(6, w1) &*&
        nth(7, w2) == nth(7, w1) &*&
        nth(8, w2) == nth(8, w1) &*&
        nth(9, w2) == nth(9, w1) &*&
        nth(11, w2) == nth(11, w1) &*&
        nth(12, w2) == nth(12, w1) &*&
        nth(0, w3) == nth(0, w2) &*&
        nth(1, w3) == nth(1, w2) &*&
        nth(3, w3) == nth(3, w2) &*&
        nth(4, w3) == nth(4, w2) &*&
        nth(5, w3) == nth(5, w2) &*&
        nth(6, w3) == nth(6, w2) &*&
        nth(7, w3) == nth(7, w2) &*&
        nth(8, w3) == nth(8, w2) &*&
        nth(10, w3) == nth(10, w2) &*&
        nth(11, w3) == nth(11, w2) &*&
        nth(12, w3) == nth(12, w2) &*&
        nth(0, w4) == nth(0, w3) &*&
        nth(1, w4) == nth(1, w3) &*&
        nth(2, w4) == nth(2, w3) &*&
        nth(4, w4) == nth(4, w3) &*&
        nth(5, w4) == nth(5, w3) &*&
        nth(6, w4) == nth(6, w3) &*&
        nth(8, w4) == nth(8, w3) &*&
        nth(9, w4) == nth(9, w3) &*&
        nth(10, w4) == nth(10, w3) &*&
        nth(11, w4) == nth(11, w3) &*&
        nth(12, w4) == nth(12, w3) &*&
        nth(0, w5) == nth(0, w4) &*&
        nth(1, w5) == nth(1, w4) &*&
        nth(2, w5) == nth(2, w4) &*&
        nth(3, w5) == nth(3, w4) &*&
        nth(4, w5) == nth(4, w4) &*&
        nth(6, w5) == nth(6, w4) &*&
        nth(7, w5) == nth(7, w4) &*&
        nth(8, w5) == nth(8, w4) &*&
        nth(9, w5) == nth(9, w4) &*&
        nth(10, w5) == nth(10, w4) &*&
        nth(12, w5) == nth(12, w4) &*&
        nth(0, w6) == nth(0, w5) &*&
        nth(1, w6) == nth(1, w5) &*&
        nth(2, w6) == nth(2, w5) &*&
        nth(3, w6) == nth(3, w5) &*&
        nth(4, w6) == nth(4, w5) &*&
        nth(5, w6) == nth(5, w5) &*&
        nth(7, w6) == nth(7, w5) &*&
        nth(9, w6) == nth(9, w5) &*&
        nth(10, w6) == nth(10, w5) &*&
        nth(11, w6) == nth(11, w5) &*&
        nth(12, w6) == nth(12, w5) &*&
        nth(0, w7) == nth(0, w6) &*&
        nth(2, w7) == nth(2, w6) &*&
        nth(3, w7) == nth(3, w6) &*&
        nth(4, w7) == nth(4, w6) &*&
        nth(5, w7) == nth(5, w6) &*&
        nth(7, w7) == nth(7, w6) &*&
        nth(8, w7) == nth(8, w6) &*&
        nth(9, w7) == nth(9, w6) &*&
        nth(10, w7) == nth(10, w6) &*&
        nth(11, w7) == nth(11, w6) &*&
        nth(12, w7) == nth(12, w6) &*&
        nth(0, w8) == nth(0, w7) &*&
        nth(1, w8) == nth(1, w7) &*&
        nth(4, w8) == nth(4, w7) &*&
        nth(5, w8) == nth(5, w7) &*&
        nth(6, w8) == nth(6, w7) &*&
        nth(7, w8) == nth(7, w7) &*&
        nth(8, w8) == nth(8, w7) &*&
        nth(9, w8) == nth(9, w7) &*&
        nth(10, w8) == nth(10, w7) &*&
        nth(11, w8) == nth(11, w7) &*&
        nth(12, w8) == nth(12, w7) &*&
        nth(0, w9) == nth(0, w8) &*&
        nth(1, w9) == nth(1, w8) &*&
        nth(2, w9) == nth(2, w8) &*&
        nth(3, w9) == nth(3, w8) &*&
        nth(5, w9) == nth(5, w8) &*&
        nth(6, w9) == nth(6, w8) &*&
        nth(7, w9) == nth(7, w8) &*&
        nth(8, w9) == nth(8, w8) &*&
        nth(9, w9) == nth(9, w8) &*&
        nth(10, w9) == nth(10, w8) &*&
        nth(12, w9) == nth(12, w8) &*&
        nth(0, w10) == nth(0, w9) &*&
        nth(1, w10) == nth(1, w9) &*&
        nth(2, w10) == nth(2, w9) &*&
        nth(3, w10) == nth(3, w9) &*&
        nth(4, w10) == nth(4, w9) &*&
        nth(5, w10) == nth(5, w9) &*&
        nth(6, w10) == nth(6, w9) &*&
        nth(8, w10) == nth(8, w9) &*&
        nth(10, w10) == nth(10, w9) &*&
        nth(11, w10) == nth(11, w9) &*&
        nth(12, w10) == nth(12, w9) &*&
        nth(0, w11) == nth(0, w10) &*&
        nth(1, w11) == nth(1, w10) &*&
        nth(2, w11) == nth(2, w10) &*&
        nth(3, w11) == nth(3, w10) &*&
        nth(4, w11) == nth(4, w10) &*&
        nth(5, w11) == nth(5, w10) &*&
        nth(6, w11) == nth(6, w10) &*&
        nth(7, w11) == nth(7, w10) &*&
        nth(9, w11) == nth(9, w10) &*&
        nth(11, w11) == nth(11, w10) &*&
        nth(12, w11) == nth(12, w10) &*&
        nth(1, w12) == nth(1, w11) &*&
        nth(2, w12) == nth(2, w11) &*&
        nth(3, w12) == nth(3, w11) &*&
        nth(5, w12) == nth(5, w11) &*&
        nth(6, w12) == nth(6, w11) &*&
        nth(7, w12) == nth(7, w11) &*&
        nth(8, w12) == nth(8, w11) &*&
        nth(9, w12) == nth(9, w11) &*&
        nth(10, w12) == nth(10, w11) &*&
        nth(11, w12) == nth(11, w11) &*&
        nth(12, w12) == nth(12, w11) &*&
        nth(0, w13) == nth(0, w12) &*&
        nth(3, w13) == nth(3, w12) &*&
        nth(4, w13) == nth(4, w12) &*&
        nth(5, w13) == nth(5, w12) &*&
        nth(6, w13) == nth(6, w12) &*&
        nth(7, w13) == nth(7, w12) &*&
        nth(8, w13) == nth(8, w12) &*&
        nth(9, w13) == nth(9, w12) &*&
        nth(10, w13) == nth(10, w12) &*&
        nth(11, w13) == nth(11, w12) &*&
        nth(12, w13) == nth(12, w12) &*&
        nth(0, w14) == nth(0, w13) &*&
        nth(1, w14) == nth(1, w13) &*&
        nth(2, w14) == nth(2, w13) &*&
        nth(4, w14) == nth(4, w13) &*&
        nth(5, w14) == nth(5, w13) &*&
        nth(7, w14) == nth(7, w13) &*&
        nth(8, w14) == nth(8, w13) &*&
        nth(9, w14) == nth(9, w13) &*&
        nth(10, w14) == nth(10, w13) &*&
        nth(11, w14) == nth(11, w13) &*&
        nth(12, w14) == nth(12, w13) &*&
        nth(0, w15) == nth(0, w14) &*&
        nth(1, w15) == nth(1, w14) &*&
        nth(2, w15) == nth(2, w14) &*&
        nth(3, w15) == nth(3, w14) &*&
        nth(4, w15) == nth(4, w14) &*&
        nth(5, w15) == nth(5, w14) &*&
        nth(6, w15) == nth(6, w14) &*&
        nth(9, w15) == nth(9, w14) &*&
        nth(10, w15) == nth(10, w14) &*&
        nth(11, w15) == nth(11, w14) &*&
        nth(12, w15) == nth(12, w14) &*&
        nth(0, w16) == nth(0, w15) &*&
        nth(1, w16) == nth(1, w15) &*&
        nth(2, w16) == nth(2, w15) &*&
        nth(3, w16) == nth(3, w15) &*&
        nth(4, w16) == nth(4, w15) &*&
        nth(5, w16) == nth(5, w15) &*&
        nth(6, w16) == nth(6, w15) &*&
        nth(7, w16) == nth(7, w15) &*&
        nth(8, w16) == nth(8, w15) &*&
        nth(11, w16) == nth(11, w15) &*&
        nth(12, w16) == nth(12, w15) &*&
        nth(0, w17) == nth(0, w16) &*&
        nth(1, w17) == nth(1, w16) &*&
        nth(2, w17) == nth(2, w16) &*&
        nth(3, w17) == nth(3, w16) &*&
        nth(4, w17) == nth(4, w16) &*&
        nth(5, w17) == nth(5, w16) &*&
        nth(6, w17) == nth(6, w16) &*&
        nth(7, w17) == nth(7, w16) &*&
        nth(8, w17) == nth(8, w16) &*&
        nth(9, w17) == nth(9, w16) &*&
        nth(10, w17) == nth(10, w16) &*&
        nth(0, w18) == nth(0, w17) &*&
        nth(1, w18) == nth(1, w17) &*&
        nth(2, w18) == nth(2, w17) &*&
        nth(3, w18) == nth(3, w17) &*&
        nth(5, w18) == nth(5, w17) &*&
        nth(7, w18) == nth(7, w17) &*&
        nth(8, w18) == nth(8, w17) &*&
        nth(9, w18) == nth(9, w17) &*&
        nth(10, w18) == nth(10, w17) &*&
        nth(11, w18) == nth(11, w17) &*&
        nth(12, w18) == nth(12, w17) &*&
        nth(0, w19) == nth(0, w18) &*&
        nth(1, w19) == nth(1, w18) &*&
        nth(2, w19) == nth(2, w18) &*&
        nth(3, w19) == nth(3, w18) &*&
        nth(4, w19) == nth(4, w18) &*&
        nth(6, w19) == nth(6, w18) &*&
        nth(7, w19) == nth(7, w18) &*&
        nth(8, w19) == nth(8, w18) &*&
        nth(10, w19) == nth(10, w18) &*&
        nth(11, w19) == nth(11, w18) &*&
        nth(12, w19) == nth(12, w18) &*&
        nth(0, w20) == nth(0, w19) &*&
        nth(1, w20) == nth(1, w19) &*&
        nth(2, w20) == nth(2, w19) &*&
        nth(3, w20) == nth(3, w19) &*&
        nth(4, w20) == nth(4, w19) &*&
        nth(5, w20) == nth(5, w19) &*&
        nth(6, w20) == nth(6, w19) &*&
        nth(7, w20) == nth(7, w19) &*&
        nth(9, w20) == nth(9, w19) &*&
        nth(10, w20) == nth(10, w19) &*&
        nth(12, w20) == nth(12, w19) &*&
        nth(0, w21) == nth(0, w20) &*&
        nth(1, w21) == nth(1, w20) &*&
        nth(2, w21) == nth(2, w20) &*&
        nth(3, w21) == nth(3, w20) &*&
        nth(4, w21) == nth(4, w20) &*&
        nth(5, w21) == nth(5, w20) &*&
        nth(6, w21) == nth(6, w20) &*&
        nth(7, w21) == nth(7, w20) &*&
        nth(8, w21) == nth(8, w20) &*&
        nth(9, w21) == nth(9, w20) &*&
        nth(11, w21) == nth(11, w20) &*&
        nth(1, w22) == nth(1, w21) &*&
        nth(2, w22) == nth(2, w21) &*&
        nth(3, w22) == nth(3, w21) &*&
        nth(4, w22) == nth(4, w21) &*&
        nth(6, w22) == nth(6, w21) &*&
        nth(7, w22) == nth(7, w21) &*&
        nth(8, w22) == nth(8, w21) &*&
        nth(9, w22) == nth(9, w21) &*&
        nth(10, w22) == nth(10, w21) &*&
        nth(11, w22) == nth(11, w21) &*&
        nth(12, w22) == nth(12, w21) &*&
        nth(0, w23) == nth(0, w22) &*&
        nth(1, w23) == nth(1, w22) &*&
        nth(2, w23) == nth(2, w22) &*&
        nth(4, w23) == nth(4, w22) &*&
        nth(5, w23) == nth(5, w22) &*&
        nth(6, w23) == nth(6, w22) &*&
        nth(7, w23) == nth(7, w22) &*&
        nth(9, w23) == nth(9, w22) &*&
        nth(10, w23) == nth(10, w22) &*&
        nth(11, w23) == nth(11, w22) &*&
        nth(12, w23) == nth(12, w22) &*&
        nth(0, w24) == nth(0, w23) &*&
        nth(1, w24) == nth(1, w23) &*&
        nth(2, w24) == nth(2, w23) &*&
        nth(3, w24) == nth(3, w23) &*&
        nth(5, w24) == nth(5, w23) &*&
        nth(6, w24) == nth(6, w23) &*&
        nth(8, w24) == nth(8, w23) &*&
        nth(9, w24) == nth(9, w23) &*&
        nth(10, w24) == nth(10, w23) &*&
        nth(11, w24) == nth(11, w23) &*&
        nth(12, w24) == nth(12, w23) &*&
        nth(0, w25) == nth(0, w24) &*&
        nth(1, w25) == nth(1, w24) &*&
        nth(2, w25) == nth(2, w24) &*&
        nth(3, w25) == nth(3, w24) &*&
        nth(4, w25) == nth(4, w24) &*&
        nth(5, w25) == nth(5, w24) &*&
        nth(7, w25) == nth(7, w24) &*&
        nth(8, w25) == nth(8, w24) &*&
        nth(9, w25) == nth(9, w24) &*&
        nth(10, w25) == nth(10, w24) &*&
        nth(12, w25) == nth(12, w24) &*&
        nth(0, w26) == nth(0, w25) &*&
        nth(1, w26) == nth(1, w25) &*&
        nth(2, w26) == nth(2, w25) &*&
        nth(3, w26) == nth(3, w25) &*&
        nth(4, w26) == nth(4, w25) &*&
        nth(5, w26) == nth(5, w25) &*&
        nth(6, w26) == nth(6, w25) &*&
        nth(7, w26) == nth(7, w25) &*&
        nth(8, w26) == nth(8, w25) &*&
        nth(11, w26) == nth(11, w25) &*&
        nth(12, w26) == nth(12, w25) &*&
        nth(2, w27) == nth(2, w26) &*&
        nth(3, w27) == nth(3, w26) &*&
        nth(4, w27) == nth(4, w26) &*&
        nth(5, w27) == nth(5, w26) &*&
        nth(6, w27) == nth(6, w26) &*&
        nth(7, w27) == nth(7, w26) &*&
        nth(8, w27) == nth(8, w26) &*&
        nth(9, w27) == nth(9, w26) &*&
        nth(10, w27) == nth(10, w26) &*&
        nth(11, w27) == nth(11, w26) &*&
        nth(12, w27) == nth(12, w26) &*&
        nth(0, w28) == nth(0, w27) &*&
        nth(1, w28) == nth(1, w27) &*&
        nth(3, w28) == nth(3, w27) &*&
        nth(4, w28) == nth(4, w27) &*&
        nth(6, w28) == nth(6, w27) &*&
        nth(7, w28) == nth(7, w27) &*&
        nth(8, w28) == nth(8, w27) &*&
        nth(9, w28) == nth(9, w27) &*&
        nth(10, w28) == nth(10, w27) &*&
        nth(11, w28) == nth(11, w27) &*&
        nth(12, w28) == nth(12, w27) &*&
        nth(0, w29) == nth(0, w28) &*&
        nth(1, w29) == nth(1, w28) &*&
        nth(2, w29) == nth(2, w28) &*&
        nth(3, w29) == nth(3, w28) &*&
        nth(4, w29) == nth(4, w28) &*&
        nth(5, w29) == nth(5, w28) &*&
        nth(7, w29) == nth(7, w28) &*&
        nth(8, w29) == nth(8, w28) &*&
        nth(10, w29) == nth(10, w28) &*&
        nth(11, w29) == nth(11, w28) &*&
        nth(12, w29) == nth(12, w28) &*&
        nth(0, w30) == nth(0, w29) &*&
        nth(1, w30) == nth(1, w29) &*&
        nth(2, w30) == nth(2, w29) &*&
        nth(3, w30) == nth(3, w29) &*&
        nth(4, w30) == nth(4, w29) &*&
        nth(5, w30) == nth(5, w29) &*&
        nth(6, w30) == nth(6, w29) &*&
        nth(9, w30) == nth(9, w29) &*&
        nth(10, w30) == nth(10, w29) &*&
        nth(11, w30) == nth(11, w29) &*&
        nth(12, w30) == nth(12, w29) &*&
        nth(0, w31) == nth(0, w30) &*&
        nth(1, w31) == nth(1, w30) &*&
        nth(2, w31) == nth(2, w30) &*&
        nth(3, w31) == nth(3, w30) &*&
        nth(4, w31) == nth(4, w30) &*&
        nth(5, w31) == nth(5, w30) &*&
        nth(6, w31) == nth(6, w30) &*&
        nth(7, w31) == nth(7, w30) &*&
        nth(8, w31) == nth(8, w30) &*&
        nth(9, w31) == nth(9, w30) &*&
        nth(12, w31) == nth(12, w30) &*&
        nth(0, w32) == nth(0, w31) &*&
        nth(2, w32) == nth(2, w31) &*&
        nth(4, w32) == nth(4, w31) &*&
        nth(5, w32) == nth(5, w31) &*&
        nth(6, w32) == nth(6, w31) &*&
        nth(7, w32) == nth(7, w31) &*&
        nth(8, w32) == nth(8, w31) &*&
        nth(9, w32) == nth(9, w31) &*&
        nth(10, w32) == nth(10, w31) &*&
        nth(11, w32) == nth(11, w31) &*&
        nth(12, w32) == nth(12, w31) &*&
        nth(0, w33) == nth(0, w32) &*&
        nth(1, w33) == nth(1, w32) &*&
        nth(3, w33) == nth(3, w32) &*&
        nth(5, w33) == nth(5, w32) &*&
        nth(6, w33) == nth(6, w32) &*&
        nth(7, w33) == nth(7, w32) &*&
        nth(8, w33) == nth(8, w32) &*&
        nth(9, w33) == nth(9, w32) &*&
        nth(10, w33) == nth(10, w32) &*&
        nth(11, w33) == nth(11, w32) &*&
        nth(12, w33) == nth(12, w32) &*&
        nth(0, w34) == nth(0, w33) &*&
        nth(1, w34) == nth(1, w33) &*&
        nth(2, w34) == nth(2, w33) &*&
        nth(3, w34) == nth(3, w33) &*&
        nth(4, w34) == nth(4, w33) &*&
        nth(7, w34) == nth(7, w33) &*&
        nth(8, w34) == nth(8, w33) &*&
        nth(9, w34) == nth(9, w33) &*&
        nth(10, w34) == nth(10, w33) &*&
        nth(11, w34) == nth(11, w33) &*&
        nth(12, w34) == nth(12, w33) &*&
        nth(0, w35) == nth(0, w34) &*&
        nth(1, w35) == nth(1, w34) &*&
        nth(2, w35) == nth(2, w34) &*&
        nth(3, w35) == nth(3, w34) &*&
        nth(4, w35) == nth(4, w34) &*&
        nth(5, w35) == nth(5, w34) &*&
        nth(6, w35) == nth(6, w34) &*&
        nth(7, w35) == nth(7, w34) &*&
        nth(8, w35) == nth(8, w34) &*&
        nth(11, w35) == nth(11, w34) &*&
        nth(12, w35) == nth(12, w34) &*&
        nth(0, w36) == nth(0, w35) &*&
        nth(3, w36) == nth(3, w35) &*&
        nth(4, w36) == nth(4, w35) &*&
        nth(5, w36) == nth(5, w35) &*&
        nth(6, w36) == nth(6, w35) &*&
        nth(7, w36) == nth(7, w35) &*&
        nth(8, w36) == nth(8, w35) &*&
        nth(9, w36) == nth(9, w35) &*&
        nth(10, w36) == nth(10, w35) &*&
        nth(11, w36) == nth(11, w35) &*&
        nth(12, w36) == nth(12, w35) &*&
        nth(0, w37) == nth(0, w36) &*&
        nth(1, w37) == nth(1, w36) &*&
        nth(2, w37) == nth(2, w36) &*&
        nth(5, w37) == nth(5, w36) &*&
        nth(6, w37) == nth(6, w36) &*&
        nth(7, w37) == nth(7, w36) &*&
        nth(8, w37) == nth(8, w36) &*&
        nth(9, w37) == nth(9, w36) &*&
        nth(10, w37) == nth(10, w36) &*&
        nth(11, w37) == nth(11, w36) &*&
        nth(12, w37) == nth(12, w36) &*&
        nth(0, w38) == nth(0, w37) &*&
        nth(1, w38) == nth(1, w37) &*&
        nth(2, w38) == nth(2, w37) &*&
        nth(3, w38) == nth(3, w37) &*&
        nth(4, w38) == nth(4, w37) &*&
        nth(6, w38) == nth(6, w37) &*&
        nth(8, w38) == nth(8, w37) &*&
        nth(9, w38) == nth(9, w37) &*&
        nth(10, w38) == nth(10, w37) &*&
        nth(11, w38) == nth(11, w37) &*&
        nth(12, w38) == nth(12, w37) &*&
        nth(0, w39) == nth(0, w38) &*&
        nth(1, w39) == nth(1, w38) &*&
        nth(2, w39) == nth(2, w38) &*&
        nth(3, w39) == nth(3, w38) &*&
        nth(4, w39) == nth(4, w38) &*&
        nth(5, w39) == nth(5, w38) &*&
        nth(7, w39) == nth(7, w38) &*&
        nth(9, w39) == nth(9, w38) &*&
        nth(10, w39) == nth(10, w38) &*&
        nth(11, w39) == nth(11, w38) &*&
        nth(12, w39) == nth(12, w38) &*&
        nth(0, w40) == nth(0, w39) &*&
        nth(1, w40) == nth(1, w39) &*&
        nth(4, w40) == nth(4, w39) &*&
        nth(5, w40) == nth(5, w39) &*&
        nth(6, w40) == nth(6, w39) &*&
        nth(7, w40) == nth(7, w39) &*&
        nth(8, w40) == nth(8, w39) &*&
        nth(9, w40) == nth(9, w39) &*&
        nth(10, w40) == nth(10, w39) &*&
        nth(11, w40) == nth(11, w39) &*&
        nth(12, w40) == nth(12, w39) &*&
        nth(0, w41) == nth(0, w40) &*&
        nth(1, w41) == nth(1, w40) &*&
        nth(2, w41) == nth(2, w40) &*&
        nth(3, w41) == nth(3, w40) &*&
        nth(6, w41) == nth(6, w40) &*&
        nth(7, w41) == nth(7, w40) &*&
        nth(8, w41) == nth(8, w40) &*&
        nth(9, w41) == nth(9, w40) &*&
        nth(10, w41) == nth(10, w40) &*&
        nth(11, w41) == nth(11, w40) &*&
        nth(12, w41) == nth(12, w40) &*&
        nth(0, w42) == nth(0, w41) &*&
        nth(1, w42) == nth(1, w41) &*&
        nth(2, w42) == nth(2, w41) &*&
        nth(3, w42) == nth(3, w41) &*&
        nth(4, w42) == nth(4, w41) &*&
        nth(5, w42) == nth(5, w41) &*&
        nth(8, w42) == nth(8, w41) &*&
        nth(9, w42) == nth(9, w41) &*&
        nth(10, w42) == nth(10, w41) &*&
        nth(11, w42) == nth(11, w41) &*&
        nth(12, w42) == nth(12, w41) &*&
        nth(0, w43) == nth(0, w42) &*&
        nth(1, w43) == nth(1, w42) &*&
        nth(2, w43) == nth(2, w42) &*&
        nth(3, w43) == nth(3, w42) &*&
        nth(4, w43) == nth(4, w42) &*&
        nth(5, w43) == nth(5, w42) &*&
        nth(6, w43) == nth(6, w42) &*&
        nth(7, w43) == nth(7, w42) &*&
        nth(10, w43) == nth(10, w42) &*&
        nth(11, w43) == nth(11, w42) &*&
        nth(12, w43) == nth(12, w42) &*&
        nth(0, w44) == nth(0, w43) &*&
        nth(1, w44) == nth(1, w43) &*&
        nth(2, w44) == nth(2, w43) &*&
        nth(5, w44) == nth(5, w43) &*&
        nth(6, w44) == nth(6, w43) &*&
        nth(7, w44) == nth(7, w43) &*&
        nth(8, w44) == nth(8, w43) &*&
        nth(9, w44) == nth(9, w43) &*&
        nth(10, w44) == nth(10, w43) &*&
        nth(11, w44) == nth(11, w43) &*&
        nth(12, w44) == nth(12, w43) &*&
        nth(0, w45) == nth(0, w44) &*&
        nth(1, w45) == nth(1, w44) &*&
        nth(2, w45) == nth(2, w44) &*&
        nth(3, w45) == nth(3, w44) &*&
        nth(4, w45) == nth(4, w44) &*&
        nth(7, w45) == nth(7, w44) &*&
        nth(8, w45) == nth(8, w44) &*&
        nth(9, w45) == nth(9, w44) &*&
        nth(10, w45) == nth(10, w44) &*&
        nth(11, w45) == nth(11, w44) &*&
        nth(12, w45) == nth(12, w44);
    ens !apply_lt(is_less_model_of::<T, F>(f0), nth(12, w45), nth(11, w45));
{
    let lt = is_less_model_of::<T, F>(f0);
    let c = nth(12, w45);
    step_done_bits::<T, F>(f0, c, 0, 12, w0, w1);
    step_done_bits::<T, F>(f0, c, 1, 10, w1, w2);
    step_done_bits::<T, F>(f0, c, 2, 9, w2, w3);
    step_done_bits::<T, F>(f0, c, 3, 7, w3, w4);
    step_done_bits::<T, F>(f0, c, 5, 11, w4, w5);
    step_done_bits::<T, F>(f0, c, 6, 8, w5, w6);
    step_done_bits::<T, F>(f0, c, 1, 6, w6, w7);
    step_done_bits::<T, F>(f0, c, 2, 3, w7, w8);
    step_done_bits::<T, F>(f0, c, 4, 11, w8, w9);
    step_done_bits::<T, F>(f0, c, 7, 9, w9, w10);
    step_done_bits::<T, F>(f0, c, 8, 10, w10, w11);
    step_done_bits::<T, F>(f0, c, 0, 4, w11, w12);
    step_done_bits::<T, F>(f0, c, 1, 2, w12, w13);
    step_done_bits::<T, F>(f0, c, 3, 6, w13, w14);
    step_done_bits::<T, F>(f0, c, 7, 8, w14, w15);
    step_done_bits::<T, F>(f0, c, 9, 10, w15, w16);
    step_done_bits::<T, F>(f0, c, 11, 12, w16, w17);
    step_done_bits::<T, F>(f0, c, 4, 6, w17, w18);
    step_done_bits::<T, F>(f0, c, 5, 9, w18, w19);
    step_done_bits::<T, F>(f0, c, 8, 11, w19, w20);
    step_done_bits::<T, F>(f0, c, 10, 12, w20, w21);
    step_done_bits::<T, F>(f0, c, 0, 5, w21, w22);
    step_done_bits::<T, F>(f0, c, 3, 8, w22, w23);
    step_done_bits::<T, F>(f0, c, 4, 7, w23, w24);
    step_done_bits::<T, F>(f0, c, 6, 11, w24, w25);
    step_done_bits::<T, F>(f0, c, 9, 10, w25, w26);
    step_done_bits::<T, F>(f0, c, 0, 1, w26, w27);
    step_done_bits::<T, F>(f0, c, 2, 5, w27, w28);
    step_done_bits::<T, F>(f0, c, 6, 9, w28, w29);
    step_done_bits::<T, F>(f0, c, 7, 8, w29, w30);
    step_done_bits::<T, F>(f0, c, 10, 11, w30, w31);
    step_done_bits::<T, F>(f0, c, 1, 3, w31, w32);
    step_done_bits::<T, F>(f0, c, 2, 4, w32, w33);
    step_done_bits::<T, F>(f0, c, 5, 6, w33, w34);
    step_done_bits::<T, F>(f0, c, 9, 10, w34, w35);
    step_done_bits::<T, F>(f0, c, 1, 2, w35, w36);
    step_done_bits::<T, F>(f0, c, 3, 4, w36, w37);
    step_done_bits::<T, F>(f0, c, 5, 7, w37, w38);
    step_done_bits::<T, F>(f0, c, 6, 8, w38, w39);
    step_done_bits::<T, F>(f0, c, 2, 3, w39, w40);
    step_done_bits::<T, F>(f0, c, 4, 5, w40, w41);
    step_done_bits::<T, F>(f0, c, 6, 7, w41, w42);
    step_done_bits::<T, F>(f0, c, 8, 9, w42, w43);
    step_done_bits::<T, F>(f0, c, 3, 4, w43, w44);
    step_done_bits::<T, F>(f0, c, 5, 6, w44, w45);
    net13_01(bit_of(apply_lt(lt, c, nth(0, w0))), bit_of(apply_lt(lt, c, nth(1, w0))), bit_of(apply_lt(lt, c, nth(2, w0))), bit_of(apply_lt(lt, c, nth(3, w0))), bit_of(apply_lt(lt, c, nth(4, w0))), bit_of(apply_lt(lt, c, nth(5, w0))), bit_of(apply_lt(lt, c, nth(6, w0))), bit_of(apply_lt(lt, c, nth(7, w0))), bit_of(apply_lt(lt, c, nth(8, w0))), bit_of(apply_lt(lt, c, nth(9, w0))), bit_of(apply_lt(lt, c, nth(10, w0))), bit_of(apply_lt(lt, c, nth(11, w0))), bit_of(apply_lt(lt, c, nth(12, w0))), bit_of(apply_lt(lt, c, nth(0, w1))), bit_of(apply_lt(lt, c, nth(12, w1))), bit_of(apply_lt(lt, c, nth(1, w2))), bit_of(apply_lt(lt, c, nth(10, w2))), bit_of(apply_lt(lt, c, nth(2, w3))), bit_of(apply_lt(lt, c, nth(9, w3))), bit_of(apply_lt(lt, c, nth(3, w4))), bit_of(apply_lt(lt, c, nth(7, w4))), bit_of(apply_lt(lt, c, nth(5, w5))), bit_of(apply_lt(lt, c, nth(11, w5))), bit_of(apply_lt(lt, c, nth(6, w6))), bit_of(apply_lt(lt, c, nth(8, w6))), bit_of(apply_lt(lt, c, nth(1, w7))), bit_of(apply_lt(lt, c, nth(6, w7))), bit_of(apply_lt(lt, c, nth(2, w8))), bit_of(apply_lt(lt, c, nth(3, w8))), bit_of(apply_lt(lt, c, nth(4, w9))), bit_of(apply_lt(lt, c, nth(11, w9))), bit_of(apply_lt(lt, c, nth(7, w10))), bit_of(apply_lt(lt, c, nth(9, w10))), bit_of(apply_lt(lt, c, nth(8, w11))), bit_of(apply_lt(lt, c, nth(10, w11))), bit_of(apply_lt(lt, c, nth(0, w12))), bit_of(apply_lt(lt, c, nth(4, w12))), bit_of(apply_lt(lt, c, nth(1, w13))), bit_of(apply_lt(lt, c, nth(2, w13))), bit_of(apply_lt(lt, c, nth(3, w14))), bit_of(apply_lt(lt, c, nth(6, w14))), bit_of(apply_lt(lt, c, nth(7, w15))), bit_of(apply_lt(lt, c, nth(8, w15))), bit_of(apply_lt(lt, c, nth(9, w16))), bit_of(apply_lt(lt, c, nth(10, w16))), bit_of(apply_lt(lt, c, nth(11, w17))), bit_of(apply_lt(lt, c, nth(12, w17))), bit_of(apply_lt(lt, c, nth(4, w18))), bit_of(apply_lt(lt, c, nth(6, w18))), bit_of(apply_lt(lt, c, nth(5, w19))), bit_of(apply_lt(lt, c, nth(9, w19))), bit_of(apply_lt(lt, c, nth(8, w20))), bit_of(apply_lt(lt, c, nth(11, w20))), bit_of(apply_lt(lt, c, nth(10, w21))), bit_of(apply_lt(lt, c, nth(12, w21))), bit_of(apply_lt(lt, c, nth(0, w22))), bit_of(apply_lt(lt, c, nth(5, w22))), bit_of(apply_lt(lt, c, nth(3, w23))), bit_of(apply_lt(lt, c, nth(8, w23))), bit_of(apply_lt(lt, c, nth(4, w24))), bit_of(apply_lt(lt, c, nth(7, w24))), bit_of(apply_lt(lt, c, nth(6, w25))), bit_of(apply_lt(lt, c, nth(11, w25))), bit_of(apply_lt(lt, c, nth(9, w26))), bit_of(apply_lt(lt, c, nth(10, w26))), bit_of(apply_lt(lt, c, nth(0, w27))), bit_of(apply_lt(lt, c, nth(1, w27))), bit_of(apply_lt(lt, c, nth(2, w28))), bit_of(apply_lt(lt, c, nth(5, w28))), bit_of(apply_lt(lt, c, nth(6, w29))), bit_of(apply_lt(lt, c, nth(9, w29))), bit_of(apply_lt(lt, c, nth(7, w30))), bit_of(apply_lt(lt, c, nth(8, w30))), bit_of(apply_lt(lt, c, nth(10, w31))), bit_of(apply_lt(lt, c, nth(11, w31))), bit_of(apply_lt(lt, c, nth(1, w32))), bit_of(apply_lt(lt, c, nth(3, w32))), bit_of(apply_lt(lt, c, nth(2, w33))), bit_of(apply_lt(lt, c, nth(4, w33))), bit_of(apply_lt(lt, c, nth(5, w34))), bit_of(apply_lt(lt, c, nth(6, w34))), bit_of(apply_lt(lt, c, nth(9, w35))), bit_of(apply_lt(lt, c, nth(10, w35))), bit_of(apply_lt(lt, c, nth(1, w36))), bit_of(apply_lt(lt, c, nth(2, w36))), bit_of(apply_lt(lt, c, nth(3, w37))), bit_of(apply_lt(lt, c, nth(4, w37))), bit_of(apply_lt(lt, c, nth(5, w38))), bit_of(apply_lt(lt, c, nth(7, w38))), bit_of(apply_lt(lt, c, nth(6, w39))), bit_of(apply_lt(lt, c, nth(8, w39))), bit_of(apply_lt(lt, c, nth(2, w40))), bit_of(apply_lt(lt, c, nth(3, w40))), bit_of(apply_lt(lt, c, nth(4, w41))), bit_of(apply_lt(lt, c, nth(5, w41))), bit_of(apply_lt(lt, c, nth(6, w42))), bit_of(apply_lt(lt, c, nth(7, w42))), bit_of(apply_lt(lt, c, nth(8, w43))), bit_of(apply_lt(lt, c, nth(9, w43))), bit_of(apply_lt(lt, c, nth(3, w44))), bit_of(apply_lt(lt, c, nth(4, w44))), bit_of(apply_lt(lt, c, nth(5, w45))), bit_of(apply_lt(lt, c, nth(6, w45))));
    is_less_irreflexive::<T, F>(f0, c);
    bit_adj(apply_lt(lt, c, nth(11, w45)), apply_lt(lt, c, c));
}

// The network of `sort13_optimal` sorts the first 13 elements (0-1 principle, see above).
lem net13_sorted<T, F>(f0: F, w0: list<T>, w1: list<T>, w2: list<T>, w3: list<T>, w4: list<T>, w5: list<T>, w6: list<T>, w7: list<T>, w8: list<T>, w9: list<T>, w10: list<T>, w11: list<T>, w12: list<T>, w13: list<T>, w14: list<T>, w15: list<T>, w16: list<T>, w17: list<T>, w18: list<T>, w19: list<T>, w20: list<T>, w21: list<T>, w22: list<T>, w23: list<T>, w24: list<T>, w25: list<T>, w26: list<T>, w27: list<T>, w28: list<T>, w29: list<T>, w30: list<T>, w31: list<T>, w32: list<T>, w33: list<T>, w34: list<T>, w35: list<T>, w36: list<T>, w37: list<T>, w38: list<T>, w39: list<T>, w40: list<T>, w41: list<T>, w42: list<T>, w43: list<T>, w44: list<T>, w45: list<T>)
    req is_less_models::<T, F>(f0) == true &*& 13 <= length(w0) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 12, w0, w1) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 10, w1, w2) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 9, w2, w3) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 7, w3, w4) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 11, w4, w5) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w5, w6) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 6, w6, w7) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w7, w8) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 11, w8, w9) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 9, w9, w10) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 10, w10, w11) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 4, w11, w12) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w12, w13) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 6, w13, w14) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w14, w15) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w15, w16) &*& [_]step_done(is_less_model_of::<T, F>(f0), 11, 12, w16, w17) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 6, w17, w18) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 9, w18, w19) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 11, w19, w20) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 12, w20, w21) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 5, w21, w22) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 8, w22, w23) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 7, w23, w24) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 11, w24, w25) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w25, w26) &*& [_]step_done(is_less_model_of::<T, F>(f0), 0, 1, w26, w27) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 5, w27, w28) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 9, w28, w29) &*& [_]step_done(is_less_model_of::<T, F>(f0), 7, 8, w29, w30) &*& [_]step_done(is_less_model_of::<T, F>(f0), 10, 11, w30, w31) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 3, w31, w32) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 4, w32, w33) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w33, w34) &*& [_]step_done(is_less_model_of::<T, F>(f0), 9, 10, w34, w35) &*& [_]step_done(is_less_model_of::<T, F>(f0), 1, 2, w35, w36) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w36, w37) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 7, w37, w38) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 8, w38, w39) &*& [_]step_done(is_less_model_of::<T, F>(f0), 2, 3, w39, w40) &*& [_]step_done(is_less_model_of::<T, F>(f0), 4, 5, w40, w41) &*& [_]step_done(is_less_model_of::<T, F>(f0), 6, 7, w41, w42) &*& [_]step_done(is_less_model_of::<T, F>(f0), 8, 9, w42, w43) &*& [_]step_done(is_less_model_of::<T, F>(f0), 3, 4, w43, w44) &*& [_]step_done(is_less_model_of::<T, F>(f0), 5, 6, w44, w45);
    ens sorted_by(is_less_model_of::<T, F>(f0), take(13, w45)) == true;
{
    let lt = is_less_model_of::<T, F>(f0);
    net13_frame::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj0::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj1::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj2::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj3::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj4::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj5::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj6::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj7::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj8::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj9::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj10::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    net13_adj11::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
    sorted13_from_adj(lt, w45);
}

@*/

// It's important to differentiate between SMALL_SORT_THRESHOLD performance for
// small slices and small-sort performance sorting small sub-slices as part of
// the main quicksort loop. For the former, testing showed that the
// representative benchmarks for real-world performance are cold CPU state and
// not single-size hot benchmarks. For the latter the CPU will call them many
// times, so hot benchmarks are fine and more realistic. And it's worth it to
// optimize sorting small sub-slices with more sophisticated solutions than
// insertion sort.

/// Using a trait allows us to specialize on `Freeze` which in turn allows us to make safe
/// abstractions.
pub(crate) trait StableSmallSortTypeImpl: Sized {
    /// For which input length <= return value of this function, is it valid to call `small_sort`.
    fn small_sort_threshold() -> usize;

    /// Sorts `v` using strategies optimized for small sizes.
    fn small_sort<F: FnMut(&Self, &Self) -> bool>(
        v: &mut [Self],
        scratch: &mut [MaybeUninit<Self>],
        is_less: &mut F,
    );
}

impl<T> StableSmallSortTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        // Optimal number of comparisons, and good perf.
        SMALL_SORT_FALLBACK_THRESHOLD
    }

    #[inline(always)]
    default fn small_sort<F: FnMut(&T, &T) -> bool>(
        v: &mut [T],
        _scratch: &mut [MaybeUninit<T>],
        is_less: &mut F,
    )
    {
        if v.len() >= 2 {
            insertion_sort_shift_left(v, 1, is_less);
        }
    }
}

impl<T: FreezeMarker> StableSmallSortTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        SMALL_SORT_GENERAL_THRESHOLD
    }

    #[inline(always)]
    fn small_sort<F: FnMut(&T, &T) -> bool>(
        v: &mut [T],
        scratch: &mut [MaybeUninit<T>],
        is_less: &mut F,
    )
    {
        small_sort_general_with_scratch(v, scratch, is_less);
    }
}

/// Using a trait allows us to specialize on `Freeze` which in turn allows us to make safe
/// abstractions.
pub(crate) trait UnstableSmallSortTypeImpl: Sized {
    /// For which input length <= return value of this function, is it valid to call `small_sort`.
    fn small_sort_threshold() -> usize;

    /// Sorts `v` using strategies optimized for small sizes.
    fn small_sort<F: FnMut(&Self, &Self) -> bool>(v: &mut [Self], is_less: &mut F);
}

impl<T> UnstableSmallSortTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        SMALL_SORT_FALLBACK_THRESHOLD
    }

    #[inline(always)]
    default fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        small_sort_fallback(v, is_less);
    }
}

impl<T: FreezeMarker> UnstableSmallSortTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        <T as UnstableSmallSortFreezeTypeImpl>::small_sort_threshold()
    }

    #[inline(always)]
    fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        <T as UnstableSmallSortFreezeTypeImpl>::small_sort(v, is_less);
    }
}

/// FIXME(const_trait_impl) use original ipnsort approach with choose_unstable_small_sort,
/// as found here <https://github.com/Voultapher/sort-research-rs/blob/438fad5d0495f65d4b72aa87f0b62fc96611dff3/ipnsort/src/smallsort.rs#L83C10-L83C36>.
pub(crate) trait UnstableSmallSortFreezeTypeImpl: Sized + FreezeMarker {
    fn small_sort_threshold() -> usize;

    fn small_sort<F: FnMut(&Self, &Self) -> bool>(v: &mut [Self], is_less: &mut F);
}

impl<T: FreezeMarker> UnstableSmallSortFreezeTypeImpl for T {
    #[inline(always)]
    default fn small_sort_threshold() -> usize {
        if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            SMALL_SORT_GENERAL_THRESHOLD
        } else {
            SMALL_SORT_FALLBACK_THRESHOLD
        }
    }

    #[inline(always)]
    default fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    {
        if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            small_sort_general(v, is_less);
        } else {
            small_sort_fallback(v, is_less);
        }
    }
}

/// SAFETY: Only used for run-time optimization heuristic.
#[unsafe(rustc_allow_lifetime_dependent_specialization)]
trait CopyMarker {}

impl<T: Copy> CopyMarker for T {}

impl<T: FreezeMarker + CopyMarker> UnstableSmallSortFreezeTypeImpl for T {
    #[inline(always)]
    fn small_sort_threshold() -> usize {
        if has_efficient_in_place_swap::<T>()
            && (size_of::<T>() * SMALL_SORT_NETWORK_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE
        {
            SMALL_SORT_NETWORK_THRESHOLD
        } else if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            SMALL_SORT_GENERAL_THRESHOLD
        } else {
            SMALL_SORT_FALLBACK_THRESHOLD
        }
    }

    #[inline(always)]
    fn small_sort<F>(v: &mut [T], is_less: &mut F)
    where
        F: FnMut(&T, &T) -> bool,
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
        *is_less |-> ?f0 &*& <F>.own(t, f0);
    @*/
    /*@
    ens thread_token(t) &*&
        array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
        *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
        if is_less_models::<T, F>(f0) {
            is_perm(vs1, vs) && sorted_by(is_less_model_of::<T, F>(f0), vs1)
        } else {
            true
        };
    @*/
    /*@
    on_unwind_ens thread_token(t) &*&
        array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
        *is_less |-> ?f1 &*& <F>.own(t, f1);
    @*/
    {
        //@ small_sort_general_instantiated::<T>();
        if has_efficient_in_place_swap::<T>()
            && (size_of::<T>() * SMALL_SORT_NETWORK_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE
        {
            small_sort_network(v, is_less);
        } else if (size_of::<T>() * SMALL_SORT_GENERAL_SCRATCH_LEN) <= MAX_STACK_ARRAY_SIZE {
            small_sort_general(v, is_less);
        } else {
            small_sort_fallback(v, is_less);
        }
    }
}

/// Optimal number of comparisons, and good perf.
const SMALL_SORT_FALLBACK_THRESHOLD: usize = 16;

/// From a comparison perspective 20 was ~2% more efficient for fully random input, but for
/// wall-clock performance choosing 32 yielded better performance overall.
///
/// SAFETY: If you change this value, you have to adjust [`small_sort_general`] !
const SMALL_SORT_GENERAL_THRESHOLD: usize = 32;

/// [`small_sort_general`] uses [`sort8_stable`] as primitive and does a kind of ping-pong merge,
/// where the output of the first two [`sort8_stable`] calls is stored at the end of the scratch
/// buffer. This simplifies panic handling and avoids additional copies. This affects the required
/// scratch buffer size.
///
/// SAFETY: If you change this value, you have to adjust [`small_sort_general`] !
pub(crate) const SMALL_SORT_GENERAL_SCRATCH_LEN: usize = SMALL_SORT_GENERAL_THRESHOLD + 16;

/// SAFETY: If you change this value, you have to adjust [`small_sort_network`] !
const SMALL_SORT_NETWORK_THRESHOLD: usize = 32;
const SMALL_SORT_NETWORK_SCRATCH_LEN: usize = SMALL_SORT_NETWORK_THRESHOLD;

/// Using a stack array, could cause a stack overflow if the type `T` is very large. To be
/// conservative we limit the usage of small-sorts that require a stack array to types that fit
/// within this limit.
const MAX_STACK_ARRAY_SIZE: usize = 4096;

fn small_sort_fallback<T, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F)
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        is_perm(vs1, vs) && sorted_by(is_less_model_of::<T, F>(f0), vs1)
    } else {
        true
    };
@*/
/*@
on_unwind_ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1);
@*/
{
    if v.len() >= 2 {
        //@ match vs { nil => {} cons(v0, vs0) => {} }
        insertion_sort_shift_left(v, 1, is_less);
    } else {
        //@ match vs { nil => {} cons(v0, vs0) => { match vs0 { nil => {} cons(v1, vs1) => {} } } }
        //@ is_perm_refl(vs);
    }
}

fn small_sort_general<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F)
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        is_perm(vs1, vs) && sorted_by(is_less_model_of::<T, F>(f0), vs1)
    } else {
        true
    };
@*/
/*@
on_unwind_ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1);
@*/
{
    // VeriFast rewrite (rewrites/005): `MaybeUninit::uninit()` through a trusted wrapper (VeriFast 26.10
    // has no spec for it).
    let mut stack_array = unsafe { maybe_uninit_uninit__VeriFast_wrapper::<[T; SMALL_SORT_GENERAL_SCRATCH_LEN]>() };
    //@ std::mem::open_MaybeUninit(&stack_array);
    //@ Array__to_array_(&stack_array as *[T; 48]);
    //@ let sp = &stack_array as *T;
    //@ std::mem::array__to_array_MaybeUninit(sp);
    //@ assert array::<std::mem::MaybeUninit<T>>(sp as *std::mem::MaybeUninit<T>, 48, ?ms);
    //@ foreach_MaybeUninit_own(t, ms);
    //@ open array::<std::mem::MaybeUninit<T>>(sp as *std::mem::MaybeUninit<T>, 48, ms);
    //@ to_u8s_(sp as *std::mem::MaybeUninit<T>);
    //@ from_u8s_(sp as *std::mem::MaybeUninit<T>);
    //@ close points_to::<std::mem::MaybeUninit<T>>(sp as *std::mem::MaybeUninit<T>, head(ms));
    //@ points_to_limits(sp as *std::mem::MaybeUninit<T>);
    //@ close array::<std::mem::MaybeUninit<T>>(sp as *std::mem::MaybeUninit<T>, 48, ms);

    // SAFETY: The memory is backed by `stack_array`, and the operation is safe as long as the len
    // is the same.
    let scratch = unsafe {
        slice::from_raw_parts_mut(
            maybe_uninit_as_mut_ptr__VeriFast_wrapper(&mut stack_array) as *mut MaybeUninit<T>,
            SMALL_SORT_GENERAL_SCRATCH_LEN,
        )
    };

    small_sort_general_with_scratch(v, scratch, is_less);
    //@ assert foreach(?ss1, own::<std::mem::MaybeUninit<T>>(t));
    //@ leak foreach(ss1, own::<std::mem::MaybeUninit<T>>(t));
    //@ array_MaybeUninit_to_array_(sp as *std::mem::MaybeUninit<T>);
    //@ MaybeUninit_array_48_layout::<T>();
    //@ array__to_u8s_(sp, 48);
    //@ from_u8s_(&stack_array);
}

fn small_sort_general_with_scratch<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    scratch: &mut [MaybeUninit<T>],
    is_less: &mut F,
)
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    array::<std::mem::MaybeUninit<T>>(strip_pointer_metadata(scratch as pointer) as *std::mem::MaybeUninit<T>, scratch.len(), ?ss) &*&
    foreach(ss, own::<std::mem::MaybeUninit<T>>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    array::<std::mem::MaybeUninit<T>>(strip_pointer_metadata(scratch as pointer) as *std::mem::MaybeUninit<T>, scratch.len(), ?ss1) &*&
    foreach(ss1, own::<std::mem::MaybeUninit<T>>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        is_perm(vs1, vs) && sorted_by(is_less_model_of::<T, F>(f0), vs1)
    } else {
        true
    };
@*/
{
    let len = v.len();
    //@ std::slice::slice_len_range(v);
    //@ std::slice::slice_len_range(scratch);
    if len < 2 {
        //@ match vs { nil => {} cons(v0, vs0) => { match vs0 { nil => {} cons(v1, vs1) => {} } } }
        //@ is_perm_refl(vs);
        return;
    }

    // VeriFast rewrite (rewrites/003): `len + 16`, through a trusted wrapper with Rust's checked
    // semantics (see README.md).
    if scratch.len() < usize_add_16__VeriFast_wrapper(len) {
        intrinsics::abort_immediate();
    }

    let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);
    let len_div_2 = len / 2;
    //@ div_rem_nonneg(len, 2);

    // SAFETY: See individual comments.
    unsafe {
        let scratch_base = slice_as_mut_ptr__VeriFast_wrapper(scratch) as *mut T;
        //@ let sbm = scratch as *std::mem::MaybeUninit<T>;
        //@ let sb = scratch_base;
        //@ let slen = scratch.len();
        //@ let h = len_div_2;
        //@ let rl = len - h;
        //@ let L = take(h, vs);
        //@ let R = drop(h, vs);
        //@ let m = is_less_models::<T, F>(f0);
        //@ let lt = is_less_model_of::<T, F>(f0);
        //@ array_MaybeUninit_to_array_(sbm);
        //@ leak foreach(ss, own::<std::mem::MaybeUninit<T>>(t));
        //@ array__split_n(sb, len);
        //@ array__split_n(sb, h);
        //@ array_size_nonneg(v_base);
        //@ array_ptr_within_limits(v_base, h);
        //@ array__ptr_within_limits(sb, h);
        //@ array__ptr_within_limits(sb + len, 0);
        //@ assert length(L) == h &*& length(R) == rl;

        let presorted_len = if const { size_of::<T>() <= 16 } && len >= 16 {
            //@ array_split(v_base, h);
            //@ array_split(v_base, 8);
            //@ array_split(v_base + h, 8);
            //@ array__split_n(sb, 8);
            //@ array__split_n(sb + h, 8);
            //@ array__split_n(sb + len, 8);
            //@ array__split_n(sb + len + 8, 8);
            // SAFETY: scratch_base is valid and has enough space.
            sort8_stable(v_base, scratch_base, scratch_base.add(len), is_less);
            sort8_stable(
                v_base.add(len_div_2),
                scratch_base.add(len_div_2),
                scratch_base.add(len + 8),
                is_less,
            );
            //@ array__join_n(sb + len + 8, 8, slen - len - 16);
            //@ array__join_n(sb + len, 8, slen - len - 8);
            //@ array_join_n(v_base + h, 8, rl - 8);
            //@ array_join_n(v_base, 8, h - 8);
            //@ array_join_n(v_base, h, rl);
            //@ take_take(8, h, vs);
            //@ assert array::<T>(sb, 8, ?s1) &*& array::<T>(sb + h, 8, ?s2);
            //@ close sregion(sb, h, 8, L, m, lt, s1);
            //@ close sregion(sb + h, rl, 8, R, m, lt, s2);

            8
        } else if len >= 8 {
            //@ array_split(v_base, h);
            //@ array_split(v_base, 4);
            //@ array_split(v_base + h, 4);
            //@ array__split_n(sb, 4);
            //@ array__split_n(sb + h, 4);
            // SAFETY: scratch_base is valid and has enough space.
            sort4_stable(v_base, scratch_base, is_less);
            sort4_stable(v_base.add(len_div_2), scratch_base.add(len_div_2), is_less);
            //@ array_join_n(v_base + h, 4, rl - 4);
            //@ array_join_n(v_base, 4, h - 4);
            //@ array_join_n(v_base, h, rl);
            //@ take_take(4, h, vs);
            //@ assert array::<T>(sb, 4, ?s1) &*& array::<T>(sb + h, 4, ?s2);
            //@ close sregion(sb, h, 4, L, m, lt, s1);
            //@ close sregion(sb + h, rl, 4, R, m, lt, s2);

            4
        } else {
            //@ array_open_at(v_base, 0);
            //@ array1_close(v_base);
            //@ array__split_n(sb, 1);
            ptr::copy_nonoverlapping(v_base, scratch_base, 1);
            //@ array1_open(v_base);
            //@ array_close_at_same(v_base, 0);
            //@ array_open_at(v_base, h);
            //@ array1_close(v_base + h);
            //@ array__split_n(sb + h, 1);
            ptr::copy_nonoverlapping(v_base.add(len_div_2), scratch_base.add(len_div_2), 1);
            //@ array1_open(v_base + h);
            //@ array_close_at_same(v_base, h);
            //@ nth_take_lt(0, h, vs);
            //@ nth_drop(0, h, vs);
            //@ is_perm_refl([nth(0, vs)]);
            //@ is_perm_refl([nth(h, vs)]);
            //@ match L { nil => {} cons(l0, l1) => {} }
            //@ match R { nil => {} cons(r0, r1) => {} }
            //@ close sregion(sb, h, 1, L, m, lt, [nth(0, vs)]);
            //@ close sregion(sb + h, rl, 1, R, m, lt, [nth(h, vs)]);

            1
        };
        //@ let p = presorted_len;

        {
        let mut offsets = array_0_and_into_iter__VeriFast_wrapper(len_div_2);
        //@ close exists::<i32>(0);
        //@ assert [?qlft]lifetime_token(?klft);
        // (The range temporary of the inner loop lives across iterations of the outer loop.)
        //@ let ra = &iter;
        //@ assert std::ops::Range_start_::<usize>(ra, _) &*& std::ops::Range_start_::<usize>(?rb, _);
        loop {
            /*@
            inv thread_token(t) &*& [qlft]lifetime_token(klft) &*&
                offsets |-> ?it &*& <core::array::IntoIter<usize, 2>>.own(t, it) &*&
                exists::<i32>(?c) &*& 0 <= c &*& c <= 2 &*& array_IntoIter_remaining(it) == drop(c, [0, h]) &*&
                *is_less |-> ?f &*& <F>.own(t, f) &*& (!m || f == f0) &*&
                array::<T>(v_base, len, vs) &*& foreach(vs, own::<T>(t)) &*&
                sregion(sb, h, if c >= 1 { h } else { p }, L, m, lt, ?sl) &*&
                sregion(sb + h, rl, if c >= 2 { rl } else { p }, R, m, lt, ?sr) &*&
                array_::<T>(sb + len, slen - len, _) &*&
                std::ops::Range_start_::<usize>(ra, _) &*& std::ops::Range_end_::<usize>(ra, _) &*&
                std::ops::struct_Range_padding::<usize>(ra) &*&
                std::ops::Range_start_::<usize>(rb, _) &*& std::ops::Range_end_::<usize>(rb, _) &*&
                std::ops::struct_Range_padding::<usize>(rb);
            @*/
            let offset = match array_usize_2_into_iter_next__VeriFast_wrapper(&mut offsets) {
                None => break,
                Some(offset) => offset,
            };
            //@ open exists::<i32>(c);
            //@ let o = if c == 0 { 0 } else { h };
            //@ let d = if c == 0 { h } else { rl };
            //@ let P = if c == 0 { L } else { R };
            //@ assert offset == o;
            // SAFETY: at this point dst is initialized with presorted_len elements.
            // We extend this to desired_len, src is valid for desired_len elements.
            let src = v_base.add(offset);
            let dst = scratch_base.add(offset);
            let desired_len = if offset == 0 { len_div_2 } else { len - len_div_2 };

            // VeriFast rewrite (rewrites/004): `for i in presorted_len..desired_len { .. }`, written as the
            // `loop` it desugars to, so that the iterator can be named in the loop invariant.
            {
            let mut iter = IntoIterator::into_iter(presorted_len..desired_len);
            loop {
                /*@
                inv thread_token(t) &*& [qlft]lifetime_token(klft) &*&
                    offsets |-> ?it1 &*& <core::array::IntoIter<usize, 2>>.own(t, it1) &*&
                    array_IntoIter_remaining(it1) == drop(c + 1, [0, h]) &*&
                    iter |-> ?ri &*& ri.end == d &*& p <= ri.start &*& ri.start <= d &*&
                    *is_less |-> ?f2 &*& <F>.own(t, f2) &*& (!m || f2 == f0) &*&
                    array::<T>(v_base, len, vs) &*& foreach(vs, own::<T>(t)) &*&
                    sregion(dst, d, ri.start, P, m, lt, ?sx) &*&
                    (if c == 0 { sregion(sb + h, rl, p, R, m, lt, sr) } else { sregion(sb, h, h, L, m, lt, sl) }) &*&
                    array_::<T>(sb + len, slen - len, _) &*&
                    std::ops::Range_start_::<usize>(rb, _) &*& std::ops::Range_end_::<usize>(rb, _) &*&
                std::ops::struct_Range_padding::<usize>(rb);
                @*/
                match Iterator::next(&mut iter) {
                    None => break,
                    Some(i) => {
                        //@ open sregion(dst, d, i, P, m, lt, sx);
                        //@ array_ptr_within_limits(v_base, o + i);
                        //@ array_open_at(v_base, o + i);
                        //@ array1_close(v_base + (o + i));
                        //@ open array_::<T>(dst + i, d - i, _);
                        //@ array_1_close(dst + i);
                        ptr::copy_nonoverlapping(src.add(i), dst.add(i), 1);
                        //@ array1_open(v_base + (o + i));
                        //@ array_close_at_same(v_base, o + i);
                        //@ array_join_n(dst, i, 1);
                        //@ let x = nth(o + i, vs);
                        insert_tail(dst, dst.add(i), is_less);
                        //@ assert array::<T>(dst, i + 1, ?sx1);
                        //@ if c == 0 { nth_take_lt(i, h, vs); } else { nth_drop(i, h, vs); }
                        //@ take_plus_one(i, P);
                        //@ is_perm_refl([x]);
                        //@ is_perm_append_both(sx, take(i, P), [x], [x]);
                        //@ is_perm_trans(sx1, append(sx, [x]), take(i + 1, P));
                        //@ take_append(i, sx, [x]);
                        //@ close sregion(dst, d, i + 1, P, m, lt, sx1);
                    }
                }
            }
            }
            //@ close exists::<i32>(c + 1);
        }
        }
        //@ open exists::<i32>(?ce);
        //@ open sregion(sb, h, h, L, m, lt, ?sl2);
        //@ open sregion(sb + h, rl, rl, R, m, lt, ?sr2);
        //@ open array_::<T>(sb + h, 0, _);
        //@ open array_::<T>(sb + h + rl, 0, _);
        //@ array_join_n(sb, h, rl);
        //@ array_to_array_(v_base);
        //@ array_open_at(sb, 0);
        //@ to_u8s_(sb);
        //@ from_u8s_(sb);
        //@ close points_to::<T>(sb, nth(0, append(sl2, sr2)));
        //@ points_to_limits(sb);
        //@ array_close_at_same(sb, 0);

        // SAFETY: see comment in `CopyOnDrop::drop`.
        let drop_guard = CopyOnDrop { src: scratch_base, dst: v_base, len };

        // SAFETY: at this point scratch_base is fully initialized, allowing us
        // to use it as the source of our merge back into the original array.
        // If a panic occurs we ensure the original array is restored to a valid
        // permutation of the input through drop_guard. This technique is similar
        // to ping-pong merging.
        bidirectional_merge(
            slice::from_raw_parts(drop_guard.src, drop_guard.len),
            drop_guard.dst,
            is_less,
        );
        //@ close CopyOnDrop_own::<T>(t, drop_guard);
        mem::forget(drop_guard);
        //@ assert array::<T>(v_base, len, ?ds);
        //@ take_append(h, sl2, sr2);
        //@ drop_append(h, sl2, sr2);
        //@ is_perm_append_both(sl2, L, sr2, R);
        //@ is_perm_trans(ds, append(sl2, sr2), vs);
        //@ is_perm_sym(ds, vs);
        //@ foreach_perm(vs, ds);
        //@ array_to_array_(sb);
        //@ array__join_n(sb, len, slen - len);
        //@ std::mem::array__to_array_MaybeUninit(sb);
        //@ assert array::<std::mem::MaybeUninit<T>>(sbm, slen, ?ss1);
        //@ foreach_MaybeUninit_own(t, ss1);
    }
}

struct CopyOnDrop<T> {
    src: *const T,
    dst: *mut T,
    len: usize,
}

/*@
// `CopyOnDrop<T>` holds raw pointers only; it owns nothing. (Its `drop` runs only while unwinding: on the
// normal paths the module forgets every guard, after rewrite 001 also in `insert_tail`.)
pred<T> <CopyOnDrop<T>>.own(t, v) = true;
@*/

impl<T> Drop for CopyOnDrop<T> {
    fn drop(&mut self) {
        // SAFETY: `src` must contain `len` initialized elements, and dst must
        // be valid to write `len` elements.
        unsafe {
            ptr::copy_nonoverlapping(self.src, self.dst, self.len);
        }
    }
}

fn small_sort_network<T, F>(v: &mut [T], is_less: &mut F)
where
    T: FreezeMarker,
    F: FnMut(&T, &T) -> bool,
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        is_perm(vs1, vs) && sorted_by(is_less_model_of::<T, F>(f0), vs1)
    } else {
        true
    };
@*/
/*@
on_unwind_ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1);
@*/
{
    // This implementation is tuned to be efficient for integer types.

    let len = v.len();
    if len < 2 {
        //@ match vs { nil => {} cons(v0, vs0) => { match vs0 { nil => {} cons(v1, vs1) => {} } } }
        //@ is_perm_refl(vs);
        return;
    }

    if len > SMALL_SORT_NETWORK_SCRATCH_LEN {
        intrinsics::abort_immediate();
    }

    // VeriFast rewrite (rewrites/006): `MaybeUninit::uninit()` through a trusted wrapper (VeriFast 26.10
    // has no spec for it).
    let mut stack_array = unsafe { maybe_uninit_uninit__VeriFast_wrapper::<[T; SMALL_SORT_NETWORK_SCRATCH_LEN]>() };

    let len_div_2 = len / 2;
    //@ div_rem_nonneg(len, 2);
    let no_merge = len < 18;

    let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);
    let initial_region_len = if no_merge { len } else { len_div_2 };
    //@ let h = len_div_2;
    //@ let il = initial_region_len;
    //@ let m = is_less_models::<T, F>(f0);
    //@ let lt = is_less_model_of::<T, F>(f0);
    //@ array_split(v_base, il);
    //@ foreach_split(vs, own::<T>(t), il);
    //@ array_nonnull_aligned(v_base);
    // SAFETY: Both possible values of `initial_region_len` are in-bounds.
    let mut region = unsafe { slice::from_raw_parts_mut(v_base, initial_region_len) };
    //@ close exists::<bool>(false);
    //@ assert [?qlft]lifetime_token(?klft);

    // Avoid compiler unrolling, we *really* don't want that to happen here for binary-size reasons.
    loop {
        /*@
        inv thread_token(t) &*& [qlft]lifetime_token(klft) &*& *is_less |-> ?f &*& <F>.own(t, f) &*& (!m || f == f0) &*&
            stack_array |-> ?sa &*& exists::<bool>(?c1) &*&
            if !c1 {
                strip_pointer_metadata(region as pointer) as *T == v_base &*& region.len() == il &*&
                array::<T>(v_base, il, take(il, vs)) &*& foreach(take(il, vs), own::<T>(t)) &*&
                array::<T>(v_base + il, len - il, drop(il, vs)) &*& foreach(drop(il, vs), own::<T>(t))
            } else {
                !no_merge &*& strip_pointer_metadata(region as pointer) as *T == v_base + h &*& region.len() == len - h &*&
                array::<T>(v_base, h, ?A) &*& foreach(A, own::<T>(t)) &*& (!m || is_perm(A, take(h, vs)) && sorted_by(lt, A)) &*&
                array::<T>(v_base + h, len - h, ?B) &*& foreach(B, own::<T>(t)) &*& (!m || is_perm(B, drop(h, vs)))
            };
        @*/
        //@ open exists::<bool>(c1);
        //@ assert array::<T>(strip_pointer_metadata(region as pointer) as *T, region.len(), ?w0);
        let presorted_len = if region.len() >= 13 {
            sort13_optimal(region, is_less);
            13
        } else if region.len() >= 9 {
            sort9_optimal(region, is_less);
            9
        } else {
            //@ is_perm_refl(w0);
            //@ sorted_take1(lt, w0);
            1
        };
        //@ assert array::<T>(strip_pointer_metadata(region as pointer) as *T, region.len(), ?w1);

        insertion_sort_shift_left(region, presorted_len, is_less);
        //@ assert array::<T>(strip_pointer_metadata(region as pointer) as *T, region.len(), ?w2);
        //@ if m { is_perm_trans(w2, w1, w0); }

        if no_merge {
            //@ open array::<T>(v_base + il, 0, _);
            //@ open foreach(drop(il, vs), own::<T>(t));
            //@ close array::<T>(v_base + il, 0, nil);
            //@ array_join_n(v_base, il, 0);
            return;
        }

        if region.as_ptr() != v_base {
            //@ if m && c1 { is_perm_trans(w2, w0, drop(h, vs)); }
            //@ close exists::<bool>(c1);
            break;
        }

        //@ array_ptr_within_limits(v_base, h);
        //@ if !c1 { array_nonnull_aligned(v_base + il); } else { array_nonnull_aligned(v_base + h); }
        // SAFETY: The right side of `v` based on `len_div_2` is guaranteed in-bounds.
        unsafe { region = slice::from_raw_parts_mut(v_base.add(len_div_2), len - len_div_2) };
        /*@
        if m {
            if !c1 {
                is_perm_refl(drop(h, vs));
            } else {
                is_perm_trans(w2, w0, drop(h, vs));
            }
        }
        @*/
        //@ close exists::<bool>(true);
    }
    //@ open exists::<bool>(?c1e);
    //@ assert array::<T>(v_base, h, ?A) &*& array::<T>(v_base + h, len - h, ?B);

    // SAFETY: We checked that T is Freeze and thus observation safe.
    // Should is_less panic v was not modified in parity_merge and retains it's original input.
    // scratch and v must not alias and scratch has v.len() space.
    unsafe {
        //@ std::mem::open_MaybeUninit(&stack_array);
        //@ Array__to_array_(&stack_array as *[T; 32]);
        //@ let sp = &stack_array as *T;
        //@ array__split_n(sp, len);
        //@ array_join_n(v_base, h, len - h);
        //@ array_nonnull_aligned(v_base);
        let scratch_base = maybe_uninit_as_mut_ptr__VeriFast_wrapper(&mut stack_array) as *mut T;
        bidirectional_merge(slice::from_raw_parts_mut(v_base, len), scratch_base, is_less);
        //@ assert array::<T>(sp, len, ?ds);
        //@ array_to_array_(v_base);
        ptr::copy_nonoverlapping(scratch_base, v_base, len);
        //@ take_append(h, A, B);
        //@ drop_append(h, A, B);
        //@ if m { is_perm_append_both(A, take(h, vs), B, drop(h, vs)); is_perm_trans(ds, append(A, B), vs); }
        //@ foreach_append(A, B);
        //@ is_perm_sym(ds, append(A, B));
        //@ foreach_perm(append(A, B), ds);
        //@ array_to_array_(sp);
        //@ array__join_n(sp, len, 32 - len);
        //@ MaybeUninit_array_32_layout::<T>();
        //@ array__to_u8s_(sp, 32);
        //@ from_u8s_(&stack_array);
    }
}

/// Swap two values in the slice pointed to by `v_base` at the position `a_pos` and `b_pos` if the
/// value at position `b_pos` is less than the one at position `a_pos`.
///
/// Purposefully not marked `#[inline]`, despite us wanting it to be inlined for integers like
/// types. `is_less` could be a huge function and we want to give the compiler an option to
/// not inline this function. For the same reasons that this function is very perf critical
/// it should be in the same module as the functions that use it.
unsafe fn swap_if_less<T, F>(v_base: *mut T, a_pos: usize, b_pos: usize, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
/*@
req thread_token(?t) &*& array::<T>(v_base, ?n, ?vs) &*& a_pos < n &*& b_pos < n &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*& array::<T>(v_base, n, ?vs1) &*& is_perm(vs1, vs) == true &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 &*& [_]step_done(is_less_model_of::<T, F>(f0), a_pos, b_pos, vs, vs1)
    } else {
        true
    };
@*/
{
    // SAFETY: the caller must guarantee that `a_pos` and `b_pos` each added to `v_base` yield valid
    // pointers into `v_base`, and are properly aligned, and part of the same allocation.
    unsafe {
        //@ let va = nth(a_pos, vs);
        //@ let vb = nth(b_pos, vs);
        //@ if a_pos == b_pos { array_open_at(v_base, a_pos); } else { array_open_at2(v_base, a_pos, b_pos); points_to_limits(v_base + b_pos); }
        //@ points_to_limits(v_base + a_pos);
        let v_a = v_base.add(a_pos);
        let v_b = v_base.add(b_pos);

        // PANIC SAFETY: if is_less panics, no scratch memory was created and the slice should still be
        // in a well defined state, without duplicates.

        // Important to only swap if it is more and not if it is equal. is_less should return false for
        // equal, so we don't swap.
        //@ pt_hide_half(v_a);
        //@ if a_pos == b_pos { points_to_split_half(v_a); } else { pt_hide_half(v_b); }
        let should_swap = is_less__VeriFast_wrapper(is_less, &*v_b, &*v_a);
        //@ pt_unhide(v_a);
        //@ if a_pos != b_pos { pt_unhide(v_b); }

        // This is a branchless version of swap if.
        // The equivalent code with a branch would be:
        //
        // if should_swap {
        //     ptr::swap(v_a, v_b, 1);
        // }

        // The goal is to generate cmov instructions here.
        //@ close raw_ptr_own::<T>()(t, v_b);
        //@ close raw_ptr_own::<T>()(t, v_a);
        let v_a_swap = hint::select_unpredictable(should_swap, v_b, v_a);
        //@ open raw_ptr_own::<T>()(t, v_a_swap);
        //@ close raw_ptr_own::<T>()(t, v_a);
        //@ close raw_ptr_own::<T>()(t, v_b);
        let v_b_swap = hint::select_unpredictable(should_swap, v_a, v_b);
        //@ open raw_ptr_own::<T>()(t, v_b_swap);

        //@ if should_swap { assert v_b_swap == v_a &*& v_a_swap == v_b; } else { assert v_b_swap == v_b &*& v_a_swap == v_a; }
        let v_b_swap_tmp = ManuallyDrop::new(ptr::read(v_b_swap));
        /*@
        if should_swap && a_pos != b_pos {
            to_u8s_(v_b);
            to_u8s_(v_a);
            close exists::<option<isize>>(none);
        } else {
            to_u8s_(v_a);
            close exists::<option<isize>>(some(0));
        }
        @*/
        ptr_copy_1__VeriFast_wrapper(v_a_swap, v_a);
        /*@
        if should_swap && a_pos != b_pos {
            from_u8s_(v_b);
            from_u8s_(v_a);
            close points_to::<T>(v_b, vb);
            close points_to::<T>(v_a, vb);
        } else {
            from_u8s_(v_a);
            close points_to::<T>(v_a, va);
        }
        @*/
        //@ let tp = &v_b_swap_tmp as *T;
        //@ assert [?ff](*tp |-> ?mdv);
        //@ points_to_limits(tp);
        //@ close [ff]array::<T>(tp + 1, 0, nil);
        //@ close [ff]array::<T>(tp, 1, [mdv]);
        //@ if a_pos != b_pos { close array::<T>(v_b + 1, 0, nil); close array::<T>(v_b, 1, [*v_b]); } else { close array::<T>(v_a + 1, 0, nil); close array::<T>(v_a, 1, [*v_a]); }
        ptr::copy_nonoverlapping(&*v_b_swap_tmp, v_b, 1);
        //@ open [ff]array::<T>(tp, 1, _);
        //@ open [ff]array::<T>(tp + 1, 0, _);
        //@ open array::<T>(v_b, 1, _);
        //@ open array::<T>(v_b + 1, 0, _);
        /*@
        if a_pos == b_pos {
            array_close_at(v_base, a_pos, va);
            update_nth_nth(a_pos, vs);
            is_perm_refl(vs);
            if is_less_models::<T, F>(f0) { is_less_irreflexive::<T, F>(f0, va); }
        } else if should_swap {
            array_close_at2(v_base, a_pos, b_pos, vb, va);
            is_perm_swap(a_pos, b_pos, vs);
        } else {
            array_close_at2(v_base, a_pos, b_pos, va, vb);
            update_nth_nth(b_pos, vs);
            update_nth_nth(a_pos, vs);
            is_perm_refl(vs);
        }
        @*/
        /*@
        if is_less_models::<T, F>(f0) {
            assert array::<T>(v_base, _, ?vs_end);
            close step_done(is_less_model_of::<T, F>(f0), a_pos, b_pos, vs, vs_end);
            leak step_done(is_less_model_of::<T, F>(f0), a_pos, b_pos, vs, vs_end);
        }
        @*/
    }
}

/// Sorts the first 9 elements of `v` with a fast fixed function.
///
/// Should `is_less` generate substantial amounts of code the compiler can choose to not inline
/// `swap_if_less`. If the code of a sort impl changes so as to call this function in multiple
/// places, `#[inline(never)]` is recommended to keep binary-size in check. The current design of
/// `small_sort_network` makes sure to only call this once.
fn sort9_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*& is_perm(vs1, vs) == true &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 &*& sorted_by(is_less_model_of::<T, F>(f0), take(9, vs1)) == true
    } else {
        true
    };
@*/
{
    if v.len() < 9 {
        intrinsics::abort_immediate();
    }

    let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);
    //@ let w0 = vs;
    //@ is_perm_refl(vs);

    // Optimal sorting network see:
    // https://bertdobbelaere.github.io/sorting_networks.html.

    // SAFETY: We checked the len.
    unsafe {
        swap_if_less(v_base, 0, 3, is_less);
        //@ assert array::<T>(v_base, _, ?w1);
        //@ is_perm_trans(w1, w0, vs);
        swap_if_less(v_base, 1, 7, is_less);
        //@ assert array::<T>(v_base, _, ?w2);
        //@ is_perm_trans(w2, w1, vs);
        swap_if_less(v_base, 2, 5, is_less);
        //@ assert array::<T>(v_base, _, ?w3);
        //@ is_perm_trans(w3, w2, vs);
        swap_if_less(v_base, 4, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w4);
        //@ is_perm_trans(w4, w3, vs);
        swap_if_less(v_base, 0, 7, is_less);
        //@ assert array::<T>(v_base, _, ?w5);
        //@ is_perm_trans(w5, w4, vs);
        swap_if_less(v_base, 2, 4, is_less);
        //@ assert array::<T>(v_base, _, ?w6);
        //@ is_perm_trans(w6, w5, vs);
        swap_if_less(v_base, 3, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w7);
        //@ is_perm_trans(w7, w6, vs);
        swap_if_less(v_base, 5, 6, is_less);
        //@ assert array::<T>(v_base, _, ?w8);
        //@ is_perm_trans(w8, w7, vs);
        swap_if_less(v_base, 0, 2, is_less);
        //@ assert array::<T>(v_base, _, ?w9);
        //@ is_perm_trans(w9, w8, vs);
        swap_if_less(v_base, 1, 3, is_less);
        //@ assert array::<T>(v_base, _, ?w10);
        //@ is_perm_trans(w10, w9, vs);
        swap_if_less(v_base, 4, 5, is_less);
        //@ assert array::<T>(v_base, _, ?w11);
        //@ is_perm_trans(w11, w10, vs);
        swap_if_less(v_base, 7, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w12);
        //@ is_perm_trans(w12, w11, vs);
        swap_if_less(v_base, 1, 4, is_less);
        //@ assert array::<T>(v_base, _, ?w13);
        //@ is_perm_trans(w13, w12, vs);
        swap_if_less(v_base, 3, 6, is_less);
        //@ assert array::<T>(v_base, _, ?w14);
        //@ is_perm_trans(w14, w13, vs);
        swap_if_less(v_base, 5, 7, is_less);
        //@ assert array::<T>(v_base, _, ?w15);
        //@ is_perm_trans(w15, w14, vs);
        swap_if_less(v_base, 0, 1, is_less);
        //@ assert array::<T>(v_base, _, ?w16);
        //@ is_perm_trans(w16, w15, vs);
        swap_if_less(v_base, 2, 4, is_less);
        //@ assert array::<T>(v_base, _, ?w17);
        //@ is_perm_trans(w17, w16, vs);
        swap_if_less(v_base, 3, 5, is_less);
        //@ assert array::<T>(v_base, _, ?w18);
        //@ is_perm_trans(w18, w17, vs);
        swap_if_less(v_base, 6, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w19);
        //@ is_perm_trans(w19, w18, vs);
        swap_if_less(v_base, 2, 3, is_less);
        //@ assert array::<T>(v_base, _, ?w20);
        //@ is_perm_trans(w20, w19, vs);
        swap_if_less(v_base, 4, 5, is_less);
        //@ assert array::<T>(v_base, _, ?w21);
        //@ is_perm_trans(w21, w20, vs);
        swap_if_less(v_base, 6, 7, is_less);
        //@ assert array::<T>(v_base, _, ?w22);
        //@ is_perm_trans(w22, w21, vs);
        swap_if_less(v_base, 1, 2, is_less);
        //@ assert array::<T>(v_base, _, ?w23);
        //@ is_perm_trans(w23, w22, vs);
        swap_if_less(v_base, 3, 4, is_less);
        //@ assert array::<T>(v_base, _, ?w24);
        //@ is_perm_trans(w24, w23, vs);
        swap_if_less(v_base, 5, 6, is_less);
        //@ assert array::<T>(v_base, _, ?w25);
        //@ is_perm_trans(w25, w24, vs);
        /*@
        if is_less_models::<T, F>(f0) {
            net9_sorted::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25);
        }
        @*/
        //@ is_perm_sym(w25, vs);
        //@ foreach_perm(vs, w25);
    }
}

/// Sorts the first 13 elements of `v` with a fast fixed function.
///
/// Should `is_less` generate substantial amounts of code the compiler can choose to not inline
/// `swap_if_less`. If the code of a sort impl changes so as to call this function in multiple
/// places, `#[inline(never)]` is recommended to keep binary-size in check. The current design of
/// `small_sort_network` makes sure to only call this once.
fn sort13_optimal<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*& is_perm(vs1, vs) == true &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 &*& sorted_by(is_less_model_of::<T, F>(f0), take(13, vs1)) == true
    } else {
        true
    };
@*/
{
    if v.len() < 13 {
        intrinsics::abort_immediate();
    }

    let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);
    //@ let w0 = vs;
    //@ is_perm_refl(vs);

    // Optimal sorting network see:
    // https://bertdobbelaere.github.io/sorting_networks.html.

    // SAFETY: We checked the len.
    unsafe {
        swap_if_less(v_base, 0, 12, is_less);
        //@ assert array::<T>(v_base, _, ?w1);
        //@ is_perm_trans(w1, w0, vs);
        swap_if_less(v_base, 1, 10, is_less);
        //@ assert array::<T>(v_base, _, ?w2);
        //@ is_perm_trans(w2, w1, vs);
        swap_if_less(v_base, 2, 9, is_less);
        //@ assert array::<T>(v_base, _, ?w3);
        //@ is_perm_trans(w3, w2, vs);
        swap_if_less(v_base, 3, 7, is_less);
        //@ assert array::<T>(v_base, _, ?w4);
        //@ is_perm_trans(w4, w3, vs);
        swap_if_less(v_base, 5, 11, is_less);
        //@ assert array::<T>(v_base, _, ?w5);
        //@ is_perm_trans(w5, w4, vs);
        swap_if_less(v_base, 6, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w6);
        //@ is_perm_trans(w6, w5, vs);
        swap_if_less(v_base, 1, 6, is_less);
        //@ assert array::<T>(v_base, _, ?w7);
        //@ is_perm_trans(w7, w6, vs);
        swap_if_less(v_base, 2, 3, is_less);
        //@ assert array::<T>(v_base, _, ?w8);
        //@ is_perm_trans(w8, w7, vs);
        swap_if_less(v_base, 4, 11, is_less);
        //@ assert array::<T>(v_base, _, ?w9);
        //@ is_perm_trans(w9, w8, vs);
        swap_if_less(v_base, 7, 9, is_less);
        //@ assert array::<T>(v_base, _, ?w10);
        //@ is_perm_trans(w10, w9, vs);
        swap_if_less(v_base, 8, 10, is_less);
        //@ assert array::<T>(v_base, _, ?w11);
        //@ is_perm_trans(w11, w10, vs);
        swap_if_less(v_base, 0, 4, is_less);
        //@ assert array::<T>(v_base, _, ?w12);
        //@ is_perm_trans(w12, w11, vs);
        swap_if_less(v_base, 1, 2, is_less);
        //@ assert array::<T>(v_base, _, ?w13);
        //@ is_perm_trans(w13, w12, vs);
        swap_if_less(v_base, 3, 6, is_less);
        //@ assert array::<T>(v_base, _, ?w14);
        //@ is_perm_trans(w14, w13, vs);
        swap_if_less(v_base, 7, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w15);
        //@ is_perm_trans(w15, w14, vs);
        swap_if_less(v_base, 9, 10, is_less);
        //@ assert array::<T>(v_base, _, ?w16);
        //@ is_perm_trans(w16, w15, vs);
        swap_if_less(v_base, 11, 12, is_less);
        //@ assert array::<T>(v_base, _, ?w17);
        //@ is_perm_trans(w17, w16, vs);
        swap_if_less(v_base, 4, 6, is_less);
        //@ assert array::<T>(v_base, _, ?w18);
        //@ is_perm_trans(w18, w17, vs);
        swap_if_less(v_base, 5, 9, is_less);
        //@ assert array::<T>(v_base, _, ?w19);
        //@ is_perm_trans(w19, w18, vs);
        swap_if_less(v_base, 8, 11, is_less);
        //@ assert array::<T>(v_base, _, ?w20);
        //@ is_perm_trans(w20, w19, vs);
        swap_if_less(v_base, 10, 12, is_less);
        //@ assert array::<T>(v_base, _, ?w21);
        //@ is_perm_trans(w21, w20, vs);
        swap_if_less(v_base, 0, 5, is_less);
        //@ assert array::<T>(v_base, _, ?w22);
        //@ is_perm_trans(w22, w21, vs);
        swap_if_less(v_base, 3, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w23);
        //@ is_perm_trans(w23, w22, vs);
        swap_if_less(v_base, 4, 7, is_less);
        //@ assert array::<T>(v_base, _, ?w24);
        //@ is_perm_trans(w24, w23, vs);
        swap_if_less(v_base, 6, 11, is_less);
        //@ assert array::<T>(v_base, _, ?w25);
        //@ is_perm_trans(w25, w24, vs);
        swap_if_less(v_base, 9, 10, is_less);
        //@ assert array::<T>(v_base, _, ?w26);
        //@ is_perm_trans(w26, w25, vs);
        swap_if_less(v_base, 0, 1, is_less);
        //@ assert array::<T>(v_base, _, ?w27);
        //@ is_perm_trans(w27, w26, vs);
        swap_if_less(v_base, 2, 5, is_less);
        //@ assert array::<T>(v_base, _, ?w28);
        //@ is_perm_trans(w28, w27, vs);
        swap_if_less(v_base, 6, 9, is_less);
        //@ assert array::<T>(v_base, _, ?w29);
        //@ is_perm_trans(w29, w28, vs);
        swap_if_less(v_base, 7, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w30);
        //@ is_perm_trans(w30, w29, vs);
        swap_if_less(v_base, 10, 11, is_less);
        //@ assert array::<T>(v_base, _, ?w31);
        //@ is_perm_trans(w31, w30, vs);
        swap_if_less(v_base, 1, 3, is_less);
        //@ assert array::<T>(v_base, _, ?w32);
        //@ is_perm_trans(w32, w31, vs);
        swap_if_less(v_base, 2, 4, is_less);
        //@ assert array::<T>(v_base, _, ?w33);
        //@ is_perm_trans(w33, w32, vs);
        swap_if_less(v_base, 5, 6, is_less);
        //@ assert array::<T>(v_base, _, ?w34);
        //@ is_perm_trans(w34, w33, vs);
        swap_if_less(v_base, 9, 10, is_less);
        //@ assert array::<T>(v_base, _, ?w35);
        //@ is_perm_trans(w35, w34, vs);
        swap_if_less(v_base, 1, 2, is_less);
        //@ assert array::<T>(v_base, _, ?w36);
        //@ is_perm_trans(w36, w35, vs);
        swap_if_less(v_base, 3, 4, is_less);
        //@ assert array::<T>(v_base, _, ?w37);
        //@ is_perm_trans(w37, w36, vs);
        swap_if_less(v_base, 5, 7, is_less);
        //@ assert array::<T>(v_base, _, ?w38);
        //@ is_perm_trans(w38, w37, vs);
        swap_if_less(v_base, 6, 8, is_less);
        //@ assert array::<T>(v_base, _, ?w39);
        //@ is_perm_trans(w39, w38, vs);
        swap_if_less(v_base, 2, 3, is_less);
        //@ assert array::<T>(v_base, _, ?w40);
        //@ is_perm_trans(w40, w39, vs);
        swap_if_less(v_base, 4, 5, is_less);
        //@ assert array::<T>(v_base, _, ?w41);
        //@ is_perm_trans(w41, w40, vs);
        swap_if_less(v_base, 6, 7, is_less);
        //@ assert array::<T>(v_base, _, ?w42);
        //@ is_perm_trans(w42, w41, vs);
        swap_if_less(v_base, 8, 9, is_less);
        //@ assert array::<T>(v_base, _, ?w43);
        //@ is_perm_trans(w43, w42, vs);
        swap_if_less(v_base, 3, 4, is_less);
        //@ assert array::<T>(v_base, _, ?w44);
        //@ is_perm_trans(w44, w43, vs);
        swap_if_less(v_base, 5, 6, is_less);
        //@ assert array::<T>(v_base, _, ?w45);
        //@ is_perm_trans(w45, w44, vs);
        /*@
        if is_less_models::<T, F>(f0) {
            net13_sorted::<T, F>(f0, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45);
        }
        @*/
        //@ is_perm_sym(w45, vs);
        //@ foreach_perm(vs, w45);
    }
}

/// Sorts range [begin, tail] assuming [begin, tail) is already sorted.
///
/// # Safety
/// begin < tail and p must be valid and initialized for all begin <= p <= tail.
unsafe fn insert_tail<T, F: FnMut(&T, &T) -> bool>(begin: *mut T, tail: *mut T, is_less: &mut F)
/*@
req thread_token(?t) &*& array::<T>(begin, ?n, ?vs) &*& 2 <= n &*& tail == begin + (n - 1) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*& array::<T>(begin, n, ?vs1) &*& *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    is_perm(vs1, vs) == true &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 &*&
        (!sorted_by(is_less_model_of::<T, F>(f0), take(n - 1, vs)) || sorted_by(is_less_model_of::<T, F>(f0), vs1))
    } else {
        true
    };
@*/
{
    // SAFETY: see individual comments.
    unsafe {
        //@ let k = n - 1;
        //@ let P = take(k, vs);
        //@ let x = nth(k, vs);
        //@ let lt = is_less_model_of::<T, F>(f0);
        //@ let m = is_less_models::<T, F>(f0);
        //@ array_split(begin, k);
        //@ drop_n_plus_one(k, vs);
        //@ open array::<T>(tail, 1, _);
        //@ open array::<T>(tail + 1, 0, _);
        //@ array_split_last(begin, k - 1);
        // SAFETY: in-bounds as tail > begin.
        let mut sift = tail.sub(1);
        //@ pt_hide_half(tail);
        //@ pt_hide_half(sift);
        if !is_less__VeriFast_wrapper(is_less, &*tail, &*sift) {
            //@ pt_unhide(tail);
            //@ pt_unhide(sift);
            //@ array_join_last(begin, k - 1);
            //@ close array::<T>(tail + 1, 0, nil);
            //@ close array::<T>(tail, 1, [x]);
            //@ array_join(begin);
            //@ is_perm_refl(vs);
            //@ if m && sorted_by(lt, P) { sorted_insert_at(lt, k, x, P); }
            return;
        }
        //@ pt_unhide(tail);
        //@ pt_unhide(sift);
        //@ array_join_last(begin, k - 1);

        // SAFETY: after this read tail is never read from again, as we only ever
        // read from sift, sift < tail and we only ever decrease sift. Thus this is
        // effectively a move, not a copy. Should a panic occur, or we have found
        // the correct insertion position, gap_guard ensures the element is moved
        // back into the array.
        let tmp = ManuallyDrop::new(tail.read());
        let mut gap_guard = CopyOnDrop { src: &*tmp, dst: tail, len: 1 };
        //@ close array::<T>(tail + 1, 0, nil);
        //@ assert [?ft](*(&tmp) |-> x);

        loop {
            /*@
            inv thread_token(t) &*& *is_less |-> ?f &*& <F>.own(t, f) &*& (!m || f == f0) &*&
                array::<T>(begin, ?j1, ?pre) &*& 1 <= j1 &*& j1 <= k &*& pre == take(j1, P) &*&
                sift == begin + (j1 - 1) &*&
                *(begin + j1) |-> ?g0 &*&
                array::<T>(begin + j1 + 1, k - j1, drop(j1, P)) &*&
                (!m || apply_lt(lt, x, nth(j1 - 1, P))) &*&
                gap_guard.src |-> (&tmp as *T) &*& gap_guard.dst |-> begin + j1 &*& gap_guard.len |-> 1 &*&
                [ft](*(&tmp) |-> x);
            @*/
            // SAFETY: we move sift into the gap (which is valid), and point the
            // gap guard destination at sift, ensuring that if a panic occurs the
            // gap is once again filled.
            //@ take_take(j1 - 1, j1, P);
            //@ array_split_last(begin, j1 - 1);
            //@ close array::<T>(sift, 1, [nth(j1 - 1, P)]);
            //@ let g = g0;
            //@ close array::<T>(begin + j1 + 1, 0, nil);
            //@ close array::<T>(begin + j1, 1, [g]);
            ptr::copy_nonoverlapping(sift, gap_guard.dst, 1);
            //@ open array::<T>(begin + j1, 1, _);
            //@ open array::<T>(begin + j1 + 1, 0, _);
            //@ close array::<T>(begin + j1, k - j1 + 1, cons(nth(j1 - 1, P), drop(j1, P)));
            //@ drop_n_plus_one(j1 - 1, P);
            //@ open array::<T>(sift, 1, _);
            //@ open array::<T>(sift + 1, 0, _);
            gap_guard.dst = sift;

            if sift == begin {
                /*@
                if m && j1 - 1 != 0 {
                    // `begin + (j1 - 1) == begin` with `j1 - 1 != 0`: `T` is zero-sized, so all its values are
                    // equal, and the comparator fact `lt(x, nth(j1 - 1, P))` contradicts irreflexivity.
                    ptr_add_eq_zst(begin, j1 - 1, sift);
                    zst_values_equal(&tmp as *T, sift);
                    is_less_irreflexive::<T, F>(f0, x);
                }
                @*/
                //@ close ins_facts(m, lt, x, P, j1 - 1);
                break;
            }

            // SAFETY: we checked that sift != begin, thus this is in-bounds.
            //@ take_take(j1 - 2, j1 - 1, P);
            //@ array_split_last(begin, j1 - 2);
            sift = sift.sub(1);
            //@ pt_hide_half(&tmp as *T);
            //@ pt_hide_half(sift);
            if !is_less__VeriFast_wrapper(is_less, &tmp, &*sift) {
                //@ pt_unhide(&tmp as *T);
                //@ pt_unhide(sift);
                //@ array_join_last(begin, j1 - 2);
                //@ assert !m || apply_lt(lt, x, nth(j1 - 1, P));
                //@ assert !m || !apply_lt(lt, x, nth(j1 - 2, take(j1 - 1, P)));
                //@ assert !m || !apply_lt(lt, x, nth(j1 - 2, P));
                //@ close ins_facts(m, lt, x, P, j1 - 1);
                break;
            }
            //@ pt_unhide(&tmp as *T);
            //@ pt_unhide(sift);
            //@ array_join_last(begin, j1 - 2);
        }
        //@ open ins_facts(m, lt, x, P, ?J);
        //@ points_to_limits(&tmp as *T);
        //@ close [ft]array::<T>((&tmp as *T) + 1, 0, nil);
        //@ close [ft]array::<T>(&tmp as *T, 1, [x]);
        //@ assert *(begin + J) |-> ?gJ;
        //@ close array::<T>(begin + J + 1, 0, nil);
        //@ close array::<T>(begin + J, 1, [gJ]);
        // VeriFast rewrite (rewrites/001): the drop of `gap_guard` at the end of this block, written out:
        // `CopyOnDrop::drop`'s body followed by `mem::forget`. Runtime-equivalent; see rewrites/LOG.md.
        ptr::copy_nonoverlapping(gap_guard.src, gap_guard.dst, gap_guard.len);
        //@ close CopyOnDrop_own::<T>(t, gap_guard);
        mem::forget(gap_guard);
        //@ open [ft]array::<T>(&tmp as *T, 1, _);
        //@ open [ft]array::<T>((&tmp as *T) + 1, 0, _);
    }
    //@ open array::<T>(begin + J, 1, _);
    //@ open array::<T>(begin + J + 1, 0, _);
    //@ close array::<T>(begin + J, k - J + 1, cons(x, drop(J, P)));
    //@ array_join_n(begin, J, k - J + 1);
    //@ is_perm_insert_at_cons(J, x, P);
    //@ is_perm_cons_snoc(x, P);
    //@ drop_n_plus_one(k, vs);
    //@ is_perm_trans(insert_at(J, x, P), cons(x, P), vs);
    /*@
    if m && sorted_by(lt, P) {
        if apply_lt(lt, nth(J, P), x) {
            is_less_transitive::<T, F>(f0, x, nth(J, P), x);
            is_less_irreflexive::<T, F>(f0, x);
        }
        sorted_insert_at(lt, J, x, P);
    }
    @*/
}

/// Sort `v` assuming `v[..offset]` is already sorted.
pub fn insertion_sort_shift_left<T, F: FnMut(&T, &T) -> bool>(
    v: &mut [T],
    offset: usize,
    is_less: &mut F,
)
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 &*& is_perm(vs1, vs) &&
        (!sorted_by(is_less_model_of::<T, F>(f0), take(offset, vs)) || sorted_by(is_less_model_of::<T, F>(f0), vs1))
    } else {
        true
    };
@*/
/*@
on_unwind_ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1);
@*/
{
    let len = v.len();
    if offset == 0 || offset > len {
        intrinsics::abort_immediate();
    }

    // SAFETY: see individual comments.
    unsafe {
        // We write this basic loop directly using pointers, as when we use a
        // for loop LLVM likes to unroll this loop which we do not want.
        // SAFETY: v_end is the one-past-end pointer, and we checked that
        // offset <= len, thus tail is also in-bounds.
        let v_base = slice_as_mut_ptr__VeriFast_wrapper(v);
        //@ let m = is_less_models::<T, F>(f0);
        //@ let lt = is_less_model_of::<T, F>(f0);
        let v_end = v_base.add(len);
        //@ array_split(v_base, offset);
        //@ array_join_n(v_base, offset, len - offset);
        let mut tail = v_base.add(offset);
        //@ close exists::<i32>(offset);
        //@ is_perm_refl(vs);
        //@ assert [?qlft]lifetime_token(?klft);
        while tail != v_end {
            /*@
            inv thread_token(t) &*& [qlft]lifetime_token(klft) &*& *is_less |-> ?f &*& <F>.own(t, f) &*& (!m || f == f0) &*&
                exists::<i32>(?i) &*& offset <= i &*& i < len &*& tail == v_base + i &*&
                array::<T>(v_base, len, ?ws) &*& foreach(ws, own::<T>(t)) &*& is_perm(ws, vs) == true &*&
                (!m || !sorted_by(lt, take(offset, vs)) || sorted_by(lt, take(i, ws)));
            @*/
            // SAFETY: v_base and tail are both valid pointers to elements, and
            // v_base < tail since we checked offset != 0.
            //@ array_split(v_base, i + 1);
            insert_tail(v_base, tail, is_less);
            //@ assert array::<T>(v_base, i + 1, ?ws1);
            //@ take_take(i, i + 1, ws);

            // SAFETY: we checked that tail is not yet the one-past-end pointer.
            tail = tail.add(1);
            //@ array_join_n(v_base, i + 1, len - i - 1);
            //@ let ws2 = append(ws1, drop(i + 1, ws));
            //@ is_perm_append_l(take(i + 1, ws), ws1, drop(i + 1, ws));
            //@ is_perm_trans(ws2, ws, vs);
            //@ is_perm_sym(ws2, ws);
            //@ foreach_perm(ws, ws2);
            //@ take_append_l(i + 1, ws1, drop(i + 1, ws));
            //@ open exists::<i32>(i);
            //@ close exists::<i32>(i + 1);
        }
        //@ open exists::<i32>(?ie);
        /*@
        if m && sorted_by(lt, take(offset, vs)) {
            assert array::<T>(v_base, len, ?wse);
            array_size_nonneg(v_base);
            if std::mem::size_of::<T>() == 0 {
                zst_array_sorted::<T, F>(f0, v_base, len);
            } else {
                ptr_add_inj(v_base, ie, len);
            }
        }
        @*/
    }
}

/// SAFETY: The caller MUST guarantee that `v_base` is valid for 4 reads and
/// `dst` is valid for 4 writes. The result will be stored in `dst[0..4]`.
pub unsafe fn sort4_stable<T, F: FnMut(&T, &T) -> bool>(
    v_base: *const T,
    dst: *mut T,
    is_less: &mut F,
)
/*@
req thread_token(?t) &*& [?fv]array::<T>(v_base, 4, ?vs) &*& array_::<T>(dst, 4, _) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*& [fv]array::<T>(v_base, 4, vs) &*&
    array::<T>(dst, 4, ?ds) &*& is_perm(ds, vs) == true &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 &*& sorted_by(is_less_model_of::<T, F>(f0), ds) == true
    } else {
        true
    };
@*/
{
    // By limiting select to picking pointers, we are guaranteed good cmov code-gen
    // regardless of type T's size. Further this only does 5 instead of 6
    // comparisons compared to a stable transposition 4 element sorting-network,
    // and always copies each element exactly once.

    // SAFETY: all pointers have offset at most 3 from v_base and dst, and are
    // thus in-bounds by the precondition.
    unsafe {
        //@ array4_open(v_base);
        //@ array__4_open(dst);
        //@ let v0 = nth(0, vs);
        //@ let v1 = nth(1, vs);
        //@ let v2 = nth(2, vs);
        //@ let v3 = nth(3, vs);
        //@ points_to_limits(v_base + 1);
        //@ points_to_limits(v_base + 2);
        //@ points_to_limits(v_base + 3);
        //@ points_to__limits(dst + 1);
        //@ points_to__limits(dst + 2);
        //@ points_to__limits(dst + 3);
        //@ let m = is_less_models::<T, F>(f0);
        //@ let lt = is_less_model_of::<T, F>(f0);
        // Stably create two pairs a <= b and c <= d.
        //@ pt_hide_half(v_base + 1);
        //@ pt_hide_half(v_base);
        let c1 = is_less__VeriFast_wrapper(is_less, &*v_base.add(1), &*v_base);
        //@ pt_unhide(v_base + 1);
        //@ pt_unhide(v_base);
        //@ if c1 {} else {}
        //@ pt_hide_half(v_base + 3);
        //@ pt_hide_half(v_base + 2);
        let c2 = is_less__VeriFast_wrapper(is_less, &*v_base.add(3), &*v_base.add(2));
        //@ pt_unhide(v_base + 3);
        //@ pt_unhide(v_base + 2);
        //@ if c2 {} else {}
        let a = v_base.add(c1 as usize);
        let b = v_base.add(!c1 as usize);
        let c = v_base.add(2 + c2 as usize);
        let d = v_base.add(2 + (!c2 as usize));
        //@ let va = *a;
        //@ let vb = *b;
        //@ let vc = *c;
        //@ let vd = *d;

        // Compare (a, c) and (b, d) to identify max/min. We're left with two
        // unknown elements, but because we are a stable sort we must know which
        // one is leftmost and which one is rightmost.
        // c3, c4 | min max unknown_left unknown_right
        //  0,  0 |  a   d    b         c
        //  0,  1 |  a   b    c         d
        //  1,  0 |  c   d    a         b
        //  1,  1 |  c   b    a         d
        //@ pt_hide_half(c);
        //@ pt_hide_half(a);
        let c3 = is_less__VeriFast_wrapper(is_less, &*c, &*a);
        //@ pt_unhide(c);
        //@ pt_unhide(a);
        //@ pt_hide_half(d);
        //@ pt_hide_half(b);
        let c4 = is_less__VeriFast_wrapper(is_less, &*d, &*b);
        //@ pt_unhide(d);
        //@ pt_unhide(b);
        //@ if c3 {} else {}
        //@ if c4 {} else {}
        //@ close raw_ptr_own::<T>()(t, c);
        //@ close raw_ptr_own::<T>()(t, a);
        let min = hint::select_unpredictable(c3, c, a);
        //@ open raw_ptr_own::<T>()(t, min);
        //@ close raw_ptr_own::<T>()(t, b);
        //@ close raw_ptr_own::<T>()(t, d);
        let max = hint::select_unpredictable(c4, b, d);
        //@ open raw_ptr_own::<T>()(t, max);
        //@ close raw_ptr_own::<T>()(t, a);
        //@ close raw_ptr_own::<T>()(t, c);
        //@ close raw_ptr_own::<T>()(t, b);
        let unknown_left = hint::select_unpredictable(c3, a, hint::select_unpredictable(c4, c, b));
        //@ open raw_ptr_own::<T>()(t, unknown_left);
        //@ close raw_ptr_own::<T>()(t, d);
        //@ close raw_ptr_own::<T>()(t, b);
        //@ close raw_ptr_own::<T>()(t, c);
        let unknown_right = hint::select_unpredictable(c4, d, hint::select_unpredictable(c3, b, c));
        //@ open raw_ptr_own::<T>()(t, unknown_right);
        //@ let vul = *unknown_left;
        //@ let vur = *unknown_right;

        // Sort the last two unknown elements.
        //@ pt_hide_half(unknown_right);
        //@ pt_hide_half(unknown_left);
        let c5 = is_less__VeriFast_wrapper(is_less, &*unknown_right, &*unknown_left);
        //@ pt_unhide(unknown_right);
        //@ pt_unhide(unknown_left);
        //@ if c5 {} else {}
        //@ close raw_ptr_own::<T>()(t, unknown_right);
        //@ close raw_ptr_own::<T>()(t, unknown_left);
        let lo = hint::select_unpredictable(c5, unknown_right, unknown_left);
        //@ open raw_ptr_own::<T>()(t, lo);
        //@ close raw_ptr_own::<T>()(t, unknown_left);
        //@ close raw_ptr_own::<T>()(t, unknown_right);
        let hi = hint::select_unpredictable(c5, unknown_left, unknown_right);
        //@ open raw_ptr_own::<T>()(t, hi);
        //@ let vmin = *min;
        //@ let vlo = *lo;
        //@ let vhi = *hi;
        //@ let vmax = *max;

        //@ array1_close(min);
        //@ array_1_close(dst);
        ptr::copy_nonoverlapping(min, dst, 1);
        //@ array1_open(min);
        //@ array1_open(dst);
        //@ array1_close(lo);
        //@ array_1_close(dst + 1);
        ptr::copy_nonoverlapping(lo, dst.add(1), 1);
        //@ array1_open(lo);
        //@ array1_open(dst + 1);
        //@ array1_close(hi);
        //@ array_1_close(dst + 2);
        ptr::copy_nonoverlapping(hi, dst.add(2), 1);
        //@ array1_open(hi);
        //@ array1_open(dst + 2);
        //@ array1_close(max);
        //@ array_1_close(dst + 3);
        ptr::copy_nonoverlapping(max, dst.add(3), 1);
        //@ array1_open(max);
        //@ array1_open(dst + 3);
        //@ array4_close(v_base);
        //@ open array_::<T>(dst + 4, 0, _);
        //@ close array::<T>(dst + 4, 0, nil);
        //@ array4_close(dst);
        /*@
        {
            let L0 = [v0, v1, v2, v3];
            is_perm_refl(L0);
            if c1 { perm_step(0, 1, L0, L0); }
            let L0b = if c1 { [v1, v0, v2, v3] } else { L0 };
            if c2 { perm_step(2, 3, L0b, L0); }
            let L1 = [va, vb, vc, vd];
            assert is_perm(L1, L0) == true;
            if !c3 && c4 {
                perm_step(1, 2, L1, L0);
                perm_step(2, 3, [va, vc, vb, vd], L0);
            } else if c3 && !c4 {
                perm_step(0, 2, L1, L0);
                perm_step(1, 2, [vc, vb, va, vd], L0);
            } else if c3 && c4 {
                perm_step(0, 2, L1, L0);
                perm_step(1, 2, [vc, vb, va, vd], L0);
                perm_step(2, 3, [vc, va, vb, vd], L0);
            }
            let L2 = [vmin, vul, vur, vmax];
            assert is_perm(L2, L0) == true;
            if c5 { perm_step(1, 2, L2, L0); }
            assert is_perm([vmin, vlo, vhi, vmax], L0) == true;
            if m {
                // !lt(b, a) and !lt(d, c)
                if c1 { lt_asym::<T, F>(f0, v1, v0); }
                if c2 { lt_asym::<T, F>(f0, v3, v2); }
                if c5 { lt_asym::<T, F>(f0, vur, vul); }
                if !c3 && !c4 {
                } else if !c3 && c4 {
                    lt_neg_trans::<T, F>(f0, va, vc, vd);
                    if !apply_lt(lt, vc, vb) { lt_neg_trans::<T, F>(f0, vb, vc, vd); }
                    lt_asym::<T, F>(f0, vc, vb);
                    lt_asym::<T, F>(f0, vd, vb);
                } else if c3 && !c4 {
                    lt_asym::<T, F>(f0, vc, va);
                    lt_neg_trans::<T, F>(f0, vc, va, vb);
                    lt_neg_trans::<T, F>(f0, va, vb, vd);
                } else {
                    lt_asym::<T, F>(f0, vc, va);
                    lt_asym::<T, F>(f0, vd, vb);
                }
            }
        }
        @*/
    }
}

/// SAFETY: The caller MUST guarantee that `v_base` is valid for 8 reads and
/// writes, `scratch_base` and `dst` MUST be valid for 8 writes. The result will
/// be stored in `dst[0..8]`.
unsafe fn sort8_stable<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v_base: *mut T,
    dst: *mut T,
    scratch_base: *mut T,
    is_less: &mut F,
)
/*@
req thread_token(?t) &*& [?fv]array::<T>(v_base, 8, ?vs) &*& array_::<T>(dst, 8, _) &*& array_::<T>(scratch_base, 8, _) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*& [fv]array::<T>(v_base, 8, vs) &*& array_::<T>(scratch_base, 8, _) &*&
    array::<T>(dst, 8, ?ds) &*& is_perm(ds, vs) == true &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 &*& sorted_by(is_less_model_of::<T, F>(f0), ds) == true
    } else {
        true
    };
@*/
{
    // SAFETY: these pointers are all in-bounds by the precondition of our function.
    unsafe {
        //@ array_split(v_base, 4);
        //@ array__split_n(scratch_base, 4);
        //@ array_ptr_within_limits(v_base, 4);
        sort4_stable(v_base, scratch_base, is_less);
        //@ assert array::<T>(scratch_base, 4, ?s1);
        //@ array__ptr_within_limits(scratch_base + 4, 0);
        sort4_stable(v_base.add(4), scratch_base.add(4), is_less);
        //@ assert array::<T>(scratch_base + 4, 4, ?s2);
        //@ array_join_n(v_base, 4, 4);
        //@ array_join_n(scratch_base, 4, 4);
        //@ array_open_at(scratch_base, 0);
        //@ to_u8s_(scratch_base);
        //@ from_u8s_(scratch_base);
        //@ close points_to::<T>(scratch_base, nth(0, append(s1, s2)));
        //@ points_to_limits(scratch_base);
        //@ array_close_at_same(scratch_base, 0);
    }

    // SAFETY: scratch_base[0..8] is now initialized, allowing us to merge back
    // into dst.
    unsafe {
        bidirectional_merge(slice::from_raw_parts(scratch_base, 8), dst, is_less);
        //@ assert array::<T>(dst, 8, ?ds8);
        //@ take_append(4, s1, s2);
        //@ drop_append(4, s1, s2);
        //@ is_perm_append_both(s1, take(4, vs), s2, drop(4, vs));
        //@ is_perm_trans(ds8, append(s1, s2), vs);
        //@ array_to_array_(scratch_base);
    }
}

#[inline(always)]
unsafe fn merge_up<T, F: FnMut(&T, &T) -> bool>(
    mut left_src: *const T,
    mut right_src: *const T,
    mut dst: *mut T,
    is_less: &mut F,
) -> (*const T, *const T, *mut T)
/*@
req thread_token(?t) &*& [?fl](*left_src |-> ?lv) &*& [?fr](*right_src |-> ?rv) &*& *dst |-> _ &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0) &*&
    pointer_within_limits(left_src + 1) == true &*& pointer_within_limits(right_src + 1) == true &*&
    pointer_within_limits(dst + 1) == true;
@*/
/*@
ens thread_token(t) &*& [fl](*left_src |-> lv) &*& [fr](*right_src |-> rv) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    exists::<bool>(?is_l) &*& *dst |-> (if is_l { lv } else { rv }) &*&
    result.0 == (if is_l { left_src + 1 } else { left_src }) &*&
    result.1 == (if is_l { right_src } else { right_src + 1 }) &*&
    result.2 == dst + 1 &*&
    if is_less_models::<T, F>(f0) { f1 == f0 &*& is_l == !apply_lt(is_less_model_of::<T, F>(f0), rv, lv) } else { true };
@*/
{
    // This is a branchless merge utility function.
    // The equivalent code with a branch would be:
    //
    // if !is_less(&*right_src, &*left_src) {
    //     ptr::copy_nonoverlapping(left_src, dst, 1);
    //     left_src = left_src.add(1);
    // } else {
    //     ptr::copy_nonoverlapping(right_src, dst, 1);
    //     right_src = right_src.add(1);
    // }
    // dst = dst.add(1);

    // SAFETY: The caller must guarantee that `left_src`, `right_src` are valid
    // to read and `dst` is valid to write, while not aliasing.
    unsafe {
        //@ pt_hide_half(right_src);
        //@ pt_hide_half(left_src);
        let is_l = !is_less__VeriFast_wrapper(is_less, &*right_src, &*left_src);
        //@ pt_unhide(right_src);
        //@ pt_unhide(left_src);
        let src = if is_l { left_src } else { right_src };
        //@ array1_close(src);
        //@ array_1_close(dst);
        ptr::copy_nonoverlapping(src, dst, 1);
        //@ array1_open(src);
        //@ array1_open(dst);
        right_src = right_src.add(!is_l as usize);
        left_src = left_src.add(is_l as usize);
        dst = dst.add(1);
        //@ close exists::<bool>(is_l);
    }

    (left_src, right_src, dst)
}

#[inline(always)]
unsafe fn merge_down<T, F: FnMut(&T, &T) -> bool>(
    mut left_src: *const T,
    mut right_src: *const T,
    mut dst: *mut T,
    is_less: &mut F,
) -> (*const T, *const T, *mut T)
/*@
req thread_token(?t) &*& [?fl](*left_src |-> ?lv) &*& [?fr](*right_src |-> ?rv) &*& *dst |-> _ &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0) &*&
    pointer_within_limits(dst - 1) == true &*& std::mem::size_of::<T>() <= isize::MAX;
@*/
/*@
ens thread_token(t) &*& [fl](*left_src |-> lv) &*& [fr](*right_src |-> rv) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    exists::<bool>(?is_l) &*& *dst |-> (if is_l { rv } else { lv }) &*&
    result.0 == ptr_wrapping_offset(left_src, if is_l { 0 } else { -1 }) &*&
    result.1 == ptr_wrapping_offset(right_src, if is_l { -1 } else { 0 }) &*&
    result.2 == dst - 1 &*&
    if is_less_models::<T, F>(f0) { f1 == f0 &*& is_l == !apply_lt(is_less_model_of::<T, F>(f0), rv, lv) } else { true };
@*/
{
    // This is a branchless merge utility function.
    // The equivalent code with a branch would be:
    //
    // if !is_less(&*right_src, &*left_src) {
    //     ptr::copy_nonoverlapping(right_src, dst, 1);
    //     right_src = right_src.wrapping_sub(1);
    // } else {
    //     ptr::copy_nonoverlapping(left_src, dst, 1);
    //     left_src = left_src.wrapping_sub(1);
    // }
    // dst = dst.sub(1);

    // SAFETY: The caller must guarantee that `left_src`, `right_src` are valid
    // to read and `dst` is valid to write, while not aliasing.
    unsafe {
        //@ pt_hide_half(right_src);
        //@ pt_hide_half(left_src);
        let is_l = !is_less__VeriFast_wrapper(is_less, &*right_src, &*left_src);
        //@ pt_unhide(right_src);
        //@ pt_unhide(left_src);
        let src = if is_l { right_src } else { left_src };
        //@ array1_close(src);
        //@ array_1_close(dst);
        ptr::copy_nonoverlapping(src, dst, 1);
        //@ array1_open(src);
        //@ array1_open(dst);
        right_src = const_ptr_wrapping_sub__VeriFast_wrapper(right_src, is_l as usize);
        left_src = const_ptr_wrapping_sub__VeriFast_wrapper(left_src, !is_l as usize);
        dst = dst.sub(1);
        //@ close exists::<bool>(is_l);
    }

    (left_src, right_src, dst)
}

/// Merge v assuming v[..len / 2] and v[len / 2..] are sorted.
///
/// Original idea for bi-directional merging by Igor van den Hoven (quadsort),
/// adapted to only use merge up and down. In contrast to the original
/// parity_merge function, it performs 2 writes instead of 4 per iteration.
///
/// # Safety
/// The caller must guarantee that `dst` is valid for v.len() writes.
/// Also `v.as_ptr()` and `dst` must not alias and v.len() must be >= 2.
///
/// Note that T must be Freeze, the comparison function is evaluated on outdated
/// temporary 'copies' that may not end up in the final array.
unsafe fn bidirectional_merge<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(
    v: &[T],
    dst: *mut T,
    is_less: &mut F,
)
/*@
req thread_token(?t) &*& [?fv]array::<T>(v as *T, v.len(), ?vs) &*& 2 <= v.len() &*&
    array_::<T>(dst, v.len(), _) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*& [fv]array::<T>(v as *T, v.len(), vs) &*&
    array::<T>(dst, v.len(), ?ds) &*& is_perm(ds, vs) == true &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 &*&
        (!sorted_by(is_less_model_of::<T, F>(f0), take(v.len() / 2, vs)) ||
         !sorted_by(is_less_model_of::<T, F>(f0), drop(v.len() / 2, vs)) ||
         sorted_by(is_less_model_of::<T, F>(f0), ds))
    } else {
        true
    };
@*/
{
    // It helps to visualize the merge:
    //
    // Initial:
    //
    //  |dst (in dst)
    //  |left               |right
    //  v                   v
    // [xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx]
    //                     ^                   ^
    //                     |left_rev           |right_rev
    //                                         |dst_rev (in dst)
    //
    // After:
    //
    //                      |dst (in dst)
    //        |left         |           |right
    //        v             v           v
    // [xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx]
    //       ^             ^           ^
    //       |left_rev     |           |right_rev
    //                     |dst_rev (in dst)
    //
    // In each iteration one of left or right moves up one position, and one of
    // left_rev or right_rev moves down one position, whereas dst always moves
    // up one position and dst_rev always moves down one position. Assuming
    // the input was sorted and the comparison function is correctly implemented
    // at the end we will have left == left_rev + 1, and right == right_rev + 1,
    // fully consuming the input having written it to dst.

    let len = v.len();
    let src = v.as_ptr();

    let len_div_2 = len / 2;

    //@ std::slice::slice_len_range(v);
    //@ div_rem_nonneg(len, 2);
    // SAFETY: The caller has to ensure that len >= 2.
    unsafe {
        intrinsics::assume(len_div_2 != 0); // This can avoid useless code-gen.
    }

    // SAFETY: no matter what the result of the user-provided comparison function
    // is, all 4 read pointers will always be in-bounds. Writing `dst` and `dst_rev`
    // will always be in bounds if the caller guarantees that `dst` is valid for
    // `v.len()` writes.
    unsafe {
        //@ let dst0 = dst;
        //@ let h = len_div_2;
        //@ let rl = len - h;
        //@ let L = take(h, vs);
        //@ let R = drop(h, vs);
        //@ let m = is_less_models::<T, F>(f0);
        //@ let lt = is_less_model_of::<T, F>(f0);
        //@ let ms = m && sorted_by(lt, L) && sorted_by(lt, R);
        //@ array_size_nonneg(src);
        //@ mul_mono_l(1, len, std::mem::size_of::<T>());
        //@ array_ptr_within_limits(src, h);
        //@ array_ptr_within_limits(src, h - 1);
        //@ array_ptr_within_limits(src, len - 1);
        //@ array__ptr_within_limits(dst, len - 1);
        let mut left = src;
        let mut right = src.add(len_div_2);
        let mut dst = dst;
        // (In ghost code, `dst_1` is this shadowing local; `dst` is the parameter.)

        let mut left_rev = src.add(len_div_2 - 1);
        let mut right_rev = src.add(len - 1);
        let mut dst_rev = dst.add(len - 1);
        //@ pwo_no_wrap(src + h, -1);
        //@ close exists::<pair<pair<i32, i32>, pair<i32, i32>>>(pair(pair(0, 0), pair(h, rl)));
        //@ close array::<T>(dst0, 0, nil);
        //@ array__ptr_within_limits(dst0, len);
        //@ close array::<T>(dst0 + len, 0, nil);
        //@ is_perm_refl::<T>(nil);
        //@ assert length(L) == h &*& length(R) == rl;
        //@ assert drop(h, L) == nil;
        //@ drop_length(R);
        //@ assert drop(rl, R) == nil;

        // VeriFast rewrite (rewrites/002): `for _ in 0..len_div_2 { .. }`, written as the `loop` it
        // desugars to, so that the iterator can be named in the loop invariant.
        {
        let mut iter = IntoIterator::into_iter(0..len_div_2);
        // (The two tuple temporaries of the destructuring assignments below live across iterations.)
        //@ assert struct_std_tuple_3__padding::<*T, *T, *T>(?tpa) &*& struct_std_tuple_3__padding::<*T, *T, *T>(?tpb);
        loop {
            /*@
            inv thread_token(t) &*& iter |-> ?it &*& it.end == h &*& 0 <= it.start &*& it.start <= h &*&
                struct_std_tuple_3__padding::<*T, *T, *T>(tpa) &*& std_tuple_3__0_::<*T, *T, *T>(tpa, _) &*&
                std_tuple_3__1_::<*T, *T, *T>(tpa, _) &*& std_tuple_3__2_::<*T, *T, *T>(tpa, _) &*&
                struct_std_tuple_3__padding::<*T, *T, *T>(tpb) &*& std_tuple_3__0_::<*T, *T, *T>(tpb, _) &*&
                std_tuple_3__1_::<*T, *T, *T>(tpb, _) &*& std_tuple_3__2_::<*T, *T, *T>(tpb, _) &*&
                *is_less |-> ?f &*& <F>.own(t, f) &*& (!m || f == f0) &*&
                [fv]array::<T>(src, len, vs) &*&
                exists::<pair<pair<i32, i32>, pair<i32, i32>>>(pair(pair(?i, ?j), pair(?qi, ?qj))) &*&
                i + j == it.start &*& (h - qi) + (rl - qj) == it.start &*& 0 <= i &*& 0 <= j &*& qi <= h &*& qj <= rl &*&
                left == src + i &*& right == src + (h + j) &*& dst_1 == dst0 + it.start &*&
                left_rev == ptr_wrapping_offset(src + qi, -1) &*& right_rev == src + (h + qj - 1) &*&
                dst_rev == dst0 + (len - 1 - it.start) &*&
                array::<T>(dst0, it.start, ?fw) &*& array_::<T>(dst0 + it.start, len - 2 * it.start, _) &*&
                array::<T>(dst0 + (len - it.start), it.start, ?bw) &*&
                is_perm(fw, append(take(i, L), take(j, R))) == true &*&
                is_perm(bw, append(drop(qi, L), drop(qj, R))) == true &*&
                (!ms ||
                    sorted_by(lt, fw) &&
                    (fw == nil || (i >= 1 && last(fw) == nth(i - 1, L)) || (j >= 1 && last(fw) == nth(j - 1, R))) &&
                    (fw == nil || ((i == h || !apply_lt(lt, nth(i, L), last(fw))) && (j == rl || !apply_lt(lt, nth(j, R), last(fw))))) &&
                    sorted_by(lt, bw) &&
                    (bw == nil || (qi < h && head(bw) == nth(qi, L)) || (qj < rl && head(bw) == nth(qj, R))) &&
                    (bw == nil || ((qi == 0 || !apply_lt(lt, head(bw), nth(qi - 1, L))) && (qj == 0 || !apply_lt(lt, head(bw), nth(qj - 1, R))))));
            @*/
            match Iterator::next(&mut iter) {
                None => break,
                Some(_) => {}
            };
            //@ let k = it.start;
            //@ open exists::<pair<pair<i32, i32>, pair<i32, i32>>>(pair(pair(i, j), pair(qi, qj)));
            // ----- forward step -----
            //@ let lv = nth(i, vs);
            //@ let rv = nth(h + j, vs);
            //@ assert i < h &*& j < rl;
            //@ nth_drop(j, h, vs);
            //@ nth_take_lt(i, h, vs);
            //@ assert nth(j, R) == rv;
            //@ array_ptr_within_limits(src, i + 1);
            //@ array_ptr_within_limits(src, h + j + 1);
            //@ array__ptr_within_limits(dst0 + k, 1);
            //@ array_open_at2(src, i, h + j);
            //@ open array_::<T>(dst0 + k, len - 2 * k, _);
            (left, right, dst) = merge_up(left, right, dst, is_less);
            //@ open exists::<bool>(?is_l);
            //@ array_close_at2_same(src, i, h + j);
            //@ let x = if is_l { lv } else { rv };
            //@ close array::<T>(dst0 + k + 1, 0, nil);
            //@ array_join_last(dst0, k);
            //@ let fw1 = append(fw, [x]);
            //@ let i1 = if is_l { i + 1 } else { i };
            //@ let j1 = if is_l { j } else { j + 1 };
            /*@
            if is_l {
                is_perm_snoc_middle(fw, take(i, L), take(j, R), x);
                take_plus_one(i, L);
            } else {
                is_perm_snoc_right(fw, take(i, L), take(j, R), x);
                take_plus_one(j, R);
            }
            @*/
            /*@
            if ms {
                sorted_snoc(lt, fw, x);
                last_snoc(fw, x);
                if is_l {
                    if i + 1 < h { sorted_adj(lt, L, i); }
                } else {
                    lt_asym::<T, F>(f0, rv, lv);
                    if j + 1 < rl { sorted_adj(lt, R, j); }
                }
            }
            @*/
            // ----- backward step -----
            //@ let lv2 = nth(qi - 1, vs);
            //@ let rv2 = nth(h + qj - 1, vs);
            //@ assert 1 <= qi &*& 1 <= qj;
            //@ nth_drop(qj - 1, h, vs);
            //@ nth_take_lt(qi - 1, h, vs);
            //@ assert nth(qj - 1, R) == rv2;
            //@ array_ptr_within_limits(src, qi);
            //@ mul_mono_l(0, qi - 1, std::mem::size_of::<T>());
            //@ mul_mono_l(0, h + qj - 2, std::mem::size_of::<T>());
            //@ pwo_no_wrap(src + qi, -1);
            //@ array_open_at2(src, qi - 1, h + qj - 1);
            //@ array__split_n(dst0 + (k + 1), len - 2 * k - 2);
            //@ open array_::<T>(dst0 + (len - 1 - k), 1, _);
            //@ open array_::<T>(dst0 + (len - 1 - k) + 1, 0, _);
            /*@
            if len - 2 * k - 2 == 0 {
                array_ptr_within_limits(dst0, k);
            } else {
                array__ptr_within_limits(dst0 + (k + 1), len - 2 * k - 3);
            }
            @*/
            (left_rev, right_rev, dst_rev) = merge_down(left_rev, right_rev, dst_rev, is_less);
            //@ open exists::<bool>(?is_l2);
            //@ array_close_at2_same(src, qi - 1, h + qj - 1);
            //@ let y = if is_l2 { rv2 } else { lv2 };
            //@ points_to_limits(dst0 + (len - 1 - k));
            //@ close array::<T>(dst0 + (len - 1 - k), k + 1, cons(y, bw));
            //@ let qi1 = if is_l2 { qi } else { qi - 1 };
            //@ let qj1 = if is_l2 { qj - 1 } else { qj };
            /*@
            if is_l2 {
                pwo_no_wrap(src + (qi - 1), 0);
                pwo_no_wrap(src + (h + qj - 1), -1);
                is_perm_cons_right(bw, drop(qi, L), drop(qj, R), y);
                drop_n_plus_one(qj - 1, R);
            } else {
                pwo_no_wrap(src + (h + qj - 1), 0);
                is_perm_cons(y, bw, append(drop(qi, L), drop(qj, R)));
                drop_n_plus_one(qi - 1, L);
            }
            @*/
            /*@
            if ms {
                if is_l2 {
                    if qj - 1 > 0 { sorted_adj(lt, R, qj - 2); }
                } else {
                    lt_asym::<T, F>(f0, rv2, lv2);
                    if qi - 1 > 0 { sorted_adj(lt, L, qi - 2); }
                }
            }
            @*/
            //@ close exists::<pair<pair<i32, i32>, pair<i32, i32>>>(pair(pair(i1, j1), pair(qi1, qj1)));
        }
        }
        //@ open exists::<pair<pair<i32, i32>, pair<i32, i32>>>(pair(pair(?ie, ?je), pair(?qie, ?qje)));
        //@ assert array::<T>(dst0, h, ?fwe) &*& array::<T>(dst0 + (len - h), h, ?bwe);
        //@ array_ptr_within_limits(src, qie);
        //@ array_ptr_within_limits(src, h + qje);
        //@ pwo_roundtrip(src + qie);
        //@ mul_mono_l(0, h + qje - 1, std::mem::size_of::<T>());
        //@ pwo_no_wrap(src + (h + qje - 1), 1);

        let left_end = const_ptr_wrapping_add_1__VeriFast_wrapper(left_rev);
        let right_end = const_ptr_wrapping_add_1__VeriFast_wrapper(right_rev);

        // Odd length, so one element is left unconsumed in the input.
        if !len.is_multiple_of(2) {
            //@ div_rem_nonneg(len, 2);
            //@ let r2 = len % 2;
            //@ assert 0 <= r2 &*& r2 < 2;
            //@ assert r2 != 0;
            //@ if r2 < 1 { assert r2 == 0; }
            //@ assert r2 == 1;
            //@ assert len == len / 2 * 2 + 1;
            //@ assert len == h * 2 + 1;
            //@ assert len - 2 * h == 1;
            //@ assert array_::<T>(dst0 + h, 1, _);
            let left_nonempty = left < left_end;
            //@ if left_nonempty { ptr_lt_index(src, ie, qie); nth_take_lt(ie, h, vs); }
            let last_src = if left_nonempty { left } else { right };
            //@ let idx = if left_nonempty { ie } else { h + je };
            //@ let x = nth(idx, vs);
            //@ array_open_at(src, idx);
            //@ array1_close(last_src);
            //@ open array_::<T>(dst0 + h, 1, _);
            //@ array_1_close(dst0 + h);
            ptr::copy_nonoverlapping(last_src, dst, 1);
            //@ array1_open(last_src);
            //@ array_close_at_same(src, idx);
            //@ array1_open(dst0 + h);
            //@ array_ptr_within_limits(src, ie + 1);
            //@ array_ptr_within_limits(src, h + je + 1);
            left = left.add(left_nonempty as usize);
            right = right.add((!left_nonempty) as usize);
            //@ open array_::<T>(dst0 + h + 1, 0, _);
            //@ close array::<T>(dst0 + h + 1, 0, nil);
            //@ array_join_last(dst0, h);
            //@ nth_drop(je, h, vs);
            /*@
            if left_nonempty {
                is_perm_snoc_middle(fwe, take(ie, L), take(je, R), x);
                take_plus_one(ie, L);
            } else {
                is_perm_snoc_right(fwe, take(ie, L), take(je, R), x);
                take_plus_one(je, R);
            }
            @*/
            //@ if ms { sorted_snoc(lt, fwe, x); last_snoc(fwe, x); }
            //@ close exists::<pair<i32, i32>>(pair(if left_nonempty { ie + 1 } else { ie }, if left_nonempty { je } else { je + 1 }));
        } else {
            //@ open array_::<T>(dst0 + h, 0, _);
            //@ close exists::<pair<i32, i32>>(pair(ie, je));
        }

        // We now should have consumed the full input exactly once. This can only fail if the
        // user-provided comparison function fails to implement a strict weak ordering. In that case
        // we panic and never access the inconsistent state in dst.
        if left != left_end || right != right_end {
            panic_on_ord_violation();
        }
        //@ open exists::<pair<i32, i32>>(pair(?i2, ?j2));
        //@ assert array::<T>(dst0, len - h, ?fw2);
        //@ array_join_n(dst0, len - h, h);
        /*@
        if std::mem::size_of::<T>() == 0 {
            zst_array_all_eq_self(src);
            zst_arrays_all_eq(dst0, src);
            match vs { nil => {} cons(v0, vs0) => {} }
            all_eq_perm(append(fw2, bwe), vs, head(vs));
            if m { all_eq_sorted::<T, F>(f0, append(fw2, bwe), head(vs)); }
        } else {
            ptr_add_inj(src, i2, qie);
            ptr_add_inj(src, h + j2, h + qje);
            is_perm_append_both(fw2, append(take(qie, L), take(qje, R)), bwe, append(drop(qie, L), drop(qje, R)));
            is_perm_middle_swap(take(qie, L), take(qje, R), drop(qie, L), drop(qje, R));
            is_perm_trans(append(fw2, bwe), append(append(take(qie, L), take(qje, R)), append(drop(qie, L), drop(qje, R))), vs);
            if ms {
                sorted_append(lt, fw2, bwe);
            }
        }
        @*/
    }
}

#[cfg_attr(not(panic = "immediate-abort"), inline(never), cold)]
#[cfg_attr(panic = "immediate-abort", inline)]
fn panic_on_ord_violation() -> !
//@ req thread_token(?t);
//@ ens false;
{
    // This is indicative of a logic bug in the user-provided comparison function or Ord
    // implementation. They are expected to implement a total order as explained in the Ord
    // documentation.
    //
    // By panicking we inform the user, that they have a logic bug in their program. If a strict
    // weak ordering is not given, the concept of comparison based sorting cannot yield a sorted
    // result. E.g.: a < b < c < a
    //
    // The Ord documentation requires users to implement a total order. Arguably that's
    // unnecessarily strict in the context of sorting. Issues only arise if the weaker requirement
    // of a strict weak ordering is violated.
    //
    // The panic message talks about a total order because that's what the Ord documentation talks
    // about and requires, so as to not confuse users.
    panic!("user-provided comparison function does not correctly implement a total order");
}

#[must_use]
pub(crate) const fn has_efficient_in_place_swap<T>() -> bool
//@ req true;
//@ ens result == (std::mem::size_of::<T>() <= 8);
{
    // Heuristic that holds true on all tested 64-bit capable architectures.
    size_of::<T>() <= 8 // size_of::<u64>()
}

// ===== BEGIN TRUSTED STD WRAPPERS =====
//
// Trusted part of the specifications, following the verify-rust-std LinkedList proof. VeriFast 26.10
// cannot attach a spec to these std calls (see README.md), so each call site in this file calls a
// wrapper instead. Each wrapper's body is exactly the original call, and refinement-checker checks
// that the code with wrappers refines the original code. Each spec is assumed (`assume_correct`),
// not proven, and follows the function's documentation in core.
// Every target crate contains this block verbatim (checked by verify.sh).

/*@

// The elements an array iterator has yet to yield.
fix array_IntoIter_remaining<T, N>(it: core::array::IntoIter<T, N>) -> list<T>;

// An address computed with wrapping `usize` arithmetic, for offsets of magnitude at most `usize::MAX + 1`.
fix wrap_usize(a: i32) -> i32 {
    if a < 0 { a + usize::MAX + 1 } else if a > usize::MAX { a - usize::MAX - 1 } else { a }
}

// `p.wrapping_offset(n)`: the same provenance and metadata, address `p + n * size_of::<T>()` modulo
// `usize::MAX + 1`.
fix ptr_wrapping_offset<T>(p: *T, n: i32) -> *T {
    pointer_ctor((p as pointer).provenance, wrap_usize((p as pointer).address + n * std::mem::size_of::<T>()), (p as pointer).metadata) as *T
}

@*/

// `v.as_mut_ptr()`: the slice's data pointer, as for `<[T]>::as_ptr`.
fn slice_as_mut_ptr__VeriFast_wrapper<T>(v: &mut [T]) -> *mut T
//@ req true;
//@ ens result == v as *T;
//@ on_unwind_ens false;
//@ assume_correct
{
    v.as_mut_ptr()
}

// `m.as_mut_ptr()`: a pointer to the contained value; `MaybeUninit<U>` is `repr(transparent)`.
fn maybe_uninit_as_mut_ptr__VeriFast_wrapper<U>(m: &mut MaybeUninit<U>) -> *mut U
//@ req true;
//@ ens result == m as *U;
//@ on_unwind_ens false;
//@ assume_correct
{
    m.as_mut_ptr()
}

// `p.wrapping_sub(count)`: `count` elements down with wrapping address arithmetic, the same provenance,
// no in-bounds requirement (core: "the resulting pointer ... has the same provenance"). Specified for
// `count * size_of::<T>() <= isize::MAX` (one wrap-around at most).
fn const_ptr_wrapping_sub__VeriFast_wrapper<T>(p: *const T, count: usize) -> *const T
//@ req true;
//@ ens if count * std::mem::size_of::<T>() <= isize::MAX { result == ptr_wrapping_offset(p, -count) } else { true };
//@ on_unwind_ens false;
//@ assume_correct
{
    p.wrapping_sub(count)
}

// `p.wrapping_add(1)`: one element up with wrapping address arithmetic, the same provenance
// (refinement-checker does not accept constants as arguments of wrapper calls, so the constant is
// inside the wrapper). Specified for `size_of::<T>() <= isize::MAX` (true of every Rust type).
fn const_ptr_wrapping_add_1__VeriFast_wrapper<T>(p: *const T) -> *const T
//@ req true;
//@ ens if std::mem::size_of::<T>() <= isize::MAX { result == ptr_wrapping_offset(p, 1) } else { true };
//@ on_unwind_ens false;
//@ assume_correct
{
    p.wrapping_add(1)
}

// `IntoIterator::into_iter([0, b])`, the head of `for offset in [0, len_div_2]`. This and the next
// wrapper are `unsafe` only so that VeriFast does not also require the specs VeriFast generates for
// safe functions (it cannot express ownership of their array and `Option` values); the call site is
// inside an `unsafe` block, and refinement-checker checks it against the original `for` loop.
unsafe fn array_0_and_into_iter__VeriFast_wrapper(b: usize) -> core::array::IntoIter<usize, 2>
//@ req thread_token(?t);
//@ ens thread_token(t) &*& <core::array::IntoIter<usize, 2>>.own(t, result) &*& array_IntoIter_remaining(result) == [0, b];
//@ on_unwind_ens false;
//@ assume_correct
{
    IntoIterator::into_iter([0, b])
}

// `iter.next()` for the iterator above: yields the remaining elements in order.
unsafe fn array_usize_2_into_iter_next__VeriFast_wrapper(iter: &mut core::array::IntoIter<usize, 2>) -> Option<usize>
//@ req thread_token(?t) &*& *iter |-> ?it0 &*& <core::array::IntoIter<usize, 2>>.own(t, it0);
/*@
ens thread_token(t) &*& *iter |-> ?it1 &*& <core::array::IntoIter<usize, 2>>.own(t, it1) &*&
    match array_IntoIter_remaining(it0) {
        nil => result == std::option::Option::None && array_IntoIter_remaining(it1) == nil,
        cons(x, xs) => result == std::option::Option::Some(x) && array_IntoIter_remaining(it1) == xs
    };
@*/
//@ on_unwind_ens false;
//@ assume_correct
{
    Iterator::next(iter)
}

// `ptr::copy(src, dst, 1)`: memmove of one element (refinement-checker does not accept constants as
// arguments of wrapper calls, so the count is inside the wrapper). VeriFast 26.10's prelude spec of
// `std::ptr::copy` does not bound `offset` in its `some(offset)` branch: at a call whose regions are
// disjoint and farther apart than `count` elements, choosing that branch yields a chunk whose byte list
// is shorter than the chunk, from which `false` follows. This spec is that prelude spec at `count = 1`
// with `-1 <= offset <= 1` added to the `some(offset)` branch; regions farther apart use `none`.
unsafe fn ptr_copy_1__VeriFast_wrapper<T>(src: *const T, dst: *mut T)
/*@
req exists::<option<isize>>(?offset_opt) &*&
    match offset_opt {
        none => // No overlap
            [?f](src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& (dst as *u8)[..1 * std::mem::size_of::<T>()] |-> _ &*&
            ens [f](src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs &*& (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs,
        some(offset) =>
            dst == src + offset &*& -1 <= offset &*& offset <= 1 &*&
            if offset == 0 {
                (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*&
                ens (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            } else if offset > 0 {
                (src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& ((src + 1) as *u8)[..offset * std::mem::size_of::<T>()] |-> _ &*&
                ens (src as *u8)[..offset * std::mem::size_of::<T>()] |-?-> take(offset * std::mem::size_of::<T>(), bs) &*&
                    (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            } else {
                (src as *u8)[..1 * std::mem::size_of::<T>()] |-?-> ?bs &*& (dst as *u8)[..-offset * std::mem::size_of::<T>()] |-> _ &*&
                ens ((dst + 1) as *u8)[..-offset * std::mem::size_of::<T>()] |-?-> drop((1 + offset) * std::mem::size_of::<T>(), bs) &*&
                    (dst as *u8)[..1 * std::mem::size_of::<T>()] |-?-> bs
            }
    };
@*/
//@ ens true;
//@ on_unwind_ens false;
//@ terminates;
//@ assume_correct
{
    ptr::copy(src, dst, 1)
}

// `a + 16` on `usize` (refinement-checker does not accept constants as arguments of wrapper calls, so
// the constant is inside the wrapper). Rust's checked semantics (a build with overflow checks): the
// result is `a + 16`, and the addition panics if that exceeds `usize::MAX`. (In a build without overflow
// checks it wraps instead; it can overflow only for zero-sized `T`, see README.md.)
fn usize_add_16__VeriFast_wrapper(a: usize) -> usize
//@ req true;
//@ ens a + 16 <= usize::MAX &*& result == a + 16;
//@ on_unwind_ens true;
//@ assume_correct
{
    a + 16
}

// `MaybeUninit::<U>::uninit()`: an uninitialized `MaybeUninit<U>` (VeriFast 26.10 has no spec for it).
// `unsafe` only so that VeriFast does not also require the spec it generates for safe functions; the call
// sites are rewritten (see rewrites/LOG.md) and refinement-checker checks them.
unsafe fn maybe_uninit_uninit__VeriFast_wrapper<U>() -> MaybeUninit<U>
//@ req true;
//@ ens result == std::mem::MaybeUninit::uninit::<U>();
//@ on_unwind_ens false;
//@ assume_correct
{
    MaybeUninit::uninit()
}

// ===== END TRUSTED STD WRAPPERS =====
// ===== BEGIN TRUSTED COMPARATOR CALL WRAPPER =====
//
// Trusted link between a comparator call and the comparator model (block TRUSTED COMPARATOR MODEL).
// Every call `is_less(&x, &y)` in this file goes through this wrapper; its body is exactly the
// original call (refinement-checker inlines it and checks the code against original/). Its spec is
// assumed (`assume_correct`), not proven: when the comparator value `f0` is well-behaved
// (`is_less_models`), the call does not unwind, leaves the comparator and both values unchanged, and
// returns the model order applied to the two values; otherwise it only returns the ownership it took.
// Every crate contains this block verbatim (checked by verify.sh).
unsafe fn is_less__VeriFast_wrapper<T, F: FnMut(&T, &T) -> bool>(f: &mut F, a: &T, b: &T) -> bool
//@ req thread_token(?t) &*& *f |-> ?f0 &*& <F>.own(t, f0) &*& [?qa](*a |-> ?a0) &*& [?qb](*b |-> ?b0);
/*@
ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1) &*& [qa](*a |-> ?a1) &*& [qb](*b |-> ?b1) &*&
    if is_less_models::<T, F>(f0) {
        f1 == f0 && a1 == a0 && b1 == b0 && result == apply_lt(is_less_model_of::<T, F>(f0), a0, b0)
    } else {
        true
    };
@*/
//@ on_unwind_ens thread_token(t) &*& *f |-> ?f1 &*& <F>.own(t, f1) &*& [qa](*a |-> _) &*& [qb](*b |-> _) &*& !is_less_models::<T, F>(f0);
//@ assume_correct
{
    f(a, b)
}
// ===== END TRUSTED COMPARATOR CALL WRAPPER =====
