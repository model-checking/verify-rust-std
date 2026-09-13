// Generic proof candidate. See ../README.md for validation status and scope.

use crate::mem::MaybeUninit;
use crate::{fmt, ptr};

//@ use array_layout::{array_borrow_tokens, collapse_window, expand_window, lend_array, matrix_elems, own_matrix_storage, pack_matrix, reclaim_array, unpack_matrix};
//@ use array_layout::{joined_window, mapped_append, mapped_length, mapped_range, mapped_uninit_upcast, matrix_upcast, owned_values_mono, owned_values_send};

struct Buffer<T, const N: usize> {
    // Invariant: `self.buffer[self.start..self.start + N]` is initialized,
    // with all other elements being uninitialized. This also
    // implies that `self.start <= N`.
    buffer: [[MaybeUninit<T>; N]; 2],
    start: usize,
}

/*@

fix width<N>() -> usize { usize_of_const(typeid(N)) }

fix base<T, N>(b: *Buffer<T, N>) -> *std::mem::MaybeUninit<T> {
    &(*b).buffer as *std::mem::MaybeUninit<T>
}

// These are constructor/layout restrictions, not a finite proof bound.
pred bounds<T, N>(b: *Buffer<T, N>; start: usize) =
    (*b).start |-> start &*& 0 < width::<N>() &*&
    width::<N>() <= usize::MAX / 2 &*& start <= width::<N>() &*&
    2 * width::<N>() * std::mem::size_of::<T>() <= isize::MAX &*&
    pointer_within_limits(base(b)) == true &*&
    pointer_within_limits(base(b) + start) == true &*&
    pointer_within_limits(base(b) + 2 * width::<N>()) == true;

// Inactive slots may retain copied bytes. They carry no ownership of T.
pred live<T, N>(t: thread_id_t, b: *Buffer<T, N>, start: usize, values: list<T>) =
    bounds(b, start) &*& length(values) == width::<N>() &*&
    base(b)[..start] |-> ?prefix &*&
    (base(b) + start)[..width::<N>()] |-> map(std::mem::MaybeUninit::new, values) &*&
    (base(b) + start + width::<N>())[..width::<N>() - start] |-> ?suffix &*&
    foreach(values, own::<T>(t));

pred storage<T, N>(b: *Buffer<T, N>; start: usize) =
    bounds(b, start) &*& base(b)[..2 * width::<N>()] |-> ?slots;

pred_ctor writable_matrix<T, N>(b: *Buffer<T, N>)(;) = (*b).buffer |-> ?matrix;

pred<T, N> <Buffer<T, N>>.own(t, buffer) =
    exists::<list<T>>(?values) &*&
    0 < width::<N>() &*& width::<N>() <= usize::MAX / 2 &*&
    0 <= buffer.start &*& buffer.start <= width::<N>() &*&
    2 * width::<N>() * std::mem::size_of::<T>() <= isize::MAX &*&
    length(values) == width::<N>() &*&
    take(width::<N>(), drop(buffer.start, matrix_elems(buffer.buffer))) ==
        map(std::mem::MaybeUninit::new, values) &*&
    foreach(values, own::<T>(t));

lem Buffer_own_mono<T0, T1, N: ?Sized>()
    req type_interp::<T0>() &*& type_interp::<T1>() &*& type_interp::<N>() &*&
        Buffer_own::<T0, N>(?t, ?buffer) &*& is_subtype_of::<T0, T1>() == true;
    ens type_interp::<T0>() &*& type_interp::<T1>() &*& type_interp::<N>() &*&
        Buffer_own::<T1, N>(t, Buffer::<T1, N> {
            buffer: upcast(buffer.buffer), start: upcast(buffer.start) });
{
    open Buffer_own::<T0, N>(t, buffer);
    open exists::<list<T0>>(?values);
    std::mem::subtype_layout::<T0, T1>();
    std::mem::upcast_identity(buffer.start);
    std::mem::MaybeUninit_subtype::<T0, T1>();
    matrix_upcast::<std::mem::MaybeUninit<T0>, std::mem::MaybeUninit<T1>, N>(buffer.buffer);
    mapped_range::<std::mem::MaybeUninit<T0>, std::mem::MaybeUninit<T1>>(upcast,
        matrix_elems(buffer.buffer), buffer.start, width::<N>());
    mapped_uninit_upcast::<T0, T1>(values);
    mapped_length::<T0, T1>(upcast, values);
    owned_values_mono::<T0, T1>(t, values);
    close exists(map::<T0, T1>(upcast, values));
    close Buffer_own::<T1, N>(t, Buffer::<T1, N> {
        buffer: upcast(buffer.buffer), start: upcast(buffer.start) });
}

lem Buffer_send<T, N: ?Sized>(t1: thread_id_t)
    req type_interp::<T>() &*& type_interp::<N>() &*& Buffer_own::<T, N>(?t0, ?buffer) &*&
        is_Send(typeid(Buffer<T, N>)) == true;
    ens type_interp::<T>() &*& type_interp::<N>() &*& Buffer_own::<T, N>(t1, buffer);
{
    open Buffer_own::<T, N>(t0, buffer);
    open exists::<list<T>>(?values);
    std::mem::array_Send::<[std::mem::MaybeUninit<T>; N], 2>();
    std::mem::array_Send::<std::mem::MaybeUninit<T>, N>();
    std::mem::MaybeUninit_Send::<T>();
    owned_values_send(t0, t1, values);
    close exists(values);
    close Buffer_own::<T, N>(t1, buffer);
}

// A destructor cannot consume ownership of the surviving window.
pred push_drop_frame<T, N>(t: thread_id_t, b: *Buffer<T, N>, start: usize,
    values: list<T>, matrix: *[[std::mem::MaybeUninit<T>; N]; 2]) =
    bounds(b, if start == width::<N>() { 0 } else { start + 1 }) &*&
    0 <= start &*& start <= width::<N>() &*& length(values) == width::<N>() &*&
    ref_mut_end_token(matrix, &(*b).buffer) &*& foreach(values, own::<T>(t)) &*&
    if start == width::<N>() {
        (matrix as *std::mem::MaybeUninit<T>)[..width::<N>()] |-> map(std::mem::MaybeUninit::new, values) &*&
        ((matrix as *std::mem::MaybeUninit<T>) + start + 1)[..width::<N>() - 1] |-> ?stale
    } else {
        (matrix as *std::mem::MaybeUninit<T>)[..start] |-> ?prefix &*&
        ((matrix as *std::mem::MaybeUninit<T>) + start + 1)[..width::<N>()] |-> map(std::mem::MaybeUninit::new, values) &*&
        ((matrix as *std::mem::MaybeUninit<T>) + start + width::<N>() + 1)[..width::<N>() - start - 1] |-> ?suffix
    };

// This ghost restoration is valid after either outcome of dropping the old front.
lem finish_push_storage<T, N: ?Sized>(t: thread_id_t, b: *Buffer<T, N>, start: usize,
    values: list<T>, matrix: *[[std::mem::MaybeUninit<T>; N]; 2])
    req push_drop_frame(t, b, start, values, matrix) &*&
        *(((matrix as *std::mem::MaybeUninit<T>) + start) as *T) |-> _;
    ens live(t, b, if start == width::<N>() { 0 } else { start + 1 }, values);
{
    open push_drop_frame(t, b, start, values, matrix);
    open bounds(b, if start == width::<N>() { 0 } else { start + 1 });
    let p = matrix as *std::mem::MaybeUninit<T>;
    std::mem::close_MaybeUninit_(p + start);
    if start == width::<N>() {
        close array(p + start, width::<N>(), _);
        assert (p + start)[..width::<N>()] |-> ?suffix;
        joined_window(nil, map(std::mem::MaybeUninit::new, values), suffix);
        array_join(p);
    } else {
        close array(p + start + 1, 0, nil);
        close array(p + start, 1, _);
        array_join(p);
        assert p[..start + 1] |-> ?prefix;
        assert (p + start + width::<N>() + 1)[..width::<N>() - start - 1] |-> ?suffix;
        joined_window(prefix, map(std::mem::MaybeUninit::new, values), suffix);
        array_join(p);
        array_join(p);
    }
    pack_matrix(matrix);
    end_ref_mut(matrix);
    unpack_matrix(&(*b).buffer);
    array_split(base(b), if start == width::<N>() { 0 } else { start + 1 });
    array_split(base(b) + (if start == width::<N>() { 0 } else { start + 1 }), width::<N>());
    close bounds(b, if start == width::<N>() { 0 } else { start + 1 });
    close live(t, b, if start == width::<N>() { 0 } else { start + 1 }, values);
}

// The same frame survives normal and unwinding generic drop glue.
pred drop_frame<T, N>(b: *Buffer<T, N>, start: usize,
    matrix: *[[std::mem::MaybeUninit<T>; N]; 2], k: lifetime_t, slice: *[T]) =
    bounds(b, start) &*& ref_mut_end_token(matrix, &(*b).buffer) &*&
    (matrix as *std::mem::MaybeUninit<T>)[..start] |-> ?prefix &*&
    ((matrix as *std::mem::MaybeUninit<T>) + start + width::<N>())[..width::<N>() - start] |-> ?suffix &*&
    array_borrow_tokens(k, ((matrix as *std::mem::MaybeUninit<T>) + start) as *T, width::<N>()) &*&
    close_points_to_at_lft_token(1, k, slice, 1) &*&
    slice as *T == ((matrix as *std::mem::MaybeUninit<T>) + start) as *T &*&
    ptr_len(slice) == width::<N>();

lem finish_drop_storage<T, N: ?Sized>(b: *Buffer<T, N>, start: usize,
    matrix: *[[std::mem::MaybeUninit<T>; N]; 2], k: lifetime_t, slice: *[T])
    nonghost_callers_only
    req drop_frame(b, start, matrix, k, slice) &*& *slice |-> _;
    ens storage(b, start);
{
    open drop_frame(b, start, matrix, k, slice);
    open bounds(b, start);
    close_points_to_at_lft_(slice);
    open_points_to_slice_at_lft_(slice);
    end_lifetime(k);
    let p = matrix as *std::mem::MaybeUninit<T>;
    reclaim_array(k, (p + start) as *T, width::<N>());
    std::mem::array__to_array_MaybeUninit((p + start) as *T);
    array_join(p);
    array_join(p);
    pack_matrix(matrix);
    end_ref_mut(matrix);
    unpack_matrix(&(*b).buffer);
    close bounds(b, start);
    close storage(b, start);
}

// Unwrap initialized slots without requiring T: Copy or duplicating T.own.
lem initialized_slots<T>(p: *std::mem::MaybeUninit<T>, values: list<T>)
    req p[..length(values)] |-> map(std::mem::MaybeUninit::new, values);
    ens (p as *T)[..length(values)] |-> values;
{
    std::mem::MaybeUninit_layout::<T>();
    open array(p, length(values), _);
    match values {
        nil => {
            close array(p as *T, 0, nil);
        }
        cons(value, tail) => {
            std::mem::open_MaybeUninit(p);
            close points_to(p as *T, value);
            initialized_slots(p + 1, tail);
            close array(p as *T, length(values), values);
        }
    }
}

lem wrap_slots<T>(p: *T, values: list<T>)
    req p[..length(values)] |-> values;
    ens (p as *std::mem::MaybeUninit<T>)[..length(values)] |-> map(std::mem::MaybeUninit::new, values);
{
    std::mem::MaybeUninit_layout::<T>();
    open array(p, length(values), values);
    match values {
        nil => {
            close array(p as *std::mem::MaybeUninit<T>, 0, nil);
        }
        cons(value, tail) => {
            std::mem::close_MaybeUninit(p as *std::mem::MaybeUninit<T>);
            wrap_slots(p + 1, tail);
            close array(p as *std::mem::MaybeUninit<T>, length(values), _);
        }
    }
}

// The caller supplies a borrow of the window. It can originate from a live
// initialized array (as_array_ref), or writable storage (as_uninit_array_mut).
// Proving the surrounding safe abstraction and its constructors is separate.

@*/

impl<T, const N: usize> Buffer<T, N> {
    #[inline]
    unsafe fn buffer_ptr(&self) -> *const MaybeUninit<T>
//@ req pointer_within_limits(base(self)) == true &*& [?f]ref_initialized(&(*self).buffer);
    //@ ens [f]ref_initialized(&(*self).buffer) &*& result == base(self);
    //@ on_unwind_ens false;
    {
        //@ reborrow_ref_(&(*self).buffer);
        self.buffer.as_ptr().cast()
    }

    #[inline]
    unsafe fn buffer_mut_ptr(&mut self) -> *mut MaybeUninit<T>
//@ req (*self).buffer |-> ?matrix;
    //@ ens *(result as *[[std::mem::MaybeUninit<T>; N]; 2]) |-> matrix &*& ref_mut_end_token(result as *[[std::mem::MaybeUninit<T>; N]; 2], &(*self).buffer);
    //@ on_unwind_ens false;
    {
        self.buffer.as_mut_ptr().cast()
    }

    #[inline]
    unsafe fn as_array_ref<'a>(&'a self) -> &'a [T; N]
/*@
    req [?f]bounds(self, ?start) &*& [?q]lifetime_token('a) &*&
        [_]frac_borrow('a, ref_initialized_(self)) &*&
        [?bf]ref_initialized(&(*self).buffer) &*&
        type_interp::<[T; N]>() &*&
        [_](<[T; N]>.share)('a, ?t, (base(self) + start) as *[T; N]);
    @*/
    /*@
    ens [f]bounds(self, start) &*& [q]lifetime_token('a) &*&
        [bf]ref_initialized(&(*self).buffer) &*&
        type_interp::<[T; N]>() &*&
        ref_origin(result) == ref_origin((base(self) + start) as *[T; N]) &*&
        [_](<[T; N]>.share)('a, t, result);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open [f]bounds(self, start);
        assert!(self.start + N <= 2 * N);

        // SAFETY: our invariant guarantees these elements are initialized.
        let buffer_ptr = unsafe { self.buffer_ptr() };
        //@ let window = (base(self) + start) as *[T; N];
        //@ let reference = precreate_ref(window);
        //@ init_ref_share('a, t, reference);
        //@ let r = open_frac_borrow('a, ref_initialized_(reference), q);
        //@ open [r]ref_initialized_::<[T; N]>(reference)();
        let result = unsafe { &*buffer_ptr.add(self.start).cast() };
        //@ close [r]ref_initialized_::<[T; N]>(reference)();
        //@ close_frac_borrow(r, ref_initialized_(reference));
        //@ close [f]bounds(self, start);
        result
    }

    #[inline]
    unsafe fn as_uninit_array_mut<'a>(&'a mut self) -> &'a mut MaybeUninit<[T; N]>
/*@
    req thread_token(?t) &*& bounds(self, ?start) &*& [?q]lifetime_token('a) &*&
        full_borrow('a, writable_matrix(self));
    @*/
    /*@
    ens thread_token(t) &*& bounds(self, start) &*& [q]lifetime_token('a) &*&
        full_borrow('a, <std::mem::MaybeUninit<[T; N]>>.full_borrow_content(t, result));
    @*/
    //@ on_unwind_ens false;
    {
        //@ open bounds(self, start);
        assert!(self.start + N <= 2 * N);

        // SAFETY: our invariant guarantees these elements are in bounds.
        //@ open_full_borrow_strong_('a, writable_matrix(self));
        //@ open writable_matrix::<T, N>(self)();
        let buffer_mut_ptr = unsafe { self.buffer_mut_ptr() };
        //@ unpack_matrix(buffer_mut_ptr as *[[std::mem::MaybeUninit<T>; N]; 2]);
        //@ array_split(buffer_mut_ptr, start);
        //@ array_split(buffer_mut_ptr + start, width::<N>());
        //@ collapse_window::<T, N>(buffer_mut_ptr + start);
        unsafe {
            let result = &mut *buffer_mut_ptr.add(self.start).cast();
            //@ let window = (buffer_mut_ptr + start) as *std::mem::MaybeUninit<[T; N]>;
            /*@
            {
                pred ctx() =
                    ref_mut_end_token(result, window) &*&
                    ref_mut_end_token(buffer_mut_ptr as *[[std::mem::MaybeUninit<T>; N]; 2], &(*self).buffer) &*&
                    buffer_mut_ptr[..start] |-> ?prefix &*&
                    (buffer_mut_ptr + start + width::<N>())[..width::<N>() - start] |-> ?suffix;
                produce_lem_ptr_chunk restore_full_borrow_(ctx,
                    <std::mem::MaybeUninit<[T; N]>>.full_borrow_content(t, result),
                    writable_matrix(self))() {
                    open ctx();
                    open_full_borrow_content::<std::mem::MaybeUninit<[T; N]>>(t, result);
                    assert *result |-> ?borrowed_contents;
                    std::mem::MaybeUninit_own_dispose::<[T; N]>(t, borrowed_contents);
                    end_ref_mut_::<std::mem::MaybeUninit<[T; N]>>();
                    expand_window(window);
                    array_join(buffer_mut_ptr);
                    array_join(buffer_mut_ptr);
                    pack_matrix(buffer_mut_ptr as *[[std::mem::MaybeUninit<T>; N]; 2]);
                    end_ref_mut_::<[[std::mem::MaybeUninit<T>; N]; 2]>();
                    close writable_matrix::<T, N>(self)();
                } {
                    assert *result |-> ?contents;
                    std::mem::MaybeUninit_own_init::<[T; N]>(t, contents);
                    close_full_borrow_content::<std::mem::MaybeUninit<[T; N]>>(t, result);
                    close ctx();
                    close_full_borrow_strong_();
                }
            }
            @*/
            //@ close bounds(self, start);
            result
        }
    }

    /// Pushes a new item `next` to the back, and pops the front-most one.
    ///
    /// All the elements will be shifted to the front end when pushing reaches
    /// the back end.
    unsafe fn push(&mut self, next: T)
    /*@
    req thread_token(?t) &*& live(t, self, ?start, ?values) &*& <T>.own(t, next);
    @*/
    /*@
    ens thread_token(t) &*& live(t, self, if start == width::<N>() { 0 } else { start + 1 },
        append(tail(values), cons(next, nil)));
    @*/
    /*@
    on_unwind_ens thread_token(t) &*&
        push_drop_frame(t, self, start, append(tail(values), cons(next, nil)), ?matrix) &*&
        *(((matrix as *std::mem::MaybeUninit<T>) + start) as *T) |-> _;
    @*/
    {
        //@ open live(t, self, start, values);
        //@ open bounds(self, start);
        //@ open array(base(self) + start, width::<N>(), map(std::mem::MaybeUninit::new, values));
        //@ assert pointer_within_limits(base(self) + start + 1) == true;
        //@ close array(base(self) + start, width::<N>(), map(std::mem::MaybeUninit::new, values));
        //@ assert base(self)[..start] |-> ?prefix_slots;
        //@ assert (base(self) + start + width::<N>())[..width::<N>() - start] |-> ?suffix_slots;
        //@ joined_window(prefix_slots, map(std::mem::MaybeUninit::new, values), suffix_slots);
        //@ array_join(base(self));
        //@ array_join(base(self));
        //@ pack_matrix(&(*self).buffer);
        let buffer_mut_ptr = unsafe { self.buffer_mut_ptr() };
        //@ unpack_matrix(buffer_mut_ptr as *[[std::mem::MaybeUninit<T>; N]; 2]);
        //@ array_split(buffer_mut_ptr, start);
        //@ array_split(buffer_mut_ptr + start, width::<N>());
        //@ open foreach(values, own::<T>(t));
        //@ open array(buffer_mut_ptr + start, width::<N>(), _);
        assert!(self.start + N <= 2 * N);

        let to_drop = if self.start == N {
            // We have reached the end of our buffer and have to copy
            // everything to the start. Example layout for N = 3.
            //
            //    0   1   2   3   4   5            0   1   2   3   4   5
            //  ┌───┬───┬───┬───┬───┬───┐        ┌───┬───┬───┬───┬───┬───┐
            //  │ - │ - │ - │ a │ b │ c │   ->   │ b │ c │ n │ - │ - │ - │
            //  └───┴───┴───┴───┴───┴───┘        └───┴───┴───┴───┴───┴───┘
            //                ↑                    ↑
            //              start                start

            // SAFETY: the two pointers are valid for reads/writes of N -1
            // elements because our array's size is semantically 2 * N. The
            // regions also don't overlap for the same reason.
            //
            // We leave the old elements in place. As soon as `start` is set
            // to 0, we treat them as uninitialized and treat their copies
            // as initialized.
            let to_drop = unsafe {
                //@ array_split(buffer_mut_ptr, width::<N>() - 1);
                //@ open array(buffer_mut_ptr + width::<N>() - 1, 1, _);
                //@ array_to_array_(buffer_mut_ptr);
                ptr::copy_nonoverlapping(buffer_mut_ptr.add(self.start + 1), buffer_mut_ptr, N - 1);
                (*buffer_mut_ptr.add(N - 1)).write(next);
                //@ end_ref_mut_::<std::mem::MaybeUninit<T>>();
                //@ open array(buffer_mut_ptr + width::<N>(), 0, _);
                //@ close array(buffer_mut_ptr + width::<N>(), 0, nil);
                //@ close array(buffer_mut_ptr + width::<N>() - 1, 1, cons(std::mem::MaybeUninit::new(next), nil));
                //@ array_join(buffer_mut_ptr);
                buffer_mut_ptr.add(self.start)
            };
            self.start = 0;
            to_drop
        } else {
            // SAFETY: `self.start` is < N as guaranteed by the invariant
            // plus the check above. Even if the drop at the end panics,
            // the invariant is upheld.
            //
            // Example layout for N = 3:
            //
            //    0   1   2   3   4   5            0   1   2   3   4   5
            //  ┌───┬───┬───┬───┬───┬───┐        ┌───┬───┬───┬───┬───┬───┐
            //  │ - │ a │ b │ c │ - │ - │   ->   │ - │ - │ b │ c │ n │ - │
            //  └───┴───┴───┴───┴───┴───┘        └───┴───┴───┴───┴───┴───┘
            //        ↑                                    ↑
            //      start                                start
            //
            let to_drop = unsafe {
                //@ open array(buffer_mut_ptr + start + width::<N>(), width::<N>() - start, _);
                (*buffer_mut_ptr.add(self.start + N)).write(next);
                //@ end_ref_mut_::<std::mem::MaybeUninit<T>>();
                //@ close array(buffer_mut_ptr + start + width::<N>() + 1, 0, nil);
                //@ close array(buffer_mut_ptr + start + width::<N>(), 1, cons(std::mem::MaybeUninit::new(next), nil));
                //@ array_join(buffer_mut_ptr + start + 1);
                buffer_mut_ptr.add(self.start)
            };
            self.start += 1;
            to_drop
        };

        // SAFETY: the index is valid and this is element `a` in the
        // diagram above and has not been dropped yet.
        //@ close foreach(nil, own::<T>(t));
        //@ close own::<T>(t)(next);
        //@ close foreach(cons(next, nil), own::<T>(t));
        //@ foreach_append(tail(values), cons(next, nil));
        //@ mapped_append::<T, std::mem::MaybeUninit<T>>(std::mem::MaybeUninit::new, tail(values), cons(next, nil));
        //@ close bounds(self, if start == width::<N>() { 0 } else { start + 1 });
        //@ close push_drop_frame(t, self, start, append(tail(values), cons(next, nil)), buffer_mut_ptr as *[[std::mem::MaybeUninit<T>; N]; 2]);
        //@ std::mem::open_MaybeUninit(to_drop);
        //@ close points_to(to_drop as *T, head(values));
        //@ open own::<T>(t)(head(values));
        unsafe { ptr::drop_in_place(to_drop.cast_init()) };
        //@ finish_push_storage(t, self, start, append(tail(values), cons(next, nil)), buffer_mut_ptr as *[[std::mem::MaybeUninit<T>; N]; 2]);
        //@ assert live(t, self, if start == width::<N>() { 0 } else { start + 1 }, append(tail(values), cons(next, nil)));
    } //~allow_dead_code // Rust emits cleanup for the already moved next argument.
}

impl<T, const N: usize> Drop for Buffer<T, N> {
    fn drop(&mut self)
    /*@
    req thread_token(?t) &*& live(t, self, ?start, ?values);
    @*/
    /*@
    ens thread_token(t) &*& drop_frame(self, start, ?matrix, ?k, ?slice) &*& *slice |-> _;
    @*/
    //@ on_unwind_ens thread_token(t) &*& drop_frame(self, start, ?matrix, ?k, ?slice) &*& *slice |-> _;
    /*@
    safety_proof {
        open Buffer_full_borrow_content::<T, N>(_t, self)();
        open <Buffer<T, N>>.own(_t, ?buffer);
        open exists::<list<T>>(?values);
        let start = buffer.start;
        unpack_matrix(&(*self).buffer);
        array_split(base(self), start);
        array_split(base(self) + start, width::<N>());
        close bounds(self, start);
        close live(_t, self, start, values);
        call();
        assert drop_frame(self, start, ?matrix, ?k, ?slice);
        finish_drop_storage(self, start, matrix, k, slice);
        open storage(self, start);
        open bounds(self, start);
        pack_matrix(&(*self).buffer);
        assert (*self).buffer |-> ?after;
        own_matrix_storage(_t, after);
    }
    @*/
    {
        //@ open live(t, self, start, values);
        //@ open bounds(self, start);
        //@ assert base(self)[..start] |-> ?prefix_slots;
        //@ assert (base(self) + start + width::<N>())[..width::<N>() - start] |-> ?suffix_slots;
        //@ joined_window(prefix_slots, map(std::mem::MaybeUninit::new, values), suffix_slots);
        //@ array_join(base(self));
        //@ array_join(base(self));
        //@ pack_matrix(&(*self).buffer);
        // SAFETY: our invariant guarantees that N elements starting from
        // `self.start` are initialized. We drop them here.
        unsafe {
            let buffer_mut_ptr = self.buffer_mut_ptr();
            //@ let matrix = buffer_mut_ptr as *[[std::mem::MaybeUninit<T>; N]; 2];
            //@ unpack_matrix(matrix);
            //@ array_split(buffer_mut_ptr, start);
            //@ array_split(buffer_mut_ptr + start, width::<N>());
            let initialized_part: *mut [T] =
                crate::ptr::slice_from_raw_parts_mut(buffer_mut_ptr.add(self.start).cast(), N);
            //@ initialized_slots(buffer_mut_ptr + start, values);
            //@ let k = begin_lifetime();
            //@ lend_array(k, (buffer_mut_ptr + start) as *T, width::<N>());
            //@ close_points_to_slice_at_lft(initialized_part);
            //@ open_points_to_at_lft(initialized_part, 1);
            //@ close <[T]>.own(t, slice_of_elems(values));
            //@ close bounds(self, start);
            //@ close drop_frame(self, start, matrix, k, initialized_part);
            ptr::drop_in_place(initialized_part);
        }
    }
}
