// Generic proof candidate. See ../README.md for validation status and scope.

use crate::mem::MaybeUninit;
use crate::{fmt, ptr};

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
    pointer_within_limits(base(b) + 2 * width::<N>()) == true;

// Inactive slots may retain copied bytes. They carry no ownership of T.
pred live<T, N>(t: thread_id_t, b: *Buffer<T, N>; start: usize, values: list<T>) =
    bounds(b, start) &*& length(values) == width::<N>() &*&
    base(b)[..start] |-> ?prefix &*&
    (base(b) + start)[..width::<N>()] |-> map(std::mem::MaybeUninit::new, values) &*&
    (base(b) + start + width::<N>())[..width::<N>() - start] |-> ?suffix &*&
    foreach(values, own::<T>(t));

pred storage<T, N>(b: *Buffer<T, N>; start: usize) =
    bounds(b, start) &*& base(b)[..2 * width::<N>()] |-> ?slots;

// Unwrap initialized slots without requiring T: Copy or duplicating T.own.
lem initialized_slots<T>(p: *std::mem::MaybeUninit<T>, values: list<T>)
    req p[..length(values)] |-> map(std::mem::MaybeUninit::new, values);
    ens (p as *T)[..length(values)] |-> values;
{
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
    fn buffer_ptr(&self) -> *const MaybeUninit<T>
//@ req true;
    //@ ens result == base(self);
    //@ on_unwind_ens false;
    {
        self.buffer.as_ptr().cast()
    }

    #[inline]
    fn buffer_mut_ptr(&mut self) -> *mut MaybeUninit<T>
//@ req true;
    //@ ens result == base(self);
    //@ on_unwind_ens false;
    {
        self.buffer.as_mut_ptr().cast()
    }

    #[inline]
    fn as_array_ref<'a>(&'a self) -> &'a [T; N]
/*@
    req [?f]bounds(self, ?start) &*& [?q]lifetime_token('a) &*&
        type_interp::<[T; N]>() &*&
        [_](<[T; N]>.share)('a, ?t, (base(self) + start) as *[T; N]);
    @*/
    /*@
    ens [f]bounds(self, start) &*& [q]lifetime_token('a) &*&
        type_interp::<[T; N]>() &*&
        ref_origin(result) == ref_origin((base(self) + start) as *[T; N]) &*&
        [_](<[T; N]>.share)('a, t, result);
    @*/
    //@ on_unwind_ens false;
    {
        //@ open [f]bounds(self, start);
        debug_assert!(self.start + N <= 2 * N);

        // SAFETY: our invariant guarantees these elements are initialized.
        //@ let window = (base(self) + start) as *[T; N];
        //@ let reference = precreate_ref(window);
        //@ init_ref_share('a, t, reference);
        //@ let r = open_frac_borrow('a, ref_initialized_(reference), q);
        //@ open [r]ref_initialized_(reference);
        let result = unsafe { &*self.buffer_ptr().add(self.start).cast() };
        //@ close [r]ref_initialized_(reference);
        //@ close_frac_borrow(r, ref_initialized_(reference));
        //@ close [f]bounds(self, start);
        result
    }

    #[inline]
    fn as_uninit_array_mut<'a>(&'a mut self) -> &'a mut MaybeUninit<[T; N]>
/*@
    req thread_token(?t) &*& bounds(self, ?start) &*& [?q]lifetime_token('a) &*&
        full_borrow('a, <std::mem::MaybeUninit<[T; N]>>.full_borrow_content(t,
            (base(self) + start) as *std::mem::MaybeUninit<[T; N]>));
    @*/
    /*@
    ens thread_token(t) &*& bounds(self, start) &*& [q]lifetime_token('a) &*&
        full_borrow('a, <std::mem::MaybeUninit<[T; N]>>.full_borrow_content(t, result));
    @*/
    //@ on_unwind_ens false;
    {
        //@ open bounds(self, start);
        debug_assert!(self.start + N <= 2 * N);

        // SAFETY: our invariant guarantees these elements are in bounds.
        let result = unsafe { &mut *self.buffer_mut_ptr().add(self.start).cast() };
        //@ close bounds(self, start);
        result
    }

    /// Pushes a new item `next` to the back, and pops the front-most one.
    ///
    /// All the elements will be shifted to the front end when pushing reaches
    /// the back end.
    fn push(&mut self, next: T)
    /*@
    req thread_token(?t) &*& live(t, self, ?start, ?values) &*& <T>.own(t, next);
    @*/
    /*@
    ens thread_token(t) &*& live(t, self, if start == width::<N>() { 0 } else { start + 1 },
        append(tail(values), cons(next, nil)));
    @*/
    //@ on_unwind_ens thread_token(t);
    {
        //@ open live(t, self, start, values);
        //@ open bounds(self, start);
        //@ open foreach(values, own::<T>(t));
        //@ open array(base(self) + start, width::<N>(), _);
        let buffer_mut_ptr = self.buffer_mut_ptr();
        debug_assert!(self.start + N <= 2 * N);

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
                ptr::copy_nonoverlapping(buffer_mut_ptr.add(self.start + 1), buffer_mut_ptr, N - 1);
                (*buffer_mut_ptr.add(N - 1)).write(next);
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
        //@ close foreach(cons(next, nil), own::<T>(t));
        //@ foreach_append(tail(values), cons(next, nil));
        //@ std::mem::open_MaybeUninit(to_drop);
        //@ close points_to(to_drop as *T, head(values));
        unsafe { ptr::drop_in_place(to_drop.cast_init()) };
        //@ std::mem::close_MaybeUninit_(to_drop);
        /*@
        {
        if start == width::<N>() {
            close array(to_drop, width::<N>(), _);
            close array(buffer_mut_ptr, 0, nil);
        } else {
            close array(to_drop + 1, 0, nil);
            close array(to_drop, 1, _);
            array_join(buffer_mut_ptr);
        }
        close bounds(self, if start == width::<N>() { 0 } else { start + 1 });
        close live(t, self, if start == width::<N>() { 0 } else { start + 1 },
            append(tail(values), cons(next, nil)));
        }
        @*/
    }
}

impl<T, const N: usize> Drop for Buffer<T, N> {
    fn drop(&mut self)
    /*@
    req thread_token(?t) &*& live(t, self, ?start, ?values);
    @*/
    /*@
    ens thread_token(t) &*& storage(self, start);
    @*/
    //@ on_unwind_ens thread_token(t);
    {
        //@ open live(t, self, start, values);
        //@ open bounds(self, start);
        // SAFETY: our invariant guarantees that N elements starting from
        // `self.start` are initialized. We drop them here.
        unsafe {
            let initialized_part: *mut [T] = crate::ptr::slice_from_raw_parts_mut(
                self.buffer_mut_ptr().add(self.start).cast(),
                N,
            );
            //@ initialized_slots(base(self) + start, values);
            // This assertion must be discharged by the Rust slice memory model.
            // No additional axiom or assumed drop contract is supplied here.
            //@ assert *initialized_part |-> slice_of_elems(values);
            //@ close <[T]>.own(t, slice_of_elems(values));
            ptr::drop_in_place(initialized_part);
            //@ assert (initialized_part as *T)[..width::<N>()] |-?-> ?remaining;
            //@ std::mem::array__to_array_MaybeUninit(initialized_part as *T);
        }
        //@ array_join(base(self));
        //@ array_join(base(self));
        //@ close bounds(self, start);
        //@ close storage(self, start);
    }
}
