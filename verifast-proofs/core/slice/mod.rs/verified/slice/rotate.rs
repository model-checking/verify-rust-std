use crate::mem::{MaybeUninit, SizedTypeProperties};
use crate::ptr;

type BufType = [usize; 32];

const unsafe fn uninit_buf__VeriFast_wrapper<BufType, T>() -> MaybeUninit<(BufType, [T; 0])>
//@ req true;
//@ ens true;
//@ on_unwind_ens false;
//@ assume_correct
{
    MaybeUninit::<(BufType, [T; 0])>::uninit()
}

const unsafe fn uninit_buf_as_mut_ptr__VeriFast_wrapper<BufType, T>(
    rawarray: &mut MaybeUninit<(BufType, [T; 0])>,
) -> *mut (BufType, [T; 0])
//@ req *rawarray |-> ?v;
//@ ens *rawarray |-> v &*& result == rawarray as *mut (BufType, [T; 0]);
//@ on_unwind_ens false;
//@ assume_correct
{
    rawarray.as_mut_ptr()
}

const unsafe fn ptr_replace__VeriFast_wrapper<T>(dst: *mut T, src: T) -> T
//@ req *dst |-> ?v;
//@ ens *dst |-> src &*& result == v;
//@ on_unwind_ens false;
//@ assume_correct
{
    unsafe { dst.replace(src) }
}

/*@
lem rotate_ptr_limits<T>(ptr: *T, len: usize, mid: usize)
    req 0 <= mid &*& mid <= len &*& 0 < std::mem::size_of::<T>() &*& len * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(ptr) == true &*& pointer_within_limits(ptr + len) == true;
    ens mid <= isize::MAX &*& len - mid <= isize::MAX &*& len <= isize::MAX &*& mid * std::mem::size_of::<T>() <= isize::MAX &*& (len - mid) * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(ptr + mid) == true &*& ((ptr + mid) + (len - mid)) == ptr + len &*& ((ptr + len) - (len - mid)) == ptr + mid;
{
    mul_mono_l(1, std::mem::size_of::<T>(), len);
    mul_mono_l(0, mid, std::mem::size_of::<T>());
    mul_mono_l(mid, len, std::mem::size_of::<T>());
    mul_mono_l(0, len - mid, std::mem::size_of::<T>());
    mul_mono_l(len - mid, len, std::mem::size_of::<T>());
}

pred rawarray_rest<U>(rawarray: *U, k: usize);

lem rawarray_to_buf<U, T>(rawarray: *U, buf: *T, k: usize)
    req *rawarray |-> ?_ &*& buf == rawarray as *T &*& 0 <= k &*& 0 < std::mem::size_of::<T>() &*& k <= std::mem::size_of(typeid([usize; 32])) / std::mem::size_of::<T>();
    ens buf[..k] |-> _ &*& rawarray_rest::<U>(rawarray, k);
{
    assume(false);
}

lem buf_to_rawarray<U, T>(rawarray: *U, buf: *T, k: usize)
    req buf[..k] |-> _ &*& rawarray_rest::<U>(rawarray, k);
    ens *rawarray |-> ?_;
{
    assume(false);
}
@*/

/// Rotates the range `[mid-left, mid+right)` such that the element at `mid` becomes the first
/// element. Equivalently, rotates the range `left` elements to the left or `right` elements to the
/// right.
///
/// # Safety
///
/// The specified range must be valid for reading and writing.
#[inline]
pub(super) const unsafe fn ptr_rotate<T>(left: usize, mid: *mut T, right: usize)
//@ req thread_token(?t) &*& (mid - left)[..left + right] |-> ?elems &*& foreach(elems, own::<T>(t)) &*& 0 <= left &*& 0 <= right &*& left + right <= usize::MAX &*& (left + right) * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(mid - left) == true &*& pointer_within_limits(mid + right) == true;
//@ ens thread_token(t) &*& (mid - left)[..left + right] |-> ?elems1 &*& foreach(elems1, own::<T>(t));
//@ on_unwind_ens false;
{
    if T::IS_ZST {
        return;
    }
    // abort early if the rotate is a no-op
    if (left == 0) || (right == 0) {
        return;
    }
    // `T` is not a zero-sized type, so it's okay to divide by its size.
    //@ std::alloc::is_valid_layout_size_of_align_of::<T>();
    if !cfg!(feature = "optimize_for_size")
        // FIXME(const-hack): Use cmp::min when available in const
        && const_min(left, right) <= size_of::<BufType>() / size_of::<T>()
    {
        // SAFETY: guaranteed by the caller
        unsafe { ptr_rotate_memmove(left, mid, right) };
    } else if !cfg!(feature = "optimize_for_size")
        && ((left + right < 24) || (size_of::<T>() > size_of::<[usize; 4]>()))
    {
        // SAFETY: guaranteed by the caller
        unsafe { ptr_rotate_gcd(left, mid, right) }
    } else {
        // SAFETY: guaranteed by the caller
        unsafe { ptr_rotate_swap(left, mid, right) }
    }
}

/// Algorithm 1 is used if `min(left, right)` is small enough to fit onto a stack buffer. The
/// `min(left, right)` elements are copied onto the buffer, `memmove` is applied to the others, and
/// the ones on the buffer are moved back into the hole on the opposite side of where they
/// originated.
///
/// # Safety
///
/// The specified range must be valid for reading and writing.
#[inline]
const unsafe fn ptr_rotate_memmove<T>(left: usize, mid: *mut T, right: usize)
//@ req thread_token(?t) &*& (mid - left)[..left + right] |-> ?elems &*& foreach(elems, own::<T>(t)) &*& 0 < left &*& 0 < right &*& (left + right) * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(mid - left) == true &*& pointer_within_limits(mid + right) == true &*& 0 < std::mem::size_of::<T>() &*& (if right < left { right } else { left }) <= std::mem::size_of(typeid([usize; 32])) / std::mem::size_of::<T>();
//@ ens thread_token(t) &*& (mid - left)[..left + right] |-> ?elems1 &*& foreach(elems1, own::<T>(t));
//@ on_unwind_ens false;
{
    //@ let p_start = mid - left;
    //@ let n_total = left + right;
    //@ rotate_ptr_limits::<T>(p_start, n_total, left);
    //@ rotate_ptr_limits::<T>(p_start, n_total, right);
    // The `[T; 0]` here is to ensure this is appropriately aligned for T
    let mut rawarray = unsafe { uninit_buf__VeriFast_wrapper::<BufType, T>() };
    let buf = unsafe { uninit_buf_as_mut_ptr__VeriFast_wrapper::<BufType, T>(&mut rawarray) } as *mut T;
    // SAFETY: `mid-left <= mid-left+right < mid+right`
    let dim = unsafe { mid.sub(left).add(right) };
    if left <= right {
        // SAFETY:
        //
        // 1) The `if` condition about the sizes ensures `[mid-left; left]` will fit in
        //    `buf` without overflow and `buf` was created just above and so cannot be
        //    overlapped with any value of `[mid-left; left]`
        // 2) [mid-left, mid+right) are all valid for reading and writing and we don't care
        //    about overlaps here.
        // 3) The `if` condition about `left <= right` ensures writing `left` elements to
        //    `dim = mid-left+right` is valid because:
        //    - `buf` is valid and `left` elements were written in it in 1)
        //    - `dim+left = mid-left+right+left = mid+right` and we write `[dim, dim+left)`
        unsafe {
            //@ rawarray_to_buf(&rawarray, buf, left);
            //@ array_split(p_start, left);
            //@ foreach_split(elems, own::<T>(t), left);
            // 1)
            ptr::copy_nonoverlapping(mid.sub(left), buf, left);
            //@ array_join(p_start);
            //@ close ptr::copy_context::<T>(p_start, n_total, left, 0, right, elems);
            // 2)
            ptr::copy(mid, mid.sub(left), right);
            //@ take_append_l(right, drop(left, elems), drop(right, elems));
            //@ array_split(p_start, right);
            //@ array_to_array_(p_start + right);
            // 3)
            ptr::copy_nonoverlapping(buf, dim, left);
            //@ array_join(p_start);
            //@ foreach_append(drop(left, elems), take(left, elems));
            //@ array_to_array_(buf);
            //@ buf_to_rawarray(&rawarray, buf, left);
        }
    } else {
        // SAFETY: same reasoning as above but with `left` and `right` reversed
        unsafe {
            //@ rawarray_to_buf(&rawarray, buf, right);
            //@ array_split(p_start, left);
            //@ foreach_split(elems, own::<T>(t), left);
            ptr::copy_nonoverlapping(mid, buf, right);
            //@ array_join(p_start);
            //@ close ptr::copy_context::<T>(p_start, n_total, 0, right, left, elems);
            ptr::copy(mid.sub(left), dim, left);
            //@ take_append_l(right, take(right, elems), take(left, elems));
            //@ drop_append(right, take(right, elems), take(left, elems));
            //@ array_split(p_start, right);
            //@ array_to_array_(p_start);
            ptr::copy_nonoverlapping(buf, mid.sub(left), right);
            //@ array_join(p_start);
            //@ foreach_append(drop(left, elems), take(left, elems));
            //@ array_to_array_(buf);
            //@ buf_to_rawarray(&rawarray, buf, right);
        }
    }
}

/*@
pred rotate_gcd_hole<T>(t: thread_id_t, x: *T, n_total: usize, hole: usize) =
    0 <= hole &*& hole < n_total &*&
    x[..hole] |-> ?prefix &*& foreach(prefix, own::<T>(t)) &*&
    *(x + hole) |-> _ &*&
    (x + hole + 1)[..n_total - hole - 1] |-> ?suffix &*& foreach(suffix, own::<T>(t));

pred rotate_gcd_step_ctxt<T>(t: thread_id_t, x: *T, n_total: usize, hole: usize, i: usize) =
    0 <= hole &*& hole < n_total &*& 0 <= i &*& i < n_total &*& i != hole &*&
    if i < hole {
        x[..i] |-> ?p1 &*& foreach(p1, own::<T>(t)) &*&
        (x + i + 1)[..hole - i - 1] |-> ?p2 &*& foreach(p2, own::<T>(t)) &*&
        *(x + hole) |-> _ &*&
        (x + hole + 1)[..n_total - hole - 1] |-> ?suffix &*& foreach(suffix, own::<T>(t))
    } else {
        x[..hole] |-> ?prefix &*& foreach(prefix, own::<T>(t)) &*&
        *(x + hole) |-> _ &*&
        (x + hole + 1)[..i - hole - 1] |-> ?s1 &*& foreach(s1, own::<T>(t)) &*&
        (x + i + 1)[..n_total - i - 1] |-> ?s2 &*& foreach(s2, own::<T>(t))
    };

lem rotate_gcd_open_hole<T>(t: thread_id_t, x: *T, n_total: usize, hole: usize)
    req x[..n_total] |-> ?elems &*& foreach(elems, own::<T>(t)) &*& 0 <= hole &*& hole < n_total;
    ens x[..hole] |-> ?prefix &*& foreach(prefix, own::<T>(t)) &*&
        *(x + hole) |-> ?v &*& (<T>.own)(t, v) &*&
        (x + hole + 1)[..n_total - hole - 1] |-> ?suffix &*& foreach(suffix, own::<T>(t));
{
    array_split(x, hole);
    foreach_split(elems, own::<T>(t), hole);
    let rest = drop(hole, elems);
    open array(x + hole, n_total - hole, rest);
    open foreach(rest, own::<T>(t));
    assert *(x + hole) |-> ?v;
    open own::<T>(t)(v);
}

lem rotate_gcd_finish_open_hole<T>(t: thread_id_t, x: *T, n_total: usize, hole: usize)
    req 0 <= hole &*& hole < n_total &*&
        x[..hole] |-> ?prefix &*& foreach(prefix, own::<T>(t)) &*&
        *(x + hole) |-> ?v &*&
        (x + hole + 1)[..n_total - hole - 1] |-> ?suffix &*& foreach(suffix, own::<T>(t));
    ens rotate_gcd_hole::<T>(t, x, n_total, hole);
{
    open points_to(x + hole, v);
    close rotate_gcd_hole::<T>(t, x, n_total, hole);
}

lem rotate_gcd_extract_i<T>(t: thread_id_t, x: *T, n_total: usize, hole: usize, i: usize)
    req rotate_gcd_hole::<T>(t, x, n_total, hole) &*& 0 <= i &*& i < n_total &*& i != hole;
    ens rotate_gcd_step_ctxt::<T>(t, x, n_total, hole, i) &*& *(x + i) |-> ?vi &*& (<T>.own)(t, vi);
{
    open rotate_gcd_hole::<T>(t, x, n_total, hole);
    assert x[..hole] |-> ?prefix;
    assert (x + hole + 1)[..n_total - hole - 1] |-> ?suffix;
    if i < hole {
        array_split(x, i);
        foreach_split(prefix, own::<T>(t), i);
        let rest = drop(i, prefix);
        open array(x + i, hole - i, rest);
        open foreach(rest, own::<T>(t));
        assert *(x + i) |-> ?vi;
        open own::<T>(t)(vi);
        close rotate_gcd_step_ctxt::<T>(t, x, n_total, hole, i);
    } else {
        let k = i - hole - 1;
        array_split(x + hole + 1, k);
        foreach_split(suffix, own::<T>(t), k);
        let rest = drop(k, suffix);
        open array(x + i, n_total - i, rest);
        open foreach(rest, own::<T>(t));
        assert *(x + i) |-> ?vi;
        open own::<T>(t)(vi);
        close rotate_gcd_step_ctxt::<T>(t, x, n_total, hole, i);
    }
}

lem rotate_gcd_restore_i<T>(t: thread_id_t, x: *T, n_total: usize, hole: usize, i: usize, v_new: T)
    req rotate_gcd_step_ctxt::<T>(t, x, n_total, hole, i) &*& *(x + i) |-> v_new &*& (<T>.own)(t, v_new);
    ens rotate_gcd_hole::<T>(t, x, n_total, hole);
{
    open rotate_gcd_step_ctxt::<T>(t, x, n_total, hole, i);
    points_to_limits(x + i);
    close own::<T>(t)(v_new);
    if i < hole {
        assert x[..i] |-> ?p1;
        assert (x + i + 1)[..hole - i - 1] |-> ?p2;
        close foreach(cons(v_new, p2), own::<T>(t));
        close array(x + i, hole - i, cons(v_new, p2));
        array_join(x);
        foreach_append(p1, cons(v_new, p2));
        close rotate_gcd_hole::<T>(t, x, n_total, hole);
    } else {
        assert (x + hole + 1)[..i - hole - 1] |-> ?s1;
        assert (x + i + 1)[..n_total - i - 1] |-> ?s2;
        close foreach(cons(v_new, s2), own::<T>(t));
        close array(x + i, n_total - i, cons(v_new, s2));
        array_join(x + hole + 1);
        foreach_append(s1, cons(v_new, s2));
        close rotate_gcd_hole::<T>(t, x, n_total, hole);
    }
}

lem rotate_gcd_prep_close_hole<T>(t: thread_id_t, x: *T, n_total: usize, hole: usize)
    req rotate_gcd_hole::<T>(t, x, n_total, hole);
    ens 0 <= hole &*& hole < n_total &*&
        x[..hole] |-> ?prefix &*& foreach(prefix, own::<T>(t)) &*&
        *(x + hole) |-> _ &*&
        (x + hole + 1)[..n_total - hole - 1] |-> ?suffix &*& foreach(suffix, own::<T>(t));
{
    open rotate_gcd_hole::<T>(t, x, n_total, hole);
}

lem rotate_gcd_finish_close_hole<T>(t: thread_id_t, x: *T, n_total: usize, hole: usize, v_final: T)
    req 0 <= hole &*& hole < n_total &*&
        x[..hole] |-> ?prefix &*& foreach(prefix, own::<T>(t)) &*&
        *(x + hole) |-> v_final &*& (<T>.own)(t, v_final) &*&
        (x + hole + 1)[..n_total - hole - 1] |-> ?suffix &*& foreach(suffix, own::<T>(t));
    ens x[..n_total] |-> ?elems1 &*& foreach(elems1, own::<T>(t));
{
    points_to_limits(x + hole);
    close own::<T>(t)(v_final);
    close foreach(cons(v_final, suffix), own::<T>(t));
    close array(x + hole, n_total - hole, cons(v_final, suffix));
    array_join(x);
    foreach_append(prefix, cons(v_final, suffix));
}
@*/

/// Algorithm 2 is used for small values of `left + right` or for large `T`. The elements
/// are moved into their final positions one at a time starting at `mid - left` and advancing by
/// `right` steps modulo `left + right`, such that only one temporary is needed. Eventually, we
/// arrive back at `mid - left`. However, if `gcd(left + right, right)` is not 1, the above steps
/// skipped over elements. For example:
/// ```text
/// left = 10, right = 6
/// the `^` indicates an element in its final place
/// 6 7 8 9 10 11 12 13 14 15 . 0 1 2 3 4 5
/// after using one step of the above algorithm (The X will be overwritten at the end of the round,
/// and 12 is stored in a temporary):
/// X 7 8 9 10 11 6 13 14 15 . 0 1 2 3 4 5
///               ^
/// after using another step (now 2 is in the temporary):
/// X 7 8 9 10 11 6 13 14 15 . 0 1 12 3 4 5
///               ^                 ^
/// after the third step (the steps wrap around, and 8 is in the temporary):
/// X 7 2 9 10 11 6 13 14 15 . 0 1 12 3 4 5
///     ^         ^                 ^
/// after 7 more steps, the round ends with the temporary 0 getting put in the X:
/// 0 7 2 9 4 11 6 13 8 15 . 10 1 12 3 14 5
/// ^   ^   ^    ^    ^       ^    ^    ^
/// ```
/// Fortunately, the number of skipped over elements between finalized elements is always equal, so
/// we can just offset our starting position and do more rounds (the total number of rounds is the
/// `gcd(left + right, right)` value). The end result is that all elements are finalized once and
/// only once.
///
/// Algorithm 2 can be vectorized by chunking and performing many rounds at once, but there are too
/// few rounds on average until `left + right` is enormous, and the worst case of a single
/// round is always there.
///
/// # Safety
///
/// The specified range must be valid for reading and writing.
#[inline]
const unsafe fn ptr_rotate_gcd<T>(left: usize, mid: *mut T, right: usize)
//@ req thread_token(?t) &*& (mid - left)[..left + right] |-> ?elems &*& foreach(elems, own::<T>(t)) &*& 0 < left &*& 0 < right &*& 0 < std::mem::size_of::<T>() &*& (left + right) * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(mid - left) == true &*& pointer_within_limits(mid + right) == true;
//@ ens thread_token(t) &*& (mid - left)[..left + right] |-> ?elems1 &*& foreach(elems1, own::<T>(t));
//@ on_unwind_ens false;
{
    //@ let n_total = left + right;
    //@ rotate_ptr_limits::<T>(mid - left, n_total, left);
    // Algorithm 2
    // Microbenchmarks indicate that the average performance for random shifts is better all
    // the way until about `left + right == 32`, but the worst case performance breaks even
    // around 16. 24 was chosen as middle ground. If the size of `T` is larger than 4
    // `usize`s, this algorithm also outperforms other algorithms.
    // SAFETY: callers must ensure `mid - left` is valid for reading and writing.
    let x = unsafe { mid.sub(left) };
    // beginning of first round
    // SAFETY: see previous comment.
    //@ rotate_gcd_open_hole::<T>(t, x, n_total, 0);
    let mut tmp: T = unsafe { x.read() };
    //@ rotate_gcd_finish_open_hole::<T>(t, x, n_total, 0);
    let mut i = right;
    // `gcd` can be found before hand by calculating `gcd(left + right, right)`,
    // but it is faster to do one loop which calculates the gcd as a side effect, then
    // doing the rest of the chunk
    let mut gcd = right;
    // benchmarks reveal that it is faster to swap temporaries all the way through instead
    // of reading one temporary once, copying backwards, and then writing that temporary at
    // the very end. This is possibly due to the fact that swapping or replacing temporaries
    // uses only one memory address in the loop instead of needing to manage two.
    loop {
        //@ inv thread_token(t) &*& rotate_gcd_hole::<T>(t, x, n_total, 0) &*& (<T>.own)(t, tmp) &*& 1 <= gcd &*& gcd <= right &*& gcd <= i &*& 1 <= i &*& i < n_total &*& 0 < std::mem::size_of::<T>() &*& n_total * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(x) == true &*& pointer_within_limits(x + n_total) == true;
        // [long-safety-expl]
        // SAFETY: callers must ensure `[left, left+mid+right)` are all valid for reading and
        // writing.
        //
        // - `i` start with `right` so `mid-left <= x+i = x+right = mid-left+right < mid+right`
        // - `i <= left+right-1` is always true
        //   - if `i < left`, `right` is added so `i < left+right` and on the next
        //     iteration `left` is removed from `i` so it doesn't go further
        //   - if `i >= left`, `left` is removed immediately and so it doesn't go further.
        // - overflows cannot happen for `i` since the function's safety contract ask for
        //   `mid+right-1 = x+left+right` to be valid for writing
        // - underflows cannot happen because `i` must be bigger or equal to `left` for
        //   a subtraction of `left` to happen.
        //
        // So `x+i` is valid for reading and writing if the caller respected the contract
        //@ rotate_ptr_limits::<T>(x, n_total, i);
        //@ rotate_gcd_extract_i::<T>(t, x, n_total, 0, i);
        //@ let old_tmp = tmp;
        tmp = unsafe { ptr_replace__VeriFast_wrapper(x.add(i), tmp) };
        //@ rotate_gcd_restore_i::<T>(t, x, n_total, 0, i, old_tmp);
        // instead of incrementing `i` and then checking if it is outside the bounds, we
        // check if `i` will go outside the bounds on the next increment. This prevents
        // any wrapping of pointers or `usize`.
        if i >= left {
            i -= left;
            if i == 0 {
                // end of first round
                // SAFETY: tmp has been read from a valid source and x is valid for writing
                // according to the caller.
                //@ rotate_gcd_prep_close_hole::<T>(t, x, n_total, 0);
                unsafe { x.write(tmp) };
                //@ rotate_gcd_finish_close_hole::<T>(t, x, n_total, 0, tmp);
                break;
            }
            // this conditional must be here if `left + right >= 15`
            if i < gcd {
                gcd = i;
            }
        } else {
            i += right;
        }
    }
    // finish the chunk with more rounds
    // FIXME(const-hack): Use `for start in 1..gcd` when available in const
    let mut start = 1;
    loop {
        //@ inv thread_token(t) &*& lifetime_token(func_lft) &*& x[..n_total] |-> ?cur_elems &*& foreach(cur_elems, own::<T>(t)) &*& 1 <= start &*& 1 <= gcd &*& gcd <= left &*& gcd <= right &*& 0 < std::mem::size_of::<T>() &*& n_total * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(x) == true &*& pointer_within_limits(x + n_total) == true;
        if start < gcd {
            // SAFETY: `gcd` is at most equal to `right` so all values in `1..gcd` are valid for
            // reading and writing as per the function's safety contract, see [long-safety-expl]
            // above
            //@ rotate_ptr_limits::<T>(x, n_total, start);
            //@ rotate_gcd_open_hole::<T>(t, x, n_total, start);
            tmp = unsafe { x.add(start).read() };
            //@ rotate_gcd_finish_open_hole::<T>(t, x, n_total, start);
            // [safety-expl-addition]
            //
            // Here `start < gcd` so `start < right` so `i < right+right`: `right` being the
            // greatest common divisor of `(left+right, right)` means that `left = right` so
            // `i < left+right` so `x+i = mid-left+i` is always valid for reading and writing
            // according to the function's safety contract.
            i = start + right;
            loop {
                //@ inv thread_token(t) &*& rotate_gcd_hole::<T>(t, x, n_total, start) &*& (<T>.own)(t, tmp) &*& 1 <= start &*& start < gcd &*& gcd <= left &*& gcd <= right &*& 0 <= i &*& i < n_total &*& i != start &*& 0 < std::mem::size_of::<T>() &*& n_total * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(x) == true &*& pointer_within_limits(x + n_total) == true;
                // SAFETY: see [long-safety-expl] and [safety-expl-addition]
                //@ rotate_ptr_limits::<T>(x, n_total, i);
                //@ rotate_gcd_extract_i::<T>(t, x, n_total, start, i);
                //@ let old_tmp2 = tmp;
                tmp = unsafe { ptr_replace__VeriFast_wrapper(x.add(i), tmp) };
                //@ rotate_gcd_restore_i::<T>(t, x, n_total, start, i, old_tmp2);
                if i >= left {
                    i -= left;
                    if i == start {
                        // SAFETY: see [long-safety-expl] and [safety-expl-addition]
                        //@ rotate_ptr_limits::<T>(x, n_total, start);
                        //@ rotate_gcd_prep_close_hole::<T>(t, x, n_total, start);
                        unsafe { x.add(start).write(tmp) };
                        //@ rotate_gcd_finish_close_hole::<T>(t, x, n_total, start, tmp);
                        break;
                    }
                } else {
                    i += right;
                }
            }

            start += 1;
        } else {
            break;
        }
    }
}

/// Algorithm 3 utilizes repeated swapping of `min(left, right)` elements.
///
/// ///
/// ```text
/// left = 11, right = 4
/// [4 5 6 7 8 9 10 11 12 13 14 . 0 1 2 3]
///                  ^  ^  ^  ^   ^ ^ ^ ^ swapping the right most elements with elements to the left
/// [4 5 6 7 8 9 10 . 0 1 2 3] 11 12 13 14
///        ^ ^ ^  ^   ^ ^ ^ ^ swapping these
/// [4 5 6 . 0 1 2 3] 7 8 9 10 11 12 13 14
/// we cannot swap any more, but a smaller rotation problem is left to solve
/// ```
/// when `left < right` the swapping happens from the left instead.
///
/// # Safety
///
/// The specified range must be valid for reading and writing.
/*@
pred rotate_swap_ctxt<T>(t: thread_id_t, p_start: *T, n_total: usize, idx: usize, k: usize, vs1: list<T>, vs2: list<T>) =
    0 <= idx &*& 0 <= k &*& idx + 2 * k <= n_total &*&
    p_start[..idx] |-> ?prefix &*& foreach(prefix, own::<T>(t)) &*&
    (p_start + idx + 2 * k)[..n_total - idx - 2 * k] |-> ?suffix &*& foreach(suffix, own::<T>(t)) &*&
    foreach(vs1, own::<T>(t)) &*& foreach(vs2, own::<T>(t));

lem rotate_swap_extract<T>(t: thread_id_t, p_start: *T, n_total: usize, idx: usize, k: usize)
    req p_start[..n_total] |-> ?elems &*& foreach(elems, own::<T>(t)) &*& 0 <= idx &*& 0 <= k &*& idx + 2 * k <= n_total;
    ens (p_start + idx)[..k] |-> ?vs1 &*& (p_start + idx + k)[..k] |-> ?vs2 &*&
        rotate_swap_ctxt::<T>(t, p_start, n_total, idx, k, vs1, vs2);
{
    array_split(p_start, idx);
    foreach_split(elems, own::<T>(t), idx);
    let rest1 = drop(idx, elems);
    array_split(p_start + idx, k);
    foreach_split(rest1, own::<T>(t), k);
    let rest2 = drop(k, rest1);
    array_split(p_start + idx + k, k);
    foreach_split(rest2, own::<T>(t), k);
    close rotate_swap_ctxt::<T>(t, p_start, n_total, idx, k, take(k, rest1), take(k, rest2));
}

lem rotate_swap_restore<T>(t: thread_id_t, p_start: *T, n_total: usize, idx: usize, k: usize)
    req rotate_swap_ctxt::<T>(t, p_start, n_total, idx, k, ?vs1, ?vs2) &*&
        (p_start + idx)[..k] |-> vs2 &*& (p_start + idx + k)[..k] |-> vs1;
    ens p_start[..n_total] |-> ?elems1 &*& foreach(elems1, own::<T>(t));
{
    open rotate_swap_ctxt::<T>(t, p_start, n_total, idx, k, vs1, vs2);
    assert p_start[..idx] |-> ?prefix;
    assert (p_start + idx + 2 * k)[..n_total - idx - 2 * k] |-> ?suffix;
    array_join(p_start + idx + k);
    foreach_append(vs1, suffix);
    array_join(p_start + idx);
    foreach_append(vs2, append(vs1, suffix));
    array_join(p_start);
    foreach_append(prefix, append(vs2, append(vs1, suffix)));
}

pred rotate_swap_state<T>(p_start: *T, n_total: usize, left: usize, mid: *T, right: usize, offset: usize) =
    0 <= offset &*& offset + left + right <= n_total &*& mid == p_start + (offset + left);
@*/

#[inline]
const unsafe fn ptr_rotate_swap<T>(mut left: usize, mut mid: *mut T, mut right: usize)
//@ req thread_token(?t) &*& (mid - left)[..left + right] |-> ?elems &*& foreach(elems, own::<T>(t)) &*& 0 < left &*& 0 < right &*& 0 < std::mem::size_of::<T>() &*& (left + right) * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(mid - left) == true &*& pointer_within_limits(mid + right) == true;
//@ ens thread_token(t) &*& (mid - left)[..left + right] |-> ?elems1 &*& foreach(elems1, own::<T>(t));
//@ on_unwind_ens false;
{
    //@ let p_start = mid - left;
    //@ let n_total = left + right;
    //@ close rotate_swap_state::<T>(p_start, n_total, left, mid, right, 0);
    loop {
        //@ inv thread_token(t) &*& p_start[..n_total] |-> ?cur_elems &*& foreach(cur_elems, own::<T>(t)) &*& rotate_swap_state::<T>(p_start, n_total, left, mid, right, ?offset) &*& 0 < left &*& 0 < right &*& 0 < std::mem::size_of::<T>() &*& n_total * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(p_start) == true &*& pointer_within_limits(p_start + n_total) == true;
        if left >= right {
            // Algorithm 3
            // There is an alternate way of swapping that involves finding where the last swap
            // of this algorithm would be, and swapping using that last chunk instead of swapping
            // adjacent chunks like this algorithm is doing, but this way is still faster.
            loop {
                //@ inv thread_token(t) &*& p_start[..n_total] |-> ?cur_elems1 &*& foreach(cur_elems1, own::<T>(t)) &*& rotate_swap_state::<T>(p_start, n_total, left, mid, right, ?offset1) &*& left >= right &*& 0 < right &*& 0 < std::mem::size_of::<T>() &*& n_total * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(p_start) == true &*& pointer_within_limits(p_start + n_total) == true;
                // SAFETY:
                // `left >= right` so `[mid-right, mid+right)` is valid for reading and writing
                // Subtracting `right` from `mid` each turn is counterbalanced by the addition and
                // check after it.
                unsafe {
                    //@ open rotate_swap_state::<T>(p_start, n_total, left, mid, right, offset1);
                    //@ let idx = offset1 + left - right;
                    //@ rotate_swap_extract::<T>(t, p_start, n_total, idx, right);
                    //@ rotate_ptr_limits::<T>(p_start, n_total, offset1 + left);
                    //@ rotate_ptr_limits::<T>(p_start, offset1 + left, idx);
                    ptr::swap_nonoverlapping(mid.sub(right), mid, right);
                    //@ rotate_swap_restore::<T>(t, p_start, n_total, idx, right);
                    mid = mid.sub(right);
                }
                left -= right;
                //@ close rotate_swap_state::<T>(p_start, n_total, left, mid, right, offset1);
                if left < right {
                    break;
                }
            }
        } else {
            // Algorithm 3, `left < right`
            loop {
                //@ inv thread_token(t) &*& p_start[..n_total] |-> ?cur_elems1 &*& foreach(cur_elems1, own::<T>(t)) &*& rotate_swap_state::<T>(p_start, n_total, left, mid, right, ?offset1) &*& right >= left &*& 0 < left &*& 0 < std::mem::size_of::<T>() &*& n_total * std::mem::size_of::<T>() <= isize::MAX &*& pointer_within_limits(p_start) == true &*& pointer_within_limits(p_start + n_total) == true;
                // SAFETY: `[mid-left, mid+left)` is valid for reading and writing because
                // `left < right` so `mid+left < mid+right`.
                // Adding `left` to `mid` each turn is counterbalanced by the subtraction and check
                // after it.
                unsafe {
                    //@ open rotate_swap_state::<T>(p_start, n_total, left, mid, right, offset1);
                    //@ rotate_swap_extract::<T>(t, p_start, n_total, offset1, left);
                    //@ rotate_ptr_limits::<T>(p_start, n_total, offset1 + left);
                    //@ rotate_ptr_limits::<T>(p_start, offset1 + left, offset1);
                    //@ rotate_ptr_limits::<T>(p_start, n_total, offset1 + 2 * left);
                    ptr::swap_nonoverlapping(mid.sub(left), mid, left);
                    //@ rotate_swap_restore::<T>(t, p_start, n_total, offset1, left);
                    mid = mid.add(left);
                }
                right -= left;
                //@ close rotate_swap_state::<T>(p_start, n_total, left, mid, right, offset1 + left);
                if right < left {
                    break;
                }
            }
        }
        if (right == 0) || (left == 0) {
            //@ open rotate_swap_state::<T>(p_start, n_total, left, mid, right, _);
            return;
        }
    }
}

// FIXME(const-hack): Use cmp::min when available in const
const fn const_min(left: usize, right: usize) -> usize
//@ req true;
//@ ens result == if right < left { right } else { left };
//@ on_unwind_ens false;
{
    if right < left { right } else { left }
}
