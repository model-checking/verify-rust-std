/*@

pred_ctor array_owned<T, N>()(t: thread_id_t, value: [T; N]) =
    foreach(Array_elems(value), own::<T>(t));
type_pred_def for<T, N> <[T; N]>.own = array_owned::<T, N>;

lem mapped_append<a, b>(f: fix(a, b), xs: list<a>, ys: list<a>)
    req true;
    ens map(f, append(xs, ys)) == append(map(f, xs), map(f, ys));
{
    match xs {
        nil => {}
        cons(x, rest) => { mapped_append(f, rest, ys); }
    }
}

lem mapped_length<a, b>(f: fix(a, b), xs: list<a>)
    req true;
    ens length(map(f, xs)) == length(xs);
{
    match xs {
        nil => {}
        cons(x, rest) => { mapped_length(f, rest); }
    }
}

lem mapped_range<a, b>(f: fix(a, b), xs: list<a>, start: usize, count: usize)
    req 0 <= start &*& 0 <= count;
    ens take(count, drop(start, map(f, xs))) == map(f, take(count, drop(start, xs)));
{
    match xs {
        nil => {}
        cons(x, rest) => {
            if start > 0 {
                mapped_range(f, rest, start - 1, count);
            } else {
                if count > 0 { mapped_range(f, rest, 0, count - 1); }
            }
        }
    }
}

lem owned_values_mono<T0, T1>(t: thread_id_t, values: list<T0>)
    req type_interp::<T0>() &*& type_interp::<T1>() &*&
        is_subtype_of::<T0, T1>() == true &*& foreach(values, own::<T0>(t));
    ens type_interp::<T0>() &*& type_interp::<T1>() &*&
        foreach(map::<T0, T1>(upcast, values), own::<T1>(t));
{
    match values {
        nil => { open foreach(values, own::<T0>(t)); }
        cons(value, rest) => {
            open foreach(values, own::<T0>(t));
            open own::<T0>(t)(value);
            own_mono::<T0, T1>(t, value);
            close own::<T1>(t)(upcast::<T0, T1>(value));
            owned_values_mono::<T0, T1>(t, rest);
        }
    }
    close foreach(map::<T0, T1>(upcast, values), own::<T1>(t));
}

lem owned_values_send<T>(t0: thread_id_t, t1: thread_id_t, values: list<T>)
    req type_interp::<T>() &*& is_Send(typeid(T)) == true &*& foreach(values, own::<T>(t0));
    ens type_interp::<T>() &*& foreach(values, own::<T>(t1));
{
    match values {
        nil => { open foreach(values, own::<T>(t0)); }
        cons(value, rest) => {
            open foreach(values, own::<T>(t0));
            open own::<T>(t0)(value);
            Send::send::<T>(t0, t1, value);
            close own::<T>(t1)(value);
            owned_values_send(t0, t1, rest);
        }
    }
    close foreach(values, own::<T>(t1));
}

lem mapped_uninit_upcast<T0, T1>(values: list<T0>)
    req is_subtype_of::<T0, T1>() == true;
    ens map::<std::mem::MaybeUninit<T0>, std::mem::MaybeUninit<T1>>(upcast,
            map(std::mem::MaybeUninit::new, values)) ==
        map(std::mem::MaybeUninit::new, map::<T0, T1>(upcast, values));
{
    match values {
        nil => {}
        cons(value, rest) => {
            std::mem::MaybeUninit_upcast_new::<T0, T1>(value);
            mapped_uninit_upcast::<T0, T1>(rest);
        }
    }
}

fix matrix_elems<T, N>(matrix: [[T; N]; 2]) -> list<T> {
    append(Array_elems(head(Array_elems(matrix))),
        Array_elems(head(tail(Array_elems(matrix)))))
}

lem matrix_upcast<T0, T1, N: ?Sized>(matrix: [[T0; N]; 2])
    req is_subtype_of::<T0, T1>() == true;
    ens matrix_elems::<T1, N>(upcast::<[[T0; N]; 2], [[T1; N]; 2]>(matrix)) ==
        map::<T0, T1>(upcast, matrix_elems(matrix));
{
    std::mem::array_subtype::<T0, T1, N>();
    std::mem::array_upcast::<[T0; N], [T1; N], 2>(matrix);
    std::mem::array_elems_length::<[T0; N], 2>(matrix);
    match Array_elems(matrix) {
        nil => {}
        cons(first, rest) => {
            match rest {
                nil => {}
                cons(second, suffix) => {
                    std::mem::array_upcast::<T0, T1, N>(first);
                    std::mem::array_upcast::<T0, T1, N>(second);
                    mapped_append::<T0, T1>(upcast, Array_elems(first), Array_elems(second));
                }
            }
        }
    }
}

// Keep a fraction while changing representations so precision relates the values.
pred_ctor saved_array<T>(p: *T, count: usize, elems: list<T>)(;) =
    [1/2]array(p, count, elems);

lem pack_array<T, N: ?Sized>(p: *[T; N])
    req (p as *T)[..usize_of_const(typeid(N))] |-> ?elems;
    ens *p |-> ?array &*& Array_elems(array) == elems;
{
    close saved_array::<T>(p as *T, usize_of_const(typeid(N)), elems)();
    array_to_Array(p);
    Array_to_array(p);
    open saved_array::<T>(p as *T, usize_of_const(typeid(N)), elems)();
    merge_fractions array(p as *T, usize_of_const(typeid(N)), _);
    array_to_Array(p);
}

lem unpack_matrix<T, N: ?Sized>(p: *[[T; N]; 2])
    req *p |-> ?matrix;
    ens (p as *T)[..2 * usize_of_const(typeid(N))] |-> matrix_elems(matrix);
{
    std::mem::array_layout::<T, N>();
    Array_to_array(p);
    open array(p as *[T; N], 2, _);
    open array((p as *[T; N]) + 1, 1, _);
    open array((p as *[T; N]) + 2, 0, _);
    Array_to_array(p as *[T; N]);
    Array_to_array((p as *[T; N]) + 1);
    array_join(p as *T);
}

lem pack_matrix<T, N: ?Sized>(p: *[[T; N]; 2])
    req (p as *T)[..2 * usize_of_const(typeid(N))] |-> ?elems;
    ens *p |-> ?matrix &*& matrix_elems(matrix) == elems;
{
    std::mem::array_layout::<T, N>();
    array_split(p as *T, usize_of_const(typeid(N)));
    pack_array(p as *[T; N]);
    pack_array((p as *[T; N]) + 1);
    assert *(p as *[T; N]) |-> ?first;
    assert *((p as *[T; N]) + 1) |-> ?second;
    close array((p as *[T; N]) + 2, 0, nil);
    close array((p as *[T; N]) + 1, 1, cons(second, nil));
    close array(p as *[T; N], 2, cons(first, cons(second, nil)));
    pack_array(p);
}

// These conversions preserve writable storage. They do not claim initialized T values.
lem collapse_window<T, N: ?Sized>(p: *std::mem::MaybeUninit<T>)
    req p[..usize_of_const(typeid(N))] |-> ?slots;
    ens *(p as *std::mem::MaybeUninit<[T; N]>) |-> ?window;
{
    std::mem::array_layout::<T, N>();
    std::mem::MaybeUninit_layout::<T>();
    array__to_u8s_(p, usize_of_const(typeid(N)));
    array_to_array_(p as *u8);
    from_u8s_(p as *[T; N]);
    std::mem::close_MaybeUninit_(p as *std::mem::MaybeUninit<[T; N]>);
}

lem expand_window<T, N: ?Sized>(p: *std::mem::MaybeUninit<[T; N]>)
    req *p |-> ?window;
    ens (p as *std::mem::MaybeUninit<T>)[..usize_of_const(typeid(N))] |-> ?slots;
{
    std::mem::MaybeUninit_layout::<T>();
    std::mem::open_MaybeUninit(p);
    Array__to_array_(p as *[T; N]);
    std::mem::array__to_array_MaybeUninit(p as *T);
}

lem own_uninit_values<T>(t: thread_id_t, values: list<std::mem::MaybeUninit<T>>)
    req true;
    ens foreach(values, own::<std::mem::MaybeUninit<T>>(t));
{
    match values {
        nil => {}
        cons(value, rest) => {
            std::mem::MaybeUninit_own_init(t, value);
            close own::<std::mem::MaybeUninit<T>>(t)(value);
            own_uninit_values(t, rest);
        }
    }
    close foreach(values, own::<std::mem::MaybeUninit<T>>(t));
}

lem own_uninit_rows<T, N: ?Sized>(t: thread_id_t, rows: list<[std::mem::MaybeUninit<T>; N]>)
    req true;
    ens foreach(rows, own::<[std::mem::MaybeUninit<T>; N]>(t));
{
    match rows {
        nil => {}
        cons(row, rest) => {
            own_uninit_values(t, Array_elems(row));
            close array_owned::<std::mem::MaybeUninit<T>, N>()(t, row);
            close own::<[std::mem::MaybeUninit<T>; N]>(t)(row);
            own_uninit_rows(t, rest);
        }
    }
    close foreach(rows, own::<[std::mem::MaybeUninit<T>; N]>(t));
}

lem own_matrix_storage<T, N: ?Sized>(t: thread_id_t, matrix: [[std::mem::MaybeUninit<T>; N]; 2])
    req true;
    ens <[[std::mem::MaybeUninit<T>; N]; 2]>.own(t, matrix);
{
    own_uninit_rows(t, Array_elems(matrix));
    close array_owned::<[std::mem::MaybeUninit<T>; N], 2>()(t, matrix);
}

pred array_borrow_tokens<T>(k: lifetime_t, p: *T, count: usize) =
    pointer_within_limits(p) == true &*&
    if count == 0 { true } else {
        points_to_at_lft_end_token(k, p) &*& array_borrow_tokens(k, p + 1, count - 1)
    };

lem lend_array<T>(k: lifetime_t, p: *T, count: usize)
    req 0 <= count &*& p[..count] |-> ?values;
    ens array_at_lft(k, p, count, values) &*& array_borrow_tokens(k, p, count);
{
    open array(p, count, values);
    if count > 0 {
        borrow_points_to_at_lft(k, p);
        lend_array(k, p + 1, count - 1);
    }
    close array_at_lft(k, p, count, values);
    close array_borrow_tokens(k, p, count);
}

lem reclaim_array<T>(k: lifetime_t, p: *T, count: usize)
    req array_borrow_tokens(k, p, count) &*& 0 <= count &*&
        [_]lifetime_dead_token(k) &*& array_at_lft_(k, p, count, _);
    ens p[..count] |-?-> _;
{
    open array_borrow_tokens(k, p, count);
    open array_at_lft_(k, p, count, _);
    if count > 0 {
        borrow_points_to_at_lft_end(p);
        // Discard expired lifetime bookkeeping after recovering the storage.
        leak points_to_at_lft_(k, p, _);
        reclaim_array(k, p + 1, count - 1);
    }
    close array_(p, count, _);
}

@*/
