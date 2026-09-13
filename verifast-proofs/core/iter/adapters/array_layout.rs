/*@

pred_ctor array_owned<T, N>()(t: thread_id_t, value: [T; N]) =
    foreach(Array_elems(value), own::<T>(t));
type_pred_def for<T, N> <[T; N]>.own = array_owned::<T, N>;

fix matrix_elems<T, N>(matrix: [[T; N]; 2]) -> list<T> {
    append(Array_elems(head(Array_elems(matrix))),
        Array_elems(head(tail(Array_elems(matrix)))))
}

// Keep a fraction while changing representations so precision relates the values.
pred_ctor saved_array<T>(p: *T, count: usize, elems: list<T>)(;) =
    [1/2]array(p, count, elems);

lem pack_array<T, N>(p: *[T; N])
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

lem unpack_matrix<T, N>(p: *[[T; N]; 2])
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

lem pack_matrix<T, N>(p: *[[T; N]; 2])
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
lem collapse_window<T, N>(p: *std::mem::MaybeUninit<T>)
    req p[..usize_of_const(typeid(N))] |-> _;
    ens *(p as *std::mem::MaybeUninit<[T; N]>) |-> _;
{
    std::mem::array_layout::<T, N>();
    std::mem::MaybeUninit_layout::<T>();
    array__to_u8s_(p, usize_of_const(typeid(N)));
    array_to_array_(p as *u8);
    from_u8s_(p as *[T; N]);
    std::mem::close_MaybeUninit_(p as *std::mem::MaybeUninit<[T; N]>);
}

lem expand_window<T, N>(p: *std::mem::MaybeUninit<[T; N]>)
    req *p |-> _;
    ens (p as *std::mem::MaybeUninit<T>)[..usize_of_const(typeid(N))] |-> _;
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

lem own_uninit_rows<T, N>(t: thread_id_t, rows: list<[std::mem::MaybeUninit<T>; N]>)
    req true;
    ens foreach(rows, own::<[std::mem::MaybeUninit<T>; N]>(t));
{
    match rows {
        nil => {}
        cons(row, rest) => {
            own_uninit_values(t, Array_elems(row));
            close <[std::mem::MaybeUninit<T>; N]>.own(t, row);
            close own::<[std::mem::MaybeUninit<T>; N]>(t)(row);
            own_uninit_rows(t, rest);
        }
    }
    close foreach(rows, own::<[std::mem::MaybeUninit<T>; N]>(t));
}

lem own_matrix_storage<T, N>(t: thread_id_t, matrix: [[std::mem::MaybeUninit<T>; N]; 2])
    req true;
    ens <[[std::mem::MaybeUninit<T>; N]; 2]>.own(t, matrix);
{
    own_uninit_rows(t, Array_elems(matrix));
    close <[[std::mem::MaybeUninit<T>; N]; 2]>.own(t, matrix);
}

pred array_borrow_tokens<T>(k: lifetime_t, p: *T, count: usize;) =
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
    req 0 <= count &*& [_]lifetime_dead_token(k) &*&
        array_borrow_tokens(k, p, count) &*& array_at_lft_(k, p, count, _);
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
