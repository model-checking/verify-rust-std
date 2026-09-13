/*@

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
    array__to_u8s_(p, usize_of_const(typeid(N)));
    array_to_array_(p as *u8);
    from_u8s_(p as *[T; N]);
    std::mem::close_MaybeUninit_(p as *std::mem::MaybeUninit<[T; N]>);
}

lem expand_window<T, N>(p: *std::mem::MaybeUninit<[T; N]>)
    req *p |-> _;
    ens (p as *std::mem::MaybeUninit<T>)[..usize_of_const(typeid(N))] |-> _;
{
    std::mem::open_MaybeUninit(p);
    Array__to_array_(p as *[T; N]);
    std::mem::array__to_array_MaybeUninit(p as *T);
}

@*/
