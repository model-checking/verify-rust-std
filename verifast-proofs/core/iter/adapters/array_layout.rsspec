/*@

fix matrix_elems<T, N>(matrix: [[T; N]; 2]) -> list<T> {
    append(Array_elems(head(Array_elems(matrix))),
        Array_elems(head(tail(Array_elems(matrix)))))
}

// Keep a fraction while changing representations so precision relates the values.
lem pack_array<T, N>(p: *[T; N])
    req (p as *T)[..usize_of_const(typeid(N))] |-> ?elems;
    ens *p |-> ?array &*& Array_elems(array) == elems;
{
    split_fraction array(p as *T, usize_of_const(typeid(N)), elems) by 1/2;
    array_to_Array(p);
    Array_to_array(p);
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

@*/
