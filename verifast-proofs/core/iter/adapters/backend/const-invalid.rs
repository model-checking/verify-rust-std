#![crate_type = "lib"]
#![crate_name = "const_invalid"]

struct Window<T, const N: usize> {
    values: [T; N],
}

fn width<T, const N: usize>(_: &Window<T, N>) -> usize
//@ req true;
//@ ens result == usize_of_const(typeid(N)) + 1;
//@ on_unwind_ens false;
{
    N
}
