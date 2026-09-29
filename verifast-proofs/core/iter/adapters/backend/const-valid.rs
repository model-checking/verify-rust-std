#![crate_type = "lib"]
#![crate_name = "const_valid"]

struct Window<T, const N: usize> {
    values: [T; N],
}

fn width<T, const N: usize>(_: &Window<T, N>) -> usize
//@ req true;
//@ ens result == usize_of_const(typeid(N));
//@ on_unwind_ens false;
{
    N
}
