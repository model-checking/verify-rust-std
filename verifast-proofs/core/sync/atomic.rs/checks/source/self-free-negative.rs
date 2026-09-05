struct A { value: u8 }
impl A {
    unsafe fn check_self()
    //@ req true;
    //@ ens typeid(Self) == typeid(A);
    //@ on_unwind_ens false;
    {}
}
unsafe fn no_self_in_free_function()
//@ req true;
//@ ens typeid(Self) == typeid(A);
//@ on_unwind_ens false;
{}
