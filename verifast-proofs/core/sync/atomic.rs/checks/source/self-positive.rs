struct A { value: u8 }
struct B { value: u16 }
struct Wrap<T> { value: T }
impl A {
    unsafe fn check_self()
    //@ req true;
    //@ ens typeid(Self) == typeid(A);
    //@ on_unwind_ens false;
    {}
}
impl B {
    unsafe fn check_self()
    //@ req true;
    //@ ens typeid(Self) == typeid(B);
    //@ on_unwind_ens false;
    {}
}
impl<T> Wrap<T> {
    unsafe fn check_self()
    //@ req true;
    //@ ens typeid(Self) == typeid(Wrap<T>);
    //@ on_unwind_ens false;
    {}
}
