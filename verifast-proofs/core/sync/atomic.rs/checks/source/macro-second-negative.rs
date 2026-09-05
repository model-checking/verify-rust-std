macro_rules! must_return_one {
    ($name:ident, $value:expr) => {
        unsafe fn $name() -> u8
        //@ req true;
        //@ ens result == 1;
        //@ on_unwind_ens false;
        { $value }
    }
}
must_return_one!(first_passes, 1);
must_return_one!(second_must_fail, 2);
