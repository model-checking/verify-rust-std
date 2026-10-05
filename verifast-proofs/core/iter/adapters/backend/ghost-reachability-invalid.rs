#![crate_type = "lib"]
#![crate_name = "ghost_reachability_invalid"]

unsafe fn inconsistent_input(value: bool)
//@ req value == true &*& value == false;
//@ ens true;
//@ on_unwind_ens false;
{
    //@ assert true;
} //~allow_dead_code // Allow the return only; the ghost assertion must still fail reachability.
