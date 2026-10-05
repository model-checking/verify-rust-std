#![allow(dead_code)]

unsafe fn missing_send<T>()
//@ req type_interp::<T>() &*& <T>.own(?t0, ?value) &*& exists::<thread_id_t>(?t1);
//@ ens type_interp::<T>() &*& <T>.own(t1, value);
{
    //@ open exists::<thread_id_t>(t1);
    //@ Send::send::<T>(t0, t1, value);
}
