// ===== BEGIN TRUSTED FREEZE SMALL SORT WRAPPER =====
//
// Only in targets/unstable_small_sort/specialized (checked by verify.sh). The `T: FreezeMarker` impl of
// `UnstableSmallSortTypeImpl::small_sort` calls `<T as UnstableSmallSortFreezeTypeImpl>::small_sort`
// for a generic `T`; VeriFast 26.10 would need a spec on the safe trait method declaration, which it
// does not support. The call goes through this wrapper instead; its body is exactly the original call
// (checked by refinement-checker). Its spec is assumed (`assume_correct`), not proven here. It is
// exactly the spec that both impls of `UnstableSmallSortFreezeTypeImpl::small_sort` carry and are
// verified against in their own crates, targets/unstable_freeze_small_sort/{default,copy} (verify.sh
// checks that the three spec texts are identical). See README.md, "Trusted base".
fn unstable_small_sort_freeze_type_impl_small_sort__VeriFast_wrapper<T: FreezeMarker, F: FnMut(&T, &T) -> bool>(v: &mut [T], is_less: &mut F)
/*@
req thread_token(?t) &*& t == currentThread &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs) &*& foreach(vs, own::<T>(t)) &*&
    *is_less |-> ?f0 &*& <F>.own(t, f0);
@*/
/*@
ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1) &*&
    if is_less_models::<T, F>(f0) {
        is_perm(vs1, vs) && sorted_by(is_less_model_of::<T, F>(f0), vs1)
    } else {
        true
    };
@*/
/*@
on_unwind_ens thread_token(t) &*&
    array::<T>(strip_pointer_metadata(v as pointer) as *T, v.len(), ?vs1) &*& foreach(vs1, own::<T>(t)) &*&
    *is_less |-> ?f1 &*& <F>.own(t, f1);
@*/
//@ assume_correct
{
    <T as UnstableSmallSortFreezeTypeImpl>::small_sort(v, is_less)
}
// ===== END TRUSTED FREEZE SMALL SORT WRAPPER =====
