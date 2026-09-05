/*@
lem unsized_pointer_domain()
    req true;
    ens std::intrinsics::atomic_type::<*[u8]>() == true;
{
    std::intrinsics::atomic_domain_ptr::<[u8]>();
}
@*/
