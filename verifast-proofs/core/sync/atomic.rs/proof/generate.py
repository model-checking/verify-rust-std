from pathlib import Path
import importlib.util

base = Path(__file__).resolve().parent
(base / 'verified').mkdir(exist_ok=True)
repository = next(p for p in base.parents if (p / 'library/core/src/sync/atomic.rs').is_file())
import json
import hashlib
lock = json.loads((base.parent / 'source-lock.json').read_text())
for name, digest in lock['sources'].items():
    assert hashlib.sha256((repository / name).read_bytes()).hexdigest() == digest, f'Source changed; review and update the proof: {name}'
source = (repository / 'library/core/src/sync/atomic.rs').read_text()
(base / 'original').mkdir(exist_ok=True)
(base / 'original/atomic.rs').write_text(source)
(base / 'original/lib.rs').write_text((base / 'templates/lib.rs').read_text())
normalized = source.replace('rustc_diagnostic_item = ', 'doc = ')
original = base / 'normalized-original'
original.mkdir(exist_ok=True)
(original / 'atomic.rs').write_text(normalized)
(original / 'lib.rs').write_text((base / 'original/lib.rs').read_text())

ghost_template = (base / 'templates/integer-share.rs').read_text()
ghosts = []
for t, atomic in [('i8','AtomicI8'),('u8','AtomicU8'),('i16','AtomicI16'),('u16','AtomicU16'),('i32','AtomicI32'),('u32','AtomicU32'),('i64','AtomicI64'),('u64','AtomicU64'),('i128','AtomicI128'),('u128','AtomicU128'),('isize','AtomicIsize'),('usize','AtomicUsize')]:
    block = ghost_template.replace('AtomicU8',atomic).replace('u8',t).replace('own_atomic_contents','own_atomic_contents_'+t)
    block = block.replace('    div_rem(l as usize, 1);', "    close_points_to(l);\n    to_u8s_(l);\n    from_u8s_(l);\n    open_points_to(l);")
    ghosts.append(block)
bool_ghost = ghost_template.replace('AtomicU8','AtomicBool').replace('accepts_u8','accepts_bool_byte').replace('own_atomic_contents','own_atomic_bool_contents')
bool_ghost = bool_ghost.replace('fix accepts_bool_byte(value: u8) -> bool { true }', 'fix accepts_bool_byte(value: u8) -> bool { value == 0 || value == 1 }')
bool_ghost = bool_ghost.replace('pred <AtomicBool>.own(t, value) = true;', 'pred <AtomicBool>.own(t, value) = value.v == 0 || value.v == 1;')
ghosts.append(bool_ghost)
ghosts.append((base / 'templates/atomic-ptr-share.rs').read_text())
ghost = '\n\n'.join(ghosts)
attributes = '''            #[inline]
            #[stable(feature = "atomic_from_ptr", since = "1.75.0")]
            #[rustc_const_stable(feature = "const_atomic_from_ptr", since = "1.84.0")]
'''
old = attributes + '''            pub const unsafe fn from_ptr<'a>(ptr: *mut $int_type) -> &'a $atomic_type {
                // SAFETY: guaranteed by the caller
                unsafe { &*ptr.cast() }
            }'''
assert normalized.count(old) == 1
method = (base / 'templates/from-ptr.rs').read_text()
verified = normalized.replace(old, attributes + method)
bool_original = """    pub const unsafe fn from_ptr<'a>(ptr: *mut bool) -> &'a AtomicBool {
        // SAFETY: guaranteed by the caller
        unsafe { &*ptr.cast() }
    }"""
bool_method = method.replace("ptr: *mut $int_type) -> &'a $atomic_type", "ptr: *mut bool) -> &'a AtomicBool")
bool_method = bool_method.replace('                    close_points_to(ptr as *Self);', '                    points_to_bool_to_u8(ptr);\n                    close_points_to(ptr as *Self);')
assert verified.count(bool_original) == 1
verified = verified.replace(bool_original, bool_method)
ptr_original = """    pub const unsafe fn from_ptr<'a>(ptr: *mut *mut T) -> &'a AtomicPtr<T> {
        // SAFETY: guaranteed by the caller
        unsafe { &*ptr.cast() }
    }"""
ptr_method = method.replace("ptr: *mut $int_type) -> &'a $atomic_type", "ptr: *mut *mut T) -> &'a AtomicPtr<T>")
ptr_method = ptr_method.replace('type_interp::<Self>()', 'type_interp::<T>() &*& type_interp::<Self>()')
assert verified.count(ptr_original) == 1
verified = verified.replace(ptr_original, ptr_method)

anchor = '#[cfg(target_has_atomic_load_store)]\nmacro_rules! atomic_int {'
assert verified.count(anchor) == 1
verified = verified.replace(anchor, ghost + '\n\n' + anchor)
module_spec = importlib.util.spec_from_file_location('atomic_operation_annotations', base.parent / 'checks/operations/annotate.py')
operation_annotations = importlib.util.module_from_spec(module_spec)
module_spec.loader.exec_module(operation_annotations)
verified = operation_annotations.annotate(verified)
(base / 'verified/atomic.rs').write_text(verified)
(base / 'verified/lib.rs').write_text((base / 'original/lib.rs').read_text())
clients_root = (base / 'original/lib.rs').read_text().replace('pub mod atomic;', '#[path="verified/atomic.rs"]\npub mod atomic;\nmod clients;')
(base / 'clients-lib.rs').write_text(clients_root)
clients = 'use crate::atomic::*;\n\n'
for primitive, atomic, name in [('bool','AtomicBool','bool'), ('*mut T','AtomicPtr<T>','ptr'), *[(t,'Atomic'+a,t) for t,a in [('i8','I8'),('u8','U8'),('i16','I16'),('u16','U16'),('i32','I32'),('u32','U32'),('i64','I64'),('u64','U64'),('i128','I128'),('u128','U128'),('isize','Isize'),('usize','Usize')]]]:
    generics = "<'a, T>" if name == 'ptr' else "<'a>"
    interp = f'type_interp::<{atomic}>() &*& ' + ('type_interp::<T>() &*& ' if name == 'ptr' else '')
    constructor = 'AtomicPtr::<T>' if name == 'ptr' else atomic
    call_args = "T, 'a" if name == 'ptr' else "'a"
    clients += f'''unsafe fn alias_{name}{generics}(ptr: *mut {primitive}) -> (&'a {atomic}, &'a {atomic})
//@ req {interp}atomic_mask(MaskTop) &*& [?q]lifetime_token('a) &*& *ptr |-> ?value &*& ptr as usize % std::mem::align_of::<{atomic}>() == 0;
//@ ens {interp}atomic_mask(MaskTop) &*& [q]lifetime_token('a) &*& [_](<{atomic}>.share)('a, currentThread, result.0) &*& [_](<{atomic}>.share)('a, currentThread, result.1) &*& borrow_end_token('a, (<{atomic}>.full_borrow_content)(currentThread, ptr as *{atomic}));
//@ on_unwind_ens false;
{{
    //@ close exists::<bool>(true);
    let first = unsafe {{ {constructor}::from_ptr/*@::<{call_args}>@*/(ptr) }};
    //@ close exists::<bool>(false);
    let second = unsafe {{ {constructor}::from_ptr/*@::<{call_args}>@*/(ptr) }};
    (first, second)
}}

'''
import re
clients = '\n'.join(re.sub(r'\bAtomic(?=[A-Z])', 'atomic::Atomic', line) if line.startswith('//@') else line for line in clients.splitlines()) + '\n'
(base / 'clients.rs').write_text(clients)
first_client = clients[:clients.index('unsafe fn alias_ptr')]
negative_clients = {
    'double-fresh': first_client.replace('close exists::<bool>(false)', 'close exists::<bool>(true)'),
    'shared-without-permission': first_client.replace('close exists::<bool>(true)', 'close exists::<bool>(false)'),
    'uninitialized': first_client.replace(' &*& *ptr |-> ?value', ''),
}
for name, client_source in negative_clients.items():
    (base / f'clients-{name}.rs').write_text(client_source)
    (base / f'clients-{name}-lib.rs').write_text(clients_root.replace('mod clients;', f'#[path="clients-{name}.rs"]\nmod clients;'))
print('Generated experimental normalized-original and Self-annotated verified copies.')
