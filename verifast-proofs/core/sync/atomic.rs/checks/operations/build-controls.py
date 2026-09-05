"""Generate concrete, independent callers and deliberately invalid calls."""
from pathlib import Path
base = Path(__file__).resolve().parent
header = '#![feature(core_intrinsics)]\n#![allow(internal_features)]\n/*@\nfix accepts<T>(value: T) -> bool { true }\nfix bool_byte(value: u8) -> bool { value == 0 || value == 1 }\n@*/\n'
q = 'std::intrinsics::'
orders = ['Relaxed','Release','Acquire','AcqRel','SeqCst']
rmw = {'xadd':'Add','xsub':'Sub','and':'And','nand':'Nand','or':'Or','xor':'Xor'}

def witness(ty, op, val='val', second=None):
    second = second or ty
    return f'''    /*@
    produce_lem_ptr_chunk {q}atomic_rmw_preserves<{ty}, {second}>(typeid({ty}), typeid({second}), {q}Rmw{rmw[op]}, accepts, {val})(old) {{
    }};
    @*/
    //@ leak {q}is_atomic_rmw_preserves::<{ty}, {second}>(_, typeid({ty}), typeid({second}), {q}Rmw{rmw[op]}, accepts, {val});
'''

matrix = header
names = []
for op in ['store','load','xchg','cxchg','cxchgweak', *rmw, 'max','min','umax','umin']:
    ty = 'i8' if op in ['max','min'] else 'u8'
    primary = ['Relaxed','Release','SeqCst'] if op == 'store' else ['Relaxed','Acquire','SeqCst'] if op == 'load' else orders
    for order in primary:
        for failure in (['Relaxed','Acquire','SeqCst'] if op in ['cxchg','cxchgweak'] else [None]):
            name = op + '_' + order.lower() + ('_' + failure.lower() if failure else '')
            names.append(name)
            ty_args = ty + (', ' + ty if op in rmw else '')
            ty_args += ', {' + q + 'AtomicOrdering::' + order + '}'
            if failure:
                ty_args += ', {' + q + 'AtomicOrdering::' + failure + '}'
            call_args = 'dst' if op == 'load' else 'dst, val, val' if failure else 'dst, val'
            result = '' if op == 'store' else f' -> ({ty}, bool)' if failure else ' -> ' + ty
            ptr = '*const' if op == 'load' else '*mut'
            fraction = '?g' if op == 'load' else '1'
            matrix += f'''\nunsafe fn {name}(dst: {ptr} {ty}, val: {ty}){result}
//@ req [?f]{q}atomic_points_to(dst, {fraction}, accepts);
//@ ens [f]{q}atomic_points_to(dst, {'g' if op == 'load' else '1'}, accepts);
//@ on_unwind_ens false;
{{
'''
            if op in rmw:
                matrix += witness(ty, op)
            matrix += f'    unsafe {{ {q}atomic_{op}::<{ty_args}>({call_args}) }}\n}}\n'
assert len(names) == 91
(base / 'ordering-matrix.rs').write_text(matrix)

types = header
for ty in ['i8','u8','i16','u16','i32','u32','i64','u64','i128','u128','isize','usize']:
    types += f'''\nunsafe fn domain_{ty}(dst: *mut {ty}, val: {ty}) -> {ty}
//@ req [?f]{q}atomic_points_to(dst, 1, accepts);
//@ ens [f]{q}atomic_points_to(dst, 1, accepts);
//@ on_unwind_ens false;
{{
''' + witness(ty,'xadd') + f'''    unsafe {{
        {q}atomic_store::<{ty}, {{{q}AtomicOrdering::Relaxed}}>(dst, val);
        {q}atomic_xadd::<{ty}, {ty}, {{{q}AtomicOrdering::SeqCst}}>(dst, val)
    }}
}}
'''
for size in range(5):
    ty = f'*mut [u8; {size}]'
    types += f'''\nunsafe fn pointer_size_{size}(dst: *mut {ty}, val: usize, new: {ty}) -> {ty}
//@ req [?f]{q}atomic_points_to(dst, 1, accepts);
//@ ens [f]{q}atomic_points_to(dst, 1, accepts);
//@ on_unwind_ens false;
{{
    //@ {q}atomic_domain_ptr::<[u8; {size}]>();
''' + witness(ty,'xadd',second='usize') + f'''    unsafe {{
        {q}atomic_store::<{ty}, {{{q}AtomicOrdering::Relaxed}}>(dst, new);
        {q}atomic_xadd::<{ty}, usize, {{{q}AtomicOrdering::SeqCst}}>(dst, val)
    }}
}}
'''
(base / 'type-domains.rs').write_text(types)

def negative(name, ty='u8', update=None, op='store', order='Relaxed', failure=None,
             pre=None, post=None, ghost='', generic=''):
    update = update or ty
    if pre is None:
        pre = f'[?f]{q}atomic_points_to(dst, 1, accepts)'
    if post is None:
        post = f'[f]{q}atomic_points_to(dst, 1, accepts)'
    type_args = ty + (', ' + update if op in rmw else '')
    type_args += ', {' + q + 'AtomicOrdering::' + order + '}'
    if failure:
        type_args += ', {' + q + 'AtomicOrdering::' + failure + '}'
    call_args = 'dst' if op == 'load' else 'dst, val, val' if failure else 'dst, val'
    code = f'''\nunsafe fn invalid{generic}(dst: *mut {ty}, val: {update})
//@ req {pre};
//@ ens {post};
//@ on_unwind_ens false;
{{
{ghost}    unsafe {{ {q}atomic_{op}::<{type_args}>({call_args}); }}
}}
'''
    (base / (name + '.rs')).write_text(header + code)

for name, ty in [('type-bool','bool'), ('type-float','f32'), ('type-tuple','(u8,u8)'), ('type-fat-pointer','*mut [u8]')]:
    negative(name, ty)
negative('missing-domain', 'T', generic='<T: Copy>')
negative('missing-resource', pre='true', post='true')
negative('ordinary-resource', pre='*dst |-> ?old', post='*dst |-> _')
negative('fractional-write', pre=f'{q}atomic_points_to(dst, 1/2, accepts)', post=f'{q}atomic_points_to(dst, 1/2, accepts)')
negative('missing-closure', op='xadd')
negative('wrong-closure-op', op='xadd', ghost=witness('u8','xsub'))
negative('wrong-closure-type', op='xadd', ghost=witness('u16','xadd',val='0'))
negative('mismatched-integers', ty='u8', update='u16', op='xadd')
negative('pointer-update-type', ty='*mut u8', update='u8', op='xadd')
negative('signed-max-unsigned', op='max')
negative('unsigned-min-signed', ty='i8', op='umin')
negative('store-acquire', order='Acquire')
negative('store-acqrel', order='AcqRel')
negative('load-release', op='load', order='Release')
negative('load-acqrel', op='load', order='AcqRel')
negative('cxchg-failure-release', op='cxchg', failure='Release')
negative('cxchgweak-failure-acqrel', op='cxchgweak', failure='AcqRel')
negative('invalid-bool-store', pre=f'[?f]{q}atomic_points_to(dst, 1, bool_byte) &*& val == 2', post=f'[f]{q}atomic_points_to(dst, 1, bool_byte)')
negative('invalid-bool-cxchg', op='cxchg', failure='Relaxed', pre=f'[?f]{q}atomic_points_to(dst, 1, bool_byte) &*& val == 2', post=f'[f]{q}atomic_points_to(dst, 1, bool_byte)')

positive = (base / 'positive.rs').read_text()
boolean = positive[positive.index('unsafe fn bool_and'):positive.index('unsafe fn bool_or')]
(base / 'bool-nand-rejected.rs').write_text(header + boolean.replace('bool_and','bool_nand').replace('RmwAnd','RmwNand').replace('bytes_and','bytes_nand').replace('atomic_and','atomic_nand'))
(base / 'bool-add-rejected.rs').write_text(header + boolean.replace('bool_and','bool_add').replace('RmwAnd','RmwAdd').replace('atomic_rmw_bool_bytes_and','atomic_rmw_u8_add').replace('atomic_and','atomic_xadd'))
print('Generated 91 ordering callers, 12 integer/5 pointer domain callers, and 25 rejection cases.')
