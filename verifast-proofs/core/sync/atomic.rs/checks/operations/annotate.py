"""Add contracts to the exact generic operation-wrapper signatures."""
OPS = ['store','load','swap','add','sub','compare_exchange','compare_exchange_weak',
       'and','nand','or','xor','max','min','umax','umin']
RMW = {'add':'Add','sub':'Sub','and':'And','nand':'Nand','or':'Or','xor':'Xor'}

def annotate(source):
    for op in OPS:
        name = 'atomic_' + op
        anchor = 'unsafe fn ' + name + '<'
        assert source.count(anchor) == 1, name
        start = source.index(anchor)
        body = source.index('{', start)
        q = 'std::intrinsics::'
        domain = q + (f'atomic_{"unsigned" if op.startswith("u") else "signed"}_type::<T>()' if op in ['max','min','umax','umin'] else 'atomic_rmw_types::<T, U>()' if op in RMW else 'atomic_type::<T>()')
        inner = '?g' if op == 'load' else '1'
        pre = f'{domain} == true &*& [?f]{q}atomic_points_to(dst, {inner}, ?inv_)'
        post = f'[f]{q}atomic_points_to(dst, {"g" if op == "load" else "1"}, inv_)'
        if op not in ['load', *RMW]:
            pre += ' &*& inv_(' + ('new' if op.startswith('compare_exchange') else 'val') + ') == true'
        if op in RMW:
            pre += f' &*& [_]{q}is_atomic_rmw_preserves::<T, U>(?preserves, typeid(T), typeid(U), {q}Rmw{RMW[op]}, inv_, val)'
        if op in ['store','load','compare_exchange','compare_exchange_weak']:
            pre = 'thread_token(?t) &*& ' + pre
            post = 'thread_token(t) &*& ' + post
        unwind = post if op in ['store','load','compare_exchange','compare_exchange_weak'] else 'false'
        if op != 'store':
            post += ' &*& match result { Result::Ok(v) => inv_(v) == true, Result::Err(v) => inv_(v) == true }' if op.startswith('compare_exchange') else ' &*& inv_(result) == true'
        contract = f'\n//@ req {pre};\n//@ ens {post};\n//@ on_unwind_ens {unwind};\n'
        source = source[:body].rstrip() + contract + source[body:]
    return source
