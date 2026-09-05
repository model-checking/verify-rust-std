"""Adversarial MIR decoder tests, NOT Rust proofs or a proof exporter.

Replay mutated copies of the real pinned exporter output through an isolated
runtime. The actual proof runtime and exporter are never modified.
"""
from pathlib import Path
import os
import subprocess
import sys

repo = next(p for p in Path(__file__).resolve().parents if (p / 'library/core/src/sync/atomic.rs').is_file())
base = Path(__file__).resolve().parent
runtime = base / 'replay-runtime'
fixtures = base / 'replay-fixtures'
runtime.mkdir(exist_ok=True)
fixtures.mkdir(exist_ok=True)
if len(sys.argv) != 3:
    raise SystemExit('usage: check.py /path/to/runtime/bin /path/to/vf_mir.capnp')
proof_bin = Path(sys.argv[1]).resolve()
for source in proof_bin.iterdir():
    target = runtime / source.name
    if source.name != 'vf-rust-mir-exporter' and not target.exists():
        target.symlink_to(source)
exporter = runtime / 'vf-rust-mir-exporter'
exporter.write_text('#!/bin/sh\nset -eu\ncat "$TF_REPLAY_CAPNP"\n')
exporter.chmod(0o755)

original = (base / 'original-mir.txt').read_text().replace('__ATOMIC_DECODER_FIXTURE__', str(base / 'intrinsic-gate.rs'))
leaf = '( leaf = (data = (h = 0, l = 0), size = 4) )'
branch = 'branch = [\n                                              ' + leaf + ' ]'
assert original.count(branch) == 1

def replace_once(old, new):
    assert original.count(old) == 1, (old, original.count(old))
    return original.replace(old, new)

def replace_value_with_param():
    start = original.index('value = (\n                                          ty = (')
    begin = original.index('(', start)
    depth = 1
    end = begin + 1
    while depth:
        depth += (original[end] == '(') - (original[end] == ')')
        end += 1
    return original[:start] + 'param = (index = 0, name = "ORD")' + original[end:]

malformed = 'expected a concrete fieldless AtomicOrdering enum constant'
cases = {
    'valid-relaxed': (original, 'No matching heap chunks:'),
    'valid-release': (replace_once(leaf, leaf.replace('l = 0', 'l = 1')), 'No matching heap chunks:'),
    'valid-seqcst': (replace_once(leaf, leaf.replace('l = 0', 'l = 4')), 'No matching heap chunks:'),
    'other-enum': (replace_once('std::intrinsics::AtomicOrdering', 'unrelated::AtomicOrdering'), malformed),
    'data-type-u16': (replace_once('type = (\n                                      kind = (uInt = (u8 = void)) )', 'type = (kind = (uInt = (u16 = void)))'), malformed),
    'data-type-tuple': (replace_once('type = (\n                                      kind = (uInt = (u8 = void)) )', 'type = (kind = (tuple = [(kind = (uInt = (u8 = void))), (kind = (uInt = (u8 = void)))]))'), malformed),
    'data-type-param': (replace_once('type = (\n                                      kind = (uInt = (u8 = void)) )', 'type = (kind = (param = "T"))'), malformed),
    'integer-instead-of-enum': (replace_once('ty = (\n                                            kind = (\n                                              adt = (\n                                                id = (\n                                                  name = \"std::intrinsics::AtomicOrdering\" ),\n                                                kind = (enumKind = void),\n                                                substs = [] ) ) )', 'ty = (kind = (uInt = (u32 = void)))'), malformed),
    'struct-kind': (replace_once('enumKind = void', 'structKind = void'), malformed),
    'union-kind': (replace_once('enumKind = void', 'unionKind = void'), malformed),
    'enum-has-type-args': (replace_once('substs = []', 'substs = [(kind = (type = (kind = (uInt = (u8 = void))))) ]'), malformed),
    'empty-branch': (replace_once(branch, 'branch = []'), malformed),
    'payload-branch': (replace_once(branch, 'branch = [' + leaf + ', ' + leaf + ']'), malformed),
    'bare-leaf': (replace_once(branch, 'leaf = (data = (h = 0, l = 0), size = 4)'), malformed),
    'scalar-width-0': (replace_once(leaf, leaf.replace('size = 4', 'size = 0')), malformed),
    'scalar-width-1': (replace_once(leaf, leaf.replace('size = 4', 'size = 1')), malformed),
    'scalar-width-8': (replace_once(leaf, leaf.replace('size = 4', 'size = 8')), malformed),
    'symbolic-param': (replace_value_with_param(), malformed),
    'late-bound-param': (replace_once('lateBoundGenericParamCount = 0', 'lateBoundGenericParamCount = 1'), 'late-bound generic arguments are not permitted'),
    'invalid-acquire': (replace_once(leaf, leaf.replace('l = 0', 'l = 2')), 'Acquire and AcqRel are not permitted for stores'),
    'invalid-acqrel': (replace_once(leaf, leaf.replace('l = 0', 'l = 3')), 'Acquire and AcqRel are not permitted for stores'),
    'index-5': (replace_once(leaf, leaf.replace('l = 0', 'l = 5')), 'invalid AtomicOrdering variant index'),
    'index-over-u32': (replace_once(leaf, leaf.replace('l = 0', 'l = 4294967296')), 'invalid AtomicOrdering variant index'),
    'index-high-u64': (replace_once(leaf, leaf.replace('h = 0', 'h = 1')), 'invalid AtomicOrdering variant index'),
    'other-function': (replace_once('std::intrinsics::atomic_store', 'unrelated::atomic_store'), 'Unsupported constant value tree'),
}
# The fixture's surrounding pointer type still says u8, so changing only
# the intrinsic type to u16 reaches argument type checking. It is not a proof.
cases['data-type-u16'] = (cases['data-type-u16'][0], 'Type mismatch')
cases['data-type-tuple'] = (cases['data-type-tuple'][0], 'operand must be an integer')
cases['data-type-param'] = (cases['data-type-param'][0], 'No such type parameter')
schema = Path(sys.argv[2]).resolve()
include = Path(os.environ['CAPNP_INC_DIR'])
summary = []
for name, (fixture, expected) in cases.items():
    text_file = fixtures / f'{name}.txt'
    binary_file = fixtures / f'{name}.bin'
    log_file = fixtures / f'{name}.log'
    text_file.write_text(fixture)
    binary = subprocess.run(['capnp', 'encode', '-I' + str(include), str(schema), 'VfMir'], input=fixture.encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
    binary_file.write_bytes(binary)
    env = dict(os.environ, TF_REPLAY_CAPNP=str(binary_file))
    result = subprocess.run([str(runtime / 'verifast'), '-rustc_args', '--edition=2024 --crate-type=lib', str(base / 'intrinsic-gate.rs')], cwd=repo, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=30)
    log_file.write_text('LOCALPATCH / MUTATED MIR REPLAY TEST ONLY\n' + result.stdout)
    ok = result.returncode != 0 and expected in result.stdout
    summary.append(f'{name}: {"PASS" if ok else "FAIL"} (exit {result.returncode}); expected {expected}')
    if not ok:
        print(result.stdout)
        raise RuntimeError(name)
(base / 'translator-mutations.log').write_text('LOCALPATCH / MUTATED MIR REPLAY TESTS ONLY\n' + '\n'.join(summary) + '\n')
print('\n'.join(summary))
