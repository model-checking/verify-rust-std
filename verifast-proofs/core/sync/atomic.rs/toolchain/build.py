#!/usr/bin/env python3
"""Rebuild the experimental atomic verifier from pinned release inputs.

The source and dependency trees are freshly extracted. No previous verifier
binary is used except for unchanged runtime resources from the verified release.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import shlex
import shutil
import subprocess
import tarfile

parser = argparse.ArgumentParser()
parser.add_argument('--workdir', type=Path, required=True)
parser.add_argument('--downloads', type=Path, required=True)
parser.add_argument('--cargo-home', type=Path)
parser.add_argument('--offline', action='store_true')
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
base = Path(__file__).resolve().parent
repo = next(p for p in base.parents if (p / 'library/core/src/sync/atomic.rs').is_file())
provenance = json.loads((base / 'provenance.json').read_text())
if platform.system() != 'Darwin' or platform.machine() != 'arm64':
    raise SystemExit('This complete-type proof build requires native ARM64 macOS.')
work = args.workdir.resolve()
if work.exists():
    raise SystemExit(f'Refusing to reuse a previous build tree: {work}')
work.mkdir(parents=True)
downloads = args.downloads.resolve()
downloads.mkdir(parents=True, exist_ok=True)

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()

def run(command, *, cwd=repo, env=None, log=None):
    print('+ ' + shlex.join(map(str, command)), flush=True)
    if log:
        with (work / log).open('w') as output:
            subprocess.run(list(map(str, command)), cwd=cwd, env=env, stdout=output, stderr=subprocess.STDOUT, check=True)
    else:
        subprocess.run(list(map(str, command)), cwd=cwd, env=env, check=True)

inputs = [
    ('verifast-source-26.01.tar.gz', 'https://api.github.com/repos/verifast/verifast/tarball/26.01', provenance['source_archive_sha256']),
    ('vfdeps-adf88dc-macos-aarch64.txz', 'https://github.com/verifast/vfdeps/releases/download/25.01/vfdeps-adf88dc-macos-aarch64.txz', provenance['vfdeps_archive_sha256']),
    ('verifast-26.01-macos-aarch.tar.gz', 'https://github.com/verifast/verifast/releases/download/26.01/verifast-26.01-macos-aarch.tar.gz', 'f316062f224b51f0956bf7375f34089558f4847671ef60e13899da6e079caf00'),
]
for name, url, digest in inputs:
    archive = downloads / name
    if not archive.exists():
        if args.offline:
            raise SystemExit(f'Missing offline input: {archive}')
        run(['curl','--fail','--location','--retry','3','--output',archive,url])
    if sha(archive) != digest:
        raise SystemExit(f'Archive digest mismatch: {archive}')
    print(f'Extracting verified {name}', flush=True)
    with tarfile.open(archive) as packed:
        # All release links are relative. The data filter rejects extraction
        # outside this fresh build directory and disallows special files.
        packed.extractall(work, filter='data')

source = work / provenance['source_archive_prefix']
deps = work / 'vfdeps-adf88dc'
runtime = work / 'verifast-26.01'
patch = base / 'verifast-26.01-atomic-source.patch'
if sha(patch) != provenance['source_patch_sha256']:
    raise SystemExit('Patch digest does not match its provenance record.')
run(['git','apply','--check',patch], cwd=source)
run(['git','apply',patch], cwd=source)

env = os.environ.copy()
cargo_home = (args.cargo_home or (work / 'cargo-home')).resolve()
decoder = work / 'decoder'
env.update({
    'CARGO_HOME': str(cargo_home),
    'PATH': os.pathsep.join([str(deps / 'bin'), str(decoder / 'bin'), env['PATH']]),
    'OCAMLLIB': str(deps / 'lib/ocaml'),
    'OCAMLPATH': str(deps / 'lib/ocaml'),
    'OCAMLFIND_CONF': str(deps / 'etc/findlib-relocated.conf'),
    'CAML_LD_LIBRARY_PATH': str(deps / 'lib/ocaml/stublibs'),
    'DYLD_LIBRARY_PATH': str(deps / 'lib'),
    'CAPNP_INCLUDE': str(deps / 'include'),
    'CAPNP_INC_DIR': str(deps / 'include'),
    'Z3_DLL_DIR': str(deps / 'lib'),
})
(deps / 'etc/findlib-relocated.conf').write_text(
    f'destdir="{deps / "lib/ocaml"}"\npath="{deps / "lib/ocaml"}"\n'
    'ocamlc="ocamlc.opt"\nocamlopt="ocamlopt.opt"\nocamldep="ocamldep.opt"\nocamldoc="ocamldoc.opt"\n')
rust = provenance['rust']
run(['rustc','+' + rust,'--version'], env=env)
offline = ['--offline'] if args.offline else []
run(['cargo','+' + rust,'install','--locked','--git','https://github.com/btj/capnpc-ocaml-decoder',
     '--rev',provenance['decoder_utility_commit'],'--root',decoder,*offline], env=env, log='decoder-build.log')
run(['cargo','+' + rust,'build','--release','--locked',*offline,'--manifest-path',
     source / 'src/rust_frontend/vf_mir_exporter/Cargo.toml'], env=env, log='exporter-build.log')
run(['dune','build','vfconsole/vfconsole.exe','refinement_checker/main.exe'], cwd=source / 'src', env=env, log='verifier-build.log')

stage = [
    ('src/_build/default/vfconsole/vfconsole.exe','bin/verifast'),
    ('src/_build/default/refinement_checker/main.exe','bin/refinement-checker'),
    ('src/rust_frontend/vf_mir_exporter/target/release/vf_mir_exporter','bin/vf-rust-mir-exporter'),
    ('bin/rust/std/lib.rsspec','bin/rust/std/lib.rsspec'),
]
for source_name, destination_name in stage:
    destination = runtime / destination_name
    destination.unlink()
    shutil.copy2(source / source_name, destination)
(runtime / 'bin/VERSION').write_text('26.01-local-atomic-source\n26.01 + LOCAL atomic-source probe (unsubmitted experimental patch)\n')

# This wrapper is portable between checkouts: only generated output contains
# absolute relocation paths. It does not replace the user's global toolchain.
wrapper = work / 'with-build-env'
keys = ['CARGO_HOME','PATH','OCAMLLIB','OCAMLPATH','OCAMLFIND_CONF','CAML_LD_LIBRARY_PATH',
        'DYLD_LIBRARY_PATH','CAPNP_INCLUDE','CAPNP_INC_DIR','Z3_DLL_DIR']
wrapper.write_text('#!/bin/sh\nset -eu\n' + ''.join('export ' + key + '=' + shlex.quote(env[key]) + '\n' for key in keys) + 'exec "$@"\n')
wrapper.chmod(0o755)

if args.check:
    run(['python3',base.parent / 'check.py',runtime / 'bin'], env=env, log='proof-suite.log')
manifest = {
    'approved_release': False,
    'fresh_source_build': True,
    'rust': rust,
    'platform': platform.platform(),
    'input_archives': {name: digest for name, _, digest in inputs},
    'patch_sha256': sha(patch),
    'decoder_revision': provenance['decoder_utility_commit'],
    'patched_sources': {name: sha(source / name) for name in provenance['modified_files']},
    'staged_outputs': {destination: sha(runtime / destination) for _, destination in stage},
    'proof_suite_passed': args.check,
    'runtime': str(runtime),
}
(work / 'build-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'PASS: fresh build{" and proof suite" if args.check else ""}; manifest: {work / "build-manifest.json"}', flush=True)
