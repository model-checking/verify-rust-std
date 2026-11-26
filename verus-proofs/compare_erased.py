#!/usr/bin/env python3
"""Check that a Verus-annotated crate, with its ghost code erased, is an original crate.

Usage:
  compare_erased.py --verus VERUS --original ORIG/lib.rs --verified VER/lib.rs
                    [--allow 'ATTR=COUNT' ...] [-- RUSTC_ARGS...]

Both crates are compiled with the rustc that Verus is built for, and their HIR
is printed (`-Zunpretty=hir`). The verified crate is compiled the way
`verus --compile` compiles it: without `--cfg verus_keep_ghost`, so Verus's
macros erase every spec, proof and `#[cfg(verus_keep_ghost)]` item, and with the
crate attributes and externs Verus adds (`rust_verify/src/config.rs`,
`rust_verify/src/externs.rs`).

The two HIR printouts must be identical after dropping comments, doc comments,
blank lines and source positions, except for:
  - the crate-level `#![..]` attributes, and
    `#[macro_use] extern crate verus_builtin_macros;` in the verified crate;
  - `#[verifier::ATTR]` attributes, which Verus's erasure keeps. Each one must
    be listed with `--allow 'ATTR=COUNT'` (for example
    `--allow 'loop_isolation(false)=2'`), and must occur exactly COUNT times.

Ghost code itself (`assume`, `admit`, proof blocks) is erased and so is not
compared here.
"""

import argparse
import difflib
import os
import re
import shutil
import subprocess
import sys
import tempfile

# Crate attributes and features that Verus adds when it runs rustc.
VERUS_FEATURES = [
    "stmt_expr_attributes", "box_patterns", "negative_impls", "rustc_attrs",
    "unboxed_closures", "register_tool", "tuple_trait", "custom_inner_attributes",
    "try_trait_v2",
]


def verus_rustc_args(root):
    args = ["-A", "unused_imports", "-A", "unused_mut",
            "-Zcrate-attr=allow(internal_features)", "-Zcrate-attr=allow(unused_features)"]
    args += [f"-Zcrate-attr=feature({f})" for f in VERUS_FEATURES]
    args += [f"-Zcrate-attr=register_tool({t})" for t in ("verus", "verifier", "verusfmt")]
    args += ["-L", f"dependency={root}",
             "--extern", f"verus_builtin={root}/libverus_builtin.rlib",
             "--extern", f"verus_builtin_macros={root}/libverus_builtin_macros.so",
             "--extern", f"vstd={root}/libvstd.rlib"]
    return args


def toolchain(verus):
    out = subprocess.run([verus, "--version"], capture_output=True, text=True, check=True).stdout
    m = re.search(r"Toolchain: (\S+)", out)
    if not m:
        sys.exit(f"cannot find the toolchain in `{verus} --version`")
    return m.group(1)


def hir(toolchain, crate_root, args):
    with tempfile.TemporaryDirectory() as tmp:
        cmd = ["rustc", f"+{toolchain}", "--edition", "2024", "--crate-type=lib",
               "-Zunpretty=hir", "--out-dir", tmp] + args + [os.path.basename(crate_root)]
        env = dict(os.environ, RUSTC_BOOTSTRAP="1")
        r = subprocess.run(cmd, cwd=os.path.dirname(os.path.abspath(crate_root)),
                           capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"failed to compile {crate_root}:\n{r.stderr}")
    return r.stdout


SPAN = re.compile(r"[\w./-]+\.rs:\d+:\d+: \d+:\d+ \(#\d+\)")


def normalize(text):
    """Drop comments, doc comments, blank lines and source positions, and the
    leading crate-level attributes (which may span several lines)."""
    lines = []
    for line in text.split("\n"):
        s = line.strip()
        if not s or s.startswith("//") or re.fullmatch(r'#!?\[doc = ".*"\]', s):
            continue
        lines.append(SPAN.sub("SPAN", line.rstrip()))
    i, depth = 0, 0
    while i < len(lines) and (depth > 0 or lines[i].startswith("#![")):
        depth += lines[i].count("[") - lines[i].count("]")
        i += 1
    return lines[i:]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--verus", required=True)
    ap.add_argument("--original", required=True)
    ap.add_argument("--verified", required=True)
    ap.add_argument("--allow", action="append", default=[])
    ap.add_argument("rustc_args", nargs="*")
    a = ap.parse_args()

    verus_path = shutil.which(a.verus)
    if verus_path is None:
        ap.error(f"cannot find Verus executable: {a.verus}")
    verus = os.path.realpath(verus_path)
    tc = toolchain(verus)
    original = normalize(hir(tc, a.original, a.rustc_args))
    verified = normalize(hir(tc, a.verified, a.rustc_args + verus_rustc_args(os.path.dirname(verus))))

    macro_use = ["#[attr = MacroUse {arguments: UseAll}]", "extern crate verus_builtin_macros;"]
    for k in range(len(verified) - 1):
        if verified[k:k + 2] == macro_use:
            del verified[k:k + 2]
            break

    allowed = {}
    for spec in a.allow:
        attr, count = spec.rsplit("=", 1)
        allowed[attr] = int(count)
    found, kept = {}, []
    ok = True
    for line in verified:
        m = re.fullmatch(r"\s*#\[verifier::(.*)\]", line)
        if m:
            found[m.group(1)] = found.get(m.group(1), 0) + 1
            if m.group(1) not in allowed:
                print(f"verified crate has `#[verifier::{m.group(1)}]`, which is not allowed")
                ok = False
            continue
        kept.append(line)
    for attr, count in allowed.items():
        if found.get(attr, 0) != count:
            print(f"expected {count} `#[verifier::{attr}]`, found {found.get(attr, 0)}")
            ok = False

    diff = list(difflib.unified_diff(original, kept, "original (HIR)", "verified, erased (HIR)",
                                     lineterm=""))
    if diff:
        print("\n".join(diff))
        ok = False
    if not ok:
        sys.exit(1)
    print(f"   same HIR ({len(original)} lines); Verus attributes left: "
          + ", ".join(f"{n} x #[verifier::{k}]" for k, n in sorted(found.items())))


if __name__ == "__main__":
    main()
