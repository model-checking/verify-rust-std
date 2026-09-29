#!/usr/bin/env python3
"""Check proof inputs without invoking Rust, VeriFast, or a solver."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


PACKAGE = Path(__file__).resolve().parent
LIMIT = 1024 * 1024
PROJECTION_HEADER = "// Source projection checked by check_sources.py. Do not edit manually.\n\n"


def read_file(path):
    with path.open("rb") as source:
        data = source.read(LIMIT + 1)
    if len(data) > LIMIT:
        raise ValueError(f"input exceeds {LIMIT} bytes: {path}")
    return data


def inside(root, relative):
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()):
        raise ValueError(f"path escapes its input directory: {relative}")
    return path


def project(data, ranges):
    lines = data.decode("utf-8").splitlines(keepends=True)
    parts = []
    previous = 0
    for start, end in ranges:
        if not 1 <= start <= end <= len(lines) or start <= previous:
            raise ValueError(f"invalid or overlapping source range: {start}:{end}")
        parts.append("".join(lines[start - 1:end]))
        previous = end
    return (PROJECTION_HEADER + "\n".join(parts)).encode("utf-8")


def mask_comments(text, annotations_only=False):
    """Select Rust text or VeriFast comments, preserving source offsets."""
    masked = ["\n" if char == "\n" else " " for char in text] if annotations_only else list(text)
    position = 0
    while position < len(text):
        if text.startswith("//", position):
            end = text.find("\n", position)
            end = len(text) if end == -1 else end
        elif text.startswith("/*", position):
            end = position + 2
            depth = 1
            while depth and end < len(text):
                if text.startswith("/*", end):
                    depth += 1
                    end += 2
                elif text.startswith("*/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            if depth:
                raise ValueError("unterminated Rust block comment")
        elif text[position] == '"':
            position += 1
            while position < len(text) and text[position] != '"':
                position += 2 if text[position] == "\\" else 1
            position += 1
            continue
        else:
            position += 1
            continue
        annotation = text.startswith(("//@", "/*@"), position)
        for offset in range(position, end):
            if annotations_only and annotation:
                masked[offset] = text[offset]
            elif not annotations_only and text[offset] != "\n":
                masked[offset] = " "
        position = end
    return "".join(masked)


def check_contracts(path, names):
    text = read_file(path).decode("utf-8")
    forbidden = (
        r"\bassume\s*\(",
        r"\breq\s+false\s*;",
        r"\b(?:allow_assume|ignore_unwind_paths|ignore_ref_creation|disable_overflow_check)\b",
        r"#\s*\[\s*cfg(?:_attr)?\s*\(",
    )
    if any(re.search(pattern, text) for pattern in forbidden):
        raise ValueError(f"verification bypass in {path}")
    rust = mask_comments(text)
    annotations = mask_comments(text, annotations_only=True)
    for name in names:
        matches = list(re.finditer(r"\bfn\s+" + re.escape(name) + r"\b", rust))
        if len(matches) != 1:
            raise ValueError(f"expected exactly one body for {name} in {path}")
        begin = matches[0].end()
        nesting = 0
        end = begin
        while end < len(rust):
            character = rust[end]
            if character in "([":
                nesting += 1
            elif character in ")]":
                nesting -= 1
            elif nesting == 0 and character in "{;":
                break
            end += 1
        if end == len(rust) or rust[end] != "{":
            raise ValueError(f"missing implementation for {name} in {path}")
        clauses = annotations[begin:end]
        for clause in ("req", "ens", "on_unwind_ens"):
            if not re.search(r"\b" + clause + r"\s", clauses):
                raise ValueError(f"missing {clause} for {name} in {path}")


def check(package=PACKAGE, repo=None, generate=False):
    repo = package.parents[3] if repo is None else repo
    manifest = json.loads(read_file(package / "source-map.json"))
    if manifest.get("version") != 1 or len(manifest.get("sources", [])) != 2:
        raise ValueError("unexpected source manifest")
    for entry in manifest["sources"]:
        snapshot = read_file(inside(package, entry["snapshot"]))
        if hashlib.sha256(snapshot).hexdigest() != entry["sha256"]:
            raise ValueError(f"snapshot hash changed: {entry['snapshot']}")
        if snapshot != read_file(inside(repo, entry["upstream"])):
            raise ValueError(f"std source differs from proof snapshot: {entry['upstream']}")
        expected = project(snapshot, entry["ranges"])
        original = inside(package, entry["projection"])
        if generate:
            original.parent.mkdir(parents=True, exist_ok=True)
            original.write_bytes(expected)
        elif read_file(original) != expected:
            raise ValueError(f"original projection differs from selected std source: {original}")
        if not generate:
            check_contracts(package / "verified" / original.name, entry["contracts"])
    if not generate:
        original_root = read_file(package / "original/lib.rs")
        if original_root != read_file(package / "verified/lib.rs"):
            raise ValueError("original and verified crate roots must match")
    return len(manifest["sources"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate-original", action="store_true",
                        help="regenerate projections from unchanged, hash-checked snapshots")
    args = parser.parse_args()
    try:
        count = check(generate=args.generate_original)
    except (OSError, UnicodeError, ValueError, KeyError, TypeError) as error:
        print(f"source check failed: {error}", file=sys.stderr)
        return 1
    action = "generated" if args.generate_original else "checked"
    print(f"{action} {count} source projections; no compiler or verifier was invoked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
