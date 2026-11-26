#!/usr/bin/env python3
"""Reject trust identifiers outside pattern/trusted.rs in a proof's source tree.

This lexical guard skips Rust comments, literals and exactly #[cfg(kani)] items
(Kani is disabled in this Verus run). It checks identifier references as well as
calls, so qualification, whitespace and import aliases cannot hide a direct use.
It does not expand macros or resolve external source.
"""

import argparse
from pathlib import Path
import re
import sys


TRUSTED_FILE = Path("pattern/trusted.rs")
FORBIDDEN = {
    "assume", "assume_", "admit", "axiom", "assume_specification",
    "external", "external_body", "external_fn_specification",
    "external_type_specification", "external_trait_specification",
}
IDENT = re.compile(r"(?:r#)?[^\W\d]\w*")
RAW_STRING = re.compile(r'(?:br|cr|r)(#*)"')
CHAR = re.compile(r"""(?:b)?'(?:[^\\'\r\n]|\\(?:['"nrt0\\]|x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\}))'""")
LIFETIME = re.compile(r"'[^\W\d]\w*")


class LexError(ValueError):
    def __init__(self, line, message):
        self.line = line
        super().__init__(message)


def tokens(source):
    """Yield (token, line), excluding comments, literals and lifetimes."""
    i, line = 0, 1
    while i < len(source):
        start = i
        if source.startswith("//", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source.startswith("/*", i):
            depth = 1
            i += 2
            while depth and i < len(source):
                if source.startswith("/*", i):
                    depth += 1
                    i += 2
                elif source.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise LexError(line, "unterminated block comment")
        elif (raw := RAW_STRING.match(source, i)):
            closing = '"' + raw.group(1)
            end = source.find(closing, raw.end())
            if end < 0:
                raise LexError(line, "unterminated raw string")
            i = end + len(closing)
        elif source[i] == '"' or source.startswith(('b"', 'c"'), i):
            i += 1 if source[i] == '"' else 2
            while i < len(source):
                if source[i] == '"':
                    i += 1
                    break
                i += 2 if source[i] == "\\" else 1
            else:
                raise LexError(line, "unterminated string")
        elif (char := CHAR.match(source, i)):
            i = char.end()
        elif (lifetime := LIFETIME.match(source, i)):
            i = lifetime.end()
        elif source[i] == "'":
            raise LexError(line, "invalid or unterminated character literal")
        elif (ident := IDENT.match(source, i)):
            name = ident.group()
            yield name[2:] if name.startswith("r#") else name, line
            i = ident.end()
        else:
            if not source[i].isspace():
                yield source[i], line
            i += 1
        line += source.count("\n", start, i)


DELIMITERS = {"(": ")", "[": "]", "{": "}"}
CFG_KANI = ["#", "[", "cfg", "(", "kani", ")", "]"]


def group_end(lexed, start):
    """Find the token after a balanced delimiter group."""
    stack = []
    for i in range(start, len(lexed)):
        token, line = lexed[i]
        if token in DELIMITERS:
            stack.append(DELIMITERS[token])
        elif token in DELIMITERS.values():
            if not stack or stack.pop() != token:
                raise LexError(line, "mismatched delimiter in cfg(kani) item")
            if not stack:
                return i + 1
    raise LexError(lexed[start][1], "unterminated delimiter in cfg(kani) item")


def identifiers(source):
    """Yield active identifier references; ignore exactly #[cfg(kani)] items."""
    lexed = list(tokens(source))
    i = 0
    while i < len(lexed):
        name, line = lexed[i]
        if [token for token, _ in lexed[i:i + len(CFG_KANI)]] == CFG_KANI:
            i += len(CFG_KANI)
            while i < len(lexed):
                token = lexed[i][0]
                if token in DELIMITERS:
                    i = group_end(lexed, i)
                    if token == "{":
                        break
                elif token == ";":
                    i += 1
                    break
                elif token in DELIMITERS.values():
                    raise LexError(lexed[i][1], "mismatched delimiter in cfg(kani) item")
                else:
                    i += 1
            else:
                raise LexError(line, "cfg(kani) attribute without a complete item")
            continue
        if IDENT.fullmatch(name):
            yield name, line
        i += 1


def check_tree(root):
    failed = False
    if not root.is_dir() or not (root / TRUSTED_FILE).is_file():
        print(f"{root}: expected a source directory containing {TRUSTED_FILE}", file=sys.stderr)
        return False
    for path in sorted(root.rglob("*.rs")):
        try:
            trusted = path.relative_to(root) == TRUSTED_FILE
            for name, line in identifiers(path.read_text(encoding="utf-8")):
                if not trusted and name in FORBIDDEN:
                    print(f"{path}:{line}: trust identifier `{name}` outside {TRUSTED_FILE}",
                          file=sys.stderr)
                    failed = True
        except LexError as error:
            print(f"{path}:{error.line}: {error}", file=sys.stderr)
            failed = True
        except (OSError, UnicodeError) as error:
            print(f"{path}: {error}", file=sys.stderr)
            failed = True
    return not failed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path, help="verified Rust source directory")
    args = parser.parse_args()
    if not check_tree(args.root):
        sys.exit(1)
    print(f"   trust identifiers confined to {TRUSTED_FILE}")


if __name__ == "__main__":
    main()
