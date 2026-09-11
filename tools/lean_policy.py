#!/usr/bin/env python3
"""Reject Lean sources that contain constructs weakening kernel verification.

Scans every .lean file under lean/ (excluding .lake/) with comments and string
literals removed, and fails if any forbidden construct appears. See
CONTRIBUTING.md section 3.
"""
from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "lean"

FORBIDDEN = [
    (re.compile(r"\bsorry\b"), "sorry"),
    (re.compile(r"\badmit\b"), "admit"),
    (re.compile(r"(^|\s)axiom\s"), "axiom declaration"),
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"\bimplemented_by\b"), "implemented_by"),
    (re.compile(r"@\[\s*extern\b"), "@[extern]"),
    (re.compile(r"\bunsafe\b"), "unsafe"),
    (re.compile(r"\bskipKernelTC\b"), "debug.skipKernelTC"),
    (re.compile(r"\bdebug\.\w+"), "debug.* option"),
    (re.compile(r"(^|\s)opaque\s"), "opaque constant"),
    (re.compile(r"\bofReduceBool\b"), "Lean.ofReduceBool"),
]


def strip_comments_and_strings(src: str) -> str:
    """Replace comments and string literals by spaces, preserving newlines."""
    out = []
    i, n, depth = 0, len(src), 0
    in_line = in_str = False
    while i < n:
        c = src[i]
        two = src[i : i + 2]
        if in_line:
            if c == "\n":
                in_line = False
                out.append(c)
            else:
                out.append(" ")
            i += 1
        elif depth > 0:
            if two == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif two == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_str:
            if c == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            else:
                if c == '"':
                    in_str = False
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif two == "--":
            in_line = True
            out.append("  ")
            i += 2
        elif two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif c == '"' and not (i > 0 and src[i - 1] == "'"):
            in_str = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def main() -> int:
    files = sorted(p for p in LEAN_DIR.rglob("*.lean") if ".lake" not in p.parts)
    failures = []
    for path in files:
        text = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(text.splitlines(), 1):
            for pattern, label in FORBIDDEN:
                if pattern.search(line):
                    failures.append(f"{path.relative_to(ROOT)}:{lineno}: forbidden {label}")
    print(f"lean_policy: scanned {len(files)} files")
    if failures:
        print("\n".join(failures))
        print(f"lean_policy: FAIL ({len(failures)} violations)")
        return 1
    print("lean_policy: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
