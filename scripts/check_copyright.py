#!/usr/bin/env python3
"""Check that Lean files start with a copyright header.

    scripts/check_copyright.py --base <git-ref>   files added or modified since <ref> (PR check)
    scripts/check_copyright.py [--fix] FILE...    the given files

A file passes if it starts with the standard Meta header (exactly) or with a block comment that
names another copyright holder and a license, as kept on code copied from another project such as
Formal Conjectures (Apache 2.0). `--fix` prepends the Meta header to files that have neither.
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

META = """/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
"""
LEADING_BLOCK = re.compile(r"/-(?![-!]).*?-/", re.S)


def problem(text: str) -> str | None:
    if text.startswith(META):
        return None
    block = LEADING_BLOCK.match(text)
    if block is None:
        return "missing copyright header"
    if "Meta Platforms" in block.group(0):
        return "Meta copyright header differs from the standard text"
    if "Copyright" in block.group(0) and re.search(r"[Ll]icen[cs]e", block.group(0)):
        return None
    return "leading comment is not a copyright header"


def changed_files(base: str) -> list[str]:
    out = subprocess.run(["git", "diff", "--name-only", "--diff-filter=AMR", f"{base}...HEAD", "--", "*.lean"],
                         check=True, capture_output=True, text=True).stdout
    return [f for f in out.splitlines() if f and Path(f).is_file()]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--base", help="check .lean files added or modified since this git ref")
    ap.add_argument("--fix", action="store_true", help="prepend the Meta header to files without any header")
    ap.add_argument("files", nargs="*")
    a = ap.parse_args()
    files = changed_files(a.base) if a.base else a.files
    failures = 0
    for f in files:
        text = Path(f).read_text(encoding="utf-8")
        why = problem(text)
        if why == "missing copyright header" and a.fix:
            Path(f).write_text(META + "\n" + text.lstrip("\n"), encoding="utf-8")
            continue
        if why:
            print(f"FAIL [copyright]: {f}: {why}", file=sys.stderr)
            failures += 1
    if not failures:
        print(f"ok [copyright]: {len(files)} file(s) checked.")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
