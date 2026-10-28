"""Append one root import block, hash-guarded and idempotent.

Usage: python patch_root.py <expect_sha|any> <import_module> <comment-file>
The comment text is read from a file so the audit trail stays byte-exact.
"""
from pathlib import Path
import hashlib
import sys

expect, module, comment_file = sys.argv[1], sys.argv[2], sys.argv[3]
root = Path(__file__).resolve().parents[2] / "lean" / "N11Formalization.lean"
text = root.read_text(encoding="utf-8")
sha = hashlib.sha256(root.read_bytes()).hexdigest().upper()
line = f"import {module}"

if line in text.splitlines():
    print("already imported; sha", sha)
    raise SystemExit(0)

assert expect == "any" or sha == expect, f"ROOT GUARD {sha} != {expect}"
assert text.endswith("\n"), "root does not end with newline"
comment = Path(comment_file).read_text(encoding="utf-8").rstrip("\n")
comment = "\n".join(l for l in comment.splitlines() if not l.startswith("import "))
new = text + "\n" + comment + "\n" + line + "\n"
root.write_text(new, encoding="utf-8", newline="\n")
print("patched ->", hashlib.sha256(root.read_bytes()).hexdigest().upper())
