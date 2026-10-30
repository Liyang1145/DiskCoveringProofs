#!/usr/bin/env python3
"""Restore one hash-checked EnergyRefine module from the archive branch."""
import argparse
import hashlib
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BRANCH = "origin/ci/n11-build"
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("node", type=int)
    args = ap.parse_args()
    rel = f"ci-n11/drafts/energy/N11Formalization/EnergyRefineN{args.node:04d}.lean"
    source = subprocess.check_output(
        ["git", "show", f"{BRANCH}:{rel}"], text=True, cwd=ROOT)
    if FORBIDDEN.search(source):
        raise SystemExit("refusing archive source with forbidden tokens")
    expected = f"N11Formalization.EnergyRefineN{args.node:04d}"
    if source.count(expected) != 3 or f"{args.node:04d}" not in rel:
        raise SystemExit("archive source has unexpected namespace/count")
    out = (ROOT / "n11-work/lean/N11Formalization" /
           f"EnergyRefineN{args.node:04d}.lean")
    if out.exists():
        raise SystemExit(f"refusing to overwrite {out}")
    out.write_text(source, encoding="utf-8")
    print(out)
    print("archive", rel)
    print("sha256", hashlib.sha256(out.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
