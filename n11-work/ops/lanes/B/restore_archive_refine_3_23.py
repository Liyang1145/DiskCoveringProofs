#!/usr/bin/env python3
"""Restore archived exact refinements for residual ids 3 and 23.

The archive sources contain one prohibited `set_option maxHeartbeats 0` each.
This exporter copies every other byte, removes only that directive, and writes
fresh lane-owned modules; it never edits the archived source.
"""
from __future__ import annotations

import hashlib
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUTDIR = ROOT / "n11-work" / "lean" / "N11Formalization"
BRANCH = "origin/ci/n11-build"
ARCHIVE = "ci-n11/drafts/energy/N11Formalization"
IDS = (3, 23)
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b")


def git_show(path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{BRANCH}:{path}"], cwd=ROOT)


def main() -> None:
    for node in IDS:
        archive = f"{ARCHIVE}/EnergyRefineN{node:04d}.lean"
        source = git_show(archive)
        directive = b"set_option maxHeartbeats 0\n"
        if source.count(directive) != 1:
            raise SystemExit(f"{archive}: expected exactly one unbounded heartbeat")
        restored = source.replace(directive, b"")
        text = restored.decode("utf-8")
        if FORBIDDEN.search(text):
            raise SystemExit(f"node {node}: another forbidden declaration remains")
        if f"namespace N11Formalization.EnergyRefineN{node:04d}" not in text:
            raise SystemExit(f"node {node}: unexpected namespace")
        if f"def newIDs : Finset (Fin 5011) := {{{node}}}" not in text:
            raise SystemExit(f"node {node}: unexpected newIDs")
        output = OUTDIR / f"EnergyRefineN{node:04d}Restored.lean"
        output.write_bytes(restored)
        print(
            node,
            "archive_sha256", hashlib.sha256(source).hexdigest().upper(),
            "restored_sha256", hashlib.sha256(restored).hexdigest().upper(),
            "bytes", len(restored),
        )


if __name__ == "__main__":
    main()
