#!/usr/bin/env python3
"""Restore unused token-clean archive refinements and emit B13 wrappers.

The archive bytes are copied verbatim from origin/ci/n11-build. The wrappers
are generated from the reviewed 3853 template. This script performs static
checks only; no module is paid until CI builds it.
"""
from pathlib import Path
import hashlib
import re
import subprocess

HERE = Path(__file__).resolve().parent
LEAN = HERE.parents[2] / "lean" / "N11Formalization"
PREFIX = "ci-n11/drafts/energy/N11Formalization/"
BRANCH = "origin/ci/n11-build"
IDS = (3149, 3496, 3794, 3795, 3800, 3803, 3979, 3865, 4684)
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|native_decide|implemented_by)\b|"
    r"\bLean\.ofReduceBool\b|\bmaxHeartbeats\s+0\b"
)


def git_show(path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{BRANCH}:{path}"])


def main() -> None:
    template = (LEAN / "EnergyTerminalBatchB13Refine3853.lean").read_text()
    old = ("/-! Refine the B13 paid set by the validated split certificate for source\n"
           "terminal 3853.  The membership proof stays hierarchical: B10 has 100 paid\n"
           "ids, the remaining-210 and every Next1182 part have at most 210 literals,\n"
           "and Next505 is bounded below 2565. -/")
    new = ("/-! Refine the B13 paid set by the archived split certificate for source\n"
           "terminal 3853.  The archive bytes are restored verbatim and remain CI\n"
           "pending; the membership proof stays hierarchical. -/")
    assert old in template
    template = template.replace(old, new)
    template_main = (LEAN / "EnergyTerminalBatchB13Refine3853Main.lean").read_text()
    for node in IDS:
        source = git_show(f"{PREFIX}EnergyRefineN{node}.lean")
        text = source.decode()
        assert not FORBIDDEN.search(text), node
        assert f"def newIDs : Finset (Fin 5011) := {{{node}}}" in text, node
        assert f"DBMSourceTree.data {node}).terminal = true" in text, node
        (LEAN / f"EnergyRefineN{node}.lean").write_bytes(source)
        wrapper = template.replace("3853", str(node))
        wrapper_main = template_main.replace("3853", str(node))
        assert "3853" not in wrapper and "3853" not in wrapper_main, node
        (LEAN / f"EnergyTerminalBatchB13Refine{node}.lean").write_text(wrapper)
        (LEAN / f"EnergyTerminalBatchB13Refine{node}Main.lean").write_text(wrapper_main)
        print(node, len(source), hashlib.sha256(source).hexdigest())


if __name__ == "__main__":
    main()
