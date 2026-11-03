#!/usr/bin/env python3
"""Lane-A closure driver (session 2026-11-02 part 2).

One deterministic entry point that re-runs the fast lane-A static gates and
records the exact current state needed for the supervisor-only root edit:

  * c450-import-closure   (all chain imports resolve to real .lean files)
  * c450-transfer-shapes  (telescope K=12..36 declared + applied once, descending)
  * c450-consumer-signatures (chain <-> consumer boundary types match)
  * root markers          (root still carries exactly the two HARK-MISSING lines)
  * q0 pre-flight         (SevenClassQ0Deg3 import closure green, pause readiness)

Scope: STATIC source audits only.  This is NOT a kernel verdict and NOT a build.
The slow c450-root-import-safety audit is intentionally excluded (it is run and
hashed separately); its committed report sha is recorded if present.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]                      # repo root (wt-A)
LEAN = ROOT / "n11-work" / "lean"
ROOT_LEAN = LEAN / "N11Formalization.lean"
OUT = HERE / "lane-a-closure.json"

HARK = re.compile(r"^-- HARK-MISSING[^\n]*import N11Formalization\.(\w+)\s*$", re.M)


def run(script: str, cwd: Path, timeout: int = 120):
    p = subprocess.run([sys.executable, str(HERE / script)], cwd=str(cwd),
                       capture_output=True, text=True, timeout=timeout)
    tail = (p.stdout + p.stderr).strip().splitlines()[-1:] or [""]
    return p.returncode, tail[0]


def sha_of(path: Path):
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None


def main():
    rep = {"scope": "static source audits; NOT a kernel verdict",
           "checks": [], "failures": []}

    def record(name, ok, detail):
        rep["checks"].append({"name": name, "ok": bool(ok), "detail": detail})
        if not ok:
            rep["failures"].append(name)

    for script, key, cwd in (("audit_c450_import_closure.py", "import_closure", ROOT),
                            ("audit_c450_transfer_shapes.py", "transfer_shapes", HERE),
                            ("audit_c450_consumer_signatures.py", "consumer_signatures", HERE),
                            ("check_q0_degree3_imports.py", "q0_preflight", HERE)):
        try:
            rc, line = run(script, cwd)
        except subprocess.TimeoutExpired:
            rc, line = 124, "timeout"
        record(key, rc == 0, f"rc={rc}: {line}")

    root_text = ROOT_LEAN.read_text(encoding="utf-8")
    hark = HARK.findall(root_text)
    record("root_hark_missing_exactly_two", hark == ["C450ChainCompletion",
                                                     "C450ChainCompletionMain"],
           f"markers={hark}")

    rep["root_sha256"] = sha_of(ROOT_LEAN)
    rep["chain_module_sha256"] = {
        n: sha_of(LEAN / "N11Formalization" / (n + ".lean"))
        for n in ("C450ChainCompletion", "C450ChainCompletionMain")}
    rep["committed_reports"] = {
        f: sha_of(HERE / f) for f in (
            "c450-import-closure.json", "c450-transfer-shapes.json",
            "c450-consumer-signatures.json", "c450-root-import-safety.json")}

    rep["verdict"] = ("PASS_LANE_A_CLOSURE" if not rep["failures"]
                      else "FAIL:" + ",".join(rep["failures"]))
    text = json.dumps(rep, indent=2, sort_keys=True) + "\n"
    OUT.write_text(text, encoding="utf-8")
    print(f"verdict: {rep['verdict']}  ({len(rep['checks'])} checks)")
    for c in rep["checks"]:
        print(f"  [{'ok' if c['ok'] else 'FAIL'}] {c['name']}: {c['detail']}")
    print("report sha256", hashlib.sha256(text.encode()).hexdigest())
    return 0 if not rep["failures"] else 1


if __name__ == "__main__":
    sys.exit(main())
