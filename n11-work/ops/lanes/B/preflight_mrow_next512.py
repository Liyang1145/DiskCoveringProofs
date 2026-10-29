#!/usr/bin/env python3
"""Preflight the public next512 records through the generic m-row auditor.

The next512 artifact mixes six row counts. The generic emitter accepts one
row count per invocation, so partition its 505 passing records exactly and
audit every partition without writing Lean packet modules.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SURVEY = ROOT / "n11-work/evidence-20261028/inputs/paid16-general-next512.json"
EMITTER = ROOT / "n11-work/ops/lanes/C/emit_mrow_packets.py"
DBM = ROOT / "n11-work/lean/N11Formalization/DBMSourceTreeData.lean"
OUT = HERE / "mrow-next512-preflight-report.json"
SURVEY_SHA256 = "F49F06FC57A818E464D8DCBDAACE2E4D57A3C2E84CEA27FE86C4551363F3DD16"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def load_emitter():
    spec = importlib.util.spec_from_file_location("emit_mrow_packets", EMITTER)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load generic m-row emitter")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main() -> int:
    if sha256(SURVEY) != SURVEY_SHA256:
        raise SystemExit("next512 survey hash mismatch")
    doc = json.loads(SURVEY.read_text(encoding="utf-8-sig"))
    passing = [r for r in doc["records"] if r.get("pass") is True]
    if len(passing) != 505:
        raise SystemExit(f"expected 505 passing records, got {len(passing)}")

    emitter = load_emitter()
    db_text = DBM.read_text(encoding="utf-8")
    partitions = []
    for m in sorted({len(r["lam"]) for r in passing}):
        records = [r for r in passing if len(r["lam"]) == m]
        audits = [emitter.audit_record(r, m, db_text) for r in records]
        partitions.append({
            "m": m,
            "records": len(records),
            "ids_sha256": hashlib.sha256(
                ",".join(str(r["id"]) for r in sorted(records, key=lambda r: r["id"]))
                .encode("ascii")
            ).hexdigest().upper(),
            "min_exact_gap": str(min(a["gap"] for a in audits)),
            "min_reduced_slack": str(min(a["slack"] for a in audits)),
        })

    if sum(p["records"] for p in partitions) != 505:
        raise SystemExit("m-row partitions do not cover all passing records")
    report = {
        "scope": "exact-rational preflight only; no Lean kernel credit",
        "survey_sha256": sha256(SURVEY),
        "emitter_sha256": sha256(EMITTER),
        "dbm_sha256": sha256(DBM),
        "passing_records": len(passing),
        "row_counts": dict(Counter(p["m"] for p in partitions for _ in range(p["records"]))),
        "partitions": partitions,
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
