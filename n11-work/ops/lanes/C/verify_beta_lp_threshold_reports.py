#!/usr/bin/env python3
"""Independently replay stored threshold-Farkas certificates over Q."""
from fractions import Fraction as Q
import argparse
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import audit_beta_lp_active_vertex as active
import recheck_next512_rows as common
import search_beta_row_lp as coefficients

C2 = Q(2 * Q(1150475603510479590494077, 2951479051793528258560000))


def exact_rows(rec, weights, db, mask):
    clc, f0c, _ = coefficients.coeffs(rec, weights)
    cscale = C2 if mask >> 9 & 1 else common.LQ
    _, _, _, _, _, _, aubq = active.build(rec, weights, db, mask)
    rows = [list(row) + [Q(0)] for row in aubq]
    objective = [Q(0)] * 107
    for f in range(16):
        objective[f] = -(f0c[f] + cscale * clc[f])
    for k, (i, j) in enumerate(common.PAIRS):
        objective[16 + k] = Q(db[i][j], 4096)
    objective[-1] = Q(-1)
    rows.append(objective + [-common.T2])
    for j in range(106):
        row = [Q(0)] * 108
        row[j] = Q(-1)
        rows.append(row)
    equality = [Q(1)] * 16 + [Q(0)] * 91
    rows.append(equality + [Q(1)])
    return rows


def verify(path, proposal, db_text, require_complete):
    report = json.loads(path.read_text())
    expected_sha = hashlib.sha256(proposal.read_bytes()).hexdigest().upper()
    if report["proposal_sha256"] != expected_sha:
        raise AssertionError(f"{path}: proposal hash mismatch")
    if report["threshold_T2"] != str(common.T2):
        raise AssertionError(f"{path}: threshold mismatch")
    doc = json.loads(proposal.read_text(encoding="utf-8-sig"))
    rec = next(r for r in doc["records"] if r["id"] == report["id"])
    db = common.parse_db(db_text, report["id"])
    masks = [item["mask"] for item in report["records"]]
    if masks != sorted(set(masks)) or any(mask < 0 or mask >= 512 for mask in masks):
        raise AssertionError(f"{path}: invalid or duplicate mask coverage")
    if require_complete and masks != list(range(512)):
        raise AssertionError(f"{path}: mask coverage is not exactly 0..511")
    digested = 0
    for item in report["records"]:
        if item["status"] != "exact-l1-normalized-Farkas":
            raise AssertionError(f"{path}: mask {item['mask']} is {item['status']}")
        rows = exact_rows(rec, doc["weights"], db, item["mask"])
        y = [Q(value) for value in item["y"]]
        if len(y) != len(rows):
            raise AssertionError(f"{path}: mask {item['mask']} multiplier length")
        if not all(value >= 0 for value in y[:-1]):
            raise AssertionError(f"{path}: mask {item['mask']} negative multiplier")
        if any(sum(y[i] * rows[i][j] for i in range(len(rows)))
               for j in range(107)):
            raise AssertionError(f"{path}: mask {item['mask']} nonzero residual")
        if sum(y[i] * rows[i][-1] for i in range(len(rows))) != -1:
            raise AssertionError(f"{path}: mask {item['mask']} normalization")
        if item["nonzero_inequalities"] != sum(value != 0 for value in y[:-1]):
            raise AssertionError(f"{path}: mask {item['mask']} nonzero count")
        digested ^= int.from_bytes(
            hashlib.sha256("".join(item["y"]).encode()).digest()[:8], "big")
    return {
        "id": report["id"],
        "certificates": len(report["records"]),
        "masks": f"0..{masks[-1]}" if masks else "empty",
        "complete": masks == list(range(512)),
        "xor_certificate_digest": f"{digested:016X}",
        "report_sha256": hashlib.sha256(path.read_bytes()).hexdigest().upper(),
        "status": "all-512-exact-rechecks-pass",
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("reports", nargs="+", type=Path)
    ap.add_argument("--require-complete", action="store_true")
    ap.add_argument("--out", type=Path,
                    default=HERE / "beta-lp-threshold-verification.json")
    args = ap.parse_args()
    db_text = common.DBM.read_text()
    results = [verify(path, common.PROPOSAL, db_text, args.require_complete)
               for path in args.reports]
    args.out.write_text(json.dumps({"records": results}, indent=1) + "\n")
    print(json.dumps({"records": results}, indent=1))


if __name__ == "__main__":
    main()
