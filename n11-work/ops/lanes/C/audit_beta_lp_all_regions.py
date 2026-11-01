#!/usr/bin/env python3
"""Exact Fraction active-vertex audit across every sign region of one id.

The float LP selects the active rows in each of the 512 sign regions.  Each
full-rank active system is then solved over Q and rechecked.  This is a
search/audit diagnostic, not an infeasibility proof or kernel credit.
"""
from fractions import Fraction as Q
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import audit_beta_lp_active_vertex as active
import audit_beta_lp_exact_rank as exact_rank
import recheck_next512_rows as common
import search_beta_row_lp as coefficients

OUT = HERE / "beta-lp-all-regions.json"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--id", type=int, default=2356)
    ap.add_argument("--start-mask", type=int, default=0)
    ap.add_argument("--stop-mask", type=int, default=512)
    ap.add_argument("--time-budget", type=float, default=180)
    ap.add_argument("--out", type=Path, default=OUT)
    args = ap.parse_args()
    start = time.monotonic()
    doc = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    weights = doc["weights"]
    rec = next(r for r in doc["records"] if r["id"] == args.id)
    db = common.parse_db(common.DBM.read_text(), args.id)
    records = []
    first = max(args.start_mask, 0)
    stop = min(args.stop_mask, 512)
    for mask in range(first, stop):
        if time.monotonic() - start > args.time_budget:
            records.append({"mask": mask, "status": "time-budget"})
            break
        solved = active.solve_region(rec, weights, db, mask)
        lp = solved[0]
        item = {"mask": mask, "float_fun": str(lp.fun),
                "float_success": bool(lp.success)}
        if not lp.success:
            item["status"] = "float-infeasible"
            records.append(item)
            continue
        _, Aeq, beq, Aub, bub, Aeqq, Aubq = solved
        selected, _ = active.active_system(lp, Aeq, beq, Aub, bub, Aeqq, Aubq)
        rank, _, free, inconsistent, solution = exact_rank.rref(selected)
        item.update(selected_rows=len(selected), exact_rank=rank,
                    free_columns=free, augmented_inconsistent=inconsistent)
        if solution is None:
            item["status"] = ("inconsistent-active-set" if inconsistent
                              else "underdetermined-active-set")
        else:
            beta, lam, rmin = solution[:16], solution[16:106], solution[-1]
            evaluation = coefficients.exact_eval(
                rec, weights, beta, lam, rmin, db)
            item.update(exact_gap_float=float(Q(evaluation["gap"])),
                        status="PASS" if evaluation["pass"] else "exact-negative")
            if evaluation["pass"]:
                item.update(beta=[str(x) for x in beta], exact=evaluation)
        records.append(item)
        if mask % 32 == 31:
            print("mask", mask, "elapsed", round(time.monotonic() - start, 1),
                  flush=True)
    counts = {}
    for item in records:
        counts[item["status"]] = counts.get(item["status"], 0) + 1
    report = {
        "scope": ("exact Fraction active-vertex audit over tested sign regions "
                  "for one public residual id; not an infeasibility proof and "
                  "not kernel credit"),
        "proposal_sha256": hashlib.sha256(
            common.PROPOSAL.read_bytes()).hexdigest().upper(),
        "id": args.id,
        "requested_masks": min(args.stop_mask, 512),
        "tested_masks": len([r for r in records
                             if r["status"] != "time-budget"]),
        "status_counts": counts,
        "pass_count": counts.get("PASS", 0),
        "elapsed_seconds": round(time.monotonic() - start, 3),
        "records": records,
    }
    report["first_mask"] = first
    report["stop_mask"] = stop
    args.out.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: report[k] for k in
                      ("id", "tested_masks", "status_counts", "pass_count",
                       "elapsed_seconds")}, indent=1))


if __name__ == "__main__":
    main()
