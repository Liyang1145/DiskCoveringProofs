#!/usr/bin/env python3
"""Reconstruct the best corrected beta/row LP vertex for each public residual.

The float sign-region sweep only selects a mask.  The selected active system is
then solved exactly over Fraction and every candidate is rechecked by
search_beta_row_lp.exact_eval.  A positive exact gap would be a candidate, not
kernel credit; a negative gap is only a diagnostic for one sign region.
"""
from fractions import Fraction as Q
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

IDS = (1409, 2337, 2341, 2360, 2368, 2370)
OUT = HERE / "beta-lp-exact-sweep.json"


def main():
    start = time.monotonic()
    doc = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    weights = doc["weights"]
    db_text = common.DBM.read_text()
    records = []
    for rid in IDS:
        rec = next(r for r in doc["records"] if r["id"] == rid)
        db = common.parse_db(db_text, rid)
        best = None
        for mask in range(512):
            solved = active.solve_region(rec, weights, db, mask)
            lp = solved[0]
            if lp.success and (best is None or lp.fun < best[0].fun):
                best = (lp, mask, solved)
        item = {"id": rid, "branches": 512}
        if best is None:
            item.update(status="no-float-candidate")
            records.append(item)
            print(rid, item["status"])
            continue
        lp, mask, solved = best
        _, Aeq, beq, Aub, bub, Aeqq, Aubq = solved
        selected, _ = active.active_system(
            lp, Aeq, beq, Aub, bub, Aeqq, Aubq)
        rank, _, free, inconsistent, solution = exact_rank.rref(selected)
        item.update(mask=mask, float_fun=str(lp.fun),
                    selected_rows=len(selected), exact_rank=rank,
                    free_columns=free,
                    augmented_inconsistent=inconsistent)
        if solution is None:
            item["status"] = ("inconsistent-active-set" if inconsistent
                              else "underdetermined-active-set")
        else:
            beta, lam, rmin = solution[:16], solution[16:106], solution[-1]
            item["beta"] = [str(x) for x in beta]
            item["lam_nonzero"] = [[list(common.PAIRS[k]), str(lam[k])]
                                   for k in range(90) if lam[k]]
            evaluation = coefficients.exact_eval(
                rec, weights, beta, lam, rmin, db)
            item.update(exact=evaluation, exact_gap_float=float(
                Q(evaluation["gap"])),
                status="PASS" if evaluation["pass"] else "exact-negative")
        records.append(item)
        print(rid, item["status"], "mask", mask, "rank", rank,
              "gap", item.get("exact_gap_float"))
    report = {
        "scope": ("exact Fraction active-vertex reconstruction at the best "
                  "float sign region for six public residual ids; negative "
                  "results are not global infeasibility proofs and no result "
                  "is kernel credit"),
        "proposal_sha256": hashlib.sha256(
            common.PROPOSAL.read_bytes()).hexdigest().upper(),
        "records": records,
        "pass_count": sum(r["status"] == "PASS" for r in records),
        "elapsed_seconds": round(time.monotonic() - start, 3),
    }
    OUT.write_text(json.dumps(report, indent=1) + "\n")
    print("pass_count", report["pass_count"], "->", OUT.name)


if __name__ == "__main__":
    main()
