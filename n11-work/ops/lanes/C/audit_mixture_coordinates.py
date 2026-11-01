#!/usr/bin/env python3
"""Exactly reconstruct f0Lo/g from beta for the seven public residuals.

This isolates the beta-dependent part of `PaidCellCertificateM.Packet` when
the 36 cosine lines are frozen.  It is an arithmetic audit, not a certificate.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import recheck_next512_rows as common

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = HERE / "mixture-coordinate-audit.json"
IDS = (1409, 2337, 2341, 2356, 2360, 2368, 2370)
Lq = 2 * Q(1150475603510479590494077, 2951479051793528258560000)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def main():
    doc = json.loads(common.PROPOSAL.read_text(encoding="utf-8-sig"))
    records = {rec["id"]: rec for rec in doc["records"]}
    weights = [[Q(str(value)) / 10**12 for value in row] for row in doc["weights"]]
    pairs = [(i, j) for i in range(9) for j in range(i + 1, 9)]
    checks = []
    for node in IDS:
        rec = records[node]
        beta = [Q(str(value)) for value in rec["beta"]]
        W = [sum(beta[f] * weights[f][k] for f in range(16)) for k in range(36)]
        slopes = [Q(str(packet["s"])) for packet in rec["packets"]]
        intercepts = [Q(str(packet["c"])) for packet in rec["packets"]]
        cl = sum(W[k] * slopes[k] * (pairs[k][0] - pairs[k][1]) for k in range(36))
        f0 = sum(W[k] * intercepts[k] for k in range(36)) + (
            Lq * cl if cl >= 0 else common.LQ * cl)
        g = [sum(W[k] * slopes[k] for k in range(36)
                 if pairs[k][0] <= q < pairs[k][1]) for q in range(9)]
        errors = {
            "cl": str(cl - Q(rec["cl"])),
            "f0Lo": str(f0 - Q(rec["f0Lo"])),
            "g_max_abs": str(max(abs(g[q] - Q(rec["g"][q])) for q in range(9))),
        }
        if any(Q(value) != 0 for value in errors.values()):
            raise AssertionError((node, errors))
        checks.append({
            "id": node,
            "beta_nonzero": sum(value != 0 for value in beta),
            "cl_exact": True,
            "f0Lo_exact": True,
            "g_exact": True,
        })
    result = {
        "scope": "exact beta-coordinate reconstruction; not a kernel or payment claim",
        "proposal_sha256": sha256(common.PROPOSAL),
        "records_checked": len(checks),
        "records": checks,
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
