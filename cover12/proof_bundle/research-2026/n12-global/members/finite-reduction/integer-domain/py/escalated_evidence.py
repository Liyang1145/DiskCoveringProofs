#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""escalated_evidence.py -- full evidence record for the leaves that needed scale 28.

For each such leaf it stores, from source bytes read once:
  snapshot sha256, leaf index, atom count N, the integer SCALE actually used, the full
  sha256 of the exact rational H and of the exact weights, the vector-set hash, the frozen
  kernel and N-kernel hashes, the certify() result (status/boxes/leaves/outside/max/demand
  /gap), the scale-26 attempt outcome (for honesty: it stopped), and the manifest's own
  recorded result for comparison (a diagnostic, never a substitute).

The scale-28 verdict stands on its own integers; agreement with the float-era recorded
numbers is reported as a diagnostic only.
"""
import hashlib
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
OUT = os.path.join(MEM, "out")
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(N12, "members", "upper-audit", "integer-atomic", "py"))
import cache_tools as CT
import verify_manifest as V
import integer_kernel as IK

SNAP = os.path.join(EV, "hubline-domain-stage11825.json")
ESCALATED = [4398, 4846, 5018]


def main():
    snap_raw = open(SNAP, "rb").read()
    snap_sha = hashlib.sha256(snap_raw).hexdigest()
    st = json.loads(snap_raw.decode("utf-8"))
    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
    kernel = hashlib.sha256(open(V.KERNEL, "rb").read()).hexdigest()
    kn = V.kernel_n_sha()

    rows = {}
    for src in (os.path.join(OUT, "verify-stage11825.jsonl"),
                os.path.join(MEM, "archive", "verify-stage11825-run2.jsonl")):
        if os.path.exists(src):
            for line in open(src, encoding="utf-8"):
                line = line.strip()
                if not line:
                    continue
                r = json.loads(line)
                if r.get("idx") in ESCALATED:
                    rows.setdefault(r["idx"], r)
    if len(rows) < len(ESCALATED):
        for i in ESCALATED:
            rows.setdefault(i, {})

    out = {"snapshot": os.path.relpath(SNAP, N12).replace("\\", "/"),
           "snapshot_sha256": snap_sha, "kernel_sha256": kernel,
           "kernel_n_sha256": kn, "records": []}
    for idx in ESCALATED:
        L = atomic[idx]
        H_raw, W_raw = L["H"], L["proposal"]["weights"]
        N = L.get("atomN", 2048)
        usha = hashlib.sha256(open(V.vectors_path(N), "rb").read()).hexdigest()
        H = [(F(x[0]), F(x[1])) for x in H_raw]
        W = [[F(x) for x in row] for row in W_raw]
        rec = L.get("result") or {}
        r = rows[idx]
        # re-derive the two attempts here, from source, so the evidence is self-contained
        A26 = IK.IntAtoms(H, W, 26)
        res26 = A26.certify()
        A28 = IK.IntAtoms(H, W, 28)
        res28 = A28.certify()
        out["records"].append(dict(
            idx=idx, n=N, scale_26_result=res26, scale_28_result=res28,
            used_scale=28, escalated=True,
            h_sha256=CT.full_h_sha(H_raw), w_sha256=CT.full_w_sha(W_raw),
            units_sha256=usha, n_atoms=len(A28.W), demand=A28.total,
            recorded_manifest_result=rec,
            diagnostic_gap_matches_recorded=bool(
                res28.get("gap_integer") == rec.get("gap_integer")),
            ledger_row=r,
        ))
    dest = os.path.join(OUT, "escalated-scale28-evidence.json")
    with open(dest, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    for r in out["records"]:
        print("idx %d: scale26=%s | scale28=%s gap=%s boxes=%s | recorded gap=%s match=%s"
              % (r["idx"], r["scale_26_result"].get("status"),
                 r["scale_28_result"].get("status"), r["scale_28_result"].get("gap_integer"),
                 r["scale_28_result"].get("boxes"), r["recorded_manifest_result"].get("gap_integer"),
                 r["diagnostic_gap_matches_recorded"]))
    print("evidence ->", dest)


if __name__ == "__main__":
    main()