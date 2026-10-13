#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""audit_existing_cache.py -- does the CURRENT cache file really correspond to real rows?

For every entry: locate its origin JSONL and origin snapshot, recompute the snapshot bytes
hash, find the row at origin_idx, and re-derive H/W hashes from that snapshot's leaf.
An entry is accepted only if all of that agrees; the entry's own text is never trusted.

Also reports the negative controls required by the Lead for the corrected builder:
  C1 same H, different weights  -> must be rejected / must not transfer
  C2 wrong snapshot field       -> must be rejected
  C3 status "unresolved" with a self-consistent key -> must be rejected by the loader
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
OUTDIR = os.path.join(MEM, "out")
sys.path.insert(0, HERE)
import cache_tools as CT
import verify_manifest as V          # only for vectors_path / kernel hashes (read-only use)

CACHE = os.path.join(OUTDIR, "certified-cache.jsonl")


def snapshot_for_stem(stem):
    """resolve a stem to its snapshot via the SINGLE registry used everywhere else
    (cache_provenance.STEM_SNAPSHOT), then the historical evidence/ naming, then none."""
    import cache_provenance as CP
    if stem in CP.STEM_SNAPSHOT and os.path.exists(CP.STEM_SNAPSHOT[stem]):
        return CP.STEM_SNAPSHOT[stem]
    p = os.path.join(EV, "hubline-domain-%s.json" % stem)
    return p if os.path.exists(p) else None


def main():
    kernel = hashlib.sha256(open(V.KERNEL, "rb").read()).hexdigest()
    kn = V.kernel_n_sha()
    rep = {}

    a = CT.audit_cache(CACHE, snapshot_for_stem, kernel, V.vectors_path, kn)
    rep["audit"] = a
    print("== audit of the existing cache ==")
    print(json.dumps(a, indent=1)[:1800])

    # ---- C1: same H, different weights ----
    st = json.loads(open(snapshot_for_stem("stage6700"), encoding="utf-8").read())
    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
    src_jl = os.path.join(OUTDIR, "verify-stage6700.jsonl")
    rows = [json.loads(l) for l in open(src_jl, encoding="utf-8") if l.strip()]
    # take row 0, but tamper its weights-derived hash to another leaf's W
    L0 = atomic[0]
    W_other = atomic[1]["proposal"]["weights"]
    tampered = dict(rows[0])
    tampered["w_sha"] = CT.full_w_sha(W_other)
    tampered["h_sha"] = CT.full_h_sha(L0["H"])
    c1_in = os.path.join(OUTDIR, "ctl-c1-sameH-otherW.jsonl")
    with open(c1_in, "w", encoding="utf-8") as f:
        f.write(json.dumps(tampered) + "\n")
    r1 = CT.build_cache_checked(c1_in, snapshot_for_stem("stage6700"),
                               os.path.join(OUTDIR, "ctl-c1-cache.jsonl"),
                               kernel, V.vectors_path, kn, 26,
                               scale_provenance="control")
    rep["C1_sameH_otherW"] = dict(admitted=r1["admitted"], rejected=r1["rejected"],
                                  sample=(r1["rejected_samples"][:2] if r1["rejected"] else []))

    # ---- C2: wrong snapshot field ----
    bad = dict(rows[1])
    bad["snapshot"] = "0" * 64
    c2_in = os.path.join(OUTDIR, "ctl-c2-wrong-snapshot.jsonl")
    with open(c2_in, "w", encoding="utf-8") as f:
        f.write(json.dumps(bad) + "\n")
    r2 = CT.build_cache_checked(c2_in, snapshot_for_stem("stage6700"),
                               os.path.join(OUTDIR, "ctl-c2-cache.jsonl"),
                               kernel, V.vectors_path, kn, 26,
                               scale_provenance="control")
    rep["C2_wrong_snapshot"] = dict(admitted=r2["admitted"], rejected=r2["rejected"],
                                    sample=(r2["rejected_samples"][:2] if r2["rejected"] else []))

    # ---- C3: unresolved verdict with self-consistent key -> loader must reject ----
    e = json.loads(open(CACHE, encoding="utf-8").readline())
    e3 = dict(e); e3["status"] = "unresolved"
    c3_cache = os.path.join(OUTDIR, "ctl-c3-unresolved.jsonl")
    with open(c3_cache, "w", encoding="utf-8") as f:
        f.write(json.dumps(e3) + "\n")
    c3, foreign3, bad3 = CT.load_cache_checked(c3_cache, kernel)
    rep["C3_unresolved_selfconsistent"] = dict(loaded=len(c3), rejected=len(bad3),
                                              reason=bad3[0][1] if bad3 else None)
    e4 = dict(e); e4["gap"] = -5
    c4_cache = os.path.join(OUTDIR, "ctl-c4-negative-gap.jsonl")
    with open(c4_cache, "w", encoding="utf-8") as f:
        f.write(json.dumps(e4) + "\n")
    c4, _, bad4 = CT.load_cache_checked(c4_cache, kernel)
    rep["C4_negative_gap"] = dict(loaded=len(c4), rejected=len(bad4),
                                  reason=bad4[0][1] if bad4 else None)
    e5 = dict(e); e5["ckey"] = e5["ckey"][:-4] + "dead"
    c5_cache = os.path.join(OUTDIR, "ctl-c5-key-tamper.jsonl")
    with open(c5_cache, "w", encoding="utf-8") as f:
        f.write(json.dumps(e5) + "\n")
    c5, _, bad5 = CT.load_cache_checked(c5_cache, kernel)
    rep["C5_key_tamper"] = dict(loaded=len(c5), rejected=len(bad5),
                                reason=bad5[0][1] if bad5 else None)

    rep["checks"] = {
        "audit_no_problems": a["n_problems"] == 0,
        "C1_sameH_otherW_rejected": r1["admitted"] == 0 and r1["rejected"] >= 1,
        "C2_wrong_snapshot_rejected": r2["admitted"] == 0 and r2["rejected"] >= 1,
        "C3_unresolved_rejected_by_loader": len(c3) == 0 and len(bad3) == 1,
        "C4_negative_gap_rejected": len(c4) == 0 and len(bad4) == 1,
        "C5_key_tamper_rejected": len(c5) == 0 and len(bad5) == 1,
    }
    rep["all_pass"] = all(rep["checks"].values())
    with open(os.path.join(OUTDIR, "cache-audit.json"), "w", encoding="utf-8") as f:
        json.dump(rep, f, indent=1)
    print(json.dumps(rep["checks"], indent=1))
    print("audit verified %d/%d entries; problems %d"
          % (a["verified"], a["n_entries"], a["n_problems"]))
    if not rep["all_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()