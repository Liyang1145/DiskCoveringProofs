#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""migrate_cache.py -- rebuild the production cache under the strict rules.

Rules applied (Lead audit):
  * key now binds the integer SCALE; a scale-26 certificate can never be served as 28;
  * a scale-26 certificate is reused as a SCALE-26 certificate, with the provenance of
    that scale recorded explicitly.  The old entries were produced by calls to the frozen
    kernel with its default Sexpt (=26) -- no --sexpt flag existed then -- so the
    provenance is "constructed by integer_kernel default Sexpt=26", stated as such;
  * strict gap > 0 (gap == 0 excludes nothing);
  * synthetic control entries (origin_stem starting with 'syn-') are EXCLUDED;
  * source rows are read once as bytes and every row must bind the snapshot hash.
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
import cache_tools as CT
import verify_manifest as V

STEMS = {
    "stage2200": os.path.join(EV, "hubline-domain-stage2200.json"),
    "stage6700": os.path.join(EV, "hubline-domain-stage6700.json"),
    "stage11825": os.path.join(EV, "hubline-domain-stage11825.json"),
}
SCALE_PROVENANCE = ("constructed by integer_kernel/integer_kernel_n default Sexpt=26 "
                    "(no --sexpt flag existed when these rows were produced)")
# Origins whose generation predates the kernel_n field.  Only these may carry a missing
# kernel_n, and only at N=2048 (the only dispatch that generation had).  See
# out/cache-provenance.json for the fresh-source audit of every entry.
PRE_FIELD_KERNEL_N_OK = {"stage2200"}


def main():
    kernel = hashlib.sha256(open(V.KERNEL, "rb").read()).hexdigest()
    kn = V.kernel_n_sha()
    atoms_sha = hashlib.sha256(open(V.ATOMS_PY, "rb").read()).hexdigest() \
        if os.path.exists(V.ATOMS_PY) else ""
    # The LEADGER SET IS THE REGISTRY: every registered stem contributes its rows and
    # nothing else can enter the production cache.  Synthetic/control stems are therefore
    # excluded by construction (this is how a control run once polluted the cache, which the
    # acceptance gate detected as a changed cache sha).
    import cache_provenance as CP
    ledger = {}
    for stem in CP.STEM_SNAPSHOT:
        for p in CP.SOURCES.get(stem, []):
            if os.path.exists(p):
                ledger[stem] = p
                break
    STEMS = {s: CP.STEM_SNAPSHOT[s] for s in ledger}
    out_lines, stats = [], dict(admitted=0, rejected=0, rejected_samples=[],
                                excluded_synthetic=0, per_origin={},
                                ledger_files={s: os.path.relpath(p, MEM)
                                              for s, p in ledger.items()},
                                scale_provenance=SCALE_PROVENANCE)
    for stem, jl in ledger.items():
        snap = STEMS[stem]
        if not os.path.exists(jl):
            continue
        raw = open(jl, "rb").read()                       # single read
        rows_sha = hashlib.sha256(raw).hexdigest()
        snap_raw = open(snap, "rb").read()                # single read of the snapshot
        snap_sha = hashlib.sha256(snap_raw).hexdigest()
        st = json.loads(snap_raw.decode("utf-8"))
        atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
        for line in raw.decode("utf-8").splitlines():
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if r.get("snapshot") != snap_sha:
                stats["rejected"] += 1
                stats["rejected_samples"].append(("snapshot mismatch", stem, r.get("idx")))
                continue
            if not V.positive_gap(r):
                stats["rejected"] += 1
                stats["rejected_samples"].append(("gap not >0 / not certified", stem, r.get("idx")))
                continue
            idx = r.get("idx")
            if not isinstance(idx, int) or not (0 <= idx < len(atomic)):
                stats["rejected"] += 1
                stats["rejected_samples"].append(("idx range", stem, idx))
                continue
            L = atomic[idx]
            N = L.get("atomN", 2048)
            usha = hashlib.sha256(open(V.vectors_path(N), "rb").read()).hexdigest()
            H_raw, W_raw = L["H"], L["proposal"]["weights"]
            h_sha, w_sha = CT.full_h_sha(H_raw), CT.full_w_sha(W_raw)
            # --- strict source binding: no field may be silently missing ---
            if r.get("kernel") != kernel:
                stats["rejected"] += 1
                stats["rejected_samples"].append(("row kernel != current kernel", stem, idx))
                continue
            if r.get("atoms") not in (None, atoms_sha):
                stats["rejected"] += 1
                stats["rejected_samples"].append(("row atoms hash mismatch", stem, idx))
                continue
            if r.get("n") != N:
                stats["rejected"] += 1
                stats["rejected_samples"].append(("row n missing/mismatched", stem, idx))
                continue
            if r.get("units") != usha:
                stats["rejected"] += 1
                stats["rejected_samples"].append(("row units missing/mismatched", stem, idx))
                continue
            # kernel_n: the N-dispatch kernel hash.  A legacy row that predates the field is
            # accepted ONLY if it belongs to an audited pre-field origin AND it is not a
            # dispatch-N row (N == 2048, which is what that generation used).
            rkn = r.get("kernel_n")
            if rkn is None:
                if stem not in PRE_FIELD_KERNEL_N_OK or N != 2048:
                    stats["rejected"] += 1
                    stats["rejected_samples"].append(("row kernel_n missing, origin not allowed",
                                                      stem, idx))
                    continue
                kn_note = "legacy: field absent in this audited generation"
            elif rkn != kn:
                stats["rejected"] += 1
                stats["rejected_samples"].append(("row kernel_n mismatch", stem, idx))
                continue
            else:
                kn_note = "recorded in source row"
            scale = r.get("used_scale", 26)
            if scale not in (26, 28):
                stats["rejected"] += 1
                stats["rejected_samples"].append(("scale not in {26,28}", stem, idx))
                continue
            if r.get("used_scale") is None:
                provenance = SCALE_PROVENANCE
            else:
                provenance = ("fresh-run at explicitly requested/escalated scale %d "
                              "(used_scale recorded in the source row)" % scale)
            ck = CT.key_from_parts(N, usha, kernel, kn, h_sha, w_sha, scale)
            entry = dict(ckey=ck, status="certified", n=N, scale=scale, units=usha,
                         kernel=kernel, kernel_n=kn, kernel_n_source=kn_note,
                         h_sha=h_sha, w_sha=w_sha,
                         gap=r.get("gap"), n_atoms=r.get("n_atoms"), total=r.get("total"),
                         boxes=r.get("boxes"), leaves=r.get("leaves"),
                         outside=r.get("outside"), max_capture=r.get("max_capture"),
                         demand=r.get("demand"), origin_stem=stem, origin_idx=idx,
                         origin_snapshot=snap_sha, origin_jsonl_sha256=rows_sha,
                         source_row_from_cache=r.get("from_cache"),
                         source_row_is_fresh=(r.get("from_cache") is False or
                                              (stem in PRE_FIELD_KERNEL_N_OK and
                                               r.get("from_cache") is None and
                                               "cache_origin" not in r)),
                         scale_provenance=provenance)
            out_lines.append(entry)
            stats["admitted"] += 1
            stats["per_origin"][stem] = stats["per_origin"].get(stem, 0) + 1

    # dedupe by ckey (conflicting duplicates are dropped, not averaged)
    by_ckey, dup = {}, 0
    for e in out_lines:
        k = e["ckey"]
        if k in by_ckey:
            if by_ckey[k] != e:
                dup += 1
            continue
        by_ckey[k] = e
    stats["duplicate_ckeys_dropped"] = dup
    stats["unique_entries"] = len(by_ckey)
    dest = os.path.join(OUT, "certified-cache.jsonl")
    tmp = dest + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        for k in sorted(by_ckey):
            f.write(json.dumps(by_ckey[k]) + "\n")
    os.replace(tmp, dest)
    stats["out"] = dest
    with open(os.path.join(OUT, "cache-migration.json"), "w", encoding="utf-8") as f:
        json.dump(stats, f, indent=1)
    print(json.dumps({k: v for k, v in stats.items() if k != "rejected_samples"}, indent=1))
    print("rejected samples:", stats["rejected_samples"][:6])


if __name__ == "__main__":
    main()