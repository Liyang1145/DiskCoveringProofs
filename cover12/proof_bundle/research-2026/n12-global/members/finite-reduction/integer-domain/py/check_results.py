#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_results.py -- independent post-hoc check of a replay (mixed-N, mixed-scale).

Verifies, from source bytes read once:
  * every row binds the CURRENT snapshot bytes hash, the base kernel hash, the atoms
    source hash, and (per leaf) the correct vector-set hash for that leaf's N;
  * every row's idx is unique and the idx set is EXACTLY range(n_atomic);
  * every row carries status certified AND a STRICTLY positive gap (gap == 0 excludes
    nothing, so it is not a certificate);
  * every row's ckey is RE-DERIVED from (N, used_scale, units, kernel, kernel_n, H-hash,
    W-hash) with H/W taken from the CURRENT snapshot leaf at that idx; the stored key is
    never trusted;
  * used_scale is recorded per row (the scale is not an input of the proposition, but it
    must be honest: a scale-26 certificate is not a scale-28 certificate);
  * the summary's own numbers agree with this recomputation;
  * global_certificate only when: exact partition (independent recursive tiling), all
    prunes reproduced, every leaf bound+certified with gap>0, and pending == 0.

Usage: py -3 -B py/check_results.py --snapshot PATH --out-stem NAME
"""
from __future__ import annotations

import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
sys.path.insert(0, HERE)
import verify_manifest as V


def main():
    argv = sys.argv[1:]
    snap = os.path.join(EV, "hubline-domain-stage11825.json")
    stem = "stage11825"
    if "--snapshot" in argv:
        snap = argv[argv.index("--snapshot") + 1]
    if "--out-stem" in argv:
        stem = argv[argv.index("--out-stem") + 1]
    jsonl = os.path.join(MEM, "out", "verify-%s.jsonl" % stem)
    summary = os.path.join(MEM, "out", "verify-%s-summary.json" % stem)

    snap_raw = open(snap, "rb").read()                     # single read
    snap_sha = hashlib.sha256(snap_raw).hexdigest()
    st = json.loads(snap_raw.decode("utf-8"))
    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
    n_atomic = len(atomic)
    kernel = hashlib.sha256(open(V.KERNEL, "rb").read()).hexdigest()
    kn = V.kernel_n_sha()
    atoms_sha = hashlib.sha256(open(V.ATOMS_PY, "rb").read()).hexdigest() \
        if os.path.exists(V.ATOMS_PY) else ""

    rows, dup, seen = [], 0, set()
    for line in open(jsonl, encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        if r.get("idx") in seen:
            dup += 1
        seen.add(r.get("idx"))
        rows.append(r)

    problems, per_n, per_scale, cert = [], {}, {}, 0
    for r in rows:
        idx = r.get("idx")
        tag = "idx=%s" % idx
        if not isinstance(idx, int) or not (0 <= idx < n_atomic):
            problems.append((tag, "idx out of range")); continue
        L = atomic[idx]
        N = L.get("atomN", 2048)
        per_n[N] = per_n.get(N, 0) + 1
        sc = r.get("used_scale")
        per_scale[sc] = per_scale.get(sc, 0) + 1
        usha = hashlib.sha256(open(V.vectors_path(N), "rb").read()).hexdigest()
        H_raw, W_raw = L["H"], L["proposal"]["weights"]
        if r.get("snapshot") != snap_sha:
            problems.append((tag, "snapshot binding")); continue
        if r.get("kernel") != kernel or r.get("atoms") != atoms_sha:
            problems.append((tag, "kernel/atoms binding")); continue
        if r.get("n") != N:
            problems.append((tag, "N %r != leaf N %r" % (r.get("n"), N))); continue
        if r.get("units") != usha or r.get("kernel_n") != kn:
            problems.append((tag, "units/kernel_n binding")); continue
        if sc not in (26, 28):
            problems.append((tag, "used_scale %r not in {26,28}" % sc)); continue
        if not V.positive_gap(r):
            problems.append((tag, "not certified with gap>0")); continue
        # gap must BE the arithmetic quantity demand - 10*max_capture, strictly positive:
        # a positive 'gap' field alone does not guard against a recording error.
        try:
            dem, mx = r.get("demand"), r.get("max_capture")
            if dem is None or mx is None:
                problems.append((tag, "missing demand/max_capture for gap recheck")); continue
            derived = int(dem) - 10 * int(mx)
            if derived <= 0:
                problems.append((tag, "recomputed gap %d <= 0" % derived)); continue
            if int(r.get("gap")) != derived:
                problems.append((tag, "recorded gap %s != demand-10*max %d"
                                 % (r.get("gap"), derived))); continue
        except Exception as e:
            problems.append((tag, "gap recheck failed: %s" % e)); continue
        ck = V.content_key(H_raw, W_raw, N, usha, kernel, kn, sc)
        if r.get("ckey") != ck:
            problems.append((tag, "ckey != re-derived key (scale %r)" % sc)); continue
        cert += 1

    pending_empty = (len(st.get("pending", [])) == 0)
    idx_ok = (seen == set(range(n_atomic)))
    s = json.loads(open(summary, encoding="utf-8").read()) if os.path.exists(summary) else {}
    # the summary's structural booleans are only meaningful for THIS snapshot: bind them.
    summary_bound = (s.get("snapshot_sha256") == snap_sha) or \
        (s.get("binding", {}).get("snapshot") == snap_sha)
    ar = s.get("atomic_replay", {})
    partition_ok = bool(summary_bound and s.get("partition", {}).get("exact_partition"))
    prunes_ok = bool(summary_bound and s.get("infeasible", {}).get("all_reproduced"))
    structural_ok = bool(summary_bound and s.get("structural_checks_pass"))
    real_global = bool(idx_ok and not problems and not dup and partition_ok and
                       prunes_ok and structural_ok and pending_empty)
    rep = dict(
        snapshot=os.path.relpath(snap, N12).replace("\\", "/"), snapshot_sha256=snap_sha,
        n_atomic_manifest=n_atomic, jsonl_rows=len(rows), duplicate_idx=dup,
        idx_set_exact=bool(idx_ok), certified_with_positive_gap=cert,
        n_problems=len(problems), problems=problems[:8],
        per_N=per_n, per_used_scale=per_scale,
        summary_snapshot_bound=bool(summary_bound),
        partition_exact=partition_ok,
        prunes_all_reproduced=prunes_ok,
        prune3=s.get("prune3_vs_radical"),
        pending_nonempty_boxes=len(st.get("pending", [])),
        summary_verdict=ar.get("verdict"),
        summary_global_certificate=ar.get("global_certificate"),
        recomputed_global_certificate=real_global,
        scope_note=("post-hoc INTERFACE check (bindings / index completeness / gap "
                    "arithmetic / explicit scale) -- it is NOT an independent proof of the "
                    "covering radius; the independent partition check is the Lead's prefix "
                    "tree (evidence/merged-partial-prefix-partition.json)"),
        checks=dict(
            rows_bound_to_current_sources=bool(not problems),
            idx_set_exactly_range=bool(idx_ok),
            no_duplicate_idx=bool(dup == 0),
            all_certified_strict_positive_gap=bool(cert == n_atomic),
            ckey_rederived_matches=bool(not any("ckey" in p[1] for p in problems)),
            summary_numbers_match=(ar.get("certified") == cert and
                                   ar.get("replayed") == len(rows)),
            summary_global_not_overclaimed=bool(
                bool(ar.get("global_certificate")) == real_global),
        ),
    )
    rep["all_pass"] = all(rep["checks"].values())
    dest = os.path.join(MEM, "out", "verify-results-check-%s.json" % stem)
    with open(dest, "w", encoding="utf-8") as f:
        json.dump(rep, f, indent=1)
    print(json.dumps(rep, indent=1)[:2600])
    print("check ->", dest)
    if not rep["all_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()