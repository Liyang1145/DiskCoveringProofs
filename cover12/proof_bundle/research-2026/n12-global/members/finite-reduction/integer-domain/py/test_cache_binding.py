#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""test_cache_binding.py -- negative controls for the content-keyed cache.

N1  a cache line with a FOREIGN kernel hash is ignored (not a hit);
N2  a cache line with a FOREIGN units hash is ignored;
N3  changing the leaf CONTENT changes the content key => no hit (must recompute);
N4  permuting two leaves in a synthetic snapshot: hits follow CONTENT, and the resulting
    rows bind the CURRENT snapshot hash and the CURRENT index (an old index is never
    inherited) -- this is the exact failure the "don't trust old idx" rule forbids;
N5  the cache is not consulted without --cache (a run with no --cache does fresh work).
"""
import hashlib
import json
import os
import subprocess
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
SNAP = os.path.join(EV, "hubline-domain-stage2200.json")
CACHE = os.path.join(MEM, "out", "certified-cache.jsonl")
OUTDIR = os.path.join(MEM, "out")
sys.path.insert(0, HERE)
import verify_manifest as V

rep, checks = {}, {}


def main():
    kernel = hashlib.sha256(open(V.KERNEL, "rb").read()).hexdigest()
    units = hashlib.sha256(open(V.UNITS, "rb").read()).hexdigest()

    # N1 / N2: foreign / tampered cache lines cannot be used
    lines = [l for l in open(CACHE, encoding="utf-8") if l.strip()]
    fake = os.path.join(OUTDIR, "cache-fake-kernel.jsonl")
    with open(fake, "w", encoding="utf-8") as f:
        r = json.loads(lines[0]); r["kernel"] = "0" * 64; f.write(json.dumps(r) + "\n")
        f.write(lines[1])
    c, foreign, legacy = V.load_cache(fake, kernel)
    checks["N1_foreign_kernel_ignored"] = (foreign == 1 and len(c) == 1)
    fake2 = os.path.join(OUTDIR, "cache-fake-units.jsonl")
    with open(fake2, "w", encoding="utf-8") as f:
        r = json.loads(lines[0]); r["units"] = "0" * 64; f.write(json.dumps(r) + "\n")
        f.write(lines[1])
    c2, foreign2, tampered2 = V.load_cache(fake2, kernel)
    # the tampered line is now REJECTED at load time (its stored ckey no longer matches the
    # key re-derived from its own declared ingredients), so it can never be looked up
    checks["N2_tampered_units_rejected_at_load"] = bool(
        tampered2 == 1 and
        all(x["units"] != "0" * 64 for x in c2.values()))

    # N3: content perturbation changes the key (key now also binds N + units + kernels)
    usha = hashlib.sha256(open(V.vectors_path(2048), "rb").read()).hexdigest()
    st = json.loads(open(SNAP, encoding="utf-8").read())
    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
    H0, W0 = atomic[0]["H"], atomic[0]["proposal"]["weights"]
    base = V.hashlib.sha256(open(V.KERNEL, "rb").read()).hexdigest()
    kn = V.kernel_n_sha()
    ck0 = V.content_key(H0, W0, 2048, usha, base, kn, 26)
    Hp = [[str(F(x[0]) + F(1, 10 ** 9)), x[1]] for x in H0]
    ckp = V.content_key(Hp, W0, 2048, usha, base, kn, 26)
    Wp = [[str(F(w) + F(1, 10 ** 9)) for w in row] for row in W0]
    ckw = V.content_key(H0, Wp, 2048, usha, base, kn, 26)
    ck8192 = V.content_key(H0, W0, 8192,
                           hashlib.sha256(open(V.vectors_path(8192), "rb").read()).hexdigest(),
                           base, kn, 26)
    cache, _, _ = V.load_cache(CACHE, kernel)
    checks["N3_content_change_misses_cache"] = (ck0 in cache and ckp not in cache and
                                                ckw not in cache)
    checks["N3b_N_binding_changes_key"] = (ck8192 not in cache and ck8192 != ck0)

    # N4: permuted synthetic snapshot -- hits follow content, rows bind CURRENT idx+snapshot
    i, j = 0, 5
    leaves = [dict(L) for L in st["leaves"]]
    ai = next(k for k, L in enumerate(leaves) if L.get("type") == "atomic")
    # swap the CONTENT of two atomic leaves while keeping their positions
    idxs = [k for k, L in enumerate(leaves) if L.get("type") == "atomic"]
    a, b = idxs[i], idxs[j]
    leaves[a], leaves[b] = dict(leaves[b]), dict(leaves[a])
    syn = dict(st)
    syn["leaves"] = leaves
    syn_path = os.path.join(OUTDIR, "synthetic-permuted-snapshot.json")
    with open(syn_path, "w", encoding="utf-8") as f:
        json.dump(syn, f)
    stem = "synthetic-permuted"
    subprocess.run([sys.executable, "-B", os.path.join(HERE, "verify_manifest.py"),
                    "--snapshot", syn_path, "--out-stem", stem,
                    "--cache", CACHE],
                   cwd=MEM, capture_output=True, text=True)
    rows = [json.loads(l) for l in open(os.path.join(OUTDIR, "verify-%s.jsonl" % stem),
                                        encoding="utf-8") if l.strip()]
    by_idx = {r["idx"]: r for r in rows}
    syn_sha = hashlib.sha256(open(syn_path, "rb").read()).hexdigest()
    orig_ck_a = V.content_key(atomic[j]["H"], atomic[j]["proposal"]["weights"],
                             2048, usha, base, kn, 26)  # content now at position a
    # the row at position a must carry content that ORIGINATED at index j of the real snapshot
    row_a = by_idx[i]
    hit_a = cache.get(row_a["ckey"])
    # the hit must be recorded with an origin (any index of the manifest the cache was
    # built from) and the row's key must equal the key of the content now sitting at
    # position a -- i.e. the hit follows CONTENT, not the current index
    checks["N4a_hit_follows_content_not_index"] = bool(
        row_a["from_cache"] and hit_a is not None and
        hit_a.get("origin_idx") is not None and row_a["ckey"] == orig_ck_a and
        row_a["ckey"] != V.content_key(atomic[i]["H"], atomic[i]["proposal"]["weights"],
                                       2048, usha, base, kn, 26))
    checks["N4a2_origin_differs_from_current_index"] = bool(
        hit_a is not None and hit_a.get("origin_idx") != row_a["idx"])
    checks["N4b_row_binds_current_snapshot"] = all(r["snapshot"] == syn_sha for r in rows)
    checks["N4c_row_binds_current_index"] = (set(by_idx) == set(range(len(atomic))))
    rep["N4"] = dict(row_a_idx=row_a["idx"], origin_idx=hit_a and hit_a.get("origin_idx"),
                     from_cache=row_a["from_cache"],
                     current_snapshot=row_a["snapshot"][:16], syn_sha=syn_sha[:16],
                     synthetic_partition_expected_to_fail=True,
                     note="the synthetic permutation does not tile the root by design; "
                          "only the cache-attribution logic is under test here")

    # N5: no --cache => no cache consulted
    subprocess.run([sys.executable, "-B", os.path.join(HERE, "verify_manifest.py"),
                    "--snapshot", SNAP, "--out-stem", "nocache-ctl", "--max", "2"],
                   cwd=MEM, capture_output=True, text=True)
    r5 = json.loads(open(os.path.join(OUTDIR, "verify-nocache-ctl-summary.json"),
                         encoding="utf-8").read())
    checks["N5_no_cache_does_fresh_work"] = (r5["atomic_replay"]["certified_from_cache"] == 0
                                            and r5["atomic_replay"]["replayed"] >= 1)

    rep["checks"] = checks
    rep["all_pass"] = all(checks.values())
    with open(os.path.join(OUTDIR, "cache-binding-controls.json"), "w",
              encoding="utf-8") as f:
        json.dump(rep, f, indent=1)
    print(json.dumps(rep, indent=1)[:2200])
    if not rep["all_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()