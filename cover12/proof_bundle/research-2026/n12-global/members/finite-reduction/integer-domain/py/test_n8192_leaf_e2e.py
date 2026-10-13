#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""test_n8192_leaf_e2e.py -- end-to-end control for PER-LEAF atom-count dispatch.

Builds a synthetic snapshot containing the two-hub saved instance as a single leaf and
verifies through the real verifier CLI that

  E1  leaf.get('atomN') == 8192 dispatches to upper-audit's integer_kernel_n.py with the
      explicit canonical-8192 vector file, and reproduces the saved FastAtoms numbers
      exactly (boxes 16911, leaves 8334, outside 122, max 130169221852,
      total 1301696319067, gap 4100547, atoms 18886);
  E2  the row records n=8192 plus the 8192 units hash and the N-kernel hash, i.e. the
      binding is per leaf, not global;
  E3  the 2048 entry in the cache is NOT used for this 8192 leaf (from_cache is false and
      the 2048-vs-8192 content keys differ), so a 2048 verdict can never be misapplied;
  E4  the same H/W relabelled atomN=2048 produces a DIFFERENT content key (and a different
      verdict), demonstrating that the dispatch is driven by the leaf, not by the data;
  E5  an unknown atomN (e.g. 4096) is REJECTED with a non-zero exit instead of silently
      generating a vector set.
"""
import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
OUT = os.path.join(MEM, "out")
sys.path.insert(0, HERE)
import verify_manifest as V

VEC8192 = os.path.join(N12, "members", "upper-audit", "integer-atomic", "evidence",
                       "canonical-unit-vectors-8192.json")
N_SCAN = os.path.join(N12, "members", "two-hub", "proposal-repair", "N_scan.json")
EXPECT = dict(status="certified", boxes=16911, leaves=8334, outside=122,
              max_capture=130169221852, demand=1301696319067, gap=4100547, n_atoms=18886)
# cache-hit rows legitimately omit 'outside' (it is a traversal counter, not a verdict);
# the fresh path must record it, which E3c checks with the full dict.
EXPECT_CORE = {k: v for k, v in EXPECT.items() if k != "outside"}


def run(stem, snap_path, extra=()):
    return subprocess.run([sys.executable, "-B", os.path.join(HERE, "verify_manifest.py"),
                           "--snapshot", snap_path, "--out-stem", stem, *extra],
                          cwd=MEM, capture_output=True, text=True)


def main():
    rep, checks = {}, {}
    d = json.loads(open(N_SCAN, encoding="utf-8").read())
    H, W = d["H"], d["weights_o6"]

    def snap_with(atomN):
        return {
            "status": "partial (synthetic control)",
            "domain": [[str(x) for x in r] for r in V.ROOT],
            "counts": {"infeasible": 0, "certified": 1, "split": 0, "processed": 1},
            "pending": [],
            "leaves": [{"type": "atomic", "H": H, "proposal": {"weights": W},
                        **({"atomN": atomN} if atomN is not None else {})}],
        }

    p8192 = os.path.join(OUT, "synthetic-n8192.json")
    open(p8192, "w", encoding="utf-8").write(json.dumps(snap_with(8192)))
    r = run("syn-n8192", p8192, ("--cache", os.path.join(OUT, "certified-cache.jsonl")))
    rows = [json.loads(l) for l in open(os.path.join(OUT, "verify-syn-n8192.jsonl"),
                                        encoding="utf-8") if l.strip()]
    row = rows[0]
    checks["E1_n8192_dispatch_reproduces_saved"] = all(
        row.get(k) == v for k, v in EXPECT_CORE.items())
    checks["E1b_fresh_path_records_outside"] = bool(
        row.get("outside") == EXPECT["outside"] or row.get("from_cache") is True)
    vec_sha = hashlib.sha256(open(VEC8192, "rb").read()).hexdigest()
    kn_sha = hashlib.sha256(open(V.KERNEL_N, "rb").read()).hexdigest()
    checks["E2_row_binds_n8192_and_its_hashes"] = bool(
        row.get("n") == 8192 and row.get("units") == vec_sha and
        row.get("kernel_n") == kn_sha and row.get("kernel") == V.hashlib.sha256(
            open(V.KERNEL, "rb").read()).hexdigest())
    # E3: the 2048 cache can never serve this 8192 leaf.
    #   E3a every cache entry matching this content is an 8192 entry;
    #   E3b the 2048 and 8192 content keys differ;
    #   E3c DIRECT non-misapplication test: build a cache holding ONLY a 2048-key entry for
    #       exactly this H/W and run the 8192 leaf against it -> it must not be used.
    vec2048 = hashlib.sha256(open(V.vectors_path(2048), "rb").read()).hexdigest()
    kn_sha = hashlib.sha256(open(V.KERNEL_N, "rb").read()).hexdigest()
    base_sha = hashlib.sha256(open(V.KERNEL, "rb").read()).hexdigest()
    ck8192 = row["ckey"]
    ck2048 = V.content_key(H, W, 2048, vec2048, base_sha, kn_sha, 26)
    cache_path = os.path.join(OUT, "certified-cache.jsonl")
    cache_all = [json.loads(l) for l in open(cache_path, encoding="utf-8") if l.strip()]
    matching = [x for x in cache_all if x.get("ckey") == ck8192]
    # the certificate that must never be reachable from this 8192 leaf is the 2048-key one
    checks["E3a_no_2048_key_entry_for_this_content"] = bool(
        all(x.get("ckey") != ck2048 for x in cache_all))
    checks["E3a_matching_cache_entries_are_8192"] = bool(
        all(m.get("n") == 8192 and
            m.get("units") == hashlib.sha256(open(VEC8192, "rb").read()).hexdigest()
            for m in matching))
    checks["E3b_content_keys_differ_across_N"] = (ck8192 != ck2048)
    only2048 = os.path.join(OUT, "cache-2048key-only.jsonl")
    with open(only2048, "w", encoding="utf-8") as f:
        f.write(json.dumps(dict(ckey=ck2048, status="certified", n=2048, units=vec2048,
                                kernel=base_sha, kernel_n=kn_sha, scale=26, n_atoms=1, total=1,
                                gap=1, origin_stem="fabricated-2048", origin_idx=0,
                                origin_snapshot="fabricated")) + "\n")
    run("syn-n8192-nocache", p8192, ("--cache", only2048))
    row3 = [json.loads(l) for l in
            open(os.path.join(OUT, "verify-syn-n8192-nocache.jsonl"),
                 encoding="utf-8") if l.strip()][0]
    checks["E3c_2048only_cache_not_used_for_8192"] = bool(
        row3.get("from_cache") is False and
        all(row3.get(k) == v for k, v in EXPECT.items()))
    rep["E3"] = dict(ckey_8192_prefix=ck8192[:34], ckey_2048_prefix=ck2048[:34],
                     n_matching_cache_entries=len(matching),
                     n8192_verdict_origin=(matching[0].get("origin_stem") if matching else None),
                     with_2048only_cache=dict(from_cache=row3.get("from_cache"),
                                              status=row3.get("status"),
                                              boxes=row3.get("boxes")))

    # E4: same H/W labelled 2048 -> different key and different verdict
    p2048 = os.path.join(OUT, "synthetic-n2048.json")
    open(p2048, "w", encoding="utf-8").write(json.dumps(snap_with(2048)))
    run("syn-n2048", p2048, ("--cache", os.path.join(OUT, "certified-cache.jsonl")))
    row2 = [json.loads(l) for l in open(os.path.join(OUT, "verify-syn-n2048.jsonl"),
                                        encoding="utf-8") if l.strip()][0]
    rep["E4"] = dict(status_2048=row2.get("status"), boxes_2048=row2.get("boxes"),
                     gap_2048=row2.get("gap"), n_2048=row2.get("n"))
    checks["E4_same_data_other_N_differs"] = bool(
        row2.get("n") == 2048 and row2.get("ckey") != ck8192 and
        not (row2.get("status") == "certified" and row2.get("boxes") == EXPECT["boxes"]))

    # E5: unknown N rejected, non-zero exit, no vector generation
    p4096 = os.path.join(OUT, "synthetic-n4096.json")
    open(p4096, "w", encoding="utf-8").write(json.dumps(snap_with(4096)))
    r5 = run("syn-n4096", p4096)
    checks["E5_unknown_N_rejected"] = bool(
        r5.returncode != 0 and "unknown" in (r5.stdout + r5.stderr).lower())
    rep["E5"] = dict(returncode=r5.returncode,
                     message=(r5.stderr or r5.stdout).strip().splitlines()[-1][:120]
                     if (r5.stderr or r5.stdout).strip() else "")

    rep["checks"] = checks
    rep["all_pass"] = all(checks.values())
    with open(os.path.join(OUT, "n8192-leaf-e2e-controls.json"), "w",
              encoding="utf-8") as f:
        json.dump(rep, f, indent=1)
    print(json.dumps(rep, indent=1)[:2000])
    if not rep["all_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()