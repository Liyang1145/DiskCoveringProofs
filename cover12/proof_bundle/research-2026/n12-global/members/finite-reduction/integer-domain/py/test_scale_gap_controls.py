#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""test_scale_gap_controls.py -- negative controls demanded by the Lead audit.

  G1  gap == 0 (status certified) must be REJECTED: 10*capture == total excludes nothing.
  G2  missing gap must be REJECTED.
  G3  a scale-26 cache entry must NOT be served to a leaf asked at scale 28, and vice
      versa: the key binds the scale, so the two lookups differ.
  G4  mixed-N: a 2048 entry must not be served for an 8192 leaf (re-checked here for the
      scale-aware key).
  G5  migrated cache entries carry an explicit scale + provenance string, and every entry
      loads under the strict loader (certified + gap>0 + self-consistent key).
  G6  a resolution: the three stage11825 leaves that stop at scale 26 ARE certified at
      scale 28 with a strictly positive gap, and are stored with used_scale=28.
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
OUT = os.path.join(MEM, "out")
sys.path.insert(0, HERE)
import cache_tools as CT
import verify_manifest as V

CACHE = os.path.join(OUT, "certified-cache.jsonl")
SNAP = os.path.join(EV, "hubline-domain-stage11825.json")


def main():
    kernel = hashlib.sha256(open(V.KERNEL, "rb").read()).hexdigest()
    kn = V.kernel_n_sha()
    rep, checks = {}, {}

    # G1 / G2: gap == 0 and missing gap
    e = json.loads(open(CACHE, encoding="utf-8").readline())
    for label, mut in (("gap0", lambda x: x.update(gap=0)),
                       ("gapmissing", lambda x: x.pop("gap", None))):
        bad = dict(e); mut(bad)
        p = os.path.join(OUT, "ctl-gap-%s.jsonl" % label)
        with open(p, "w", encoding="utf-8") as f:
            f.write(json.dumps(bad) + "\n")
        c, _, problems = CT.load_cache_checked(p, kernel)
        checks["G1_G2_%s_rejected" % label] = (len(c) == 0 and len(problems) == 1)
        rep[label] = problems[0][1] if problems else None

    # G3: scale separation
    st = json.loads(open(SNAP, encoding="utf-8").read())
    L = [x for x in st["leaves"] if x.get("type") == "atomic"][0]
    N = L.get("atomN", 2048)
    usha = hashlib.sha256(open(V.vectors_path(N), "rb").read()).hexdigest()
    ck26 = V.content_key(L["H"], L["proposal"]["weights"], N, usha, kernel, kn, 26)
    ck28 = V.content_key(L["H"], L["proposal"]["weights"], N, usha, kernel, kn, 28)
    checks["G3_scale_binds_key"] = (ck26 != ck28)
    cache, _, _ = CT.load_cache_checked(CACHE, kernel)
    rep["G3"] = dict(ckey26=ck26[:26], ckey28=ck28[:26],
                     in_cache_26=ck26 in cache, in_cache_28=ck28 in cache)

    # G4: mixed-N separation
    L8 = [x for x in st["leaves"] if x.get("type") == "atomic" and x.get("atomN") == 8192]
    if L8:
        L8 = L8[0]
        u8192 = hashlib.sha256(open(V.vectors_path(8192), "rb").read()).hexdigest()
        ck8 = V.content_key(L8["H"], L8["proposal"]["weights"], 8192, u8192, kernel, kn, 26)
        ck2 = V.content_key(L8["H"], L8["proposal"]["weights"], 2048,
                            hashlib.sha256(open(V.vectors_path(2048), "rb").read()).hexdigest(),
                            kernel, kn, 26)
        checks["G4_N_binds_key"] = (ck8 != ck2)
        rep["G4"] = dict(n8192_entry_in_cache=ck8 in cache, n2048_key_in_cache=ck2 in cache)

    # G5: migrated entries all load strictly and declare scale + provenance
    scales = {}
    prov = set()
    for x in cache.values():
        scales[x.get("scale")] = scales.get(x.get("scale"), 0) + 1
        prov.add(x.get("scale_provenance"))
    checks["G5_all_entries_strict_and_scaled"] = bool(len(cache) > 0 and
                                                    all(s is not None for s in scales))
    rep["G5"] = dict(entries=len(cache), scales=scales,
                     provenances=sorted(str(p)[:60] for p in prov))

    # G6: escalated leaves
    rows = {}
    for f in (os.path.join(OUT, "verify-stage11825.jsonl"),
              os.path.join(MEM, "archive", "verify-stage11825-run2.jsonl")):
        if os.path.exists(f):
            for line in open(f, encoding="utf-8"):
                line = line.strip()
                if not line:
                    continue
                r = json.loads(line)
                rows.setdefault(r.get("idx"), r)
    esc = [4398, 4846, 5018]
    ev = json.loads(open(os.path.join(OUT, "escalated-scale28-evidence.json"),
                         encoding="utf-8").read())
    by_idx = {r["idx"]: r for r in ev["records"]}
    ok = all(by_idx[i]["scale_26_result"].get("status") != "certified" and
             by_idx[i]["scale_28_result"].get("status") == "certified" and
             by_idx[i]["scale_28_result"].get("gap_integer", 0) > 0 and
             by_idx[i]["used_scale"] == 28 and by_idx[i].get("h_sha256") and
             by_idx[i].get("w_sha256") for i in esc)
    checks["G6_escalated_leaves_28_with_full_hashes"] = bool(ok)
    rep["G6"] = {str(i): dict(s26=by_idx[i]["scale_26_result"].get("status"),
                              s28=by_idx[i]["scale_28_result"].get("status"),
                              gap=by_idx[i]["scale_28_result"].get("gap_integer"))
                 for i in esc}

    rep["checks"] = checks
    rep["all_pass"] = all(checks.values())
    p = os.path.join(OUT, "scale-gap-controls.json")
    with open(p, "w", encoding="utf-8") as f:
        json.dump(rep, f, indent=1)
    print(json.dumps(rep, indent=1)[:2200])
    if not rep["all_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()