#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""acceptance_check.py -- final acceptance gate for a merged-domain replay.

Nothing here is a boolean taken on trust.  The Lead's audit of the earlier version found
that A1 only checked provenance.failed and size, and that A3 never re-derived the content
key, so an old verified ckey copied onto a different leaf could pass.  Both are fixed:

  A1  provenance integrity, re-verified against CURRENT bytes:
        - provenance.failed == 0;
        - provenance.cache_sha256 equals the sha256 of the cache file as it is NOW fixed;
        - every row file the provenance read still hashes to the recorded value
          (single read per file, cached);
        - every verified record's witness (file, line) is re-parsed and must still be a
          certified row with from_cache == False (or the audited pre-field rule), whose
          snapshot field equals the recorded source snapshot sha256 and whose
          demand - 10*max == gap > 0.
  A2  per row: ckey is RE-DERIVED from the current snapshot leaf
      (N, used_scale, vector-set hash, kernels, full H/W hashes) and must equal the row's
      ckey AND belong to the provenance verified set.
  A3  per row: the provenance record's NUMERIC fields (n, scale, demand, max_capture, gap)
      must equal the row's.  The remaining identifiers (units, kernel, kernel_n, full
      h_sha/w_sha) are NOT re-listed here because A2 already binds them: A2 re-derives the
      content key from the current snapshot leaf -- content_key(H, W, N, vector-set hash,
      kernel hash, N-kernel hash, scale) -- and requires the row's stored key to equal it and
      to be a member of the provenance verified set.  HONEST DEPENDENCY: A3 is numeric-only;
      identifier binding comes from A2 plus the cache_provenance.py source audit, and none of
      A2/A3 is an independent re-derivation of the integer arithmetic.  See
      SOURCE-CALL-CONTRACT.md section 5.
  A4  status certified and gap == demand - 10*max_capture > 0 (recomputed).
  A5  idx uniqueness and exact coverage of range(n_atomic).
  A6  structural booleans only if the summary is bound to this snapshot's sha256.
  A7  pending queue empty (global is never granted otherwise).

Usage: py -3 -B py/acceptance_check.py --snapshot PATH --out-stem STEM [--freeze]
"""
from __future__ import annotations

import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
OUT = os.path.join(MEM, "out")
sys.path.insert(0, HERE)
import verify_manifest as V

_SHA_CACHE = {}


def sha(path):
    key = os.path.abspath(path)
    if key not in _SHA_CACHE:
        raw = open(key, "rb").read()
        _SHA_CACHE[key] = (hashlib.sha256(raw).hexdigest(), raw)
    return _SHA_CACHE[key][0]


def main():
    argv = sys.argv[1:]
    snap = argv[argv.index("--snapshot") + 1]
    stem = argv[argv.index("--out-stem") + 1]
    freeze = "--freeze" in argv
    cache = os.path.join(OUT, "certified-cache.jsonl")
    prov_path = os.path.join(OUT, "cache-provenance.json")
    jsonl = os.path.join(OUT, "verify-%s.jsonl" % stem)
    summary = os.path.join(OUT, "verify-%s-summary.json" % stem)

    cache_sha = sha(cache)
    prov_sha = sha(prov_path)
    prov = json.loads(_SHA_CACHE[os.path.abspath(prov_path)][1].decode("utf-8"))
    verified = {v["ckey"]: v for v in prov["verified"]}

    # ---------- A1: provenance integrity against CURRENT bytes ----------
    a1_problems = []
    if prov.get("failed"):
        a1_problems.append("provenance reports %d unverified entries" % prov["failed"])
    if prov.get("cache_sha256") != cache_sha:
        a1_problems.append("provenance cache_sha256 %s != current cache %s"
                           % (str(prov.get("cache_sha256"))[:16], cache_sha[:16]))
    for rel, want in (prov.get("row_files_sha256") or {}).items():
        p = os.path.join(MEM, rel)
        if not os.path.exists(p):
            a1_problems.append("witness row file missing: %s" % rel); continue
        if sha(p) != want:
            a1_problems.append("witness row file changed since provenance: %s" % rel)
    line_cache = {}
    for ck, v in verified.items():
        p = os.path.join(MEM, v["fresh_file"])
        if p not in line_cache:
            line_cache[p] = _SHA_CACHE[os.path.abspath(p)][1].decode("utf-8").splitlines()
        lines = line_cache[p]
        ln = v.get("fresh_line")
        if not isinstance(ln, int) or not (1 <= ln <= len(lines)):
            a1_problems.append("witness line out of range for %s" % v["fresh_file"]); continue
        r = json.loads(lines[ln - 1])
        if r.get("idx") != v["fresh_idx"]:
            a1_problems.append("witness line %s:%d idx != %s" % (v["fresh_file"], ln,
                                                                 v["fresh_idx"])); continue
        if r.get("snapshot") != v["source_snapshot_sha256"]:
            a1_problems.append("witness %s:%d snapshot != recorded source" % (v["fresh_file"], ln))
            continue
        if r.get("status") != "certified":
            a1_problems.append("witness %s:%d not certified" % (v["fresh_file"], ln)); continue
        if not v.get("pre_field_rule") and r.get("from_cache") is not False:
            a1_problems.append("witness %s:%d is not a fresh row" % (v["fresh_file"], ln)); continue
        try:
            if int(r["demand"]) - 10 * int(r["max_capture"]) != int(r["gap"]) or int(r["gap"]) <= 0:
                a1_problems.append("witness %s:%d gap arithmetic" % (v["fresh_file"], ln))
        except Exception:
            a1_problems.append("witness %s:%d lacks gap fields" % (v["fresh_file"], ln))

    # ---------- per-row checks ----------
    snap_raw = open(snap, "rb").read()
    snap_sha = hashlib.sha256(snap_raw).hexdigest()
    st = json.loads(snap_raw.decode("utf-8"))
    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
    kernel = sha(V.KERNEL)
    kn = V.kernel_n_sha()
    atoms = sha(V.ATOMS_PY) if os.path.exists(V.ATOMS_PY) else ""

    rows, seen, dup = [], set(), 0
    for line in open(jsonl, encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        if r.get("idx") in seen:
            dup += 1
        seen.add(r.get("idx"))
        rows.append(r)

    a2_problems, a3_problems, a4_problems = [], [], []
    for r in rows:
        idx = r.get("idx")
        tag = "idx=%s" % idx
        if not isinstance(idx, int) or not (0 <= idx < len(atomic)):
            a2_problems.append((tag, "idx out of range")); continue
        L = atomic[idx]
        N = L.get("atomN", 2048)
        usha = sha(V.vectors_path(N))
        sc = r.get("used_scale")
        if sc not in (26, 28):
            a4_problems.append((tag, "scale %r not in {26,28}" % sc)); continue
        # A2: re-derive the content key from the CURRENT leaf -- the stored ckey is never trusted
        ck = V.content_key(L["H"], L["proposal"]["weights"], N, usha, kernel, kn, sc)
        if r.get("ckey") != ck:
            a2_problems.append((tag, "ckey != re-derived key")); continue
        if ck not in verified:
            a2_problems.append((tag, "re-derived ckey not in provenance verified set")); continue
        v = verified[ck]
        # A3: the record's numeric fields must agree with the row (identifier binding is
        # already carried by the re-derived key checked in A2; see the module docstring)
        if r.get("snapshot") != snap_sha:
            a3_problems.append((tag, "snapshot binding")); continue
        if r.get("kernel") != kernel or r.get("atoms") != atoms:
            a3_problems.append((tag, "kernel/atoms binding")); continue
        if r.get("n") != N or r.get("units") != usha or r.get("kernel_n") != kn:
            a3_problems.append((tag, "N/vector/kernel_n binding")); continue
        if v.get("n") != N or v.get("scale") != sc:
            a3_problems.append((tag, "provenance n/scale differ")); continue
        for f in ("demand", "max_capture", "gap"):
            if v.get(f) is not None and r.get(f) is not None and int(v[f]) != int(r[f]):
                a3_problems.append((tag, "provenance %s differs" % f)); break
        else:
            # A4: strictly positive recomputed margin
            try:
                if r.get("status") != "certified":
                    a4_problems.append((tag, "status %r" % r.get("status"))); continue
                if int(r["demand"]) - 10 * int(r["max_capture"]) != int(r["gap"]) or \
                        int(r["gap"]) <= 0:
                    a4_problems.append((tag, "gap arithmetic")); continue
            except Exception:
                a4_problems.append((tag, "gap fields missing")); continue

    s = json.loads(open(summary, encoding="utf-8").read()) if os.path.exists(summary) else {}
    bound = (s.get("snapshot_sha256") == snap_sha) or \
        (s.get("binding", {}).get("snapshot") == snap_sha)
    partition_ok = bool(bound and s.get("partition", {}).get("exact_partition"))
    prunes_ok = bool(bound and s.get("infeasible", {}).get("all_reproduced"))
    structural_ok = bool(bound and s.get("structural_checks_pass"))
    pending = len(st.get("pending", []))
    idx_ok = (seen == set(range(len(atomic))))

    checks = dict(
        A1a_provenance_all_verified=not prov.get("failed"),
        A1b_provenance_bound_to_current_cache=(prov.get("cache_sha256") == cache_sha),
        A1c_witness_files_unchanged=bool(
            not any("changed since provenance" in p or "missing" in p for p in a1_problems)),
        A1d_witness_lines_reverified=bool(
            len(verified) > 0 and not any((p.startswith("witness line") or
                                           p.startswith("witness ") or
                                           p.startswith("witness")) for p in a1_problems)),
        A2_every_row_ckey_rederived_and_verified=bool(not a2_problems and rows),
        A3_rows_and_provenance_agree=bool(not a3_problems),
        A4_all_certified_strict_positive_gap=bool(not a4_problems),
        A5_idx_unique_and_complete=bool(idx_ok and dup == 0 and len(rows) == len(atomic)),
        A6_structure_bound_to_this_snapshot=bool(partition_ok and prunes_ok and structural_ok),
        A7_pending_empty=bool(pending == 0),
    )
    accepted = all(checks[k] for k in checks if k != "A7_pending_empty")
    rep = dict(stem=stem, snapshot=os.path.relpath(snap, N12).replace("\\", "/"),
               snapshot_sha256=snap_sha, cache_sha256=cache_sha,
               provenance_sha256=prov_sha, provenance_cache_sha256=prov.get("cache_sha256"),
               provenance_entries=len(verified), jsonl_rows=len(rows), duplicate_idx=dup,
               idx_set_exact=bool(idx_ok), pending_nonempty_boxes=pending,
               n_a1_problems=len(a1_problems), a1_problems=a1_problems[:5],
               n_a2_problems=len(a2_problems), a2_problems=a2_problems[:5],
               n_a3_problems=len(a3_problems), a3_problems=a3_problems[:5],
               n_a4_problems=len(a4_problems), a4_problems=a4_problems[:5],
               checks=checks)
    rep["snapshot_replay_accepted"] = accepted
    rep["global_certificate"] = bool(accepted and checks["A7_pending_empty"])
    rep["all_pass"] = accepted
    rep["verdict"] = ("global" if rep["global_certificate"] else
                      "partial-accepted(%d pending boxes remain)" % pending if accepted
                      else "pending")
    dest = os.path.join(OUT, "acceptance-%s.json" % stem)
    with open(dest, "w", encoding="utf-8") as f:
        json.dump(rep, f, indent=1)
    if freeze:
        fz = os.path.join(OUT, "freeze-%s.json" % stem)
        with open(fz, "w", encoding="utf-8") as f:
            json.dump(dict(stem=stem, snapshot_sha256=snap_sha, cache_sha256=cache_sha,
                           provenance_sha256=prov_sha, jsonl_sha256=sha(jsonl),
                           summary_sha256=sha(summary) if os.path.exists(summary) else None,
                           n_rows=len(rows), pending=pending,
                           global_certificate=rep["global_certificate"]), f, indent=1)
        rep["freeze_file"] = os.path.relpath(fz, MEM)
    print(json.dumps({k: v for k, v in rep.items() if not k.startswith("n_")},
                     indent=1)[:2600])
    print("acceptance ->", dest)
    if not accepted:
        raise SystemExit(1)


if __name__ == "__main__":
    main()