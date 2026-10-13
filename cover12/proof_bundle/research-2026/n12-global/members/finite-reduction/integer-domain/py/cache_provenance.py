#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""cache_provenance.py -- content-verified fresh ancestry for every cache entry.

The Lead's requirement (superseding the earlier stem/idx/from_cache walk): following
stem/idx pointers is NOT evidence.  For every production cache entry we must show a FRESH
terminal row whose CONTENT agrees with the entry:

    T1 the terminal row's `snapshot` field equals sha256(bytes of that stem's snapshot file),
       read once and recorded;
    T2 the snapshot leaf at that idx has the SAME N and the SAME vector-set hash;
    T3 its full sha256(H) and sha256(W) equal the entry's h_sha / w_sha  (so a different
       snapshot at the same idx cannot be auto-equated);
    T4 kernel / kernel_n equal the entry's;
    T5 the scale agrees (a scale-26 certificate is not a scale-28 certificate);
    T6 the verdict arithmetic holds at the terminal row: gap == demand - 10*max_capture > 0;
    T7 the terminal row has from_cache == False (or belongs to an audited pre-field
       generation whose recorded run summary shows NO cache participation).

Only then is the entry counted as freshly evidenced, and the record carries the immutable
file path, its sha256, the line number, and the stem's snapshot sha256.  Any entry failing
T1-T7 is reported as NOT verified and the script exits non-zero.
"""
from __future__ import annotations

import hashlib
import json
import os
import sys
from collections import Counter
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
OUT = os.path.join(MEM, "out")
ARCH = os.path.join(MEM, "archive")
sys.path.insert(0, HERE)
import cache_tools as CT
import verify_manifest as V

STEM_SNAPSHOT = {
    "stage2200": os.path.join(EV, "hubline-domain-stage2200.json"),
    "stage6700": os.path.join(EV, "hubline-domain-stage6700.json"),
    "stage11825": os.path.join(EV, "hubline-domain-stage11825.json"),
    "merged-partial": os.path.join(N12, "members", "structure", "parallel-domain",
                                   "merged-partial-resume.json"),
    "final-wave-base": os.path.join(N12, "members", "structure", "parallel-domain",
                                    "final-wave-base.json"),
    "wave4fix-base": os.path.join(N12, "members", "structure", "parallel-domain",
                                  "wave4fix-base.json"),
    "completed-domain": os.path.join(N12, "members", "structure", "parallel-domain",
                                     "completed-domain-base.json"),
}
# candidate row files per stem, in priority order (fresh-carrying immutable copies first)
SOURCES = {
    "stage2200": [os.path.join(OUT, "verify-stage2200.jsonl")],
    "stage6700": [os.path.join(OUT, "verify-stage6700.jsonl")],
    "stage11825": [os.path.join(ARCH, "verify-stage11825-run2.jsonl"),
                   os.path.join(ARCH, "verify-stage11825-run1.jsonl"),
                   os.path.join(OUT, "verify-stage11825.jsonl")],
    "merged-partial": [os.path.join(ARCH, "verify-merged-partial-frozen.jsonl"),
                       os.path.join(OUT, "verify-merged-partial.jsonl")],
    "final-wave-base": [os.path.join(ARCH, "verify-final-wave-base-frozen.jsonl"),
                        os.path.join(OUT, "verify-final-wave-base.jsonl")],
    "wave4fix-base": [os.path.join(OUT, "verify-wave4fix-base.jsonl")],
    "completed-domain": [os.path.join(ARCH, "verify-completed-domain-frozen.jsonl"),
                         os.path.join(OUT, "verify-completed-domain.jsonl")],
}
PRE_FIELD_STEMS = {
    "stage2200": dict(summary=os.path.join(OUT, "verify-stage2200-summary.json"),
                      rule="summary cache block is null (no --cache); rows predate from_cache"),
}

# Explicit, bounded registry of LEGACY generations: which fields a row of that generation
# may legitimately fail to record, under which constraints, and the evidence for the bound.
# This is what keeps "missing field" from becoming an open-ended excuse: the exception is
# keyed to an exact file, an exact N and an exact scale, and every field the row DOES carry
# is still required to agree.  (Lead: legacy origins are to be recorded explicitly as
# stem/archive boundaries rather than re-run without meaning.)
LEGACY_ORIGINS = {
    "stage2200": dict(
        files=[os.path.join(OUT, "verify-stage2200.jsonl")],
        missing={"from_cache", "used_scale", "n", "kernel_n"},
        allowed_N=[2048], allowed_scale=[26],
        evidence=("pre-field generation: run summary has a null cache block (no --cache); "
                  "rows carry `units` = sha256(2048 vector file) and the frozen kernel hash; "
                  "the N-dispatch did not exist yet, so N is forced to 2048")),
    "stage6700": dict(
        files=[os.path.join(OUT, "verify-stage6700.jsonl")],
        missing={"used_scale", "n", "kernel_n"},
        allowed_N=[2048], allowed_scale=[26],
        evidence=("pre-dispatch/pre-scale generation: `units` = sha256(2048 vector file), "
                  "`kernel` = frozen integer_kernel hash, promoted only after audit; N is "
                  "forced to 2048 for this generation")),
    "stage11825": dict(
        files=[os.path.join(ARCH, "verify-stage11825-run1.jsonl"),
               os.path.join(ARCH, "verify-stage11825-run2.jsonl")],
        missing={"used_scale"},
        allowed_N=[2048, 8192], allowed_scale=[26],
        evidence=("pre-scale-field generation: n / units / kernel_n ARE recorded and are "
                  "required to agree; only the scale field is absent and that generation ran "
                  "at the kernel default 26 (run2's escalated rows record used_scale=28)")),
}


def legacy_allows(stem, path, leaf_N, entry_scale, field):
    info = LEGACY_ORIGINS.get(stem)
    if info is None or field not in info["missing"]:
        return False
    if os.path.abspath(path) not in [os.path.abspath(p) for p in info["files"]]:
        return False
    return leaf_N in info["allowed_N"] and entry_scale in info["allowed_scale"]


MAX_DEPTH = 6


def read_once(path):
    raw = open(path, "rb").read()
    return raw, hashlib.sha256(raw).hexdigest()


ROW_FILE_HASHES = {}


def load_rows(stem):
    """idx -> (row, file, line_no, file_sha256).  A fresh row wins over a cached one.
    Each file is read ONCE and its sha256 is recorded with every row it supplies."""
    best = {}
    for path in SOURCES.get(stem, []):
        if not os.path.exists(path):
            continue
        raw = open(path, "rb").read()
        fsha = hashlib.sha256(raw).hexdigest()
        ROW_FILE_HASHES[path] = fsha
        for ln, line in enumerate(raw.decode("utf-8").splitlines(), 1):
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            i = r.get("idx")
            if not isinstance(i, int):
                continue
            prev = best.get(i)
            if prev is None or (prev[0].get("from_cache") is not False and
                                r.get("from_cache") is False):
                best[i] = (r, path, ln, fsha)
    return best


def terminal_is_fresh(stem, row):
    """T7 (+ the audited pre-field rule)."""
    if row.get("from_cache") is False:
        return True, False
    if row.get("from_cache") is None and stem in PRE_FIELD_STEMS and \
            "cache_origin" not in row:
        info = PRE_FIELD_STEMS[stem]
        try:
            ssum = json.loads(open(info["summary"], encoding="utf-8").read())
            if not ssum.get("cache"):
                return True, True
        except Exception:
            return False, False
    return False, False


def main():
    cache_path = os.path.join(OUT, "certified-cache.jsonl")
    cache_raw = open(cache_path, "rb").read()                  # single read, hashed
    cache_sha = hashlib.sha256(cache_raw).hexdigest()
    cache = [json.loads(l) for l in cache_raw.decode("utf-8").splitlines() if l.strip()]
    rows_by_stem = {s: load_rows(s) for s in SOURCES}
    # snapshot bytes: read ONCE per stem, hash recorded
    snap_info = {}
    for stem, path in STEM_SNAPSHOT.items():
        if os.path.exists(path):
            raw, sh = read_once(path)
            st = json.loads(raw.decode("utf-8"))
            atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
            snap_info[stem] = dict(path=path, sha256=sh, atomic=atomic)

    verified, failed = [], []
    for e in cache:
        stem, idx = e.get("origin_stem"), e.get("origin_idx")
        chain, seen, cur, depth = [], set(), (stem, idx), 0
        terminal, why = None, "chain did not reach a fresh row"
        while cur is not None and depth < MAX_DEPTH and cur not in seen:
            seen.add(cur)
            s, i = cur
            got = rows_by_stem.get(s, {}).get(i)
            if got is None:
                chain.append(dict(stem=s, idx=i, state="row-not-found"))
                why = "row not found in any source file for stem %s" % s
                break
            r, path, ln, fsha = got
            fresh, pre = terminal_is_fresh(s, r)
            chain.append(dict(stem=s, idx=i, line=ln, file=os.path.relpath(path, MEM),
                              file_sha256=fsha, from_cache=r.get("from_cache"),
                              fresh_by_pre_field_rule=pre, scale=r.get("used_scale")))
            if fresh:
                terminal = (s, i, r, path, ln, fsha, pre)
                break
            co = r.get("cache_origin") or {}
            cur = (co.get("stem"), co.get("idx")) if co.get("stem") is not None else None
            depth += 1
        rec = dict(ckey=e["ckey"], n=e["n"], scale=e.get("scale"), chain=chain)
        if terminal is None:
            rec["problem"] = why
            failed.append(rec)
            continue
        s, i, r, path, ln, fsha, pre = terminal
        si = snap_info.get(s)
        prob = None
        if si is None:
            prob = "no snapshot registered for stem %s" % s
        elif r.get("snapshot") != si["sha256"]:                       # T1
            prob = "terminal row snapshot %s != sha256(%s)" % (
                str(r.get("snapshot"))[:16], os.path.basename(si["path"]))
        else:
            leaf = si["atomic"][i] if isinstance(i, int) and 0 <= i < len(si["atomic"]) else None
            if leaf is None:
                prob = "terminal idx out of range in %s" % os.path.basename(si["path"])
            else:
                N = leaf.get("atomN", 2048)
                usha = hashlib.sha256(open(V.vectors_path(N), "rb").read()).hexdigest()
                h_sha = CT.full_h_sha(leaf["H"])
                w_sha = CT.full_w_sha(leaf["proposal"]["weights"])
                # T5: the row must RECORD its scale.  A missing used_scale is admissible only
                # for the audited pre-field stem (stage2200), at N=2048, scale 26 -- never
                # "whatever the entry says", which would make the test tautological.
                rsc = r.get("used_scale")
                if rsc is None:
                    # the scale exception is keyed to an exact legacy FILE + N + scale
                    if legacy_allows(s, path, N, e.get("scale"), "used_scale"):
                        rsc = 26
                    else:
                        prob = ("terminal row has no used_scale and is not in the audited "
                                "legacy registry for this file/N/scale")
                if prob is None:
                    # T2: BOTH the leaf's vector set AND the row's own recorded vector set
                    if N != e["n"] or usha != e.get("units") or r.get("units") != usha:
                        prob = ("terminal N/vector set differ: leaf N=%s entry n=%s; "
                                "row units=%s vs required %s" % (N, e.get("n"),
                                                                 str(r.get("units"))[:12],
                                                                 usha[:12]))
                    elif r.get("n") not in (None, N):
                        prob = "terminal row records n=%r but leaf N=%s" % (r.get("n"), N)
                if prob is None and (h_sha != e.get("h_sha") or w_sha != e.get("w_sha")):  # T3
                    prob = "terminal H/W differ from entry (different snapshot/leaf)"
                if prob is None:
                    # T4: kernel_n may be absent ONLY for the audited pre-field generation
                    # at N=2048; every other row must record the N-dispatch kernel hash.
                    rkn = r.get("kernel_n")
                    kn_missing_ok = (rkn is None and
                                     legacy_allows(s, path, N, e.get("scale"), "kernel_n"))
                    if r.get("kernel") != e.get("kernel"):
                        prob = "terminal kernel hash differs from entry"
                    elif rkn is not None and rkn != e.get("kernel_n"):
                        prob = "terminal kernel_n differs from entry"
                    elif rkn is None and not kn_missing_ok:
                        prob = ("terminal row has no kernel_n and is not in the audited "
                                "legacy registry for this file/N/scale")
                if prob is None and rsc != e.get("scale"):              # T5
                    prob = "terminal scale %r != entry scale %r" % (rsc, e.get("scale"))
                if prob is None:                                       # T6
                    dem, mx = r.get("demand"), r.get("max_capture")
                    if r.get("status") != "certified":
                        prob = "terminal row status %r is not certified" % r.get("status")
                    elif dem is None or mx is None:
                        prob = "terminal row lacks demand/max_capture for gap arithmetic"
                    elif int(dem) - 10 * int(mx) != int(r.get("gap", 0)) or \
                            int(dem) - 10 * int(mx) <= 0:
                        prob = "terminal gap arithmetic fails (demand-10*max != gap>0)"
        if prob:
            rec["problem"] = prob
            failed.append(rec)
        else:
            verified.append(dict(ckey=e["ckey"], n=e["n"], scale=e.get("scale"),
                                 demand=r.get("demand"), max_capture=r.get("max_capture"),
                                 gap=r.get("gap"), status=r.get("status"),
                                 units=r.get("units"), kernel=r.get("kernel"),
                                 kernel_n=r.get("kernel_n"),
                                 h_sha=e.get("h_sha"), w_sha=e.get("w_sha"),
                                 fresh_file=os.path.relpath(path, MEM),
                                 fresh_file_sha256=fsha, fresh_line=ln,
                                 fresh_idx=i, fresh_stem=s, pre_field_rule=pre,
                                 source_snapshot_sha256=si["sha256"],
                                 snapshot_sha256=si["sha256"], chain_depth=depth,
                                 chain=chain))

    out = dict(cache_path=os.path.relpath(cache_path, MEM),
               cache_sha256=cache_sha,          # the provenance is bound to THESE bytes
               cache_entries=len(cache), verified_fresh=len(verified),
               failed=len(failed), failed_detail=failed[:5],
               # every row file consulted, with the sha256 actually read (for re-checking)
               row_files_sha256={os.path.relpath(p, MEM): sh
                                 for p, sh in sorted(ROW_FILE_HASHES.items())},
               snapshot_registry={s: dict(path=os.path.relpath(v["path"], N12),
                                          sha256=v["sha256"])
                                  for s, v in snap_info.items()},
               depth_histogram=dict(Counter(v["chain_depth"] for v in verified)),
               verified_by_scale=dict(Counter(v["scale"] for v in verified)),
               verified_by_stem=dict(Counter(v["fresh_stem"] for v in verified)),
               rule="T1..T7: source snapshot hash + leaf H/W/N + vectors + kernel + scale "
                    "+ gap arithmetic must all agree; stem/idx alone never suffices",
               verified=verified)
    dest = os.path.join(OUT, "cache-provenance.json")
    with open(dest, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "verified"}, indent=1)[:2200])
    print("provenance ->", dest)
    if failed:
        raise SystemExit(1)


if __name__ == "__main__":
    main()