#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""cache_tools.py -- corrected cache promotion/loading + an audit of the existing cache.

WHY (Lead audit, accepted):
  * the previous build_cache bound a row to a snapshot leaf by INDEX + a SHORT (16 hex)
    digest of H only.  Weights were not bound at all, so a verdict certified for
    (H, W_other) could be transferred to (H, W_this) -- a same-H/different-W transfer.
  * the previous load_cache did not require status=='certified' and did not check the
    gap, so a self-consistent entry carrying a non-certified verdict could be laundered
    into a cache hit.
Both are fixed here.  This module is deliberately SEPARATE from verify_manifest.py so the
running verifier's source is not modified mid-run; the caller patches verify_manifest.py
only after the live run exits.

Guarantees implemented:
  B1 single bytes read of the input JSONL, hashed; every admitted row must carry
     row['snapshot'] == sha256(bytes of the named snapshot)   (snapshot binding)
  B2 content binding uses FULL sha256 of the exact rational H and of the exact weights
     re-derived from that snapshot's leaf; short digests are never used
  B3 only status=='certified' rows are admitted; a positive gap is required when the row
     records one
  B4 entries are deduplicated by ckey; conflicting duplicates are rejected, not averaged
  L1 load-time validation: self-consistent ckey (re-derived from the entry's own fields),
     status=='certified', gap>=0 when present, kernel/units/kernel_n present
"""
from __future__ import annotations

import hashlib
import json
import os
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")


def key_from_parts(N, units_sha, kernel_sha, kernel_n_sha, h_sha, w_sha, scale):
    """the cache key binds the integer SCALE as well: a scale-26 certificate and a
    scale-28 certificate of the same (N,H,W) are distinct objects (both legitimate; the
    scale is not an input of the proposition, but it must be stored honestly)."""
    return "N%d:S%d:%s:%s:%s:%s:%s" % (N, scale, units_sha, kernel_sha, kernel_n_sha,
                                       h_sha, w_sha)


def full_h_sha(H_raw):
    return hashlib.sha256(json.dumps(H_raw, sort_keys=True).encode()).hexdigest()


def full_w_sha(W_raw):
    return hashlib.sha256(json.dumps(W_raw, sort_keys=True).encode()).hexdigest()


def entry_is_self_consistent(r):
    need = ("ckey", "n", "units", "kernel", "kernel_n", "h_sha", "w_sha", "scale")
    if not all(k in r for k in need):
        return False
    return r["ckey"] == key_from_parts(r["n"], r["units"], r["kernel"], r["kernel_n"],
                                       r["h_sha"], r["w_sha"], r["scale"])


def entry_is_certified(r):
    """strict: status certified AND the margin must EXIST and be STRICTLY positive.
    gap == 0 means 10*capture == total, which excludes nothing (T = 10M equality), so a
    zero or missing gap is not a certificate."""
    if r.get("status") != "certified":
        return False
    g = r.get("gap")
    if g is None:
        return False
    try:
        return F(g) > 0
    except Exception:
        return False


def load_cache_checked(path, kernel_sha):
    """corrected loader: self-consistent AND certified AND base-kernel-matching."""
    cache, foreign, bad = {}, 0, []
    if not path or not os.path.exists(path):
        return cache, foreign, bad
    for ln, line in enumerate(open(path, encoding="utf-8"), 1):
        line = line.strip()
        if not line:
            continue
        try:
            r = json.loads(line)
        except Exception:
            bad.append((ln, "unparsable")); continue
        if r.get("kernel") != kernel_sha:
            foreign += 1; continue
        if not entry_is_self_consistent(r):
            bad.append((ln, "self-inconsistent ckey")); continue
        if not entry_is_certified(r):
            bad.append((ln, "not certified (status=%r gap=%r)" % (r.get("status"), r.get("gap"))))
            continue
        k = r["ckey"]
        if k in cache and cache[k] != r:
            bad.append((ln, "conflicting duplicate ckey")); continue
        cache[k] = r
    return cache, foreign, bad


def snapshot_bytes_hash(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def build_cache_checked(from_jsonl, snapshot_path, out_cache, kernel_sha,
                        vectors_path_fn, kernel_n_sha, scale,
                        atomN_default=2048, scale_provenance=None):
    """corrected promotion (see B1-B4).  The snapshot is read ONCE as bytes; both its hash
    and the parsed leaves come from that same buffer, so the two can never disagree."""
    raw = open(from_jsonl, "rb").read()                  # B1a: single read of the rows
    rows_sha = hashlib.sha256(raw).hexdigest()
    snap_raw = open(snapshot_path, "rb").read()          # B1b: single read of the snapshot
    snap_sha = hashlib.sha256(snap_raw).hexdigest()
    st = json.loads(snap_raw.decode("utf-8"))            # parsed from the SAME bytes
    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]

    admitted, rejected = {}, []
    n_rows = 0
    for line in raw.decode("utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        n_rows += 1
        try:
            r = json.loads(line)
        except Exception:
            rejected.append(("unparsable", None)); continue
        if r.get("status") != "certified":
            rejected.append(("status!=certified", r.get("idx"))); continue
        if r.get("gap") is None or F(r["gap"]) <= 0:      # strict positivity
            rejected.append(("gap not strictly positive", r.get("idx"))); continue
        if r.get("snapshot") != snap_sha:                 # B1 snapshot binding
            rejected.append(("snapshot binding mismatch", r.get("idx"))); continue
        idx = r.get("idx")
        if not isinstance(idx, int) or not (0 <= idx < len(atomic)):
            rejected.append(("idx out of range", idx)); continue
        L = atomic[idx]
        N = L.get("atomN", atomN_default)
        if r.get("n") not in (None, N):
            rejected.append(("row N != leaf N", idx)); continue
        if r.get("used_scale") not in (None, scale) or r.get("scale") not in (None, scale):
            rejected.append(("row scale != declared scale", idx)); continue
        try:
            usha = hashlib.sha256(open(vectors_path_fn(N), "rb").read()).hexdigest()
        except SystemExit:
            rejected.append(("unknown N", idx)); continue
        except OSError:
            rejected.append(("vectors missing", idx)); continue
        H_raw, W_raw = L["H"], L["proposal"]["weights"]
        h_sha, w_sha = full_h_sha(H_raw), full_w_sha(W_raw)     # B2 full hashes
        if r.get("h_sha") not in (None, h_sha) or r.get("w_sha") not in (None, w_sha):
            rejected.append(("row H/W hash mismatch (transfer risk)", idx)); continue
        if r.get("units") not in (None, usha):
            rejected.append(("row units mismatch", idx)); continue
        if r.get("kernel_n") not in (None, kernel_n_sha):
            rejected.append(("row kernel_n mismatch", idx)); continue
        ck = key_from_parts(N, usha, kernel_sha, kernel_n_sha, h_sha, w_sha, scale)
        entry = dict(ckey=ck, status="certified", n=N, scale=scale, units=usha,
                     kernel=kernel_sha, kernel_n=kernel_n_sha, h_sha=h_sha, w_sha=w_sha,
                     gap=r.get("gap"), n_atoms=r.get("n_atoms"), total=r.get("total"),
                     boxes=r.get("boxes"), leaves=r.get("leaves"),
                     outside=r.get("outside"), max_capture=r.get("max_capture"),
                     demand=r.get("demand"), origin_jsonl_sha256=rows_sha,
                     origin_snapshot=snap_sha, origin_idx=idx,
                     scale_provenance=scale_provenance)
        if ck in admitted:
            if admitted[ck] != entry:
                rejected.append(("conflicting duplicate ckey", idx)); continue
        else:
            admitted[ck] = entry

    tmp = out_cache + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        for ck in sorted(admitted):
            f.write(json.dumps(admitted[ck]) + "\n")
    os.replace(tmp, out_cache)
    return dict(input_jsonl=from_jsonl, input_jsonl_sha256=rows_sha,
                snapshot=snapshot_path, snapshot_sha256=snap_sha,
                scale=scale, scale_provenance=scale_provenance,
                rows_read=n_rows, admitted=len(admitted), rejected=len(rejected),
                rejected_samples=rejected[:8], out_cache=out_cache)


# ------------------------------------------------------------------ audit of a cache
def audit_cache(cache_path, snapshot_for_stem, kernel_sha, vectors_path_fn,
                kernel_n_sha, kernel_sha_expected_note=True):
    """Independently re-derive every entry's provenance: the referenced origin JSONL and
    origin snapshot must exist, the row at origin_idx must exist, its snapshot field must
    equal origin_snapshot, its H/W must hash to the entry's h_sha/w_sha, and the entry's
    ckey must follow.  Nothing is taken on trust from the entry's own text."""
    entries = [json.loads(l) for l in open(cache_path, encoding="utf-8") if l.strip()]
    problems, ok_entries = [], 0
    per_origin = {}
    # index rows / snapshots ONCE per origin (the previous per-entry scan was O(n^2))
    row_index, snap_index, vec_index = {}, {}, {}
    for e in entries:
        stem = e.get("origin_stem")
        idx = e.get("origin_idx")
        prob = None
        jl = os.path.join(MEM, "out", "verify-%s.jsonl" % stem) if stem else None
        snap = snapshot_for_stem(stem) if stem else None
        if jl is None or not os.path.exists(jl):
            prob = "origin jsonl missing"
        elif snap is None or not os.path.exists(snap):
            prob = "origin snapshot missing"
        else:
            if stem not in row_index:
                idx_map = {}
                for line in open(jl, encoding="utf-8"):
                    line = line.strip()
                    if not line:
                        continue
                    rr = json.loads(line)
                    k = rr.get("idx")
                    if k not in idx_map or (rr.get("from_cache") is False and
                                            idx_map[k].get("from_cache") is not False):
                        idx_map[k] = rr
                row_index[stem] = idx_map
            if stem not in snap_index:
                raw = open(snap, "rb").read()
                snap_index[stem] = (hashlib.sha256(raw).hexdigest(),
                                    json.loads(raw.decode("utf-8")))
            snap_sha, st = snap_index[stem]
            if e.get("origin_snapshot") != snap_sha:
                prob = "origin_snapshot field != sha256(origin snapshot bytes)"
            else:
                row = row_index[stem].get(idx)
                if row is None:
                    prob = "origin row not found"
                elif row.get("snapshot") != snap_sha:
                    prob = "origin row snapshot != entry origin_snapshot"
                elif row.get("status") != "certified":
                    prob = "origin row not certified"
                else:
                    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
                    if not isinstance(idx, int) or not (0 <= idx < len(atomic)):
                        prob = "origin idx out of range"
                    else:
                        L = atomic[idx]
                        H_raw, W_raw = L["H"], L["proposal"]["weights"]
                        N = L.get("atomN", 2048)
                        if N not in vec_index:
                            vec_index[N] = hashlib.sha256(
                                open(vectors_path_fn(N), "rb").read()).hexdigest()
                        usha = vec_index[N]
                        if e.get("h_sha") != full_h_sha(H_raw) or e.get("w_sha") != full_w_sha(W_raw):
                            prob = "entry H/W hash != snapshot leaf H/W (TRANSFER RISK)"
                        elif e.get("n") != N or e.get("units") != usha:
                            prob = "entry N/units != snapshot leaf N/vectors"
                        elif e.get("ckey") != key_from_parts(N, usha, kernel_sha,
                                                             kernel_n_sha,
                                                             full_h_sha(H_raw),
                                                             full_w_sha(W_raw),
                                                             e.get("scale")):
                            prob = "entry ckey != re-derived key (scale %r)" % e.get("scale")
                        elif not entry_is_certified(e):
                            prob = "entry not certified with gap>0 (status=%r gap=%r)" % (
                                e.get("status"), e.get("gap"))
        if prob:
            problems.append(dict(origin_stem=stem, origin_idx=idx, problem=prob))
        else:
            ok_entries += 1
        per_origin[stem] = per_origin.get(stem, 0) + 1
    return dict(cache=cache_path, n_entries=len(entries), verified=ok_entries,
                n_problems=len(problems), problems=problems[:10],
                per_origin=per_origin)