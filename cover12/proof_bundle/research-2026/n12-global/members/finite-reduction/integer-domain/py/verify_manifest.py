#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""verify_manifest.py -- independent manifest re-verifier (finite-reduction/integer-domain).

Read-only on all Lead/evidence sources; writes only under this member directory.
No mpmath/scipy is used for any bearing computation (mpmath appears only in the
non-bearing rounding-robustness check of the core net).  U is an exact literal.

CLI (stable):
  py -3 -B py/verify_manifest.py                                  # default snapshot, default stem
  py -3 -B py/verify_manifest.py --snapshot PATH --out-stem NAME   # generalized
  py -3 -B py/verify_manifest.py --snapshot PATH --out-stem NAME --cache out/certified-cache.jsonl
  py -3 -B py/verify_manifest.py --build-cache --snapshot PATH --out-stem NAME --from-jsonl PATH
  py -3 -B py/verify_manifest.py --max N                           # compute at most N new leaves

Proof-state interface:
  P1 SNAPSHOT BINDING : snapshot read ONCE as bytes; sha256 recorded for snapshot, units,
                        kernel and the atoms source.  Every row binds all four.
  P1b CONTENT-KEYED CACHE (optional): a cached verdict is reused only when the CONTENT
                        key (exact rational H + exact weights) AND kernel/units hashes
                        match.  Cache entries are never addressed by an old leaf index,
                        and new rows never inherit an old index: they bind the CURRENT
                        snapshot hash and the CURRENT index, so hitting the cache can
                        never mis-state which box was verified.
  P2 STRUCTURE        : 3-dimensional boxes, lo<hi, known leaf types, no duplicate H.
  P3 PARTITION (exact): independent RECURSIVE TILING from the exact root; a box resolves
                        iff it is a recorded frontier box or both exact mid-halves
                        resolve; exactness additionally requires visited==frontier.
                        (Containment + equal volume is NOT used: overlaps can hide holes.)
  P4 ILLEGAL LEAVES   : the three criteria re-derived in exact Fractions; the radical-free
                        form is checked against the radical form with scaled isqrt
                        (+100 bits); undecided cases are reported, never called verified.
  P5 ATOMIC LEAVES    : IntAtoms(H, weights, 26).certify() replayed (kernel NOT rewritten
                        -- this is a repeat execution of upper-audit's kernel, not an
                        independent implementation of it).  Agreement with the recorded
                        capture is diagnostic only.
  P6 HONEST LABELS    : 'complete' needs the exact index set, every status certified and
                        structural checks passing; 'global' additionally needs an empty
                        pending queue.  Cache hits are counted separately from fresh
                        computation and never presented as new work.
"""
from __future__ import annotations

import hashlib
import json
import math
import os
import sys
import time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
MEM = os.path.abspath(os.path.join(HERE, ".."))
N12 = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
EV = os.path.join(N12, "evidence")
UPPER = os.path.join(N12, "members", "upper-audit", "integer-atomic", "py")
sys.path.insert(0, UPPER)

DEF_SNAP = os.path.join(EV, "hubline-domain-stage2200.json")
UNITS = os.path.join(EV, "atomic-unit-vectors-2048.json")
KERNEL = os.path.join(UPPER, "integer_kernel.py")
KERNEL_N = os.path.join(UPPER, "integer_kernel_n.py")
VECDIR_MEMBER = os.path.join(N12, "members", "upper-audit", "integer-atomic", "evidence")
GUARD = os.path.join(UPPER, "guard_selftest.py")
ATOMS_PY = os.path.join(N12, "lead", "hubline_atoms.py")
OUTDIR = os.path.join(MEM, "out")
os.makedirs(OUTDIR, exist_ok=True)
DEF_CACHE = os.path.join(OUTDIR, "certified-cache.jsonl")


def vectors_path(N):
    """vector-set file for atom count N.

    N=2048 : the frozen evidence file (keeps the existing cache valid).
    N=8192 : upper-audit's member-scope canonical file (explicit path, never generated).
    other  : REJECTED -- the verifier never auto-generates a vector set, so an unknown N
             can never silently acquire a vacuous proof.
    """
    if N == 2048:
        return UNITS
    if N == 8192:
        return os.path.join(VECDIR_MEMBER, "canonical-unit-vectors-8192.json")
    raise SystemExit("unknown atomN=%r: refusing to auto-generate a vector set" % (N,))


def kernel_n_sha():
    return hashlib.sha256(open(KERNEL_N, "rb").read()).hexdigest() \
        if os.path.exists(KERNEL_N) else ""

U = F('0.361102963744508672616920293904')
A_CORE = 1 - 2 * U
E0 = 3 * U - 1
ROOT = ((F(1, 20), U), (F(0), 1 - U - F(1, 20)), (F(0), E0))
ALLOWED_TYPES = {"atomic", "infeasible"}


# ---------------------------------------------------------------- exact helpers
def isquare(lo, hi):
    if lo <= 0 <= hi:
        return F(0), max(lo * lo, hi * hi)
    return min(lo * lo, hi * hi), max(lo * lo, hi * hi)


def normlower(X, Y):
    return isquare(*X)[0] + isquare(*Y)[0]


def core_net_32():
    """the generator's core net: stereographic rational parameter t = round(tan(pi j/32)
    * 1e8)/1e8 gives an EXACT point of S1, scaled by A_CORE.  Uniformity is never used in
    the proof; only legality of the rational points.  Rounding robustness is checked."""
    import mpmath as mp
    mp.mp.dps = 60
    pts, robust = [], True
    for j in range(32):
        if 2 * j == 32:
            c, s = F(-1), F(0)
        else:
            t_exact = mp.tan(mp.pi * j / 32)
            scaled = t_exact * mp.mpf(10) ** 8
            t_round = round(float(scaled))
            robust &= abs(scaled - mp.mpf(t_round)) < mp.mpf('0.49')
            t = F(t_round, 10 ** 8)
            c = (1 - t * t) / (1 + t * t)
            s = 2 * t / (1 + t * t)
        assert c * c + s * s == 1
        pts.append((A_CORE * c, A_CORE * s))
    return pts, bool(robust)


def check_infeasible(B, CORE):
    (sl, sh), (xl, xh), (yl, yh) = B
    nl = normlower((xl + sl, xh + sh), (yl, yh))
    if nl > (1 - U) ** 2:
        return "outer hub inactive", dict(normlower=str(nl))
    h1x = (xl - sh, xh - sl)
    h2x = (xl + sl, xh + sh)
    closest = None
    for (cx, cy) in CORE:
        d1 = normlower((h1x[0] - cx, h1x[1] - cx), (yl - cy, yh - cy))
        d2 = normlower((h2x[0] - cx, h2x[1] - cx), (yl - cy, yh - cy))
        m = min(d1, d2)
        if m > U * U:
            return "rational core witness", dict(point=[str(cx), str(cy)], min_d2=str(m))
        closest = m if closest is None else min(closest, m)
    if xh < A_CORE:
        q2 = A_CORE * A_CORE - xh * xh
        rhs = U * U - sl * sl - yl * yl - q2
        if rhs < 0 or 4 * yl * yl * q2 > rhs * rhs:
            return "core bisector endpoints", dict(q2=str(q2), rhs=str(rhs))
    return None, dict(closest_core_min_d2=None if closest is None else str(closest))


def radical_form_exact(B):
    """exact True/False/None for sl^2+(yl+sqrt(q2))^2 > U^2 via scaled isqrt (+100 bits)."""
    (sl, sh), (xl, xh), (yl, yh) = B
    if not (xh < A_CORE):
        return None
    q2 = A_CORE * A_CORE - xh * xh
    if q2 <= 0:
        return None
    BITS = 100
    num = (q2.numerator << (2 * BITS)) // q2.denominator
    lo = math.isqrt(num)
    slo, shi = F(lo, 1 << BITS), F(lo + 1, 1 << BITS)
    lo_left = sl * sl + (yl + slo) ** 2 if (yl + slo) >= 0 else sl * sl
    hi_left = sl * sl + (yl + shi) ** 2 if (yl + shi) >= 0 else sl * sl
    if lo_left > U * U:
        return True
    if hi_left <= U * U:
        return False
    return None


def box_key(B):
    return tuple((lo, hi) for lo, hi in B)


def volume(B):
    v = F(1)
    for lo, hi in B:
        v *= (hi - lo)
    return v


def widest_split(B):
    dims = [hi - lo for lo, hi in B]
    k = max(range(3), key=lambda j: dims[j])
    lo, hi = B[k]
    m = (lo + hi) / 2
    a = list(B); a[k] = (lo, m)
    b = list(B); b[k] = (m, hi)
    return tuple(a), tuple(b)


def tiling_ok(frontier_set):
    memo, unresolved, visited = {}, [], set()
    nodes = [0]

    def resolve(B, depth):
        nodes[0] += 1
        k = box_key(B)
        if k in memo:
            return memo[k]
        if depth > 64:
            memo[k] = False; unresolved.append(str(B)); return False
        if k in frontier_set:
            visited.add(k); memo[k] = True; return True
        if max(hi - lo for lo, hi in B) == 0:
            memo[k] = False; unresolved.append(str(B)); return False
        a, b = widest_split(B)
        r = resolve(a, depth + 1) and resolve(b, depth + 1)
        memo[k] = r
        if not r:
            unresolved.append(str(B))
        return r

    ok = resolve(ROOT, 0)
    return ok, dict(nodes=nodes[0], n_unresolved=len(unresolved),
                    visited_frontier=len(visited),
                    visited_equals_frontier=bool(visited == frontier_set),
                    first_unresolved=unresolved[:3])


def content_key(H_raw, W_raw, N, units_sha, kernel_sha, kernel_n_sha, scale):
    """snapshot-independent key.  It binds EVERY ingredient that can change the verdict:

        N (atom count) + the units file actually used + the frozen base kernel + the
        N-dispatching kernel hash + the INTEGER SCALE actually used + sha256(exact H) +
        sha256(exact weights)

    Two certificates of the same (N, H, W) at different scales are different objects: a
    scale-26 certificate can never be served as a scale-28 one (both are legitimate, but
    the scale must be stored honestly; the scale is not an input of the proposition)."""
    return key_from_parts(N, units_sha, kernel_sha, kernel_n_sha,
                          hashlib.sha256(json.dumps(H_raw, sort_keys=True).encode()).hexdigest(),
                          hashlib.sha256(json.dumps(W_raw, sort_keys=True).encode()).hexdigest(),
                          scale)


def key_from_parts(N, units_sha, kernel_sha, kernel_n_sha, h_sha, w_sha, scale):
    return "N%d:S%d:%s:%s:%s:%s:%s" % (N, scale, units_sha, kernel_sha, kernel_n_sha,
                                       h_sha, w_sha)


def positive_gap(r):
    """strictly positive margin: gap == 0 means 10*capture == total, i.e. the exclusion
    test is NOT satisfied (T = 10M equality cannot exclude anything)."""
    if r.get("status") != "certified":
        return False
    g = r.get("gap")
    if g is None:
        return False
    try:
        return F(g) > 0
    except Exception:
        return False


def validate_entry(r):
    """a cache line is usable only if its stored ckey is EXACTLY the key re-derived from
    its own declared ingredients (N, scale, units, base kernel, N-kernel, H-hash, W-hash)
    AND it carries a strictly positive margin (status certified, gap > 0)."""
    need = ("ckey", "n", "units", "kernel", "kernel_n", "h_sha", "w_sha", "scale")
    if not all(k in r for k in need):
        return False
    if r["ckey"] != key_from_parts(r["n"], r["units"], r["kernel"], r["kernel_n"],
                                   r["h_sha"], r["w_sha"], r["scale"]):
        return False
    return positive_gap(r)


def atomic_write(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=1)
    os.replace(tmp, path)


def parse_args(argv):
    a = dict(snapshot=DEF_SNAP, out_stem=None, cache=None, max_new=None,
             build_cache=False, from_jsonl=None, atomN=2048, expect_hash=None,
             sexpt=26, escalate=True, allow_hash_mismatch=False, append_cache=False)
    i = 0
    while i < len(argv):
        v = argv[i]
        if v == "--snapshot":
            a["snapshot"] = argv[i + 1]; i += 2
        elif v == "--out-stem":
            a["out_stem"] = argv[i + 1]; i += 2
        elif v == "--cache":
            a["cache"] = argv[i + 1]; i += 2
        elif v == "--max":
            a["max_new"] = int(argv[i + 1]); i += 2
        elif v == "--atomN":
            a["atomN"] = int(argv[i + 1]); i += 2
        elif v == "--expect-hash":
            a["expect_hash"] = argv[i + 1].strip().lower(); i += 2
        elif v == "--sexpt":
            a["sexpt"] = int(argv[i + 1]); i += 2
        elif v == "--no-escalate":
            a["escalate"] = False; i += 1
        elif v == "--allow-hash-mismatch":
            a["allow_hash_mismatch"] = True; i += 1
        elif v == "--append-cache":
            a["append_cache"] = True; i += 1
        elif v == "--build-cache":
            a["build_cache"] = True; i += 1
        elif v == "--from-jsonl":
            a["from_jsonl"] = argv[i + 1]; i += 2
        elif v == "--no-cache":
            a["cache"] = ""; i += 1
        elif v == "--help" or v == "-h":
            print(__doc__); raise SystemExit(0)
        else:
            raise SystemExit("unknown argument: %s" % v)
    return a


def load_cache(path, kernel_sha):
    """load the content-keyed cache.

    Entries must declare their full ingredient tuple (N, units, base kernel, N-kernel).
    Entries whose BASE kernel differs from the current frozen one are dropped as foreign.
    Everything else is kept keyed by the full content key, so a lookup can only succeed
    for an identical (N, units, base kernel, N-kernel, H, weights) tuple; a 2048 entry is
    therefore unreachable from an 8192 leaf even if H and weights coincide.
    """
    cache, foreign, tampered = {}, 0, 0
    if not path or not os.path.exists(path):
        return cache, foreign, tampered
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        try:
            r = json.loads(line)
        except Exception:
            tampered += 1; continue
        if r.get("kernel") != kernel_sha:
            foreign += 1; continue
        if not validate_entry(r):
            tampered += 1; continue
        cache[r["ckey"]] = r
    return cache, foreign, tampered


def build_cache(a, kernel_sha, snap_sha):
    """verified import: for each row of an existing JSONL, map its index to the leaf of the
    named snapshot, RE-DERIVE the content key (including N / units / kernels), and require
    the recorded fingerprint and binding to agree before admitting the verdict."""
    st = json.loads(open(a["snapshot"], encoding="utf-8").read())
    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
    kn_sha = kernel_n_sha()
    admitted = rejected = 0
    out = open(a["cache"] or DEF_CACHE, "w", encoding="utf-8")
    for line in open(a["from_jsonl"], encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        idx = r.get("idx")
        if not isinstance(idx, int) or not (0 <= idx < len(atomic)):
            rejected += 1; continue
        L = atomic[idx]
        N = L.get("atomN", 2048)
        H_raw, W_raw = L["H"], L["proposal"]["weights"]
        usha = hashlib.sha256(open(vectors_path(N), "rb").read()).hexdigest()
        ck = content_key(H_raw, W_raw, N, usha, kernel_sha, kn_sha)
        lh = hashlib.sha256(json.dumps(H_raw).encode()).hexdigest()[:16]
        if r.get("kernel") != kernel_sha or r.get("units") != usha or \
                r.get("leaf_sha") != lh or r.get("status") != "certified":
            rejected += 1; continue
        has_binding = ("n" in r and "kernel_n" in r)
        if has_binding:
            if r.get("n") != N or r.get("kernel_n") != kn_sha:
                rejected += 1; continue
            legacy = False
        else:
            # pre-dispatch generation: only admissible for the ORIGINAL N=2048 vector set,
            # because that generation's kernel was exactly the frozen 2048 kernel.
            if N != 2048:
                rejected += 1; continue
            legacy = True
        out.write(json.dumps(dict(ckey=ck, status="certified", n=N, units=usha,
                                  kernel=kernel_sha, kernel_n=kn_sha,
                                  legacy_2048_import=legacy,
                                  h_sha=hashlib.sha256(json.dumps(H_raw, sort_keys=True).encode()).hexdigest(),
                                  w_sha=hashlib.sha256(json.dumps(W_raw, sort_keys=True).encode()).hexdigest(),
                                  n_atoms=r.get("n_atoms"), total=r.get("total"),
                                  gap=r.get("gap"), boxes=r.get("boxes"),
                                  leaves=r.get("leaves"), outside=r.get("outside"),
                                  max_capture=r.get("max_capture"),
                                  demand=r.get("demand"),
                                  origin_stem=a["out_stem"],
                                  origin_snapshot=snap_sha, origin_idx=idx)) + "\n")
        admitted += 1
    out.close()
    return dict(admitted=admitted, rejected=rejected, source=a["from_jsonl"],
                cache=a["cache"] or DEF_CACHE)


def main():
    argv = sys.argv[1:]
    a = parse_args(argv)
    SNAP = a["snapshot"]
    stem = a["out_stem"] or os.path.splitext(os.path.basename(SNAP))[0]
    JSONL = os.path.join(OUTDIR, "verify-%s.jsonl" % stem)
    SUMMARY = os.path.join(OUTDIR, "verify-%s-summary.json" % stem)

    raw = open(SNAP, "rb").read()
    snap_sha = hashlib.sha256(raw).hexdigest()
    st = json.loads(raw.decode("utf-8"))
    units_sha = hashlib.sha256(open(UNITS, "rb").read()).hexdigest()
    kernel_sha = hashlib.sha256(open(KERNEL, "rb").read()).hexdigest()
    atoms_sha = hashlib.sha256(open(ATOMS_PY, "rb").read()).hexdigest() \
        if os.path.exists(ATOMS_PY) else ""
    guard_sha = hashlib.sha256(open(GUARD, "rb").read()).hexdigest() \
        if os.path.exists(GUARD) else ""

    # ---- atom-count dispatch: N=2048 uses the frozen kernel (cache stays valid);
    #      N!=2048 uses the N-generalized companion (same inherited bound/certify).
    N_DEFAULT = a["atomN"]
    KN_SHA = kernel_n_sha()
    VEC_SHA = {}

    def vec_sha_for(N):
        """hash of the vector set actually used for atom count N (explicit files only)."""
        if N not in VEC_SHA:
            p = vectors_path(N)
            if not os.path.exists(p):
                raise SystemExit("vector file missing for N=%d: %s" % (N, p))
            VEC_SHA[N] = hashlib.sha256(open(p, "rb").read()).hexdigest()
        return VEC_SHA[N]

    vec_sha_for(N_DEFAULT)          # validate the default N up front (rejects unknown N)
    units_sha = vec_sha_for(N_DEFAULT)
    kernel_n_sha_val = KN_SHA
    BIND = dict(snapshot=snap_sha, units=units_sha, kernel=kernel_sha, atoms=atoms_sha)
    BIND_FULL = dict(BIND, kernel_n=kernel_n_sha_val, atomN=N_DEFAULT)

    if a["build_cache"]:
        # DISABLED.  This legacy entry had two hazards: it called content_key() without the
        # scale argument (TypeError) AFTER opening the cache with mode 'w', which truncated
        # the production cache.  Promotion now lives in the strict, atomic tooling:
        #   py/migrate_cache.py          (production migration, verifies every binding)
        #   py/cache_tools.py            (build_cache_checked / load_cache_checked / audit)
        raise SystemExit(
            "--build-cache is DISABLED in verify_manifest.py.  Use the strict builder:\n"
            "  py -3 -B py/migrate_cache.py          # promote/renew the production cache\n"
            "  py -3 -B py/audit_existing_cache.py   # re-derive provenance of every entry\n"
            "The old entry could truncate the production cache before failing; it is now "
            "unreachable by design.")

    t0 = time.time()
    exp = a.get("expect_hash")
    rep = dict(snapshot=os.path.relpath(SNAP, N12).replace("\\", "/"),
               snapshot_sha256=snap_sha,
               quoted_hash=exp,
               quoted_hash_matches=bool(exp is None or exp == snap_sha),
               out_stem=stem, binding=BIND_FULL, guard_sha256=guard_sha,
               manifest_status=st.get("status"), manifest_counts=st.get("counts"),
               U=str(U), root=[[str(x) for x in r] for r in ROOT])
    if exp is not None and exp != snap_sha:
        common = 0
        for x, y in zip(exp, snap_sha):
            if x != y:
                break
            common += 1
        rep["quoted_hash_discrepancy"] = dict(
            common_prefix_hex_chars=common,
            quoted_tail=exp[common:], file_tail=snap_sha[common:],
            note="the run is bound to the RECOMPUTED file hash; the quoted hash is recorded "
                 "only for provenance")
        # FAIL, do not merely note: a caller that asserts a hash must not silently proceed
        # on a different file.  (Use --allow-hash-mismatch only for deliberate diagnostics.)
        if not a.get("allow_hash_mismatch"):
            raise SystemExit(
                "FATAL: --expect-hash %s does not match the snapshot bytes (%s).\n"
                "Recompute the hash from the file bytes, or pass --allow-hash-mismatch to "
                "run anyway with the discrepancy recorded." % (exp, snap_sha))
    ok = True

    def leaf_box(L):
        return tuple(tuple(F(v) for v in r) for r in L["H"])

    # ---- P2 structure ----
    reasons, struct_bad, seen = {}, [], {}
    for i, L in enumerate(st["leaves"]):
        t = L.get("type")
        if t not in ALLOWED_TYPES:
            struct_bad.append(("unknown type", i, t)); continue
        B = leaf_box(L)
        if len(B) != 3 or any(len(r) != 2 for r in B):
            struct_bad.append(("dimension", i, str(B))); continue
        if any(not (r[0] < r[1]) for r in B):
            struct_bad.append(("empty/point box", i, str(B))); continue
        k = box_key(B)
        if k in seen:
            struct_bad.append(("duplicate H", i, str(B)))
        seen[k] = i
        if t == "infeasible":
            r = L.get("reason")
            reasons[r] = reasons.get(r, 0) + 1
            if not isinstance(r, str) or not r:
                struct_bad.append(("missing reason", i, str(r)))
    pend = [tuple(tuple(F(v) for v in r) for r in B) for B in st.get("pending", [])]
    for j, B in enumerate(pend):
        if len(B) != 3 or any(not (r[0] < r[1]) for r in B):
            struct_bad.append(("pending box malformed", j, str(B)))
    rep["structure"] = dict(n_struct_bad=len(struct_bad), samples=struct_bad[:5],
                            reason_counts=reasons,
                            types_present=sorted({L.get("type") for L in st["leaves"]}))
    ok &= not struct_bad

    # ---- P3 exact partition ----
    leaf_keys = [box_key(leaf_box(L)) for L in st["leaves"]]
    pend_keys = [box_key(B) for B in pend]
    dup_leaf = len(leaf_keys) != len(set(leaf_keys))
    dup_pend = len(pend_keys) != len(set(pend_keys))
    cross_dup = bool(set(leaf_keys) & set(pend_keys))
    frontier_set = set(leaf_keys) | set(pend_keys)
    t_ok, t_diag = tiling_ok(frontier_set)
    vol_sum = sum((volume(B) for B in frontier_set), F(0))
    rep["partition"] = dict(
        n_leaves=len(leaf_keys), n_pending=len(pend_keys), n_frontier=len(frontier_set),
        recursive_tiling_exact=t_ok, **t_diag,
        no_duplicate_leaf_H=not dup_leaf, no_duplicate_pending_H=not dup_pend,
        no_leaf_pending_overlap=not cross_dup,
        volume_sum=str(vol_sum), volume_root=str(volume(ROOT)),
        volume_equal=bool(vol_sum == volume(ROOT)),
        counts_consistent=bool(
            st["counts"]["processed"] ==
            st["counts"]["infeasible"] + st["counts"]["certified"] + st["counts"]["split"]),
        exact_partition=bool(t_ok and t_diag["visited_equals_frontier"] and
                             not dup_leaf and not dup_pend and not cross_dup and
                             len(frontier_set) == t_diag["visited_frontier"]))
    ok &= (t_ok and rep["partition"]["counts_consistent"] and
           rep["partition"]["exact_partition"])

    # ---- P4 illegal leaves ----
    CORE, net_robust = core_net_32()
    inf_rows, inf_ok = [], True
    for L in st["leaves"]:
        if L.get("type") != "infeasible":
            continue
        B = leaf_box(L)
        why, detail = check_infeasible(B, CORE)
        match = (why == L.get("reason")) and (why is not None)
        inf_ok &= match
        inf_rows.append(dict(reason=L.get("reason"), mine=why, match=bool(match), detail=detail))
    rep["infeasible"] = dict(n=len(inf_rows), all_reproduced=bool(inf_ok),
                             core_net_points=len(CORE), core_net_rounding_robust=net_robust,
                             samples=inf_rows[:4])
    ok &= inf_ok and net_robust

    eq_n = eq_consistent = eq_inconcl = 0
    for L in st["leaves"]:
        if L.get("reason") != "core bisector endpoints":
            continue
        B = leaf_box(L)
        crit = check_infeasible(B, CORE)[0] == "core bisector endpoints"
        rf = radical_form_exact(B)
        eq_n += 1
        if rf is None:
            eq_inconcl += 1
        else:
            if crit != rf:
                ok = False
            else:
                eq_consistent += 1
    rep["prune3_vs_radical"] = dict(checked=eq_n, consistent=eq_consistent,
                                    undecided=eq_inconcl,
                                    note="undecided cases are NOT counted as verified")

    # ---- P5 atomic replay with per-leaf N dispatch and content-keyed cache ----
    import integer_kernel as IK
    _IKN = None

    def make_atoms(N, H, W, scale):
        """per-leaf dispatch: N=2048 -> frozen kernel; N=8192 -> upper's N kernel with the
        explicit canonical-8192 file; any other N is rejected (never auto-generated).
        `scale` is the integer scale exponent actually used for this leaf and is recorded."""
        if N == 2048:
            return IK.IntAtoms(H, W, scale)
        if N != 8192:
            raise SystemExit("unknown per-leaf atomN=%r: refusing to auto-generate" % (N,))
        nonlocal _IKN
        if _IKN is None:
            import integer_kernel_n as _m
            _IKN = _m
        return _IKN.IntAtomsN(H, W, vectors_path(8192), Sexpt=scale)

    def certify_leaf(N, H, W):
        """try the configured scale; if the kernel stops (unresolved/budget) and escalation
        is allowed, retry at the finer scale 28.  Returns (result, used_scale, escalated)."""
        for sc in ([a["sexpt"]] + ([28] if (a["escalate"] and a["sexpt"] < 28) else [])):
            A = make_atoms(N, H, W, sc)
            res = A.certify()
            if res.get("status") == "certified" and F(res.get("gap_integer", 0)) > 0:
                return res, sc, (sc != a["sexpt"]), A
        return res, sc, (sc != a["sexpt"]), A

    cache, cache_foreign, cache_tampered = load_cache(a["cache"], kernel_sha)
    rep["cache"] = dict(path=a["cache"], entries_loaded=len(cache),
                        rejected_foreign_base_kernel=cache_foreign,
                        rejected_self_inconsistent=cache_tampered)

    # ---- resume: re-derive EVERY row's binding against the CURRENT snapshot leaf ----
    atomic = [L for L in st["leaves"] if L.get("type") == "atomic"]
    done, retry_rows, bad_preload = {}, [], 0
    if os.path.exists(JSONL):
        for line in open(JSONL, encoding="utf-8"):
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except Exception:
                bad_preload += 1; continue
            idx = r.get("idx")
            if not isinstance(idx, int) or not (0 <= idx < len(atomic)):
                bad_preload += 1; continue
            if r.get("snapshot") != snap_sha or r.get("kernel") != kernel_sha or \
                    r.get("atoms") != atoms_sha:
                bad_preload += 1; continue
            L = atomic[idx]
            N = L.get("atomN", 2048)
            try:
                usha = vec_sha_for(N)
            except SystemExit:
                bad_preload += 1; continue
            H_raw, W_raw = L["H"], L["proposal"]["weights"]
            sc = r.get("used_scale")
            if not isinstance(sc, int):
                # pre-scale rows: they were produced by the frozen kernel at its default 26
                sc = 26 if (r.get("units") == vec_sha_for(N)) else None
            if sc is None:
                bad_preload += 1; continue
            ck = content_key(H_raw, W_raw, N, usha, kernel_sha, KN_SHA, sc)
            # accept the row if its INGREDIENTS bind to this leaf and it carries a strictly
            # positive margin; the stored ckey string is informational (the key format has
            # evolved), so the key is RE-DERIVED here rather than trusted.
            row_ok = (r.get("n") in (None, N) and r.get("units") in (None, usha) and
                      r.get("kernel_n") in (None, KN_SHA) and positive_gap(r))
            if row_ok:
                # keep the row's OWN from_cache label: resuming a ledger does not change
                # where the verdict originally came from.  (An earlier revision forced
                # pre-scale rows to True, which mislabelled fresh pre-field rows.)
                done[idx] = dict(r, ckey=ck, n=N, units=usha, kernel_n=KN_SHA,
                                 used_scale=sc, rebound_on_resume=True)
            elif r.get("status") in ("certified", "unresolved", "budget"):
                retry_rows.append(r)          # kept for the retry log, never a certificate
            else:
                bad_preload += 1
    rep["resume"] = dict(preloaded_valid=len(done), rejected_by_binding=bad_preload,
                         unresolved_carried_over=len(retry_rows),
                         note="a carried-over row is retried, never counted as a certificate")

    t1 = time.time()
    fh = open(JSONL, "a", encoding="utf-8")
    cfh = open(a["cache"], "a", encoding="utf-8") if a["cache"] else None
    newly = cache_hits = 0
    N_seen = {}
    scale_seen = {}
    for idx, L in enumerate(atomic):
        if idx in done:
            continue
        N = L.get("atomN", 2048)
        usha = vec_sha_for(N)               # rejects unknown N
        N_seen[N] = N_seen.get(N, 0) + 1
        H_raw, W_raw = L["H"], L["proposal"]["weights"]
        H = [(F(x[0]), F(x[1])) for x in H_raw]
        W = [[F(x) for x in row] for row in W_raw]
        lh = hashlib.sha256(json.dumps(H_raw).encode()).hexdigest()[:16]
        ck26 = content_key(H_raw, W_raw, N, usha, kernel_sha, KN_SHA, a["sexpt"])
        ck28 = content_key(H_raw, W_raw, N, usha, kernel_sha, KN_SHA,
                           28 if a["escalate"] else a["sexpt"])
        row_bind = dict(snapshot=snap_sha, units=usha, kernel=kernel_sha,
                        kernel_n=KN_SHA, atoms=atoms_sha, n=N)
        hit = None
        for cand_ck, cand_scale in ((ck26, a["sexpt"]),
                                    (ck28, 28 if a["escalate"] else a["sexpt"])):
            if a["cache"] and cand_ck in cache:
                hit = cache[cand_ck]
                ck = cand_ck
                break
        if hit is not None:
            row = dict(idx=idx, ckey=ck, leaf_sha=lh, status="certified",
                       boxes=hit.get("boxes"), leaves=hit.get("leaves"),
                       outside=hit.get("outside"), n_atoms=hit.get("n_atoms"),
                       total=hit.get("total"), max_capture=hit.get("max_capture"),
                       demand=hit.get("demand"), gap=hit.get("gap"), from_cache=True,
                       used_scale=hit.get("scale"), escalated=False,
                       positive_gap=positive_gap(hit),
                       cache_origin=dict(stem=hit.get("origin_stem"),
                                         snapshot=hit.get("origin_snapshot"),
                                         idx=hit.get("origin_idx")), **row_bind)
            cache_hits += 1
        else:
            if a["max_new"] is not None and newly >= a["max_new"]:
                break
            res, used_scale, escalated, A = certify_leaf(N, H, W)
            scale_seen[used_scale] = scale_seen.get(used_scale, 0) + 1
            ck = content_key(H_raw, W_raw, N, usha, kernel_sha, KN_SHA, used_scale)
            rec = L.get("result") or {}
            gapv = res.get("gap_integer")
            row = dict(idx=idx, ckey=ck, leaf_sha=lh, status=res.get("status"),
                       boxes=res.get("boxes"), leaves=res.get("leaves"),
                       outside=res.get("outside"),
                       gap=gapv, used_scale=used_scale, escalated=bool(escalated),
                       scale_attempted=a["sexpt"],
                       positive_gap=bool(gapv is not None and F(gapv) > 0),
                       unresolved_box=res.get("box"),
                       n_atoms=len(A.W), total=A.total,
                       max_capture=res.get("max_integer_capture"),
                       demand=res.get("total_integer_demand"), from_cache=False,
                       diagnostic_recorded_status=rec.get("status"),
                       diagnostic_agrees_recorded=bool(res.get("status") == rec.get("status")),
                       **row_bind)
            if row["positive_gap"] and cfh is not None:
                entry = dict(ckey=ck, status="certified", n=N, scale=used_scale,
                             units=usha, kernel=kernel_sha, kernel_n=KN_SHA,
                             h_sha=hashlib.sha256(json.dumps(H_raw, sort_keys=True).encode()).hexdigest(),
                             w_sha=hashlib.sha256(json.dumps(W_raw, sort_keys=True).encode()).hexdigest(),
                             gap=row["gap"], n_atoms=row["n_atoms"], total=row["total"],
                             boxes=row.get("boxes"), leaves=row.get("leaves"),
                             outside=row.get("outside"), max_capture=row.get("max_capture"),
                             demand=row.get("demand"), scale_provenance="fresh-run",
                             origin_stem=stem, origin_snapshot=snap_sha, origin_idx=idx)
                assert validate_entry(entry), "self-inconsistent cache entry"
                cfh.write(json.dumps(entry) + "\n")
                cache[ck] = entry
            newly += 1
        fh.write(json.dumps(row) + "\n")
        done[idx] = row
        if (newly + cache_hits) and (newly + cache_hits) % 100 == 0:
            fh.flush()
            if cfh is not None:
                cfh.flush()
            rep["atomic_replay"] = _summarize(done, atomic, st, ok, t1, newly, cache_hits)
            atomic_write(SUMMARY, rep)
            print("  [%d/%d] new=%d cache=%d" % (len(done), len(atomic), newly, cache_hits),
                  flush=True)
    fh.close()
    # ---- cache APPEND guard: only a registered production snapshot may grow the cache.
    # A synthetic/control snapshot run against the production cache must never deposit
    # entries into it (that happened once and the acceptance gate caught the changed sha). ----
    append_ok = bool(a.get("append_cache"))
    if not append_ok:
        try:
            import cache_provenance as _CP
            snap_abs = os.path.abspath(SNAP)
            append_ok = any(os.path.abspath(p) == snap_abs
                            for p in _CP.STEM_SNAPSHOT.values())
        except Exception:
            append_ok = False
    if cfh is not None and not append_ok:
        cfh.close()
        cfh = None
    rep["cache_write"] = dict(path=a["cache"], appending=bool(cfh is not None),
                              reason=("registered production snapshot" if append_ok else
                                      "snapshot is not a registered production snapshot; "
                                      "use --append-cache to override"))

    # ---- compact the JSONL: one row per idx, only bound+positive-gap rows are certificates;
    #      unresolved/duplicate rows go to a separate retry log and are NOT counted ----
    compact = {}
    for r in done.values():
        i = r.get("idx")
        if not isinstance(i, int):
            continue
        prev = compact.get(i)
        if prev is None or (positive_gap(r) and not positive_gap(prev)):
            compact[i] = r
    retry = [r for r in retry_rows] + [r for i, r in done.items() if not positive_gap(r)]
    with open(JSONL, "w", encoding="utf-8") as f:
        for i in sorted(compact):
            f.write(json.dumps(compact[i]) + "\n")
    retry_path = os.path.join(OUTDIR, "verify-%s-retry.jsonl" % stem)
    with open(retry_path, "w", encoding="utf-8") as f:
        for r in retry:
            f.write(json.dumps(r) + "\n")
    rep["compaction"] = dict(unique_idx=len(compact),
                             rows_written=len(compact),
                             unresolved_or_duplicate=len(retry),
                             retry_log=os.path.relpath(retry_path, N2 := N12).replace("\\", "/"))
    rep["scale_histogram"] = dict(sorted(scale_seen.items()))
    rep["atomN_histogram"] = dict(sorted(N_seen.items()))

    rep["atomic_replay"] = _summarize(compact, atomic, st, ok, t1, newly, cache_hits)
    rep["structural_checks_pass"] = bool(ok)
    _ = atomic_write(SUMMARY, rep)          # persist for real
    print(json.dumps({k: rep[k] for k in ("out_stem", "manifest_status", "structure",
                                          "partition", "infeasible", "prune3_vs_radical",
                                          "cache", "compaction", "atomN_histogram",
                                          "scale_histogram", "atomic_replay",
                                          "structural_checks_pass")}, indent=1)[:3000])
    print("summary ->", SUMMARY)


def _summarize(done, atomic, st, structural_ok, t1, newly=None, cache_hits=None):
    n = len(atomic)
    cert = sum(1 for r in done.values() if positive_gap(r))
    other = len(done) - cert
    n_unresolved = sum(1 for r in done.values() if r.get("status") == "unresolved")
    n_budget = sum(1 for r in done.values() if r.get("status") == "budget")
    idx_ok = (set(done) == set(range(n)))
    all_cert = (other == 0 and cert == n)
    pending_empty = (len(st.get("pending", [])) == 0)
    if idx_ok and all_cert and structural_ok:
        verdict = "complete" if pending_empty else "complete-for-snapshot(partial frontier)"
    else:
        verdict = "pending"
    return dict(n_atomic=n, replayed=len(done), certified=cert, not_certified=other,
                n_unresolved=n_unresolved, n_budget=n_budget,
                certified_from_cache=sum(1 for r in done.values() if r.get("from_cache")),
                certified_fresh=newly, cache_hits_this_run=cache_hits,
                idx_set_exact=bool(idx_ok), all_certified=bool(all_cert),
                all_positive_gap=bool(all_cert),
                pending_empty=bool(pending_empty),
                structural_checks_pass=bool(structural_ok),
                prunes_and_partition_ok=bool(structural_ok),
                global_certificate=bool(idx_ok and all_cert and structural_ok and pending_empty),
                seconds=time.time() - t1, verdict=verdict,
                rule="global requires: exact partition + all prunes reproduced + every leaf "
                     "bound and certified with gap>0 + empty pending queue")


if __name__ == "__main__":
    main()