"""exact_checker.py -- quantifier-free, denominator-free, EXACT rational checker for
the covering criterion of PROOF-finite-reduction.md / QE-interface.md.

Object: D = closed unit disk, C = finite rational center set, f_C(x)=min_i|x-c_i|,
R(C) = max_D f_C.  The criterion is

    D covered by the disks B(c_i,r)   <=>   A ^ B ^ C ^ D          (r rational, rho=r^2)

with (all data polynomial in c and rho; NO domain quantifier, NO extra variables):

  A = OR_i  |c_i|^2 - 2 c_{i,1} + 1 <= rho                       [fixed point (1,0)]
  B_i = OR_j  a_ij + b_ij * sqrt(s_i) <= 0,
        a_ij = 2 c_i.c_j,  b_ij = |c_j|^2 + 1 - rho,  s_i = |c_i|^2 > 0
        (antipode point of c_i, after clearing the denominator t_i=|c_i|)
  C_ij = AND_{sigma=+-1} OR_k  A'_k - sigma*sqrt(s_ij) * (n^perp.c_k) <= 0,
        n = c_j - c_i, N = |n|^2 > 0, H = |c_j|^2 - |c_i|^2,
        A'_k = N(1 + |c_k|^2 - rho) - H (n.c_k),  s_ij = 4N - H^2 > 0
        (the two bisector-cap-circle points, after clearing 2N)
  D_ijk : with u1 = c_j-c_i, u2 = c_k-c_i, Delta = u1 x u2, H = |c_j|^2-|c_i|^2,
        J = |c_k|^2-|c_i|^2, v = (H u2_y - J u1_y, J u1_x - H u2_x)  [ x = v/(2Delta) ]:
          Delta = 0                -> vacuous (collinear / repeated positions)
          |v|^2 > 4 Delta^2        -> vacuous (circumcenter outside the disk)
          else  OR_m  |v - 2 Delta c_m|^2 <= 4 Delta^2 rho   must hold
        (circumcenter, after clearing 2Delta)

Every sqrt is eliminated by the exact sign-branch rule for a + b*sqrt(s) <= 0 with
rational a,b and rational s > 0 -- no intervals, no floating point anywhere.

Calibration targets (known answers, exact rationals):
  {(0,0)} at r=1 -> TRUE;  r<1 -> FALSE             (R=1)
  {(0,0),(1/2,0)}: R=1
  {(1/2,0),(-1/2,0)}: R=sqrt(5)/2, so rho=5/4 TRUE, rho=31/25 FALSE
  12 centres at the origin: R=1
C182: the saved 17-decimal rational configuration, tested at the registered exact
rational threshold U (read-only reuse; no old evidence is modified).

Usage: py -3 -B exact_checker.py [outfile]
"""
from __future__ import annotations

import itertools
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))

# registered exact rational threshold of claim C182 (lead/FOUNDATIONS.md §3);
# read-only constant, written as an exact rational:
U = F(22568935234031792038557518369, 62500000000000000000000000000)
C182_PATH = os.path.join(HERE, "..", "..", "..", "..", "session2", "n1314", "cfg",
                         "cert_n12_othern.json")


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]


def le_zero_sqrt(a: F, b: F, s: F) -> bool:
    """Exact decision of  a + b*sqrt(s) <= 0  for rational a,b and rational s > 0."""
    if s <= 0:
        raise ValueError("s must be > 0")
    if b == 0:
        return a <= 0
    if a <= 0 and b < 0:
        return True                       # both terms <= 0
    if a > 0 and b > 0:
        return False                      # both terms > 0
    if a <= 0 and b > 0:                  # b*sqrt(s) <= -a, both sides >= 0
        return a * a >= b * b * s
    if a > 0 and b < 0:                   # (-b)*sqrt(s) >= a, both sides >= 0
        return b * b * s >= a * a
    raise AssertionError("unreachable")


def check_domain(C, rho):
    """Explicit domain invariants.  Out-of-domain input must be REJECTED, never
    silently accepted: a violated precondition means the criterion has no meaning.

      * C nonempty;
      * rho >= 0  (rho = r^2, r >= 0);
      * every centre inside the closed unit disk, |c_i|^2 <= 1  (side condition of
        the theorem; centres outside need the radial projection first).
    """
    if len(C) == 0:
        raise AssertionError("domain violation: C is empty")
    if rho < 0:
        raise AssertionError(f"domain violation: rho={rho} < 0")
    for idx, c in enumerate(C):
        nrm2 = dot(c, c)
        if nrm2 > 1:
            raise AssertionError(
                f"domain violation: centre {idx} has |c|^2={nrm2} > 1; "
                "project the centres into D first (FOUNDATIONS §1)")


def criterion(C, r: F, verbose=False):
    """Exact quantifier-free criterion. Returns (ok, parts, diag)."""
    if r < 0:
        raise AssertionError(f"domain violation: r={r} < 0")
    rho = r * r
    check_domain(C, rho)
    n = len(C)
    parts = {}
    diag = {}

    # ---- A : fixed point (1,0)
    parts["A"] = any(dot(c, c) - 2 * c[0] + 1 <= rho for c in C)

    # ---- B : antipodes
    B = True
    B_fail = []
    for i in range(n):
        s = dot(C[i], C[i])
        if s == 0:
            continue                       # guard t_i>0 unsatisfiable -> vacuous
        ok = False
        for j in range(n):
            a = 2 * dot(C[i], C[j])
            b = dot(C[j], C[j]) + 1 - rho
            if le_zero_sqrt(a, b, s):
                ok = True
                break
        if not ok:
            B_fail.append(i)
        B = B and ok
    parts["B"] = B
    diag["B_fail"] = B_fail

    # ---- C : pair bisector cap circle
    Cc = True
    C_fail = []
    for i, j in itertools.combinations(range(n), 2):
        nv = (C[j][0] - C[i][0], C[j][1] - C[i][1])
        N = dot(nv, nv)
        if N == 0:
            continue                       # repeated position -> vacuous
        H = dot(C[j], C[j]) - dot(C[i], C[i])
        s = 4 * N - H * H
        if s <= 0:
            # PROOF L2' guarantees s = 4N - H^2 > 0 for two DISTINCT positions inside D
            # (the bisector always crosses the open disk; no tangency case).  Reaching
            # this branch is out-of-domain input, so raise instead of skipping.
            raise AssertionError(
                f"domain violation: pair ({i},{j}) with N={N}, H={H} gives "
                f"4N-H^2={s} <= 0; PROOF L2' forbids this for distinct centres in D")
        perp = (-nv[1], nv[0])
        for sigma in (1, -1):
            ok = False
            for k in range(n):
                a = N * (1 + dot(C[k], C[k]) - rho) - H * dot(nv, C[k])
                b = -sigma * dot(perp, C[k])
                if le_zero_sqrt(a, b, s):
                    ok = True
                    break
            if not ok:
                C_fail.append((i, j, sigma))
            Cc = Cc and ok
    parts["C"] = Cc
    diag["C_fail"] = C_fail

    # ---- D : circumcentres (only inside D)
    D = True
    D_fail = []
    D_kept = 0
    for i, j, k in itertools.combinations(range(n), 3):
        u1 = (C[j][0] - C[i][0], C[j][1] - C[i][1])
        u2 = (C[k][0] - C[i][0], C[k][1] - C[i][1])
        Delta = u1[0] * u2[1] - u1[1] * u2[0]
        if Delta == 0:
            continue                       # collinear / repeated -> vacuous
        H = dot(C[j], C[j]) - dot(C[i], C[i])
        J = dot(C[k], C[k]) - dot(C[i], C[i])
        v = (H * u2[1] - J * u1[1], J * u1[0] - H * u2[0])
        if dot(v, v) > 4 * Delta * Delta:
            continue                       # circumcentre outside D -> vacuous
        D_kept += 1
        ok = False
        for m in range(n):
            w = (v[0] - 2 * Delta * C[m][0], v[1] - 2 * Delta * C[m][1])
            if dot(w, w) <= 4 * Delta * Delta * rho:
                ok = True
                break
        if not ok:
            D_fail.append((i, j, k))
        D = D and ok
    parts["D"] = D
    diag["D_fail"] = D_fail
    diag["n_kept_circumcentres"] = D_kept

    ok_all = parts["A"] and parts["B"] and parts["C"] and parts["D"]
    if verbose:
        print(f"    parts={parts}  B_fail={B_fail} C_fail={len(C_fail)} "
              f"D_fail={len(D_fail)} kept_cc={D_kept}")
    return ok_all, parts, diag


def load_c182(path=None):
    """Exact rational centres from the saved 17-decimal literals (read-only)."""
    path = path or C182_PATH
    with open(path, encoding="utf-8") as fh:
        obj = json.load(fh)
    obj = obj["centers_dec17"]
    return [(F(str(p[0])), F(str(p[1]))) for p in obj]


def bisect_radius(C, lo: F, hi: F, iters=60):
    """Exact bisection: criterion(hi)=True, criterion(lo)=False -> R in [lo,hi]."""
    ok_hi, _, _ = criterion(C, hi)
    ok_lo, _, _ = criterion(C, lo)
    if not ok_hi or ok_lo:
        raise ValueError(f"bisection bracket invalid: lo_ok={ok_lo} hi_ok={ok_hi}")
    for _ in range(iters):
        mid = (lo + hi) / 2
        ok_mid, _, _ = criterion(C, mid)
        if ok_mid:
            hi = mid
        else:
            lo = mid
    return lo, hi


def selftest_domain():
    """Self-test of the domain invariants: violations must raise, legal input must not.

    Returns (n_pass, failures)."""
    Z = (F(0), F(0))
    half = (F(1, 2), F(0))
    bad = (F(11, 10), F(0))
    must_raise = [
        ("empty C", lambda: criterion([], F(1))),
        ("negative r", lambda: criterion([Z], F(-1))),
        ("negative rho", lambda: criterion_rho([Z], F(-1, 4))),
        ("centre outside D", lambda: criterion([bad], F(1))),
        ("centre outside D (rho-form)", lambda: criterion_rho([bad], F(1, 4))),
    ]
    must_not_raise = [
        ("centre on boundary |c|^2=1", lambda: criterion([(F(1), F(0))], F(1))),
        ("duplicates inside D", lambda: criterion([Z, Z], F(1))),
        ("zero radius, centre at origin", lambda: criterion([Z], F(0))),
    ]
    n_pass, failures = 0, []
    for name, fn in must_raise:
        try:
            fn()
            failures.append(f"{name}: expected AssertionError, none raised")
        except AssertionError:
            n_pass += 1
        except Exception as exc:                        # wrong exception type
            failures.append(f"{name}: expected AssertionError, got "
                            f"{type(exc).__name__}: {exc}")
    for name, fn in must_not_raise:
        try:
            fn()
            n_pass += 1
        except Exception as exc:
            failures.append(f"{name}: unexpected {type(exc).__name__}: {exc}")
    return n_pass, failures


# ------------------------------------------------------------------ driver
def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        HERE, "..", "evidence", "exact-checker.json")
    rows = []

    n_st_pass, st_fail = selftest_domain()
    print(f"domain self-test: {n_st_pass} pass, {len(st_fail)} fail")
    for f in st_fail:
        print("  [FAIL]", f)

    def rec(name, C, r, expect=None):
        ok, parts, diag = criterion(C, r)
        rows.append(dict(kind="known-control", name=name, r=str(r), rho=str(r * r),
                         ok=ok, parts=parts,
                         diag={k: (v if not isinstance(v, list) else v[:8])
                               for k, v in diag.items()},
                         expect=expect))
        tag = "" if expect is None else ("  OK" if ok == expect else "  <== MISMATCH")
        print(f"{name:34s} r={float(r):.17g} rho={float(r*r):.17g} ok={ok}{tag}")
        return ok

    Z = (F(0), F(0))
    # --- calibration on known answers -------------------------------------
    rec("calib-origin-r1", [Z], F(1), True)
    rec("calib-origin-r0.9999", [Z], F(9999, 10000), False)
    rec("calib-origin+half-r1", [Z, (F(1, 2), F(0))], F(1), True)
    rec("calib-origin+half-r0.9999", [Z, (F(1, 2), F(0))], F(9999, 10000), False)
    pair = [(F(1, 2), F(0)), (F(-1, 2), F(0))]

    # rho-probes for cases where r itself is irrational: rho = r^2 is rational,
    # and every conjunct of the criterion uses rho only.
    for nm, rho_val, expect in (("calib-pair-rho5/4", F(5, 4), True),
                                ("calib-pair-rho31/25", F(31, 25), False)):
        okp, partsp, _ = criterion_rho(pair, rho_val)
        rows.append(dict(kind="known-control", name=nm, r=f"sqrt(rho)", rho=str(rho_val),
                         ok=okp, parts=partsp, expect=expect))
        tag = "  OK" if okp == expect else "  <== MISMATCH"
        print(f"{nm:34s} rho={rho_val} ok={okp}{tag}")
    rec("calib-all-zero-12-r1", [Z] * 12, F(1), True)
    rec("calib-all-zero-12-r0.9", [Z] * 12, F(9, 10), False)
    onep = [(F(3, 5), F(4, 5))]
    # single centre c: R = 1 + |c| = 2 for (0.6,0.8)  (note: NOT 1+|c| with |c|=0.8)
    rec("calib-single-0.6-0.8-r2", onep, F(2), True)
    rec("calib-single-0.6-0.8-r1.99", onep, F(199, 100), False)
    rec("calib-single-0.6-0.8-r2.01", onep, F(201, 100), True)

    # --- C182: exact rational configuration at the registered threshold ---
    # This is an INSTANCE evaluation (not an independent known-answer control) and
    # any failure here is a hard error: it must NOT be downgraded to a warning.
    errors = []
    try:
        C = load_c182()
        outside = [i for i, c in enumerate(C) if dot(c, c) > 1]
        print(f"\nC182 (instance, not a control): n={len(C)}  distinct={len(set(C))}  "
              f"centres with |c|^2>1: {outside}")
        okU, partsU, _ = criterion(C, U)          # exact; raises on domain violation
        rows.append(dict(kind="instance", name="c182-at-U", r=str(U), rho=str(U * U),
                         ok=okU, parts=partsU, expect=None))
        print(f"{'c182-at-U':34s} ok={okU}  (instance evaluation, no expectation set)")
        # frozen 52-step bisection bracket around U (no deeper bisection for now)
        lo, hi = bisect_radius(C, F(36, 100), F(37, 100), iters=52)
        print(f"C182 bisection: R in [{lo}, {hi}]  (width {float(hi-lo):.3e})")
        print(f"  U = {float(U):.20g}   lo<U<hi? {lo < U < hi}")
        rows.append(dict(kind="instance", name="c182-bisection", lo=str(lo), hi=str(hi),
                         width=float(hi - lo), U_inside=bool(lo < U < hi),
                         lo_ok=False, hi_ok=True))
    except Exception as exc:                     # hard failure, non-zero exit below
        errors.append(f"C182 processing failed: {type(exc).__name__}: {exc}")
        print(f"[ERROR] {errors[-1]}")

    mism = [r for r in rows if r.get("kind") == "known-control"
            and r.get("expect") is not None and r.get("ok") != r["expect"]]
    errors = errors + st_fail
    summary = dict(status=("error" if errors or mism else "ok"),
                   n_rows=len(rows),
                   n_domain_selftest_pass=n_st_pass,
                   n_known_controls=sum(1 for r in rows
                                        if r.get("kind") == "known-control"),
                   n_calibration_mismatch=len(mism),
                   n_instances=sum(1 for r in rows if r.get("kind") == "instance"),
                   errors=errors, U=str(U), U_float=float(U),
                   note=("C182 rows are instance evaluations, NOT independent controls; "
                         "the known-answer controls are the calib-* rows only. "
                         "Out-of-domain input raises AssertionError (never a silent skip); "
                         "any error or control mismatch exits non-zero."))
    with open(out, "w", encoding="utf-8") as fh:
        json.dump(dict(summary=summary, rows=rows), fh, indent=1)
    print("\n== summary ==")
    print(json.dumps({k: v for k, v in summary.items() if k != "errors"}, indent=1))
    for e in errors:
        print("  ERROR:", e)
    print("log ->", out)
    if errors or mism:
        print(f"[FAIL] errors={len(errors)} calibration_mismatch={len(mism)}")
        raise SystemExit(1)
    print("[OK] all known-answer controls matched; no domain violation encountered")


def criterion_rho(C, rho):
    """Criterion for a rational rho = r^2 directly (r itself need not be rational).

    Every conjunct uses rho only, so the criterion is well defined on rational rho;
    this is the same body as criterion() with the r^2 plumbing removed.
    """
    check_domain(C, rho)
    n = len(C)
    parts = {}
    parts["A"] = any(dot(c, c) - 2 * c[0] + 1 <= rho for c in C)
    B = True
    for i in range(n):
        s = dot(C[i], C[i])
        if s == 0:
            continue
        ok = False
        for j in range(n):
            if le_zero_sqrt(2 * dot(C[i], C[j]), dot(C[j], C[j]) + 1 - rho, s):
                ok = True
                break
        B = B and ok
    parts["B"] = B
    Cc = True
    for i, j in itertools.combinations(range(n), 2):
        nv = (C[j][0] - C[i][0], C[j][1] - C[i][1])
        N = dot(nv, nv)
        if N == 0:
            continue
        H = dot(C[j], C[j]) - dot(C[i], C[i])
        s = 4 * N - H * H
        if s <= 0:
            # out of the legal domain (PROOF L2'): reject, do not silently skip
            raise AssertionError(
                f"domain violation: pair ({i},{j}) with 4N-H^2={s} <= 0")
        perp = (-nv[1], nv[0])
        for sigma in (1, -1):
            ok = False
            for k in range(n):
                a = N * (1 + dot(C[k], C[k]) - rho) - H * dot(nv, C[k])
                b = -sigma * dot(perp, C[k])
                if le_zero_sqrt(a, b, s):
                    ok = True
                    break
            Cc = Cc and ok
    parts["C"] = Cc
    D = True
    for i, j, k in itertools.combinations(range(n), 3):
        u1 = (C[j][0] - C[i][0], C[j][1] - C[i][1])
        u2 = (C[k][0] - C[i][0], C[k][1] - C[i][1])
        Delta = u1[0] * u2[1] - u1[1] * u2[0]
        if Delta == 0:
            continue
        H = dot(C[j], C[j]) - dot(C[i], C[i])
        J = dot(C[k], C[k]) - dot(C[i], C[i])
        v = (H * u2[1] - J * u1[1], J * u1[0] - H * u2[0])
        if dot(v, v) > 4 * Delta * Delta:
            continue
        ok = False
        for m in range(n):
            w = (v[0] - 2 * Delta * C[m][0], v[1] - 2 * Delta * C[m][1])
            if dot(w, w) <= 4 * Delta * Delta * rho:
                ok = True
                break
        D = D and ok
    parts["D"] = D
    return (parts["A"] and B and Cc and D), parts, {}


if __name__ == "__main__":
    main()
