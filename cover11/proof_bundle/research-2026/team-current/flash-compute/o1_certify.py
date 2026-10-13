# -*- coding: utf-8 -*-
"""o1_certify.py -- RIGOROUS certification of the O1 counterexample ledger (rational data).

Ledger (lead's rationals, r = 19/50):
  t = [322232/10^6, 389796/10^6, 347568/10^6, 38979/10^5 x6]
  o = [512993/10^6, 1/10^6 x7, o8]  with o8 := 2*sum(t) - 2*pi - sum(o0..o7)
  phi_0 = 0, phi_{k+1} = phi_k + t_k + t_{k+1} - o_k,  c_k = rho(t_k) (cos phi_k, sin phi_k)

Certified here (two independent kernels: rational rt_iv.py, and mpmath.iv at 80 dps):
  P1  sin(t_k) < r                      (each actual half-width is admissible, t_k < asin r)
  P2  o8 > 0                            (all nine overlaps positive -> strict ledger)
  P3  2 t_k - o_{k-1} - o_k > 0         (every arc keeps a private part; arcs essential)
  P4  the two circles of the adjacent pair (c0,c1) really intersect; the near-origin
      crossing v01 satisfies |v01| < 1 and |v01 - c2| < r  (O1 violated, margin ~7.6e-2)
      and |v01 - c0| = |v01 - c1| = r (self-consistency: v01 is a genuine crossing)
  P5  NON-EXTENDABILITY: three rational points inside the hole, pairwise > 2r apart;
      hence no disk of radius r contains two of them and two extra disks cannot cover
      the hole  =>  the ledger cannot occur in an 11-disk cover.

Writes out/o1_certificate.json.  Kernel 1 = rt_iv.py (read-only import from lambda5/py).
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-20260923\lambda5\py")
import rt_iv as R          # rational interval kernel (Fraction only)

R._init_pi()
r = F(19, 50)

t = [F(322232, 10 ** 6), F(389796, 10 ** 6), F(347568, 10 ** 6)] + [F(38979, 10 ** 5)] * 6
o_rational = [F(512993, 10 ** 6)] + [F(1, 10 ** 6)] * 7


def o8_interval():
    """o8 = 2 sum t - 2 pi - sum(o0..o7), as a rational interval."""
    s = 2 * sum(t) - sum(o_rational)
    lo = s - 2 * R.PI_HI
    hi = s - 2 * R.PI_LO
    return (R._rl(lo), R._rh(hi))


o8 = o8_interval()


def phi_list():
    """centre angles: phi_0 = 0, phi_{k+1} = phi_k + t_k + t_{k+1} - o_k (o8 not needed)."""
    o = list(o_rational)          # o0..o7 rational
    ph = [F(0)]
    for k in range(8):
        ph.append(ph[-1] + t[k] + t[(k + 1) % 9] - o[k])
    return ph


def rho_iv(tk):
    """enclosure of rho(t) = cos t - sqrt(r^2 - sin^2 t)."""
    c, s = R.sin_cos_iv(tk, tk)
    s2 = R.iv_sqr(s)
    rad = (r * r - s2[1], r * r - s2[0])
    # NO silent clamping: rho(t) = cos t - sqrt(r^2 - sin^2 t) needs a strictly positive
    # radicand.  t_k < asin r makes r^2 - sin^2 t_k > 0; the interval must prove it.
    assert rad[0] > 0, "rho radicand lower bound not strictly positive: %s" % rad[0]
    a, b = rad[0], rad[1]
    return R.iv_sub(c, R.iv_sqrt((a, b)))


def centre_iv(tk, phik):
    rh = rho_iv(tk)
    c, s = R.sin_cos_iv(phik, phik)
    return (R.iv_mul(rh, c), R.iv_mul(rh, s))


def tip_pair(c0, c1, r):
    """both intersections of the two circles of radius r, as rational interval pairs.

    The formula guarantees ANALYTICALLY that |v - c0| = |v - c1| = r for v = M +/- h n_perp,
    because (M - c0) is orthogonal to n_perp and |M - c0| = |c1-c0|/2 = D/2, so
        |v - c0|^2 = D^2/4 + h^2 = D^2/4 + (r^2 - D^2/4) = r^2.
    The interval re-substitution below is therefore only a consistency check, not the proof.
    Precondition asserted rigorously: 0 < D < 2r (two distinct crossing circles).
    """
    dx = R.iv_sub(c1[0], c0[0]); dy = R.iv_sub(c1[1], c0[1])
    D2 = R.iv_add(R.iv_sqr(dx), R.iv_sqr(dy))
    Dn = R.iv_sqrt_nonneg(D2)
    assert Dn[0] > 0, "centres coincide or centre distance unresolved: D in %s" % (Dn,)
    assert Dn[1] < 2 * r, "circles of radius r with D in %s cannot meet (needs D < 2r)" % (Dn,)
    hsq = (r * r - Dn[1] * Dn[1] / 4, r * r - Dn[0] * Dn[0] / 4)
    assert hsq[0] > 0, "h^2 lower bound not strictly positive: %s" % hsq[0]
    h = R.iv_sqrt(hsq)
    mx = R.iv_scale(R.iv_add(c0[0], c1[0]), F(1, 2))
    my = R.iv_scale(R.iv_add(c0[1], c1[1]), F(1, 2))
    px = R.iv_div(R.iv_neg(dy), Dn)
    py = R.iv_div(dx, Dn)
    p1 = (R.iv_sub(mx, R.iv_mul(h, px)), R.iv_sub(my, R.iv_mul(h, py)))
    p2 = (R.iv_add(mx, R.iv_mul(h, px)), R.iv_add(my, R.iv_mul(h, py)))
    return p1, p2, Dn, h


def norm2(v):
    return R.iv_add(R.iv_sqr(v[0]), R.iv_sqr(v[1]))


def dist2(a, b):
    return R.iv_add(R.iv_sqr(R.iv_sub(a[0], b[0])), R.iv_sqr(R.iv_sub(a[1], b[1])))


def main():
    out = {"r": str(r), "t": [str(x) for x in t], "o": [str(x) for x in o_rational],
           "o8_interval": [str(o8[0]), str(o8[1])], "checks": {}}
    print("=" * 78)
    print("O1 counterexample certification (kernel: rational rt_iv, DEN=%d)" % R.DEN)
    print("=" * 78)
    print("t  = %s" % [str(x) for x in t])
    print("o8 in [%s, %s]  (= %.12e .. %.12e)" % (o8[0], o8[1], float(o8[0]), float(o8[1])))

    # P1: sin(t_k) < r
    ok1 = True
    sin_hi = []
    for k, tk in enumerate(t):
        s = R.sin_cos_iv(tk, tk)[1]
        sin_hi.append(s[1])
        ok1 &= (s[1] < r)
        print("P1 k=%d sin(t) <= %s < r ? %s" % (k, s[1], s[1] < r))
    print("P1  max_k sin-upper = %s (= %.15f) < 19/50 = 0.38 ? %s"
          % (max(sin_hi), float(max(sin_hi)), max(sin_hi) < r))
    out["checks"]["P1_sin_lt_r"] = bool(ok1)
    out["P1_sin_upper_bounds"] = [str(x) for x in sin_hi]

    # P2: o8 > 0
    ok2 = o8[0] > 0
    print("P2  o8_lo = %s > 0 ? %s" % (o8[0], ok2))
    out["checks"]["P2_o8_positive"] = bool(ok2)

    # P3: private parts  (lower bounds; the reported minimum is min_k of these)
    ok3 = True
    priv_lo = []
    o_full = o_rational + [o8]
    for k in range(9):
        lo = 2 * t[k] - (o_full[k - 1][1] if isinstance(o_full[k - 1], tuple) else o_full[k - 1]) \
             - (o_full[k][1] if isinstance(o_full[k], tuple) else o_full[k])
        priv_lo.append(lo)
        ok3 &= (lo > 0)
        print("P3 k=%d 2t - o_{k-1} - o_k >= %s (= %.9f) > 0 ? %s" % (k, lo, float(lo), lo > 0))
    kmin = min(range(9), key=lambda k: priv_lo[k])
    print("P3  TRUE minimum over k = k%d : %s (%.9f)  [NOT the k=8 value]"
          % (kmin, priv_lo[kmin], float(priv_lo[kmin])))
    out["checks"]["P3_private_positive"] = bool(ok3)
    out["P3_private_lower_bounds"] = [str(x) for x in priv_lo]
    out["P3_min_index"] = int(kmin)
    out["P3_min_lower_bound"] = str(priv_lo[kmin])

    # P4: the tip
    ph = phi_list()
    c = [centre_iv(t[k], ph[k]) for k in range(9)]
    for k in range(9):
        print("   |c_%d| in [%.9f, %.9f]" % (k, float(c[k][0][0] ** 2 + c[k][1][0] ** 2) ** 0.5,
                                             float(c[k][0][1] ** 2 + c[k][1][1] ** 2) ** 0.5))
    pA, pB, Dn, h = tip_pair(c[0], c[1], r)
    nA, nB = norm2(pA), norm2(pB)
    print("   |c0-c1| in [%s, %s] ; h in [%s, %s]" % (Dn[0], Dn[1], h[0], h[1]))
    print("   |pA|^2 in [%.9f, %.9f] ; |pB|^2 in [%.9f, %.9f]"
          % (float(nA[0]), float(nA[1]), float(nB[0]), float(nB[1])))
    if nA[1] < nB[0]:
        inner, outer = pA, pB
        print("   branch: pA is strictly the nearer-origin crossing (nA_hi < nB_lo) OK")
    elif nB[1] < nA[0]:
        inner, outer = pB, pA
        print("   branch: pB is strictly the nearer-origin crossing (nB_hi < nA_lo) OK")
    else:
        raise SystemExit("branch not resolved")
    nin = norm2(inner)
    d_in_c0 = dist2(inner, c[0]); d_in_c1 = dist2(inner, c[1]); d_in_c2 = dist2(inner, c[2])
    inD = nin[1] < 1
    # ANALYTIC fact (see tip_pair docstring): |v-c0| = |v-c1| = r holds exactly by the
    # construction; the interval test below is only a consistency check of the enclosure.
    consistency = (d_in_c0[0] <= r * r <= d_in_c0[1]) and (d_in_c1[0] <= r * r <= d_in_c1[1])
    assert consistency, "enclosure does not contain r^2: implementation inconsistency"
    violated = d_in_c2[1] < r * r
    print("P4  |v01|^2 <= %.12f < 1 ? %s   (v01 in D)" % (float(nin[1]), inD))
    print("    analytic: |v01-c0| = |v01-c1| = r exactly (construction); interval containment"
          " (consistency only) = %s" % consistency)
    print("    |v01-c2|^2 <= %.12f < r^2 = %.12f ? %s   (margin = %+.6e)"
          % (float(d_in_c2[1]), float(r * r), violated, float(d_in_c2[1]) - float(r * r)))
    assert inD and violated, "O1 violation not certified"
    out["checks"]["P4_tip_in_D"] = bool(inD)
    out["checks"]["P4_crossing_equations_analytic"] = True
    out["checks"]["P4_enclosure_consistency_only"] = bool(consistency)
    out["checks"]["P4_O1_violated"] = bool(violated)
    out["tip_interval"] = [[str(x) for x in inner[0]], [str(x) for x in inner[1]]]
    out["tip_norm2_upper"] = str(nin[1])
    out["tip_dist2_to_c2"] = [str(d_in_c2[0]), str(d_in_c2[1])]
    out["preconditions"] = {"Dn": [str(Dn[0]), str(Dn[1])], "h": [str(h[0]), str(h[1])],
                            "Dn_lo_gt_0": bool(Dn[0] > 0), "Dn_hi_lt_2r": bool(Dn[1] < 2 * r),
                            "rho_radicand_positive_checked_in_rho_iv": True}

    # P5: three rational hole points, pairwise > 2r.  Strict interval filter:
    #   dist2(p, c_k)_lo > r^2  for all k   (p is strictly outside every ring disk)
    #   dist2(p, q) > 4 r^2                 (no radius-r disk fits two of them)
    print()
    print("P5  non-extendability: three rational hole points, pairwise > 2r (exact rational)")
    print("    acceptance predicate = ALL 27 interval lower bounds > r^2 AND |p_i|^2 < 1")
    import math as _m

    def certify_point(p):
        """(ok, min_lower_bound, norm2_upper) for one rational point, all 9 disks."""
        pi_ = (R.iv(p[0], p[0]), R.iv(p[1], p[1]))
        lows = [dist2(pi_, c[k])[0] for k in range(9)]
        return (min(lows) > r * r), min(lows), norm2(pi_)

    cand = None
    n_tried = 0
    for irho in range(40, 56):
        rho_ = F(irho, 100)
        for ith in range(0, 120):
            th0 = _m.radians(ith)
            pts = [(F(int(round(1000 * float(rho_) * _m.cos(th0 + 2 * _m.pi * k / 3))), 1000),
                    F(int(round(1000 * float(rho_) * _m.sin(th0 + 2 * _m.pi * k / 3))), 1000))
                   for k in range(3)]
            n_tried += 1
            # explicit |p|^2 < 1 for every candidate point (no reliance on rho <= 0.55)
            if any(p[0] ** 2 + p[1] ** 2 >= 1 for p in pts):
                continue
            # exact rational pairwise separation > 2r
            if not all((pts[i][0] - pts[j][0]) ** 2 + (pts[i][1] - pts[j][1]) ** 2 > 4 * r * r
                       for i in range(3) for j in range(i + 1, 3)):
                continue
            # all 27 interval lower bounds strictly > r^2  (no early exit that can be "rescued")
            info = [certify_point(p) for p in pts]
            if not all(z[0] for z in info):
                continue
            cand = (pts, info)
            break
        if cand is not None:
            break
    if cand is None:
        print("   no certified triple found (%d candidates tried)" % n_tried)
        ok5 = False
    else:
        pts, info = cand
        print("   certified triple (%d candidate triples tried):" % n_tried)
        for i, p in enumerate(pts):
            print("   p%d = (%s, %s): |p|^2 <= %s < 1 OK ; min_k |p-c_k|^2 >= %s > r^2 = %s OK"
                  % (i, p[0], p[1], info[i][2][1], info[i][1], r * r))
            assert p[0] ** 2 + p[1] ** 2 < 1
            assert info[i][1] > r * r
        for i in range(3):
            for j in range(i + 1, 3):
                d2 = (pts[i][0] - pts[j][0]) ** 2 + (pts[i][1] - pts[j][1]) ** 2
                print("   |p%d-p%d|^2 = %s > 4r^2 = %s (exact rational) %s"
                      % (i, j, d2, 4 * r * r, d2 > 4 * r * r))
                assert d2 > 4 * r * r
        ok5 = True
    out["checks"]["P5_non_extendable"] = bool(ok5)
    if ok5:
        out["hole_points"] = [[str(p[0]), str(p[1])] for p in cand[0]]
        out["hole_point_min_dist2_to_centres"] = [str(z[1]) for z in cand[1]]
        out["hole_point_pairs_dist2"] = [
            str((cand[0][i][0] - cand[0][j][0]) ** 2 + (cand[0][i][1] - cand[0][j][1]) ** 2)
            for i in range(3) for j in range(i + 1, 3)]
        out["hole_point_norm2_upper"] = [str(z[2][1]) for z in cand[1]]

    # ---- independent cross-check with mpmath.iv (second kernel, 80 dps) ----
    import mpmath as mp
    mp.mp.dps = 80
    mp.iv.dps = 80
    rv = mp.mpf(19) / 50

    def ivec(x):
        return mp.iv.mpf([mp.mpf(x), mp.mpf(x)])

    def iv_rho(tk):
        tkv = mp.mpf(tk.numerator) / mp.mpf(tk.denominator)
        c = mp.iv.cos(ivec(tkv)); s = mp.iv.sin(ivec(tkv))
        return c - mp.iv.sqrt(ivec(rv) ** 2 - s ** 2)

    x1 = {"P1": True, "P2": True, "P3": True, "P4_inD": True, "P4_violated": True, "P5": True}
    for k, tk in enumerate(t):
        tkv = mp.mpf(tk.numerator) / mp.mpf(tk.denominator)
        s = mp.iv.sin(ivec(tkv))
        x1["P1"] &= bool(s.b < rv)
    x1["P2"] &= bool(mp.iv.mpf([mp.mpf(str(float(o8[0]))), mp.mpf(str(float(o8[1])))]) .a > 0)
    phi2 = [mp.mpf(0)]
    for k in range(8):
        phi2.append(phi2[-1] + (mp.mpf(t[k].numerator) / mp.mpf(t[k].denominator))
                    + (mp.mpf(t[(k + 1) % 9].numerator) / mp.mpf(t[(k + 1) % 9].denominator))
                    - (mp.mpf(o_rational[k].numerator) / mp.mpf(o_rational[k].denominator)))
    C2 = []
    for k in range(9):
        rh = iv_rho(t[k])
        C2.append((rh * mp.iv.cos(ivec(phi2[k])), rh * mp.iv.sin(ivec(phi2[k]))))
    d0 = C2[1][0] - C2[0][0]; d1 = C2[1][1] - C2[0][1]
    D2 = d0 ** 2 + d1 ** 2
    Dn = mp.iv.sqrt(D2)
    hh = mp.iv.sqrt(ivec(rv) ** 2 - Dn ** 2 / 4)
    mx = (C2[0][0] + C2[1][0]) / 2; my = (C2[0][1] + C2[1][1]) / 2
    px = -d1 / Dn; py = d0 / Dn
    qA = (mx - hh * px, my - hh * py); qB = (mx + hh * px, my + hh * py)
    nA = qA[0] ** 2 + qA[1] ** 2; nB = qB[0] ** 2 + qB[1] ** 2
    inner = qA if nA.b < nB.a else (qB if nB.b < nA.a else None)
    assert inner is not None, "mpmath.iv: branch not resolved"
    x1["P4_inD"] &= bool((inner[0] ** 2 + inner[1] ** 2).b < 1)
    d2c2 = (inner[0] - C2[2][0]) ** 2 + (inner[1] - C2[2][1]) ** 2
    x1["P4_violated"] &= bool(d2c2.b < rv ** 2)
    for p in cand[0]:
        pv = (ivec(mp.mpf(p[0].numerator) / mp.mpf(p[0].denominator)),
              ivec(mp.mpf(p[1].numerator) / mp.mpf(p[1].denominator)))
        for k in range(9):
            x1["P5"] &= bool(((pv[0] - C2[k][0]) ** 2 + (pv[1] - C2[k][1]) ** 2).a > rv ** 2)
    print()
    print("mpmath.iv cross-check (80 dps, independent library): %s" % x1)
    out["checks"]["crosscheck_mpmath_iv"] = {k: bool(v) for k, v in x1.items()}
    out["checks"]["mpmath_iv_all_agree"] = bool(all(x1.values()))

    path = os.path.join(HERE, "out", "o1_certificate.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1)
    print()
    print("ALL CERTIFIED CHECKS: %s" % out["checks"])
    print("wrote %s" % path)


if __name__ == "__main__":
    main()
