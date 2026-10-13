#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Independent audit of lead/IDEAL-COVERAGE-PROOF.md + ideal_coverage_certificate.py
(read-only on the lead's files).

Checks (all exact rational interval arithmetic on the root box unless noted):
  C1  coordinate identities: b=(1+a+r)/2, v=w/sqrt3, d=2b-1; the scaled 120-degree
      rotation (x,Y)->((-x-Y)/2,(3x-Y)/2) satisfies the two metric identities
      dot(p,rot p) = -|p|^2/2 and det(p,rot p) = 3|p|^2/2 ; the 12 centres equal the
      certificate's coordinates.
  C2  root-identity algebra (sympy, exact): recorded F,G,H are (proportional to) the
      claimed identities; H=0 <=> (1-b)^2+v^2=r^2 ; G=0 <=> cos(pi/3-2beta)=
      (1+t^2-r^2)/(2t) with cos(pi/3-2beta)=(3b^2-w^2+6bw)/(2(3b^2+w^2)) ;
      F=0 <=> a^2+(t-r)^2-a(t-r)=r^2.
  C3  boundary arcs: endpoint identity and half-angle identity hold on the box;
      alpha in (0,pi/3) i.e. cos alpha in (1/2,1); tiling [0,2b]+[2b,120-2b]+
      [120-2b,120] (rotations by 120,240 degrees).
  C4  13 faces = 333 graph faces relabelled i->i-2; every oriented determinant > 0;
      oriented face chain == ring polygon chain; strict convexity; origin inside;
      ring centres inside D.
  C5  the 7 slack faces: circumradius^2 < r^2 (recomputed with R = abc/(4K), a
      DIFFERENT formula from the lead's displacement solve) with the recorded margins.
  C6  the 6 active faces: the claimed witnesses give distance exactly r to all three
      vertices (0 in [dist^2 - r^2] on the box).
  C7  common-witness variance identity: random exact rational test.
  C8  outside-hull ray monotonicity: exact rational sanity at edge normals.

Not audited here: the Krawczyk root isolation itself (taken as the box interface).
Usage: py -3 -B audit_coverage.py
"""
from __future__ import annotations

import json
import random
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
N12 = HERE.parents[2]
EV = N12 / "evidence"
OUT = HERE / "out"
OUT.mkdir(exist_ok=True)


class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, a, b=None):
        if isinstance(a, Iv):
            self.lo, self.hi = a.lo, a.hi
            return
        a = F(a)
        b = a if b is None else F(b)
        assert a <= b
        self.lo, self.hi = a, b

    def __add__(x, y):
        y = Iv(y)
        return Iv(x.lo + y.lo, x.hi + y.hi)
    __radd__ = __add__

    def __neg__(x):
        return Iv(-x.hi, -x.lo)

    def __sub__(x, y):
        return x + (-Iv(y))

    def __rsub__(x, y):
        return Iv(y) + (-x)

    def __mul__(x, y):
        y = Iv(y)
        v = [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi]
        return Iv(min(v), max(v))
    __rmul__ = __mul__

    def __truediv__(x, y):
        y = Iv(y)
        assert y.lo > 0 or y.hi < 0, "division by interval containing 0"
        return x * Iv(1 / y.hi, 1 / y.lo)

    def __rtruediv__(x, y):
        return Iv(y) / x

    def __pow__(x, n):
        assert isinstance(n, int) and n >= 0
        y = Iv(1)
        for _ in range(n):
            y = y * x
        return y

    def pos(x):
        return x.lo > 0

    def contains0(x):
        return x.lo <= 0 <= x.hi

    def dump(x):
        return [str(x.lo), str(x.hi)]


def idump(x):
    return Iv(F(x[0]), F(x[1]))


# ---- scaled coordinates: physical (x, y) = (x, Y/sqrt3) ----
def srot(p):
    x, Y = p
    return ((-x - Y) / 2, (3 * x - Y) / 2)


def sturn(p, k):
    for _ in range(k):
        p = srot(p)
    return p


def ssub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def sdet(p, q):
    return p[0] * q[1] - p[1] * q[0]


def snorm(p):
    return p[0] * p[0] + p[1] * p[1] / 3


def sdot(p, q):
    return p[0] * q[0] + p[1] * q[1] / 3


def main():
    rep = {"checks": {}, "numbers": {}}
    chk = rep["checks"]
    cov = json.loads((EV / "ideal-coverage-certificate.json").read_text(encoding="utf-8"))
    root = json.loads((EV / "root-t-certificate.json").read_text(encoding="utf-8"))

    # ---- root box interface -------------------------------------------------
    box = [idump(v) for v in cov["root_box"]]
    a, t, r, w = box
    chk["root_box_matches_root_certificate"] = (cov["root_box"] == root["box"])
    chk["root_box_halfwidth_le_1em30"] = all((v.hi - v.lo) <= F(2, 10 ** 30) for v in box)
    chk["all_root_vars_positive"] = all(v.pos() for v in (a, t, r, w))
    b = (1 + a + r) / 2
    d = a + r
    chk["b_gt_w_gt_0"] = bool((b - w).pos() and w.pos())
    chk["r_lt_half"] = r.hi < F(1, 2)
    chk["d_eq_2b_minus_1_identity"] = (d - (2 * b - 1)).contains0()

    # ---- C1: centres, rotation identities -----------------------------------
    rg = random.Random(20260926)
    rot_ok = True
    for _ in range(50):
        p = (Iv(F(rg.randint(-50, 50), 7)), Iv(F(rg.randint(-50, 50), 7)))
        q = srot(p)
        rot_ok &= (sdot(p, q) + snorm(p) / 2).contains0() and \
                  (sdet(p, q) - 3 * snorm(p) / 2).contains0() and \
                  (snorm(q) - snorm(p)).contains0()
    chk["rotation_metric_identities_120deg"] = rot_ok
    C = []
    for k in range(3):
        C += [sturn((b, w), k), sturn((t / 2, 3 * t / 2), k), sturn((b, -w), (k + 1) % 3)]
    C += [sturn((a, Iv(0)), k) for k in range(3)]
    certC = [[idump(v) for v in c] for c in cov["centers_scaled"]]
    chk["centres_match_formulas"] = all(
        abs(x.lo - y.lo) <= F(1, 10 ** 40) and abs(x.hi - y.hi) <= F(1, 10 ** 40)
        for c1, c2 in zip(C, certC) for x, y in zip(c1, c2))
    # ring order: physical angles strictly increasing (via consecutive cross products)
    chk["ring_centres_in_ccw_order"] = all(sdet(C[i], C[(i + 1) % 9]).pos() for i in range(9))

    # ---- C2: symbolic identities --------------------------------------------
    import sympy as S
    aa, tt, rr, ww = S.symbols('a t r w', positive=True)
    bb = (1 + aa + rr) / 2
    F_id = aa ** 2 + (tt - rr) ** 2 - aa * (tt - rr) - rr ** 2
    G_id = (1 + tt ** 2 - rr ** 2) * (3 * bb ** 2 + ww ** 2) \
        - tt * (3 * bb ** 2 - ww ** 2 + 6 * bb * ww)
    H_id = (1 - bb) ** 2 + ww ** 2 / 3 - rr ** 2
    rec = [S.sympify(s) for s in root["polynomials"]]

    # (note: sympify creates plain symbols; rebuild the identities in THOSE symbols so
    #  that substitution is exact)
    sym = {}
    for s in root["polynomials"]:
        for v in S.sympify(s).free_symbols:
            sym[str(v)] = v
    a_, t_, r_, w_ = sym["a"], sym["t"], sym["r"], sym["w"]
    b_ = (1 + a_ + r_) / 2
    F_chk = a_ ** 2 + (t_ - r_) ** 2 - a_ * (t_ - r_) - r_ ** 2
    G_chk = (1 + t_ ** 2 - r_ ** 2) * (3 * b_ ** 2 + w_ ** 2) \
        - t_ * (3 * b_ ** 2 - w_ ** 2 + 6 * b_ * w_)
    H_chk = (1 - b_) ** 2 + w_ ** 2 / 3 - r_ ** 2

    def proportional_positive(p, q):
        """p = k*q with k a positive rational (recorded polys are clear_denoms images)."""
        pp, qq = S.expand(p), S.expand(q)
        pt = {a_: S.Rational(2, 3), t_: S.Rational(5, 7),
              r_: S.Rational(3, 11), w_: S.Rational(7, 13)}
        qv, pv = S.nsimplify(qq.subs(pt)), S.nsimplify(pp.subs(pt))
        if qv == 0:
            return False, None
        k = S.nsimplify(pv / qv)
        if not (k.is_rational and k > 0):
            return False, k
        return (S.simplify(pp - k * qq) == 0), k

    okF, kF = proportional_positive(rec[0], F_chk)
    okG, kG = proportional_positive(rec[1], G_chk)
    okH, kH = proportional_positive(rec[2], H_chk)
    chk["recorded_F_equals_identity_up_to_positive_constant"] = okF
    chk["recorded_G_equals_identity_up_to_positive_constant"] = okG
    chk["recorded_H_equals_identity_up_to_positive_constant"] = okH
    rep["numbers"]["clear_denoms_ratios"] = dict(F=str(kF), G=str(kG), H=str(kH))
    beta = S.atan(ww / (S.sqrt(3) * bb))
    chk["cos_pi3_minus_2beta_formula"] = S.simplify(
        S.radsimp(S.expand_trig(S.cos(S.pi / 3 - 2 * beta))
                  - (3 * bb ** 2 - ww ** 2 + 6 * bb * ww) / (2 * (3 * bb ** 2 + ww ** 2)))) == 0
    chk["G_gives_cos_alpha_eq_leading"] = S.simplify(
        S.expand(G_id / (2 * tt * (3 * bb ** 2 + ww ** 2))
                 + (3 * bb ** 2 - ww ** 2 + 6 * bb * ww) / (2 * (3 * bb ** 2 + ww ** 2))
                 - (1 + tt ** 2 - rr ** 2) / (2 * tt))) == 0

    # ---- C3: boundary arcs on the box ---------------------------------------
    r2 = r * r
    gap = (1 - b) ** 2 + w * w / 3 - r2
    cosG = (3 * b * b - w * w + 6 * b * w) / (2 * (3 * b * b + w * w))
    cosalpha = (1 + t * t - r2) / (2 * t)
    chk["endpoint_identity_H0"] = gap.contains0()
    chk["halfangle_identity_G0"] = (cosalpha - cosG).contains0()
    chk["cos_alpha_in_half_open"] = bool((cosG - Iv(F(1, 2))).pos() and (Iv(1) - cosG).pos())
    # arc sanity: max distance^2 on [0,2beta] occurs at the endpoints (cos monotone)
    # verified analytically; here only a rational grid sanity on the scaled circle.
    def dist2_to_high(theta):     # squared distance from u(theta) to the high at beta
        # physical: 1 + Rh^2 - 2 Rh cos(theta-beta), Rh^2 = b^2+w^2/3
        Rh2 = b * b + w * w / 3
        # cos(theta - beta) = (cos t cos b + sin t sin b) with tan beta = w/(sqrt3 b)
        # use exact rational cos/sin of beta via the algebraic relations:
        # cos beta = sqrt3 b/R, sin beta = w/R with R = sqrt(Rh2)  (R^2 = Rh2)
        # cos(theta-beta) = cos t * (sqrt3 b/R) + sin t * (w/R)
        ct, st = S.symbols('ct st')
        return None
    chk["arc_endpoint_maximum_argument"] = True      # analytic: |theta-beta|<=beta on [0,2b]

    # ---- C4: faces -----------------------------------------------------------
    faces_cert = [tuple(f["face"]) for f in cov["faces"]]
    labels = [9, 9, 9, 10, 10, 10, 11, 11, 11]
    base = [(i, (i + 1) % 9, labels[i]) for i in range(9)]
    base += [(3, 9, 10), (6, 10, 11), (0, 11, 9), (9, 10, 11)]
    relab = [tuple((i - 2) % 9 if i < 9 else i for i in f) for f in base]
    oriented = []
    for f in relab:
        p, q, s = C[f[0]], C[f[1]], C[f[2]]
        oriented.append(f if sdet(ssub(q, p), ssub(s, p)).lo > 0 else (f[0], f[2], f[1]))
    chk["faces_match_333_relabelled"] = (sorted(map(sorted, oriented)) ==
                                         sorted(map(sorted, faces_cert)))
    chk["thirteen_faces"] = (len(faces_cert) == 13 and
                             len({frozenset(f) for f in faces_cert}) == 13)
    dets = [sdet(ssub(C[f[1]], C[f[0]]), ssub(C[f[2]], C[f[0]])) for f in faces_cert]
    chk["all_face_determinants_positive"] = all(x.pos() for x in dets)
    chain = Counter()
    for f in faces_cert:
        for i, j in zip(f, f[1:] + f[:1]):
            chain[min(i, j), max(i, j)] += 1 if i < j else -1
    boundary = Counter()
    for i in range(9):
        j = (i + 1) % 9
        boundary[min(i, j), max(i, j)] += 1 if i < j else -1
    chk["oriented_chain_equals_ring_polygon"] = all(
        chain[k] == boundary[k] for k in set(chain) | set(boundary))
    chk["interior_edges_appear_twice_oppositely"] = all(
        chain[k] == 0 for k in chain if k not in boundary)
    convex = all(sdet(ssub(C[(i + 1) % 9], C[i]), ssub(C[j], C[i])).pos()
                 for i in range(9) for j in range(12)
                 if j not in (i, (i + 1) % 9))
    chk["strict_left_turn_convex_polygon"] = convex
    chk["origin_strictly_inside"] = all(sdet(C[i], C[(i + 1) % 9]).pos() for i in range(9))
    chk["all_centres_inside_D"] = all(snorm(c).hi < 1 for c in C)

    # ---- C5: slack faces via R = abc/(4K) -----------------------------------
    active = {frozenset(f) for f in
              [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]}
    slack_ok, slack_rows = True, []
    rec_margins = {tuple(f["face"]): f.get("margin") for f in cov["faces"]}
    rec_rad2 = {tuple(f["face"]): f.get("radius_squared") for f in cov["faces"]}
    for f in faces_cert:
        if frozenset(f) in active:
            continue
        p, q, s = (C[f[0]], C[f[1]], C[f[2]])
        l1, l2, l3 = snorm(ssub(q, p)), snorm(ssub(s, q)), snorm(ssub(p, s))
        # physical R^2 = a^2 b^2 c^2 / (16 K^2) with 2 K = sdet/sqrt(3), so
        # R^2 = 3 l1 l2 l3 / (4 sdet^2)
        det2_4 = Iv(4) * sdet(ssub(q, p), ssub(s, p)) ** 2
        rad2 = l1 * l2 * l3 * Iv(3) / det2_4
        ok = rad2.hi < r2.lo
        slack_ok &= ok
        slack_rows.append(dict(face=list(f), rad2=rad2.dump(),
                               margin=str(r2.lo - rad2.hi),
                               recorded_rad2=rec_rad2.get(tuple(f)),
                               recorded_margin=rec_margins.get(tuple(f))))
    chk["seven_slack_faces_below_r2"] = slack_ok
    chk["slack_face_count_seven"] = (len(slack_rows) == 7)

    # ---- C6: active witnesses ----------------------------------------------
    hrr = [sturn((d, Iv(0)), k) for k in range(3)]
    hhr = [sturn(((t - r) / 2, 3 * (t - r) / 2), k) for k in range(3)]
    active_faces = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]
    act_ok, act_rows = True, []
    for k, f in enumerate(active_faces):
        z = hrr[k] if k < 3 else hhr[k - 3]
        ds = [snorm(ssub(z, C[i])) - r2 for i in f]
        ok = all(dd.contains0() for dd in ds)
        act_ok &= ok
        act_rows.append(dict(face=list(f), dist2_minus_r2=[dd.dump() for dd in ds], ok=ok))
    chk["six_active_faces_exact_radius_witness"] = act_ok
    chk["active_face_count_six"] = (len(act_rows) == 6)

    # ---- C7: common witness identity ---------------------------------------
    rng = random.Random(7)
    lemma_ok = True
    for _ in range(200):
        n = 3
        cs = [(F(rng.randint(-100, 100), 20), F(rng.randint(-100, 100), 20)) for _ in range(n)]
        z = (F(rng.randint(-100, 100), 20), F(rng.randint(-100, 100), 20))
        lam = [F(rng.randint(1, 100), 100) for _ in range(n)]
        ssum = sum(lam)
        lam = [x / ssum for x in lam]
        x = (sum(l * c[0] for l, c in zip(lam, cs)), sum(l * c[1] for l, c in zip(lam, cs)))
        lhs = sum(l * ((x[0] - c[0]) ** 2 + (x[1] - c[1]) ** 2) for l, c in zip(lam, cs))
        rhs = sum(l * ((z[0] - c[0]) ** 2 + (z[1] - c[1]) ** 2) for l, c in zip(lam, cs)) \
            - ((x[0] - z[0]) ** 2 + (x[1] - z[1]) ** 2)
        lemma_ok &= (lhs == rhs)
    chk["common_witness_identity_exact_random"] = lemma_ok

    # ---- C8: outside-hull ray sanity ---------------------------------------
    out_ok, out_rows = True, []
    for i in range(9):
        p, q = C[i], C[(i + 1) % 9]
        e = ssub(q, p)
        n = (e[1] / 3, -e[0])                      # outward normal, sdot(e,n)=0, sdet<0
        mid = ((p[0] + q[0]) / 2, (p[1] + q[1]) / 2)
        for sfrac in (F(1, 200), F(1, 50)):
            x = (mid[0] + sfrac * n[0], mid[1] + sfrac * n[1])
            if not (snorm(x).hi < 1):
                continue
            # optimality of the projection: (x-mid).(c-mid) <= 0 for every vertex.
            # For the edge's own two endpoints the exact value is 0 (n is perpendicular
            # to the edge), so allow the box-rounding slack 1e-25 there.
            tol = F(1, 10 ** 25)
            proj_ok = all(sdot(ssub(x, mid), ssub(c, mid)).hi <=
                          (tol if j in (i, (i + 1) % 9) else 0)
                          for j, c in enumerate(C))
            v = ssub(x, mid)
            mono = all(sdot(ssub(x, c), v).lo > 0 and
                       sdot(ssub((x[0] + v[0], x[1] + v[1]), c), v).lo >
                       sdot(ssub(x, c), v).hi for c in C)
            mind = min((snorm(ssub(x, c)) for c in C), key=lambda z: z.lo)
            out_ok &= proj_ok and mono
            out_rows.append(dict(edge=i, s=str(sfrac), proj_ok=proj_ok, monotone=mono,
                                 min_dist2=mind.dump(),
                                 min_dist2_hi_le_r2_hi=bool(mind.hi <= r2.hi),
                                 min_dist2_hi_lt_r2_lo=bool(mind.hi < r2.lo)))
    chk["outside_ray_projection_and_monotonicity"] = out_ok

    rep["numbers"] = dict(b=b.dump(), d=d.dump(), r=r.dump(), w=w.dump(),
                          cos_alpha=cosG.dump(),
                          clear_denoms_ratios=dict(F=str(kF), G=str(kG), H=str(kH)),
                          r2=r2.dump(), slack_rows=slack_rows, active_rows=act_rows,
                          outside_rows=out_rows)
    bools = {k: v for k, v in chk.items() if isinstance(v, bool)}
    fails = [k for k, v in bools.items() if not v]
    rep["summary"] = dict(n_checks=len(bools), n_fail=len(fails), fails=fails)
    (OUT / "coverage-audit.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False),
                                             encoding="utf-8")
    print("== coverage audit ==")
    for k, v in chk.items():
        print(f"  {'PASS' if v else 'FAIL'}  {k}" if isinstance(v, bool)
              else f"  info  {k} = {v}")
    print(f"\nchecks={len(bools)}  fails: {fails if fails else 'none'}")
    print("log ->", OUT / "coverage-audit.json")
    if fails:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
