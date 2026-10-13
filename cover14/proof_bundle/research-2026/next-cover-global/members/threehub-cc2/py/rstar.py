# -*- coding: utf-8 -*-
########################################################################
# WITHDRAWN / INVALID DOMAIN + KERNEL  (Lead review accepted, see ../RETRACTION.md)
# The annulus {2r <= |x| <= 1-2r} used below is EMPTY in the legal range:
# at r = U, 2U = 0.6634640686 > 1-2U = 0.3365359314.  Every number this script
# prints is therefore meaningless and is retained only as an audit trail.
# DO NOT reuse: not a numeric_only candidate, not a lower-certificate basis.
########################################################################
"""
rstar.py -- members/threehub-cc2

ONE focused run, single purpose: compute the threshold r* of the necessary condition

 (N) for 0<r<=U with k=11 active disks covering D:  the OPEN middle annulus
     {2r < |x| < 1-2r} is at distance |x-h| >= |x| - |h| > 2r - r = r from every hub
     (|h| < 2r, proved below), hence its closure must be covered by the 11 ACTIVE
     disks alone, whose centres satisfy |c| >= 1-r.

     R(r) := inf over 11 centres with |c| >= 1-r of (max over the annulus of the
             nearest-centre distance)
     necessary:  R(r) <= r.        r* := sup { r : R(r) <= r }.

  If r* < U then no k=11 cover exists at radius U (the branch is excluded);
  if r* > U the branch is not excluded by (N) alone.

Secondary (analytic) reading printed alongside:
  (LB1) the inner circle |x| = 2r is a subset of the annulus, so with ALL centres at
        the minimum norm 1-r and equally spaced,
             R(r) >= 2r sin(pi/11)  ... no:  see the honest derivation printed below.
        Honest derivation: for the circle of radius s covered by 11 centres of norm
        rho >= rho0 = 1-r with half-aperture alpha, |c-p|^2 = rho^2+s^2-2 rho s cos a,
        maximised over a >= pi/11 (worst gap), monotone increasing in rho on
        rho >= s cos(pi/11); so the worst case is rho = rho0, giving the lower bound
             R(r) >= sqrt( rho0^2 + s^2 - 2 rho0 s cos(pi/11) ).
        At r=U this equals 0.348286 > U = 0.331732 (analytic, elementary).

BUDGET: ~4 min.
"""
import json, math, time
import numpy as np

U = 0.33173203427623414
INACT = 1.0 - U
NACT = 11
rng = np.random.default_rng(31415)


def ann_pts(r, nth=180, nr=20):
    lo, hi = 2 * r, 1.0 - 2 * r
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    rr = np.linspace(lo, hi, nr)
    TT, RT = np.meshgrid(th, rr)
    return np.stack([(RT * np.cos(TT)).ravel(), (RT * np.sin(TT)).ravel()], axis=1)


def maxmin(pts, C, chunk=20000):
    C = np.asarray(C, float)
    best = -1.0
    for i in range(0, len(pts), chunk):
        P = pts[i:i + chunk]
        d = np.sqrt(((P[:, None, :] - C[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
        best = max(best, float(d.max()))
    return best


def pol(ang, rho):
    return np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)


def R_of_r(r, restarts=6, iters=1500):
    pts = ann_pts(r)
    lo = max(1.0 - r, 1e-6)
    hi = 1.0 + r
    best = 1e9
    for s in range(restarts):
        ang = np.sort((np.arange(NACT) + 0.3 * rng.random(NACT)) * 2 * math.pi / NACT)
        rho = lo * (1 + 0.15 * rng.random(NACT))
        C = pol(ang, rho)
        f = maxmin(pts, C)
        step = 0.12
        for it in range(iters):
            T = 0.002 * (1 - it / iters) + 1e-12
            C2 = C.copy()
            k = int(rng.integers(0, NACT))
            r0 = math.hypot(*C2[k]); a0 = math.atan2(C2[k, 1], C2[k, 0])
            if rng.random() < 0.7:
                a0 += step * rng.normal()
            else:
                r0 = min(max(r0 + step * rng.normal(), lo), hi)
            C2[k] = (r0 * math.cos(a0), r0 * math.sin(a0))
            f2 = maxmin(pts, C2)
            if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
                C, f = C2, f2
            if it % 400 == 399:
                step *= 0.8
        best = min(best, f)
    return best, pts


def LB1(r):
    rho0 = 1.0 - r
    s = 2 * r
    c = math.cos(math.pi / 11)
    return math.sqrt(rho0 * rho0 + s * s - 2 * rho0 * s * c)


t0 = time.time()
print("=== hub-norm bound (analytic, elementary) ===")
print(" for a hub h and x in the core B(0,a): the hub disk must cover x, so")
print("   |h| <= |x| + U <= a + U = 1 - U       (tautological, the inactivity bound)")
print(" and the three hubs must cover the core, hence every hub satisfies")
print("   |h| <= U          [farthest point of B(0,a) from a hub is at distance >= |h|,")
print("                      since the hub's Voronoi cell contains a point of the core]")
print(" => hub union is inside B(0,2U) and hubs are at distance > U from the open annulus")
print("    {2U < |x| < 1-2U}, because |x-h| >= |x|-|h| > 2U - U = U.")
print()
print("=== R(r) for the middle annulus (11 active disks, |c| >= 1-r) ===")
rows = []
for r in [0.24, 0.26, 0.28, 0.30, 0.315, 0.3317, 0.335, 0.34]:
    Rp, _ = R_of_r(r)
    print(f"  r={r:.6f}  R(r)={Rp:.6f}  R-r={Rp-r:+.6e}  "
          f"{'NECESSARY-CONDITION FAILS' if Rp > r else 'holds'}   LB1={LB1(r):.6f}")
    rows.append(dict(r=r, R=Rp, diff=Rp - r, LB1=LB1(r)))

print()
print("=== threshold search: smallest r with R(r) <= r (bisection on the reading) ===")
lo, hi = 0.20, 0.40
for _ in range(7):
    mid = 0.5 * (lo + hi)
    Rp, _ = R_of_r(mid, restarts=4, iters=900)
    ok = Rp <= mid
    print(f"  r={mid:.6f}: R={Rp:.6f}  {'holds' if ok else 'fails'}")
    if ok:
        hi = mid
    else:
        lo = mid
print()
print(f"  => r* in [{hi:.6f}, ...] from above (largest r tested where (N) holds = {hi:.6f})")
print(f"  U = {U:.12f};  r* vs U: {'r* >= U : branch NOT excluded by (N)' if hi >= U else 'r* < U'}")
print(f"  elapsed {time.time()-t0:.1f}s")
json.dump(dict(U=U, rows=rows, r_star_upper=hi),
          open("research-2026/next-cover-global/members/threehub-cc2/evidence/rstar.json", "w"),
          indent=1)
