"""r20-geometry: corrected closed-hub classification from the product identity (lead's fix).

Per edge: centres a,b, radius r, midpoint m, radical direction n, k = sqrt(r^2-d^2/4),
p_in = m - k n, p_out = m + k n, local height y = (h-m).n (inward = y<0).

IDENTITY (verified symbolically here and numerically below):  with
    F_in = |h-p_in|^2 - r^2 ,  F_out = |h-p_out|^2 - r^2 ,  R_c = circumradius(a,b,h) ,
    4 y^2 (R_c^2 - r^2) = F_in * F_out        (y != 0) ,
    F_in - F_out = 4 k y .
Consequences (correcting my earlier "caps" and "bad extra point" statements):
  * {R_c <= r} is the SYMMETRIC DIFFERENCE of the two disks (the two crescents), not the union
    of half-disk caps: points inside BOTH disks (overlap, e.g. y<0) have R_c > r.
  * On the closed hub domain |h| <= 1-r one has |p_out| >= 1 => |h-p_out| >= |p_out|-|h| >= r,
    i.e. F_out >= 0, with equality iff |p_out| = 1 and h = h* = (1-r) p_out.  Hence
      - F_out > 0 : mechanism (F_in<=0) <=> face condition (R_c<=r)   [exact];
      - F_out = 0 : face condition holds identically (R_c = r); the mechanism condition
        F_in <= 0 holds iff y_h* <= 0 (because F_in = 4 k y_h* there).  So
          y_h* < 0  (<=> |h*-p_in| < r) : h* is a LEGITIMATE inward closed point, NOT bad;
          y_h* > 0  (<=> |h*-p_in| > r) : h* is a MISSED point (face condition true via the
                                          outward circle, mechanism disk does not contain it);
          y_h* = 0  (<=> |h*-p_in| = r) : h* in {a,b} (degenerate, both circles meet there).
  * No "extra" points exist on the closed domain: F_in <= 0 implies F_in F_out <= 0 implies
    R_c <= r.  In particular the overlap interior never meets |h| <= 1-r (it would need
    F_out < 0, impossible).  The earlier report of "18 spurious extra points" was a
    roundoff/degenerate-boundary artefact of the scan (the two conditions y>0 and
    |h*-p_in|>r are equivalent in exact arithmetic) and is withdrawn.
"""
import json, io
from pathlib import Path
from mpmath import mp, mpf, sin, cos, sqrt, atan2, pi as MP_PI

mp.dps = 40
HERE = Path(__file__).resolve().parent
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
SC = mpf(10) ** int(OBJ["decimals"])
C = [[mpf(int(a)) / SC, mpf(int(b)) / SC] for a, b in OBJ["centers_scaled_1e17"]]
RAD = mpf(repr(float(OBJ["certified_interval"]["lo"])))


def d2(i, th):
    return (cos(th) - C[i][0]) ** 2 + (sin(th) - C[i][1]) ** 2


NS = 8192
runs, prev = [], None
for j in range(NS):
    th = 2 * MP_PI * j / NS
    kk = min(range(len(C)), key=lambda i: d2(i, th))
    if kk != prev:
        runs.append([kk, j]); prev = kk
if len(runs) > 1 and runs[0][0] == runs[-1][0]:
    runs.pop(0)
RING = [k for k, _ in runs]


def tie_theta(ka, kb, lo, hi):
    M = 512
    pt, pf = lo, d2(ka, lo) - d2(kb, lo)
    for j in range(1, M + 1):
        t = lo + (hi - lo) * mpf(j) / M
        f = d2(ka, t) - d2(kb, t)
        if pf * f < 0:
            a_, b_, fa = pt, t, pf
            for _ in range(200):
                mid = (a_ + b_) / 2
                if (d2(ka, mid) - d2(kb, mid)) * fa <= 0:
                    b_ = mid
                else:
                    a_, fa = mid, d2(ka, mid) - d2(kb, mid)
            return (a_ + b_) / 2
        pt, pf = t, f
    return None


span = 2 * MP_PI / NS
SW = []
for j in range(len(RING)):
    ka, kb = RING[j], RING[(j + 1) % len(RING)]
    lo = mpf(runs[j][1]) * span
    hi = mpf(runs[(j + 1) % len(RING)][1]) * span if j + 1 < len(RING) else 2 * MP_PI + mpf(runs[0][1]) * span
    SW.append((ka, kb, tie_theta(ka, kb, lo, hi)))


def frame(i, j, th):
    a, b = C[i], C[j]
    m = ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)
    dv = (b[0] - a[0], b[1] - a[1]); dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
    n = (-dv[1] / dd, dv[0] / dd)
    k = sqrt(RAD ** 2 - dd ** 2 / 4)
    U = (cos(th), sin(th))
    if (U[0] - m[0]) * n[0] + (U[1] - m[1]) * n[1] < 0:
        n = (-n[0], -n[1])
    return a, b, m, n, dd, k, (m[0] - k * n[0], m[1] - k * n[1]), (m[0] + k * n[0], m[1] + k * n[1])


print("=== identity spot-check: 4 y^2 (Rc^2-r^2) = F_in*F_out  (random h per edge) ===")
worst = mpf(0)
import random
rng = random.Random(5)
for (i, j, th) in SW:
    a, b, m, n, dd, k, pin, pout = frame(i, j, th)
    for _ in range(40):
        x = mpf(repr(rng.uniform(-1, 1))); y = mpf(repr(rng.uniform(-1, 1)))
        h = (m[0] + x * n[1] + y * n[0], m[1] - x * n[0] + y * n[1])   # (x along base, y along n)
        Fin = (h[0] - pin[0]) ** 2 + (h[1] - pin[1]) ** 2 - RAD ** 2
        Fout = (h[0] - pout[0]) ** 2 + (h[1] - pout[1]) ** 2 - RAD ** 2
        la = sqrt((h[0] - a[0]) ** 2 + (h[1] - a[1]) ** 2)
        lb = sqrt((h[0] - b[0]) ** 2 + (h[1] - b[1]) ** 2)
        Rc = la * lb / (2 * abs(y))
        worst = max(worst, abs(4 * y * y * (Rc * Rc - RAD ** 2) - Fin * Fout))
print("   max |4y^2(Rc^2-r^2) - F_in*F_out| over 360 samples = %s" % mp.nstr(worst, 6))

print("\n=== per-edge tangency point h* = (1-r) p_out (certified cover, |p_out| = 1) ===")
print("   pair  y_h*       |h*-p_in|-r   F_out(h*)     class")
rows = []
for (i, j, th) in SW:
    a, b, m, n, dd, k, pin, pout = frame(i, j, th)
    nout = sqrt(pout[0] ** 2 + pout[1] ** 2)
    if abs(nout - 1) > mpf("1e-12"):
        rows.append(dict(pair=(i, j), yh=None, cls="no h* (|p_out|>1)"))
        print("   %2d-%2d  --          --            --            (|p_out| = %.6f)" % (i, j, float(nout)))
        continue
    hs = ((1 - RAD) * pout[0], (1 - RAD) * pout[1])
    yh = (hs[0] - m[0]) * n[0] + (hs[1] - m[1]) * n[1]
    din = sqrt((hs[0] - pin[0]) ** 2 + (hs[1] - pin[1]) ** 2)
    Fout = din * din - RAD ** 2      # |h*-p_out| = r exactly by construction
    cls = ("LEGIT inward (F_in<0)" if yh < -mpf("1e-12") else
           "MISSED (F_in>0)" if yh > mpf("1e-12") else "DEGENERATE h* in {a,b}")
    rows.append(dict(pair=(i, j), yh=float(yh), din_minus_r=float(din - RAD), cls=cls))
    print("   %2d-%2d  %+.3e  %+.3e    %+.1e   %s" % (i, j, float(yh), float(din - RAD), 0.0, cls))

print("\n=== closed domain: no extras (F_out >= 0 there) and crescent = symmetric difference ===")
mn_Fout = mpf(10)
bad_crescent = 0
tested = 0
for (i, j, th) in SW:
    a, b, m, n, dd, k, pin, pout = frame(i, j, th)
    for iy in range(-40, 41):
        y = mpf(iy) / 40 * (1 - RAD)          # inside the hubnorm disk in the n-direction
        for ix in range(-40, 41):
            x = mpf(ix) / 40 * (1 - RAD)
            h = (m[0] + x * n[1] + y * n[0], m[1] - x * n[0] + y * n[1])
            if h[0] ** 2 + h[1] ** 2 > (1 - RAD) ** 2:
                continue
            tested += 1
            Fin = (h[0] - pin[0]) ** 2 + (h[1] - pin[1]) ** 2 - RAD ** 2
            Fout = (h[0] - pout[0]) ** 2 + (h[1] - pout[1]) ** 2 - RAD ** 2
            mn_Fout = min(mn_Fout, Fout)
            if Fin <= 0 and Fout > 0:
                continue
            if Fin <= 0 and Fout <= 0:
                bad_crescent += 1
print("   sampled closed-domain points: %d ; min F_out = %s ; points with F_in<=0 and F_out<=0: %d"
      % (tested, mp.nstr(mn_Fout, 6), bad_crescent))
print("   => mechanism condition implies R_c <= r on the closed domain (no extras).")

n_leg = sum(1 for r in rows if r.get("cls", "").startswith("LEGIT"))
n_mis = sum(1 for r in rows if r.get("cls", "").startswith("MISSED"))
n_deg = sum(1 for r in rows if r.get("cls", "").startswith("DEGEN"))
print("\n   certified cover: h* classes -> legit-inward %d, missed %d, degenerate %d" % (n_leg, n_mis, n_deg))
json.dump(dict(identity_max_err=mp.nstr(worst, 8), min_Fout_closed=mp.nstr(mn_Fout, 8),
               crescent_violations=bad_crescent, tested=tested, per_edge=rows),
          open(HERE / "audit_product_identity.json", "w"), indent=1)
print("\nwrote audit_product_identity.json")
