# -*- coding: utf-8 -*-
"""
exp6_k11_2d.py -- members/threehub-cc2

k=11 branch with the CORRECT criterion (2D grid over the closed disk) and the
structural facts that the corrected criterion forces:

  (F1) an active disk (meeting S1) has centre norm in [1-U, 1+U]; in particular it is
       OUTSIDE the open disk of radius 1-U, and no active disk covers any point with
       |x| < 1-2U = a  (|c-x| >= |c|-|x| > (1-U) - a = U).
  (F2) hubs are the only disks covering the core B(0,a); they must cover it; hence
       |h_j| <= U and the hub union is contained in B(0, 2U).
  (F3) the middle annulus {2U <= |x| <= 1-2U} is at distance > U from every hub
       (|x - h| >= |x| - |h| >= 2U - U = U) and every point of it must be covered by
       the 11 active disks.

Search: 11 active centres (angles + radii in [1-U, 1+U]) + hub triple; objective
max over the 2D grid of the nearest-centre distance.  Coarse grid for the search,
fine grid for reporting.  Hub legality C(hub) <= U is checked and reported.

BUDGET 8 min.
"""
import json, math, time, sys
import numpy as np
from fractions import Fraction as F

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U
NACT = 11


def grid2d(n):
    xs = np.linspace(-1.0, 1.0, n)
    X, Y = np.meshgrid(xs, xs)
    m = X * X + Y * Y <= 1.0 + 1e-12
    return np.stack([X[m], Y[m]], axis=1)


PC = grid2d(241)     # coarse ~45k points
PF = grid2d(601)     # fine  ~283k points
TH = np.linspace(0, 2 * math.pi, 4000, endpoint=False)
S1 = np.stack([np.cos(TH), np.sin(TH)], axis=1)

_CT = np.linspace(0, 2 * math.pi, 90, endpoint=False)
_CR = np.linspace(A, 0.0, 45)
_TT, _RT = np.meshgrid(_CT, _CR)
COREPTS = np.stack([(_RT * np.cos(_TT)).ravel(), (_RT * np.sin(_TT)).ravel()], axis=1)

rng = np.random.default_rng(20260101)


def maxmin(pts, C):
    C = np.asarray(C, float)
    d = np.sqrt(((pts[:, None, :] - C[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    k = int(np.argmax(d))
    return float(d[k]), pts[k].tolist()


def core_radius(hub):
    hub = np.asarray(hub, float)
    d = np.sqrt(((COREPTS[:, None, :] - hub[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    return float(d.max())


def build(ang, rho, hub):
    act = np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)
    return np.vstack([hub, act])


def report(ang, rho, hub, pts=PF):
    C = build(ang, rho, hub)
    v, p = maxmin(pts, C)
    v1, p1 = maxmin(S1, C)
    cr = core_radius(hub)
    return dict(coverD_2d=v, worst_pt=[round(q, 6) for q in p],
                coverD_S1=v1, core_radius=cr, core_ok=bool(cr <= U),
                active_ok=bool(rho.min() >= INACT - 1e-12),
                hub_ok=bool(np.linalg.norm(hub, axis=1).max() <= U + 1e-12),
                rho=[round(float(q), 6) for q in rho],
                ang=[round(float(q), 6) for q in ang],
                hub=[[round(float(x), 9) for x in h] for h in hub])


def search(iters=4000, seed=None):
    """variable vector: [11 angles, 11 radii, hub angles (3), hub radius t]"""
    if seed is None:
        ang = np.sort((np.arange(NACT) + 0.4 * rng.random(NACT)) * 2 * math.pi / NACT)
        rho = np.full(NACT, 1.0) + 0.05 * rng.normal(size=NACT)
        hang = np.array([0.0, 2 * math.pi / 3, 4 * math.pi / 3]) + 0.15 * rng.normal(size=3)
        t = float(rng.uniform(0.15, 0.30))
    else:
        ang = np.array(seed[0]); rho = np.array(seed[1])
        hang = np.array(seed[2]); t = float(seed[3])

    def hue(hang, t):
        return np.stack([t * np.cos(hang), t * np.sin(hang)], axis=1)

    rho = np.clip(rho, INACT, 1.0 + U)
    hub = hue(hang, t)
    f = maxmin(PC, build(ang, rho, hub))[0]
    step = 0.12
    for it in range(iters):
        T = 0.0025 * (1 - it / iters) + 1e-11
        ang2, rho2, hang2, t2 = ang.copy(), rho.copy(), hang.copy(), t
        u = rng.random()
        if u < 0.4:
            ang2[int(rng.integers(0, NACT))] += step * rng.normal()
        elif u < 0.7:
            k = int(rng.integers(0, NACT))
            rho2[k] = min(max(rho2[k] + step * rng.normal(), INACT), 1.0 + U)
        elif u < 0.95:
            hang2[int(rng.integers(0, 3))] += step * rng.normal()
        else:
            t2 = min(max(t + step * rng.normal(), 0.02), U)
        hub2 = hue(hang2, t2)
        if core_radius(hub2) > U + 0.002:
            continue
        f2 = maxmin(PC, build(ang2, rho2, hub2))[0]
        if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
            ang, rho, hang, t, f = ang2, rho2, hang2, t2, f2
        if it % 3000 == 2999:
            step = max(step * 0.8, 2e-5)
    return ang, rho, hang, t, f


t0 = time.time()
out = {"schema": "mathlab-evidence/v1", "U": U, "a_core": A, "runs": []}

print("=== controls ===")
d0 = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
Csav = np.array([[float(F(x[0])), float(F(x[1]))] for x in d0["centers"]])
print("  saved construction, 2D fine grid  =", maxmin(PF, Csav)[0])
print("  saved construction, 2D coarse     =", maxmin(PC, Csav)[0])
print("  (both must read 0.331732034276)")
sys.stdout.flush()

print()
print("=== k=11: 11 active + 3 hubs, correct 2D criterion ===")
best = None
for trial in range(10):
    ang, rho, hang, t, f = search(iters=2500)
    hub = np.stack([t * np.cos(hang), t * np.sin(hang)], axis=1)
    rep = report(ang, rho, hub)
    rep["trial"] = trial
    rep["ratio"] = rep["coverD_2d"] / U
    if best is None or rep["coverD_2d"] < best["coverD_2d"]:
        best = rep
    print("  " + json.dumps({k: rep[k] for k in
                             ("trial", "coverD_2d", "coverD_S1", "ratio", "core_radius",
                              "core_ok", "active_ok", "worst_pt")}), flush=True)
    sys.stdout.flush()

out["runs"] = [best]
out["best"] = best
out["elapsed_s"] = time.time() - t0
out["status"] = "inconclusive"
out["summary"] = ("k=11 (2D criterion): best coverD = %.12f = %.6f * U ; core_radius=%.9f "
                  "(U=%.9f)" % (best["coverD_2d"], best["coverD_2d"] / U, best["core_radius"], U))
print()
print(out["summary"])
with open("research-2026/next-cover-global/members/threehub-cc2/evidence/exp6_k11_2d.json",
          "w") as f:
    json.dump(out, f, indent=1)
