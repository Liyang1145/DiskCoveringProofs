"""k10_feas.py -- n12 k=10 branch: is a covering configuration of the class
   '10 boundary-active disks (inner-root form, exact arcs) + 2 non-active hubs'
   feasible at a given radius r?

Scope / caution
----------------
This script is a *search/diagnostic* instrument.  R_cand is the max of
f_C(x)=min_i|x-c_i| over the finite candidate set of members/finite-reduction
(antipodes, pair-bisector x S^1, circumcenters in D, fixed (1,0)).  Under the
finite-reduction theorem R_cand = R(C); numerically R_cand is a LOWER-biased
reading of R(C).  Therefore:
  * a returned R_cand <= r is a POSITIVE finding (candidate cover) that still
    needs independent certification;
  * a returned R_cand > r is only evidence about this parametrised family and
    about the local optimiser, never a proof of infeasibility.

Parametrisation of the k=10 family (see lead/INNER-ROOT-REDUCTION.md):
  ring i : halfwidth alpha_i in [0,asin r], angle phi_i,
           norm  rho_i = cos(alpha_i) - sqrt(r^2 - sin^2 alpha_i)   (inner root)
  hub  j : norm t_j in [0,1-r], angle psi_j  (non-active: t_j + r < 1)
Rotation fixed by phi_1 = 0.  Free parameters: 10 + 9 + 4 = 23.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import sys
import time

import numpy as np
from scipy.optimize import minimize

U = 0.361102963744508672616920293904

# ------------------------------------------------------------------ geometry
def rho_minus(alpha, r):
    s = math.sin(alpha)
    inner = r * r - s * s
    return math.cos(alpha) - math.sqrt(max(inner, 0.0))


def make_centers(p, r, tmax):
    """p = [alpha(10), phi(9, ring1 fixed at 0), t(2), psi(2)] -> C (12,2)."""
    al = np.asarray(p[0:10], float)
    ph = np.concatenate([[0.0], np.asarray(p[10:19], float)])
    t = np.clip(np.asarray(p[19:21], float), 0.0, tmax)
    ps = np.asarray(p[21:23], float)
    rho = np.array([rho_minus(a, r) for a in al])
    C = np.empty((12, 2))
    C[:10, 0] = rho * np.cos(ph)
    C[:10, 1] = rho * np.sin(ph)
    C[10:, 0] = t * np.cos(ps)
    C[10:, 1] = t * np.sin(ps)
    return C


# --------------------------------------------------- fast candidate objective
def _tri_index():
    return np.array(list(itertools.combinations(range(12), 3)), dtype=int)


def _pair_index():
    return np.array(list(itertools.combinations(range(12), 2)), dtype=int)


TR = _tri_index()
PR = _pair_index()


def candidate_points(C):
    """Vectorised candidate list; returns (pts (m,2), inside mask) for m candidates."""
    pts = [np.array([[1.0, 0.0]])]
    nrm = np.hypot(C[:, 0], C[:, 1])
    nz = nrm > 1e-15
    if nz.any():
        pts.append(-C[nz] / nrm[nz, None])
    A = C[PR[:, 0]]
    B = C[PR[:, 1]]
    n = B - A
    nn = (n * n).sum(axis=1)
    h = ((B * B).sum(axis=1) - (A * A).sum(axis=1)) / 2.0
    good = nn > 1e-24
    if good.any():
        n2 = n[good]
        q = (h[good] / nn[good])[:, None]
        foot = q * n2
        t2 = 1.0 - (foot * foot).sum(axis=1)
        ok = t2 >= 0.0
        if ok.any():
            foot = foot[ok]
            t = np.sqrt(t2[ok])[:, None]
            ln = np.hypot(n2[ok, 0], n2[ok, 1])[:, None]
            u = np.stack([-n2[ok, 1], n2[ok, 0]], axis=1) / ln
            pts.append(foot + t * u)
            pts.append(foot - t * u)
    a = C[TR[:, 0]]
    b = C[TR[:, 1]]
    c = C[TR[:, 2]]
    v = b - a
    w = c - a
    # Cramer denominator of the 2x2 system [[2v_x,2v_y],[2w_x,2w_y]] = 4*(v x w)
    det = 4.0 * (v[:, 0] * w[:, 1] - v[:, 1] * w[:, 0])
    ok = np.abs(det) > 1e-14
    if ok.any():
        v, w, det = v[ok], w[ok], det[ok]
        a2 = a[ok]
        d1 = (b[ok] * b[ok]).sum(axis=1) - (a2 * a2).sum(axis=1)
        d2 = (c[ok] * c[ok]).sum(axis=1) - (a2 * a2).sum(axis=1)
        x = (d1 * 2.0 * w[:, 1] - 2.0 * v[:, 1] * d2) / det
        y = (2.0 * v[:, 0] * d2 - d1 * 2.0 * w[:, 0]) / det
        circ = np.stack([x, y], axis=1)
        inside = (circ * circ).sum(axis=1) <= 1.0 + 1e-12
        if inside.any():
            pts.append(circ[inside])
    P = np.concatenate(pts, axis=0)
    return P


def R_cand(C):
    P = candidate_points(C)
    D = P[:, None, :] - C[None, :, :]
    dist = np.sqrt((D * D).sum(axis=2))
    f = dist.min(axis=1)
    k = int(np.argmax(f))
    return float(f[k]), P[k], P


def active_info(C, r):
    nrm = np.hypot(C[:, 0], C[:, 1])
    act = nrm + r >= 1.0 - 1e-12
    return act, nrm


# ------------------------------------------------------------------- objective
def objective(p, r, tmax, pen=0.0):
    C = make_centers(p, r, tmax)
    val, _, _ = R_cand(C)
    return val


# ---------------------------------------------------------------- calibration
def calibrate_c182():
    import json as _json
    from fractions import Fraction as F
    path = os.path.join(os.path.dirname(__file__), "..", "..", "..", "..",
                        "session2", "n1314", "cfg", "cert_n12_othern.json")
    cfg = _json.load(open(os.path.normpath(path), encoding="utf-8"))
    C = np.array([[float(F(a)), float(F(b))] for a, b in cfg["centers_dec17"]])
    val, arg, P = R_cand(C)
    act, nrm = active_info(C, U)
    out = dict(R_cand=val, arg=arg.tolist(), U=U, diff=val - U,
               n_candidates=len(P), n_active=int(act.sum()),
               norms=sorted(nrm.tolist()))
    return out


# ------------------------------------------------------------------- search
def random_start(r, tmax, rng, mode):
    al = rng.uniform(0.0, math.asin(min(r, 1.0)), 10)
    if mode == "even":
        ph = np.linspace(0.0, 2 * math.pi, 11)[:-1] + rng.normal(0, 0.02 * math.pi, 10)
        ph = ph - ph[0]
        al = np.full(10, math.pi / 10.0)
    else:
        ph = np.sort(rng.uniform(0.0, 2 * math.pi, 10))
        ph = ph - ph[0]
    t = rng.uniform(0.0, max(tmax, 1e-9), 2)
    ps = rng.uniform(0.0, 2 * math.pi, 2)
    return np.concatenate([al, ph[1:], t, ps])


def hub_start(r, tmax, rng, kind):
    p = random_start(r, tmax, rng, "even")
    if kind == "merged":
        p[19:21] = rng.uniform(0, 0.05, 2)
    elif kind == "antipodal":
        tt = rng.uniform(0.1, min(0.24, tmax), 2)
        p[19:21] = tt
        p[21:23] = [0.0, math.pi + rng.normal(0, 0.1)]
    elif kind == "spread":
        tt = rng.uniform(0.3, tmax, 2)
        p[19:21] = tt
        p[21:23] = rng.uniform(0, 2 * math.pi, 2)
    return p


def search(r, restarts=40, maxfev=6000, seed=12345, tmax=None, verbose=True,
           kinds=("even", "merged", "antipodal", "spread", "rand")):
    rng = np.random.default_rng(seed)
    if tmax is None:
        tmax = 1.0 - r - 1e-9
    best = (np.inf, None)
    t0 = time.time()
    for it in range(restarts):
        kind = kinds[it % len(kinds)]
        if kind in ("merged", "antipodal", "spread"):
            p0 = hub_start(r, tmax, rng, kind)
        else:
            p0 = random_start(r, tmax, rng, "even" if kind == "even" else "rand")
        res = minimize(objective, p0, args=(r, tmax),
                       method="Nelder-Mead",
                       options=dict(maxfev=maxfev, xatol=1e-10, fatol=1e-12,
                                    adaptive=True))
        if res.fun < best[0]:
            best = (float(res.fun), res.x.copy())
            if verbose:
                print("  [%3d/%3d] new best R=%.12f  (kind=%s, t=%.3f, %.3f, "
                      "%.1fs)" % (it + 1, restarts, res.fun, kind,
                                  res.x[19], res.x[20], time.time() - t0))
    return best, tmax


def report(C, r, val):
    act, nrm = active_info(C, r)
    v2, arg2, _ = R_cand(C)
    from candlib import R_ref, sandwich
    ref = R_ref(C, n_grid=801, topk=12)
    sw = sandwich(C, n_grid=1201, chunk=400_000)
    return dict(R_cand=val, R_cand_recheck=v2, arg=arg2.tolist(),
                n_active=int(act.sum()), norms=nrm.tolist(),
                R_ref=ref["value"], R_ref_arg=ref["argmax"].tolist(),
                grid_upper=sw["upper"], lower=sw["lower"], width=sw["width"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mode", default="calibrate")
    ap.add_argument("--r", type=float, default=U)
    ap.add_argument("--restarts", type=int, default=40)
    ap.add_argument("--maxfev", type=int, default=6000)
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--out", default=None)
    ap.add_argument("--tmax", type=float, default=None,
                    help="hub norm cap; default 1-r-1e-9 (strict non-active)")
    args = ap.parse_args()

    sys.path.insert(0, os.path.normpath(os.path.join(os.path.dirname(__file__),
                                                     "..", "..", "finite-reduction", "py")))
    if args.mode == "calibrate":
        out = calibrate_c182()
        print(json.dumps(out, indent=1)[:2000])
    elif args.mode == "search":
        (val, p), tmax = search(args.r, args.restarts, args.maxfev, args.seed,
                                args.tmax)
        C = make_centers(p, args.r, tmax)
        rep = report(C, args.r, val)
        out = dict(r=args.r, tmax=tmax, R_best=val, params=p.tolist(),
                   centers=C.tolist(), report=rep)
        print(json.dumps({k: v for k, v in out.items() if k != "centers"},
                         indent=1))
        if args.out:
            json.dump(out, open(args.out, "w"), indent=1)
    else:
        raise SystemExit("unknown mode")


if __name__ == "__main__":
    main()
