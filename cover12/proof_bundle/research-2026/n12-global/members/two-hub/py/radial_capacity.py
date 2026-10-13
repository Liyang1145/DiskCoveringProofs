"""radial_capacity.py -- two-layer radial capacity test for the k=10 branch.

Necessary condition used (valid for every cover of D at radius r with 10
boundary-active disks and 2 hubs whose union contains the core B(0,a), a=1-2r):

  Let sigma_0 in (a,1].  Every point sigma_0*u that lies outside the hub union
  must be covered by one of the ten rings.  Hence

    sum_{i=1}^{10} ( measure of ring i on S(0,sigma_0) )  >=  mu(sigma_0)
    sum_{i=1}^{10} ( 2 alpha_i )                          >=  2 pi
  with  mu(sigma_0) = 2pi - |{u : sigma_0 u in H}|  >=  2pi - M_hub(sigma_0),
  M_hub = min(2pi, 2 gamma(t1) + 2 gamma(t2)),  gamma(t)= halfwidth of
  B(t*u,r) cap S(0,sigma_0).

Uniform (angle-independent) relaxation, which is what this script tests:
  for all rho in [1-r, sqrt(1-r^2)]:   2 alpha(rho) + 2 gamma_ring(rho) < (4pi - M_hub)/10
would give the exclusion.  Both sides are computed here as float diagnostics
(falsification only); a certification would redo them in interval arithmetic.
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar, differential_evolution

U = 0.361102963744508672616920293904
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "evidence"


def acos_c(x):
    return math.acos(max(-1.0, min(1.0, x)))


def beta(t, r, a):
    """core-circle halfwidth of a hub at norm t; pi if it covers the core circle."""
    if t <= 0.0:
        return math.pi
    if t + a <= r:
        return math.pi
    if abs(t - a) >= r:
        return 0.0
    return acos_c((t * t + a * a - r * r) / (2 * t * a))


def gamma(t, s, r):
    """halfwidth of B(t*u,r) cap S(0,s); clamps to [0,pi]."""
    if t <= 0.0:
        return math.pi if s <= r else 0.0
    if t + s <= r:
        return math.pi
    if abs(t - s) >= r:
        return 0.0
    return acos_c((t * t + s * s - r * r) / (2 * t * s))


def alpha_of_rho(rho, r):
    """halfwidth of the actual arc of B(c,r) on S^1 for |c|=rho >= 1-r."""
    c = (1.0 + rho * rho - r * r) / (2.0 * rho)
    return acos_c(c)


def gamma_ring(rho, s, r):
    """halfwidth of B(c,r) cap S(0,s) for |c|=rho."""
    if rho + s <= r:
        return math.pi
    if abs(rho - s) >= r:
        return 0.0
    return acos_c((rho * rho + s * s - r * r) / (2.0 * rho * s))


def M_hub_bound(s, r, a, n_grid=4000, local=True):
    """max of 2 gamma(t1)+2 gamma(t2) over {t in [0,1-r]^2 : beta(t1)+beta(t2)>=pi}."""
    tmax = 1.0 - r
    lo, hi = 0.0, tmax

    def neg(t1, t2):
        if beta(t1, r, a) + beta(t2, r, a) < math.pi - 1e-12:
            return 1e6 + (t1 + t2)
        return -(2 * gamma(t1, s, r) + 2 * gamma(t2, s, r))

    ts = np.linspace(lo, hi, n_grid)
    B = np.array([beta(t, r, a) for t in ts])
    G = np.array([gamma(t, s, r) for t in ts])
    best = -1.0
    arg = (0.0, 0.0)
    feasible = []
    for i, t1 in enumerate(ts):
        # need beta(t2) >= pi - B[i]
        need = math.pi - B[i]
        j = np.nonzero(B >= need - 1e-12)[0]
        if len(j) == 0:
            continue
        vals = G[i] + G[j]
        k = int(np.argmax(vals))
        if vals[k] > best:
            best = float(vals[k])
            arg = (float(t1), float(ts[j[k]]))
        feasible.append((t1, float(ts[j[0]]), float(ts[j[-1]])))
    val = 2.0 * best
    if local and best > 0:
        res = differential_evolution(lambda x: neg(x[0], x[1]), [(lo, hi), (lo, hi)],
                                     tol=1e-10, seed=3, polish=True)
        if -res.fun > val:
            val = -res.fun
            arg = (float(res.x[0]), float(res.x[1]))
    return val, arg, feasible


def ring_max(s, r, n=4001, refine=True):
    rho = np.linspace(1.0 - r, math.sqrt(max(1.0 - r * r, 0.0)), n)
    vals = []
    for x in rho:
        a_ = alpha_of_rho(x, r)
        g_ = gamma_ring(x, s, r)
        vals.append(2.0 * a_ + 2.0 * g_)
    vals = np.array(vals)
    k = int(np.argmax(vals))
    best, bestrho = float(vals[k]), float(rho[k])
    if refine:
        f = lambda x: -(2.0 * alpha_of_rho(x, r) + 2.0 * gamma_ring(x, s, r))
        res = minimize_scalar(f, bounds=(1.0 - r, math.sqrt(max(1.0 - r * r, 0.0))),
                              method="bounded", options=dict(xatol=1e-13))
        if -res.fun > best:
            best, bestrho = float(-res.fun), float(res.x)
    return best, bestrho


def scan(r, sigmas=None):
    a = 1.0 - 2.0 * r
    rows = []
    if sigmas is None:
        sigmas = np.linspace(a + 1e-4, min(1.0, a + 2.0 * r), 60)
    for s in sigmas:
        Mh, arg, _ = M_hub_bound(float(s), r, a)
        mu = max(0.0, 2 * math.pi - Mh)
        Req = 2 * math.pi + mu
        C, rho = ring_max(float(s), r)
        rows.append(dict(s=float(s), M_hub=Mh, mu=mu, R_req=Req, C_max=C,
                         C_rho=rho, lhs=10 * C, ok=10 * C < Req,
                         t_arg=arg, ratio=10 * C / Req))
    return rows


def main():
    r = float(sys.argv[1]) if len(sys.argv) > 1 else U
    rows = scan(r)
    print("r=%.12f  a=%.9f" % (r, 1 - 2 * r))
    ok = [x for x in rows if x["ok"]]
    print("sigma_0 grid: %d points, %d with 10*C_max < R_req" % (len(rows), len(ok)))
    best = min(rows, key=lambda x: x["ratio"])
    print("best ratio 10*C/R_req = %.6f at sigma_0=%.6f" % (best["ratio"], best["s"]))
    print("  M_hub=%.6f mu=%.6f R_req=%.6f C_max=%.6f (rho=%.6f, arg=%.4f,%.4f)"
          % (best["M_hub"], best["mu"], best["R_req"], best["C_max"],
             best["C_rho"], best["t_arg"][0], best["t_arg"][1]))
    if ok:
        w = min(ok, key=lambda x: x["ratio"])
        print("PASS example: sigma_0=%.6f ratio=%.6f  (10C=%.6f < R_req=%.6f)"
              % (w["s"], w["ratio"], 10 * w["C_max"], w["R_req"]))
    else:
        print("no sigma_0 on this grid gives the uniform two-layer exclusion")
    print("\nsigma_0, M_hub, mu, R_req, C_max, 10C/R_req, ok")
    for x in rows[::4]:
        print("%.6f  %.4f  %.4f  %.4f  %.4f  %.4f  %s"
              % (x["s"], x["M_hub"], x["mu"], x["R_req"], x["C_max"],
                 x["ratio"], x["ok"]))
    json.dump(dict(r=r, rows=rows, best=best, any_ok=bool(ok)),
              open(OUT / ("radial_capacity_r%.9f.json" % r), "w"), indent=1)


if __name__ == "__main__":
    main()
