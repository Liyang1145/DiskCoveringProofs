"""Bounded search at the FIXED radius U: minimise the violation of the
necessary conditions for a k=11 cover (see reach.py for the conditions).

Any cover at r <= U can be enlarged to r = U and re-counted, so excluding
k=11 at radius exactly U excludes it for every r <= U.  This script only
searches; it produces evidence of the size of the violation, never a proof.
"""
import json
import sys
import time
import numpy as np
from scipy.optimize import minimize

from reach import (viol_k11, viol_soft_k11, pack_k11, hub_reach,
                   ring_inner)

U = 0.361102963744508672616920293904
E = 3.0 * U - 1.0            # 0.083308891233526017850760881712
LO, HI = 1.0 - U, np.sqrt(1.0 - U * U)


def structured_starts():
    st = []
    th0 = 2 * np.pi * np.arange(11) / 11
    # (a) centred hub, uniform ring, t = S^1 tiling value
    a = np.pi / 11
    t_tile = np.cos(a) - np.sqrt(U * U - np.sin(a) ** 2)
    x = np.zeros(23); x[1:12] = th0
    x[12:23] = np.log((t_tile - LO) / (HI - t_tile))
    x[0] = -30.0
    st.append(x.copy())
    # (b) hub at maximal eccentricity, uniform ring, back direction at a midpoint
    for shift in (0.0, np.pi / 11):
        x = np.zeros(23); x[1:12] = th0 + shift
        x[12:23] = np.log(0.5)
        x[0] = 30.0
        st.append(x.copy())
    # (c) radial disk at the back direction + 10 disks on 36 deg grid
    x = np.zeros(23)
    x[1] = np.pi                       # radial disk opposite the hub (h = (-e,0))
    x[2:12] = np.pi + np.pi / 10 + 2 * np.pi * np.arange(10) / 10
    x[12] = np.log((LO + 1e-6 - LO) / (HI - LO))          # t -> 1-r
    x[13:23] = np.log(0.6)
    x[0] = 30.0
    st.append(x.copy())
    return st


def check(lo_e=True):
    r = U
    rng = np.random.default_rng(11)
    cands = structured_starts()
    for _ in range(140):
        x = np.zeros(23)
        x[0] = rng.normal(0, 1.6)
        x[1:12] = np.sort(rng.uniform(0, 2 * np.pi, 11))
        x[12:23] = rng.normal(0, 0.7, 11)
        cands.append(x)
    best = None
    t0 = time.time()
    for i, x0 in enumerate(cands):
        f = lambda x: viol_soft_k11(r, *pack_k11(r, x), N=224, ksoft=50.0)
        res = minimize(f, x0, method="Powell",
                       options=dict(maxiter=4000, xtol=1e-9, ftol=1e-11))
        v, parts = viol_k11(r, *pack_k11(r, res.x), N=1440)
        if best is None or v < best[0]:
            th, t, e = pack_k11(r, res.x)
            best = (v, parts, e, th.copy(), t.copy())
            print("  new best viol=%.6e parts=%s e=%.6f (%.0fs)"
                  % (v, tuple(round(p, 5) for p in parts), e, time.time() - t0),
                  flush=True)
        if time.time() - t0 > 420:
            print("  time budget hit after %d starts" % (i + 1), flush=True)
            break
    v, parts, e, th, t = best
    out = dict(U=U, e_max=E, violation=float(v),
               parts=dict(S1=parts[0], reach=parts[1], hubcircle=parts[2],
                          hubness=parts[3]),
               e=float(e), theta=np.round(th, 5).tolist(),
               t=np.round(t, 6).tolist(),
               t_range=[round(LO, 6), round(HI, 6)])
    print(json.dumps(out, indent=1))
    json.dump(out, open("fixedU_k11.json", "w"), indent=1)


if __name__ == "__main__":
    check()
