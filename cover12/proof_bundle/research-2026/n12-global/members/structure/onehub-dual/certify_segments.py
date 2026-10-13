"""n12 -- RIGOROUS per-segment interval certificate: no k=11 cover at R=U.

For each e-segment [e_lo,e_hi] of [0, 3U-1] we take the K=1 dual weights
solved at the segment centre (rationalised to 9 decimals), and certify with
outward-rounded interval arithmetic that

    sup over  rho in [1-U, sqrt(1-U^2)], phi in [0,2pi), e in [e_lo,e_hi]
    of   F(rho,phi,e) = sum_r w_r A[r, rho, phi, e]      is  <  pi*sum(w)/11.

The rows A[r] are the nonnegative-weight arc functionals on the two target
circles:
    boundary (circle S^1): alpha, alpha +- sin(alpha)cos(phi),
                                    alpha +- sin(alpha)sin(phi)
    hub      (circle |x-h|=U+eps, eps->0, missed by the hub):
                           beta,  beta +- sin(beta)cos(psi),
                                  beta +- sin(beta)sin(psi)
with alpha = arccos((1+rho^2-U^2)/(2rho)),
     beta  = arccos(min(1, ell/(2U))),  ell = |c-h|,
     cos(psi) = (rho cos phi - e)/ell,  sin(psi) = rho sin phi/ell.

Since every row is (1/2)*integral over the disc's arc of a NONNEGATIVE weight
(1 +- cos, 1 +- sin) and the 11 ring discs cover both circles,
      pi * sum_r w_r  <=  sum_{i=1..11} F(c_i, e)  <=  11 * sup F,
so sup F < pi*sum(w)/11 excludes the k=11 structure at radius U for every hub
offset in the segment.  Union over segments covers e in [0, 3U-1].

Run: py -3 certify_segments.py [K] [nseg] [nr] [nphi] [ne]
"""
import json
import math
import sys
import numpy as np
from scipy.optimize import linprog
from pathlib import Path
from segment_U import atoms, solve_dual

U = 0.361102963744508672616920293904
EMAX = 3.0 * U - 1.0
RHO_LO = 1.0 - U
RHO_HI = math.sqrt(1.0 - U * U)
HERE = Path(__file__).parent


def pl(x):
    return np.nextafter(x, -np.inf)


def ph(x):
    return np.nextafter(x, np.inf)


def imul(a, b):
    return (pl(a[0] * b[0]), ph(a[1] * b[1])) if (a[0] >= 0 and b[0] >= 0) else _imul(a, b)


def _imul(a, b):
    p = np.stack([a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]])
    return (pl(p.min(axis=0)), ph(p.max(axis=0)))


def isqr(a):
    lo = np.where(a[0] >= 0, a[0] * a[0], np.where(a[1] <= 0, a[1] * a[1], 0.0))
    hi = np.maximum(a[0] * a[0], a[1] * a[1])
    return (pl(lo), ph(hi))


def iscale(a, k):
    if k >= 0:
        return (pl(a[0] * k), ph(a[1] * k))
    return (pl(a[1] * k), ph(a[0] * k))


def iacos(a):
    return (pl(np.arccos(np.clip(a[1], -1.0, 1.0))),
            ph(np.arccos(np.clip(a[0], -1.0, 1.0))))


def cos_box(lo, hi):
    mid, w = 0.5 * (lo + hi), 0.5 * (hi - lo)
    c0 = np.cos(mid)
    return (pl(np.clip(c0 - w, -1.0, 1.0)), ph(np.clip(c0 + w, -1.0, 1.0)))


def sin_box(lo, hi):
    mid, w = 0.5 * (lo + hi), 0.5 * (hi - lo)
    s0 = np.sin(mid)
    return (pl(np.clip(s0 - w, -1.0, 1.0)), ph(np.clip(s0 + w, -1.0, 1.0)))


def certify_segment(w, e_lo, e_hi, nr, nphi, ne, chunk=1 << 17):
    nz = np.flatnonzero(w > 1e-12)
    wv = w[nz]
    # row index -> (which row)
    # rows order: boundary_uniform, [b cos1 +1, b cos1 -1, b sin1 +1, b sin1 -1],
    #             hub_uniform, [h cos1 +1, h cos1 -1, h sin1 +1, h sin1 -1]  (K=1)
    worst = -np.inf
    worst_at = None
    redges = np.linspace(RHO_LO, RHO_HI, nr + 1)
    eedges = np.linspace(e_lo, e_hi, ne + 1)
    dphi = 2.0 * np.pi / nphi
    for i in range(nr):
        for j in range(ne):
            for k0 in range(0, nphi, chunk):
                k1 = min(nphi, k0 + chunk)
                n = k1 - k0
                R = (np.full(n, redges[i]), np.full(n, redges[i + 1]))
                E = (np.full(n, eedges[j]), np.full(n, eedges[j + 1]))
                P_lo = k0 * dphi + np.arange(n) * dphi
                P_hi = P_lo + dphi
                cs = cos_box(P_lo, P_hi)
                sn = sin_box(P_lo, P_hi)
                # alpha
                num = (pl(1.0 + isqr(R)[0] - U * U), ph(1.0 + isqr(R)[1] - U * U))
                g = (pl(num[0] / (2.0 * R[1])), ph(num[1] / (2.0 * R[0])))
                al = iacos((g[1], g[0]))            # arccos decreasing in arg
                sal = (pl(np.sin(np.maximum(al[0], 0.0))),
                       ph(np.sin(np.minimum(al[1], np.pi / 2.0))))
                # ell^2 = rho^2 - 2 rho e cos phi + e^2
                re = _imul(R, E)
                rec = _imul(re, (cs[1], cs[0]))
                ell2 = (pl(isqr(R)[0] + isqr(E)[0] - 2.0 * ph(rec[0])),
                        ph(isqr(R)[1] + isqr(E)[1] - 2.0 * pl(rec[1])))
                ell = (np.maximum(np.sqrt(np.maximum(ell2[0], 0.0)), 1e-9),
                       np.sqrt(np.maximum(ell2[1], 1e-9)))
                s2 = (pl(ell[0] / (2.0 * U)), ph(ell[1] / (2.0 * U)))
                s_lo_c = np.minimum(1.0, s2[0])
                s_hi_c = np.minimum(1.0, s2[1])
                beta = (np.arccos(s_hi_c), np.arccos(s_lo_c))   # decreasing
                sb = (pl(np.sin(beta[0])), ph(np.sin(beta[1])))  # beta<=pi/2
                # cos psi, sin psi
                numc = (pl(R[0] * cs[0] - E[1]), ph(R[1] * cs[1] - E[0]))
                nums = _imul(R, sn)
                cpsi = (pl(numc[0] / ell[1]), ph(numc[1] / ell[0]))
                spsi = (pl(nums[0] / ell[1]), ph(nums[1] / ell[0]))
                rows = []
                # order MUST match segment_U.atoms exactly:
                # 0 boundary_uniform, 1 b_cos_-1, 2 b_cos_+1, 3 b_sin_-1,
                # 4 b_sin_+1, 5 hub_uniform, 6 h_cos_-1, 7 h_cos_+1,
                # 8 h_sin_-1, 9 h_sin_+1
                rows.append(al)                                     # 0
                rows.append((pl(al[0] - _imul(sal, cs)[1]),
                             ph(al[1] - _imul(sal, cs)[0])))        # 1
                rows.append((pl(al[0] + _imul(sal, cs)[0]),
                             ph(al[1] + _imul(sal, cs)[1])))        # 2
                rows.append((pl(al[0] - _imul(sal, sn)[1]),
                             ph(al[1] - _imul(sal, sn)[0])))        # 3
                rows.append((pl(al[0] + _imul(sal, sn)[0]),
                             ph(al[1] + _imul(sal, sn)[1])))        # 4
                rows.append(beta)                                   # 5
                rows.append((pl(beta[0] - _imul(sb, cpsi)[1]),
                             ph(beta[1] - _imul(sb, cpsi)[0])))     # 6
                rows.append((pl(beta[0] + _imul(sb, cpsi)[0]),
                             ph(beta[1] + _imul(sb, cpsi)[1])))     # 7
                rows.append((pl(beta[0] - _imul(sb, spsi)[1]),
                             ph(beta[1] - _imul(sb, spsi)[0])))     # 8
                rows.append((pl(beta[0] + _imul(sb, spsi)[0]),
                             ph(beta[1] + _imul(sb, spsi)[1])))     # 9
                Fhi = np.zeros(n)
                for idx, wt in zip(nz, wv):
                    Fhi = Fhi + ph(wt) * rows[idx][1]
                Fhi = ph(Fhi)
                m = float(np.max(Fhi))
                if m > worst:
                    worst = m
                    a = int(np.argmax(Fhi))
                    worst_at = (float(redges[i]), float(P_lo[a]), float(eedges[j]))
    return worst, worst_at


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    nseg = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    nr = int(sys.argv[3]) if len(sys.argv) > 3 else 120
    nphi = int(sys.argv[4]) if len(sys.argv) > 4 else 720
    ne = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    edges = np.linspace(0.0, EMAX, nseg + 1)
    out = dict(U=U, EMAX=EMAX, K=K, boxes=[nr, nphi, ne], segments=[])
    allok = True
    for i in range(nseg):
        lo, hi = float(edges[i]), float(edges[i + 1])
        e0 = 0.5 * (lo + hi)
        w_raw, names = solve_dual(e0, K)
        w = np.round(w_raw, 9)                    # rationalised weights
        sumw_lo = float(np.sum(pl(w)))
        sumw_hi = float(np.sum(ph(w)))
        target_lo = pl(math.pi * sumw_lo / 11.0)
        sup, at = certify_segment(w, lo, hi, nr, nphi, ne)
        ok = bool(sup < target_lo)
        allok &= ok
        print("seg %2d e[%.5f,%.5f]  sum_w=%.9f  target_lo=%.9f  "
              "sup<=%.9f  margin=%+.9f  %s"
              % (i, lo, hi, sumw_lo, target_lo, sup, target_lo - sup,
                 "OK" if ok else "FAIL"), flush=True)
        out["segments"].append(dict(
            e_lo=lo, e_hi=hi, e0=e0, sum_w=sumw_lo, target_lo=target_lo,
            certified_sup=sup, margin=float(target_lo - sup), ok=ok,
            sup_at=at,
            weights=[dict(row=names[j], weight=float(w[j]))
                     for j in range(len(w)) if w[j] > 1e-12]))
    out["excludes_k11"] = bool(allok)
    print("ALL SEGMENTS OK -> excludes k=11 at R=U for every e in [0,3U-1]:",
          allok)
    HERE.joinpath("certify_segments_K%d.json" % K).write_text(
        json.dumps(out, indent=1), encoding="utf8")


if __name__ == "__main__":
    main()
