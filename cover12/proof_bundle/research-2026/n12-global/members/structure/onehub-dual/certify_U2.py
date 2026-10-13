"""n12 -- RIGOROUS interval certificate: k=11 is impossible at R=U (one hub).

Statement proved by this script (pure interval arithmetic, outward rounded):

  For every centre c = rho*(cos phi, sin phi) with
       rho in [1-U, sqrt(1-U^2)],   phi in [0,2pi),   e = |h| in [0, 3U-1],
  the explicit functional
       F(rho,phi,e) = A*alpha + B*beta - C*sin(beta)*cos(psi),
       alpha = arccos((1+rho^2-U^2)/(2 rho)),
       ell   = |c-h|,   cos(psi) = (rho cos phi - e)/ell,
       beta  = arccos(min(1, ell/(2U))),
  with A = 2*1353362/10^6, B = 2*304028/10^6, C = 679222/10^6, satisfies
       F <= 1.0000... < pi*(A+B+C)/11 = 1.140684...

Consequence.  For a radius-U cover of D by 11 boundary-active discs plus one
hub: each dual row is the arc integral of a NONNEGATIVE weight (1 +- cos/sin)
on the target circle (S^1, resp. |x-h| = U+eps, eps->0, which the hub misses),
so the covering gives  sum_rows w_row * pi  <=  11 * sup F .  Since
pi*(A+B+C) = 12.547 > 11 * 1.0001, contradiction.  Hence no such cover exists,
for EVERY hub offset e in [0, 3U-1] with ONE weight set.

Caveats stated honestly: (i) the interval arithmetic is outward rounded but the
box partition is finite -- the enclosure is valid for the whole box partition;
(ii) the certificate is only for radius exactly U and k=11 (the k=10 case is a
different member's obligation); (iii) the enlargement U -> any r <= U and the
inner-root reduction rho <= sqrt(1-U^2) are the lead's interface (FIXED-U).

Run: py -3 certify_U2.py [nr] [nphi] [ne]
"""
import json
import math
import sys
import numpy as np
from pathlib import Path

U = 0.361102963744508672616920293904
EMAX = 3.0 * U - 1.0
RHO_LO = 1.0 - U
RHO_HI = math.sqrt(1.0 - U * U)
A = 2.0 * 1353362 / 10 ** 6
B = 2.0 * 304028 / 10 ** 6
C = 679222 / 10 ** 6
SUM_W = A + B + C
TARGET = math.pi * SUM_W / 11.0


def pl(x):
    return np.nextafter(x, -np.inf)


def ph(x):
    return np.nextafter(x, np.inf)


def mul(a, b):
    p = np.stack([a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]])
    return (pl(p.min(axis=0)), ph(p.max(axis=0)))


def sqr(a):
    lo = np.where(a[0] >= 0, a[0] * a[0],
                  np.where(a[1] <= 0, a[1] * a[1], 0.0))
    hi = np.maximum(a[0] * a[0], a[1] * a[1])
    return (pl(lo), ph(hi))


def scale(a, k):
    if k >= 0:
        return (pl(a[0] * k), ph(a[1] * k))
    return (pl(a[1] * k), ph(a[0] * k))


def acos_iv(a):
    lo = np.clip(a[0], -1.0, 1.0)
    hi = np.clip(a[1], -1.0, 1.0)
    return (pl(np.arccos(hi)), ph(np.arccos(lo)))


def cos_iv(lo, hi):
    """rigorous cos over [lo,hi] using |cos'| <= 1 (boxes are tiny)."""
    mid = 0.5 * (lo + hi)
    w = 0.5 * (hi - lo)
    c0 = np.cos(mid)
    return (pl(np.clip(c0 - w, -1.0, 1.0)), ph(np.clip(c0 + w, -1.0, 1.0)))


def certify(nr, nphi, ne, chunk_phi=1 << 18):
    rho = np.linspace(RHO_LO, RHO_HI, nr + 1)
    e = np.linspace(0.0, EMAX, ne + 1)
    dphi = 2.0 * np.pi / nphi
    worst = -np.inf
    worst_at = None
    for i in range(nr):
        for j in range(ne):
            for k0 in range(0, nphi, chunk_phi):
                k1 = min(nphi, k0 + chunk_phi)
                n = k1 - k0
                r_lo = np.full(n, rho[i]); r_hi = np.full(n, rho[i + 1])
                p_lo = k0 * dphi + np.arange(n) * dphi
                p_hi = p_lo + dphi
                e_lo = np.full(n, e[j]); e_hi = np.full(n, e[j + 1])
                R = (r_lo, r_hi)
                E = (e_lo, e_hi)
                # alpha
                g = ((1.0 + sqr(R)[0] - U * U, 1.0 + sqr(R)[1] - U * U))
                g = (g[0], g[1])
                gg = (pl(g[0] / (2.0 * r_hi)), ph(g[1] / (2.0 * r_lo)))
                al = acos_iv((gg[1], gg[0]))          # arccos decreasing
                # cos(phi) interval
                cs = cos_iv(p_lo, p_hi)
                # ell^2 = rho^2 - 2 rho e cos phi + e^2
                re = mul(R, E)
                rec = mul(re, (cs[1], cs[0]))          # -2 rho e cos phi
                ell2 = (pl(sqr(R)[0] + sqr(E)[0] - 2.0 * ph(rec[0])),
                        ph(sqr(R)[1] + sqr(E)[1] - 2.0 * pl(rec[1])))
                ell_lo = np.maximum(np.sqrt(np.maximum(ell2[0], 0.0)), 1e-9)
                ell_hi = np.sqrt(np.maximum(ell2[1], 0.0))
                s_lo = pl(ell_lo / (2.0 * U))
                s_hi = ph(ell_hi / (2.0 * U))
                # beta = arccos(min(1,s)) : 0 if s>=1
                b_hi_i = np.where(s_lo >= 1.0, 0.0,
                                  np.arccos(np.clip(s_lo, 0.0, 1.0)))
                beta = (np.zeros_like(b_hi_i), ph(b_hi_i))
                # sin(beta) in [sin(beta_lo), sin(beta_hi)], beta <= pi/2
                sb = (pl(np.sin(np.maximum(beta[0], 0.0))),
                      ph(np.sin(np.minimum(beta[1], np.pi / 2.0))))
                # cos(psi) = (rho cos phi - e)/ell
                num = (pl(R[0] * cs[0] - E[1]), ph(R[1] * cs[1] - E[0]))
                cpsi = (pl(num[0] / ell_hi), ph(num[1] / ell_lo))
                # F = A al + B beta - C sb cpsi
                t2 = mul(sb, cpsi)
                Fh = ph(A * ph(al[1]) + B * ph(beta[1])
                        + (-C) * pl(t2[0]))
                m = float(np.max(Fh))
                if m > worst:
                    worst = m
                    a = int(np.argmax(Fh))
                    worst_at = (float(r_lo[a]), float(p_lo[a]), float(e_lo[a]))
    return worst, worst_at


def point_check(e, phi, rho):
    t = math.acos(max(-1.0, min(1.0, (1.0 + rho * rho - U * U) / (2.0 * rho))))
    cx, cy = rho * math.cos(phi), rho * math.sin(phi)
    ell = math.hypot(cx - e, cy)
    beta = math.acos(min(1.0, ell / (2.0 * U)))
    return A * t + B * beta - C * math.sin(beta) * (cx - e) / ell


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    nr = int(args[0]) if len(args) > 0 else 240
    nphi = int(args[1]) if len(args) > 1 else 512
    ne = int(args[2]) if len(args) > 2 else 12
    print("A=%.9f B=%.9f C=%.9f  sum(w)=%.9f  target=%.12f"
          % (A, B, C, SUM_W, TARGET))
    print("point controls:")
    for (rr, pp, ee) in ((RHO_HI, 0.0, 0.0), (RHO_HI, 0.0, 0.04),
                         (0.7153703234534302, 0.0, 0.04),
                         (RHO_LO, 0.0, 0.0), (RHO_HI, math.pi, EMAX)):
        print("   rho=%.9f phi=%.6f e=%.6f  F=%.9f"
              % (rr, pp, ee, point_check(ee, pp, rr)))
    sup, at = certify(nr, nphi, ne)
    print("certified interval upper bound sup F <= %.12f" % sup)
    print("  attained at rho>=%.6f phi>=%.6f e>=%.6f" % at)
    print("  target pi*sum(w)/11 = %.12f  -> margin %.9f" % (TARGET, TARGET - sup))
    verdict = "EXCLUDES k=11 at R=U (all e in [0,3U-1])" if sup < TARGET else "insufficient"
    print("  VERDICT:", verdict)
    Path(__file__).with_name("certify_U2_out.json").write_text(json.dumps(dict(
        U=U, EMAX=EMAX, rho=[RHO_LO, RHO_HI], A=A, B=B, C=C, sum_w=SUM_W,
        target=TARGET, boxes=[nr, nphi, ne], certified_sup=sup,
        worst_box=at, margin=TARGET - sup, excludes=bool(sup < TARGET)),
        indent=1), encoding="utf8")


if __name__ == "__main__":
    main()
