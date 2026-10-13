"""n12 -- rigorous interval certification of the K=1 one-hub dual at R = U.

CERTIFICATE SHAPE.  Fix rational weights (a,a',b,b',c) (folded below into
A = 2a, B = 2b, C = c).  For a centre c (polar rho,phi) define

  alpha(rho)  = arccos((1+rho^2-U^2)/(2 rho))            (S^1 arc half-width)
  ell         = |c - h|,  h = (e,0),  cos(psi) = (rho cos phi - e)/ell
  beta        = arccos(min(1, ell/(2U)))                 (arc on |x-h|=U+eps)

  F = A*alpha + B*beta - C*sin(beta)*cos(psi).

Each row of the dual is the arc integral of a NONNEGATIVE weight (1 +- cos/sin)
over the target circle, so for a cover of that circle by the 11 ring discs,
sum_discs (row functional) >= pi.  Hence for any cover

        11 * sup_F  >=  sum_rows w_row * pi = pi * sum(w),

so  pi*sum(w) > 11*sup_F  is a contradiction.  Here sum(w) = 2A + B + C
(folded) and the whole claim is:  sup F over rho in [1-U, sqrt(1-U^2)],
phi in [0,2pi), e in [0, 3U-1]  is  < pi*sum(w)/11.

This script computes a RIGOROUS UPPER BOUND on sup F by interval arithmetic on
a box partition (outward rounding via np.nextafter).  All quantities are
elementary; the only conservative step is the ell-vs-2U crossing, where
beta is enclosed by [0, arccos(min(1,ell_lo/(2U)))].

Run: py -3 certify_U.py [nr] [nphi] [ne] [--exact-weights]
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


# ---------------------------------------------------------- interval ops
def pad_lo(x):
    return np.nextafter(x, -np.inf)


def pad_hi(x):
    return np.nextafter(x, np.inf)


def iadd(a, b):
    return (pad_lo(a[0] + b[0]), pad_hi(a[1] + b[1]))


def isub(a, b):
    return (pad_lo(a[0] - b[1]), pad_hi(a[1] - b[0]))


def imul(a, b):
    p = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (pad_lo(min(p)), pad_hi(max(p)))


def idiv(a, b):
    assert b[0] > 0.0, "divisor interval must be positive"
    p = (a[0] / b[0], a[0] / b[1], a[1] / b[0], a[1] / b[1])
    return (pad_lo(min(p)), pad_hi(max(p)))


def iscale(a, k):
    if k >= 0:
        return (pad_lo(a[0] * k), pad_hi(a[1] * k))
    return (pad_lo(a[1] * k), pad_hi(a[0] * k))


def isqr(a):
    if a[0] >= 0:
        return (pad_lo(a[0] * a[0]), pad_hi(a[1] * a[1]))
    if a[1] <= 0:
        return (pad_lo(a[1] * a[1]), pad_hi(a[0] * a[0]))
    return (0.0, pad_hi(max(a[0] * a[0], a[1] * a[1])))


def isqrt(a):
    lo = max(a[0], 0.0)
    return (pad_lo(math.sqrt(lo)), pad_hi(math.sqrt(max(a[1], 0.0))))


def iacos(a):
    lo = min(1.0, max(-1.0, a[0]))
    hi = min(1.0, max(-1.0, a[1]))
    return (pad_lo(math.acos(hi)), pad_hi(math.acos(lo)))


def _crit(a, b, x0, twopi):
    """does [a,b] contain a point congruent to x0 mod twopi?"""
    k0 = math.ceil((a - x0) / twopi)
    return a <= x0 + k0 * twopi <= b


def iv_sin(a, b):
    lo, hi = math.sin(a), math.sin(b)
    mn, mx = min(lo, hi), max(lo, hi)
    if _crit(a, b, math.pi / 2.0, 2 * math.pi):
        mx = 1.0
    if _crit(a, b, -math.pi / 2.0, 2 * math.pi):
        mn = -1.0
    return (pad_lo(mn), pad_hi(mx))


def iv_cos(a, b):
    lo, hi = math.cos(a), math.cos(b)
    mn, mx = min(lo, hi), max(lo, hi)
    if _crit(a, b, 0.0, 2 * math.pi):
        mx = 1.0
    if _crit(a, b, math.pi, 2 * math.pi):
        mn = -1.0
    return (pad_lo(mn), pad_hi(mx))


# ------------------------------------------------------------- the boxes
def F_interval(rho_iv, phi_iv, e_iv, A, B, C):
    """enclosure of F over the box rho_iv x phi_iv x e_iv (floats as pairs)."""
    r2 = isqr(rho_iv)
    t1 = isub(iadd(r2, (1.0 - U * U, 1.0 - U * U)), (0.0, 0.0))
    t2 = iscale(rho_iv, 2.0)
    g = idiv(t1, t2)
    al = iacos(g)
    # cos(phi), sin(phi)
    cs = iv_cos(*phi_iv)
    sn = iv_sin(*phi_iv)
    # ell = sqrt(rho^2 - 2 rho e cos phi + e^2)
    re = imul(rho_iv, e_iv)
    rec = imul(re, cs)
    e2 = isqr(e_iv)
    ell2 = isub(iadd(r2, e2), iscale(rec, 2.0))
    ell = isqrt(ell2)
    s = iscale(ell, 1.0 / (2.0 * U))
    # beta = acos(min(1,s)) ; sin(beta) = sqrt(1-min(1,s)^2)
    if s[0] >= 1.0:
        beta = (0.0, 0.0)
        sbeta = (0.0, 0.0)
    else:
        beta = iacos((s[0], min(1.0, s[1])))
        sbeta = isqrt((0.0, pad_hi(1.0 - s[0] * s[0])))
    # cos(psi) = (rho cos phi - e)/ell
    num = isub(imul(rho_iv, cs), e_iv)
    cpsi = idiv(num, ell)
    F = iadd(iadd(iscale(al, A), iscale(beta, B)),
             iscale(imul(sbeta, cpsi), -C))
    return F, al, beta, sbeta, cpsi, ell


def certify(A, B, C, nr=160, nphi=1440, ne=12, verbose=False):
    rho_edges = np.linspace(RHO_LO, RHO_HI, nr + 1)
    phi_edges = np.linspace(0.0, 2.0 * np.pi, nphi + 1)
    e_edges = np.linspace(0.0, EMAX, ne + 1)
    worst = (-1e9, None)
    for i in range(nr):
        for k in range(nphi):
            for j in range(ne):
                rho_iv = (float(rho_edges[i]), float(rho_edges[i + 1]))
                phi_iv = (float(phi_edges[k]), float(phi_edges[k + 1]))
                e_iv = (float(e_edges[j]), float(e_edges[j + 1]))
                F, *_ = F_interval(rho_iv, phi_iv, e_iv, A, B, C)
                if F[1] > worst[0]:
                    worst = (F[1], (rho_iv, phi_iv, e_iv, F))
    return worst


def point_check(e, phi, rho, A, B, C):
    """numeric F (float) for control comparison with the original scout."""
    t = math.acos(max(-1.0, min(1.0, (1.0 + rho * rho - U * U) / (2.0 * rho))))
    cx, cy = rho * math.cos(phi), rho * math.sin(phi)
    ell = math.hypot(cx - e, cy)
    psi = math.atan2(cy, cx - e)
    beta = math.acos(min(1.0, ell / (2.0 * U)))
    return A * t + B * beta - C * math.sin(beta) * math.cos(psi)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    nr = int(args[0]) if len(args) > 0 else 160
    nphi = int(args[1]) if len(args) > 1 else 1440
    ne = int(args[2]) if len(args) > 2 else 12
    # folded rational weights from the e=0.04 K=1 dual:
    #   boundary_cos1_+/-1 = 1353362/1000000 ; hub_sin1_+/-1 = 304028/1000000
    #   hub_cos1_-1 = 679222/1000000  =>  A = 2a, B = 2b, C = c
    a = 1353362 / 1000000
    b = 304028 / 1000000
    c = 679222 / 1000000
    A, B, C = 2.0 * a, 2.0 * b, c
    sum_w = A + B + C
    print("folded weights: A=%.6f B=%.6f C=%.6f  sum(w)=%.6f" % (A, B, C, sum_w))
    print("rho in [%.12f, %.12f], phi in [0,2pi), e in [0,%.12f]"
          % (RHO_LO, RHO_HI, EMAX))
    # control 1: point values against a direct evaluation
    for (rr, pp, ee) in ((0.7153703234534302, 0.0, 0.04),
                         (RHO_LO, 0.0, 0.0), (RHO_HI, math.pi, EMAX)):
        print("  control F(%.6f,%.6f,%.6f) = %.9f"
              % (rr, pp, ee, point_check(ee, pp, rr, A, B, C)))
    worst = certify(A, B, C, nr, nphi, ne)
    sup, info = worst
    target = math.pi * sum_w / 11.0
    print("interval certified sup_F <= %.12f  at rho=%s phi=%s e=%s"
          % (sup, info[0], info[1], info[2]))
    print("need sup_F < pi*sum(w)/11 = %.12f   ->  %s"
          % (target, "EXCLUDES k=11 at R=U" if sup < target else "insufficient"))
    out = dict(U=U, EMAX=EMAX, rho=[RHO_LO, RHO_HI], weights=dict(a=a, b=b, c=c),
               folded=dict(A=A, B=B, C=C, sum_w=sum_w),
               boxes=[nr, nphi, ne], certified_sup=sup, target=target,
               excludes=bool(sup < target), worst_box=info[:3])
    Path(__file__).with_name("certify_U_out.json").write_text(
        json.dumps(out, indent=1), encoding="utf8")


if __name__ == "__main__":
    main()
