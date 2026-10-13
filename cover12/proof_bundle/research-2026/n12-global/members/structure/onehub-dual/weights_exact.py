"""n12 -- hand-off artefact: EXACT RATIONAL K=1 dual weights per e-segment
plus point-algebra calibration (no certification claims here).

Outputs members/structure/onehub-dual/weights_K1_exact.json containing, for
each e-segment of [0, 3U-1], the K=1 dual weights as exact rationals
(numerator/denominator strings), the exact sum, and the row order contract.
Also prints calibration of the row algebra at explicit points against an
independent high-precision evaluation (mpmath if available, else math).

Row contract (must match segment_U.atoms exactly, K=1):
 0 boundary_uniform   = alpha
 1 boundary_cos1_-1   = alpha - sin(alpha) cos(phi)
 2 boundary_cos1_+1   = alpha + sin(alpha) cos(phi)
 3 boundary_sin1_-1   = alpha - sin(alpha) sin(phi)
 4 boundary_sin1_+1   = alpha + sin(alpha) sin(phi)
 5 hub_uniform        = beta
 6 hub_cos1_-1        = beta - sin(beta) cos(psi)
 7 hub_cos1_+1        = beta + sin(beta) cos(psi)
 8 hub_sin1_-1        = beta - sin(beta) sin(psi)
 9 hub_sin1_+1        = beta + sin(beta) sin(psi)
with alpha = arccos((1+rho^2-U^2)/(2 rho)),
     ell   = sqrt(rho^2 - 2 rho e cos phi + e^2),
     beta  = arccos(min(1, ell/(2U))),
     cos psi = (rho cos phi - e)/ell,  sin psi = rho sin phi/ell.
"""
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).parent
U = 0.361102963744508672616920293904
EMAX = 3.0 * U - 1.0

ROWS = ["boundary_uniform", "boundary_cos1_-1", "boundary_cos1_1",
        "boundary_sin1_-1", "boundary_sin1_1", "hub_uniform",
        "hub_cos1_-1", "hub_cos1_1", "hub_sin1_-1", "hub_sin1_1"]


def row_values(rho, phi, e, mp=None):
    """the ten row functionals at one centre, in the listed order."""
    c = mp.cos if mp else math.cos
    s = mp.sin if mp else math.sin
    ac = mp.acos if mp else math.acos
    sq = mp.sqrt if mp else math.sqrt
    cos = c(phi)
    sin = s(phi)
    alpha = ac(max(-1.0, min(1.0, (1.0 + rho * rho - U * U) / (2.0 * rho))))
    ell = sq(rho * rho - 2.0 * rho * e * cos + e * e)
    t = ell / (2.0 * U)
    beta = ac(min(1.0, t))
    cpsi = (rho * cos - e) / ell
    spsi = (rho * sin) / ell
    sa, sb = s(alpha), s(beta)
    return [alpha, alpha - sa * cos, alpha + sa * cos,
            alpha - sa * sin, alpha + sa * sin, beta,
            beta - sb * cpsi, beta + sb * cpsi,
            beta - sb * spsi, beta + sb * spsi]


def main():
    try:
        import mpmath as mp
        mp.mp.dps = 60
        have_mp = True
    except Exception:
        mp = None
        have_mp = False
    print("high precision backend:", "mpmath dps=60" if have_mp else "math")

    sys.path.insert(0, str(HERE))
    from segment_U import solve_dual                      # noqa: E402

    nseg = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    edges = np.linspace(0.0, EMAX, nseg + 1)
    out = dict(U=U, EMAX=EMAX, K=1, row_order=ROWS,
               weights_are="exact rationals (numerator/denominator)",
               segments=[])
    for i in range(nseg):
        lo, hi = float(edges[i]), float(edges[i + 1])
        e0 = 0.5 * (lo + hi)
        w_raw, names = solve_dual(e0, 1)
        assert list(names) == ROWS, (names, ROWS)
        fr = [Fraction(float(x)).limit_denominator(10 ** 9) for x in w_raw]
        sumf = sum(fr, Fraction(0))
        out["segments"].append(dict(
            e_lo=lo, e_hi=hi, e0=e0,
            weights=[dict(row=ROWS[j], num=fr[j].numerator,
                          den=fr[j].denominator,
                          str="%d/%d" % (fr[j].numerator, fr[j].denominator),
                          float=float(fr[j]))
                     for j in range(len(ROWS))],
            sum_num=sumf.numerator, sum_den=sumf.denominator,
            sum_float=float(sumf),
            target_float=math.pi * float(sumf) / 11.0))
        print("seg %2d e[%.5f,%.5f] sum_w=%s=%.9f target=%.9f"
              % (i, lo, hi, sumf, float(sumf), math.pi * float(sumf) / 11.0))
    HERE.joinpath("weights_K1_exact.json").write_text(
        json.dumps(out, indent=1), encoding="utf8")
    print("wrote weights_K1_exact.json")

    # ---------------------------------------------------- point calibration
    print("\npoint-algebra calibration (float pipeline vs high precision):")
    pts = [(1.0 - U, 0.0, 0.0),
           (math.sqrt(1.0 - U * U), 0.0, 0.0),
           (math.sqrt(1.0 - U * U), math.pi, EMAX),
           (0.656603302, math.pi, 0.0),
           (0.740260000, 2.0, 0.03),
           (0.80, 4.5, EMAX),
           (1.0 - U, 0.0, EMAX),
           (0.9, 1.0, 0.05)]
    seg0 = out["segments"][0]
    w0 = [Fraction(s["num"], s["den"]) for s in seg0["weights"]]
    worst = 0.0
    for (rho, phi, e) in pts:
        vf = row_values(rho, phi, e)
        vh = row_values(mp.mpf(rho), mp.mpf(phi), mp.mpf(e), mp=mp) if have_mp else None
        Ff = sum(w0[j] * Fraction(vf[j]) for j in range(10))
        if have_mp:
            Fh = sum(mp.mpf(w0[j].numerator) / w0[j].denominator * vh[j]
                     for j in range(10))
            d = abs(float(Ff - Fh))
            worst = max(worst, d)
        else:
            d = float("nan")
        print("  rho=%.9f phi=%.6f e=%.6f  F_float=%.12f  F_hi=%s  |diff|=%.3e"
              % (rho, phi, e, float(Ff),
                 ("%.12f" % Fh) if have_mp else "n/a", d))
    print("  worst point-algebra discrepancy = %.3e" % worst)


if __name__ == "__main__":
    main()
