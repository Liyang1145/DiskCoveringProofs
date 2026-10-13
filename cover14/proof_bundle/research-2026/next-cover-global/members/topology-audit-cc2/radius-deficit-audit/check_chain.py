"""Numerical verification (consistency only) of the RADIUS-DEFICIT-LEMMA chain.

Legal domain: unit disk D, covering radius rho<=U; each interior Delaunay facet triangle f has
  - circumradius R_f = distance from its Voronoi vertex O_f to the edge endpoints, with R_f <= U
    (the Voronoi vertex is a primal point covered at radius U: |O_f - site| <= U),
  - angles gamma_f, gamma_g at the two edge endpoints, shared edge length
        2 R_f sin gamma_f = 2 R_g sin gamma_g,
  - beta = pi - gamma_f - gamma_g in (0,pi) (the Voronoi facet crossing angle).

Claimed chain (with x=R_f/U, y=R_g/U, Delta=(gamma_f-gamma_g)/2):
  tau = |x-y|/(x+y) = |tan Delta| tan(beta/2)
  xy <= (1-tau)/(1+tau)          [equivalent to max(x,y) <= 1]
  1-xy >= 2 tau/(1+tau) >= tau
  D_e := U^2 (1-xy) sin beta >= U^2 tau sin beta = U^2 (1-cos beta)|tan Delta|
        >= U^2 (1-cos beta)|Delta|
Reported: violations per step, and the margin of the final inequality over random legal samples.
"""
import random
from fractions import Fraction
from pathlib import Path

from mpmath import mp, mpf, sin, cos, tan, pi, acos

mp.dps = 40
HERE = Path(__file__).resolve().parent
U = mpf('0.33173203427623414')


def main(n=20000):
    random.seed(11)
    v_c1 = v_c2 = v_c3 = v_c4 = 0
    worst3 = mpf('-1e9')
    worst4 = mpf('-1e9')
    tested = 0
    for _ in range(n):
        beta = mpf(random.uniform(1e-6, float(pi) - 1e-6))
        gf = mpf(random.uniform(1e-6, float(pi - beta) - 1e-6))
        gg = pi - beta - gf
        if gg <= 0:
            continue
        Rf = mpf(random.uniform(0.05 * float(U), float(U)))
        Rg = Rf * sin(gf) / sin(gg)
        if Rg <= 0 or Rg > U:
            continue
        tested += 1
        x = Rf / U
        y = Rg / U
        tau = abs(x - y) / (x + y)
        Delta = abs(gf - gg) / 2
        # c1: xy <= (1-tau)/(1+tau)
        if x * y > (1 - tau) / (1 + tau) + mpf('1e-30'):
            v_c1 += 1
        # c2: tau = |tan Delta| tan(beta/2)
        if abs(tau - abs(tan(Delta)) * tan(beta / 2)) > mpf('1e-20'):
            v_c2 += 1
        # c3: tau sin beta >= (1-cos beta)|Delta|
        lhs = tau * sin(beta)
        rhs = (1 - cos(beta)) * Delta
        if lhs < rhs - mpf('1e-25'):
            v_c3 += 1
        worst3 = max(worst3, rhs - lhs)
        # c4: D_e <=> final: U^2(1-xy) sin beta >= U^2(1-cos beta)|Delta|
        D = U * U * (1 - x * y) * sin(beta)
        r4 = U * U * (1 - cos(beta)) * Delta
        if D < r4 - mpf('1e-30'):
            v_c4 += 1
        worst4 = max(worst4, r4 - D)
    out = dict(tested=tested,
               violations_xy_bound=v_c1,
               violations_tau_identity=v_c2,
               violations_tau_sinbeta=dict(count=v_c3, worst_rhs_minus_lhs=str(worst3)),
               violations_final=dict(count=v_c4, worst_rhs_minus_D=str(worst4)),
               note="consistency check only; the chain is proved analytically in the audit note")
    (HERE / "radius-deficit-check.json").write_text(str(out), encoding="utf-8")
    for k, v in out.items():
        print(k, ":", v)


if __name__ == "__main__":
    main()
