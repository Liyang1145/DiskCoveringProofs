# -*- coding: utf-8 -*-
"""C849 neighbour-centre identities: eta/alpha/L, constants and uniform bounds.

Exact/complex-algebraic identities plus high-precision identity checks (calibration only).
No kernel re-audit, no sign-monotonicity re-check.
"""
import sympy as sp
import mpmath as mp
mp.mp.dps = 40
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

# ---------------------------------------------------------------- exact identities
r, b, w = sp.symbols('r b w', positive=True)
phi = sp.asin(r)
s_ = sp.sqrt(1 - r**2)
cx = s_ - 2*r*sp.sin(b)*sp.cos(b)
cy = -2*r*sp.sin(b)**2
# P(w) = clockwise rotation of P1=(s,-r)
P1x, P1y = s_, -r
Px = sp.cos(w)*P1x + sp.sin(w)*P1y
Py = -sp.sin(w)*P1x + sp.cos(w)*P1y
P("=== EXACT ALGEBRA (sympy) ===")
c2 = sp.simplify(cx**2 + cy**2)
P("|c|^2  (chart form)                    :", sp.simplify(c2))
P("|c|^2 - (1 + r^2 - 2 r sin(2b+asin r)) :",
  sp.simplify(c2 - (1 + r**2 - 2*r*sp.sin(2*b + phi))))
P("|P1 - c|^2 - r^2                       :",
  sp.simplify((P1x-cx)**2 + (P1y-cy)**2 - r**2))
P("arg(P1-c) - (2b - pi/2): direct check of the vector P1-c = r(sin2b, -cos2b):")
P("   (P1-c) - r*(sin2b, -cos2b)          :",
  sp.simplify(sp.Matrix([P1x-cx - r*sp.sin(2*b), P1y-cy + r*sp.cos(2*b)])))
P("theta1 = arg P1 = -asin r  (P1 = (cos phi, -sin phi), phi = asin r) :",
  sp.simplify(P1x - sp.cos(phi)), sp.simplify(P1y + sp.sin(phi)))
P("")
P("=> eta1 = arg(P1-c) - theta1 = (2b - pi/2) + asin r        [exact]")
P("")

# ---------------------------------------------------------------- numeric identity calibration
def geom(rr, bb, ww):
    rr = mp.mpf(rr); bb = mp.mpf(bb); ww = mp.mpf(ww)
    ss = mp.sqrt(1 - rr**2)
    c = mp.matrix([ss - 2*rr*mp.sin(bb)*mp.cos(bb), -2*rr*mp.sin(bb)**2])
    P1 = mp.matrix([ss, -rr])
    Pv = mp.matrix([mp.cos(ww)*P1[0] + mp.sin(ww)*P1[1], -mp.sin(ww)*P1[0] + mp.cos(ww)*P1[1]])
    return ss, c, P1, Pv

def eta(c, Pv):
    return mp.atan2(c[0]*Pv[1] - c[1]*Pv[0], 1 - (c[0]*Pv[0] + c[1]*Pv[1]))

P("=== HIGH-PRECISION IDENTITY CHECKS (dps=40; calibration) ===")
P("%-28s %-12s %-12s %-12s %-12s" % ("(r,b,w)", "alpha_geom", "w+eta1-eta", "L_geom", "pi/2+eta-w/2"))
for (rr, bb, ww) in [('0.38', '1.0', '0.3'), ('0.38', '0.7', '0.9'), ('0.375', '1.1', '1.4'),
                     ('0.38', '0.6', '0.2'), ('0.38', '1.0', '0.0'), ('0.38', '0.9', '1.6')]:
    ss, c, P1, Pv = geom(rr, bb, ww)
    e = eta(c, Pv)
    e1 = 2*mp.mpf(bb) + mp.asin(mp.mpf(rr)) - mp.pi/2
    # alpha at c between (P-c) and (P1-c)
    v0 = Pv - c; v1 = P1 - c
    alpha = mp.atan2(v0[0]*v1[1] - v0[1]*v1[0], v0[0]*v1[0] + v0[1]*v1[1])
    L = mp.atan2((c - Pv)[0]*(P1 - Pv)[1] - (c - Pv)[1]*(P1 - Pv)[0],
                 (c - Pv)[0]*(P1 - Pv)[0] + (c - Pv)[1]*(P1 - Pv)[1])
    P("%-28s %-12s %-12s %-12s %-12s"
      % ("(%s,%s,%s)" % (rr, bb, ww),
         mp.nstr(alpha, 10), mp.nstr(mp.mpf(ww) + e1 - e, 10),
         mp.nstr(L, 10), mp.nstr(mp.pi/2 + e - mp.mpf(ww)/2, 10)))
P("")
P("(each column pair must agree to ~1e-30; the two 'eta' forms are the DEFINITION and the")
P(" derived expression, so agreement calibrates the identity alpha = w + eta1 - eta(w))")
P("")
P("=== SIGN / UNIFORM BOUNDS ===")
P("|eta| < pi/2 : 1 - c.P > 0 is the real part of 1 - conj(c)P, so atan2 lands in (-pi/2,pi/2).")
for (rr, bb, ww) in [('0.38', '0.6', '0.2'), ('0.38', '1.18', '0.0'), ('0.375', '0.6', '0.4')]:
    ss, c, P1, Pv = geom(rr, bb, ww)
    e = eta(c, Pv)
    den = 1 - (c[0]*Pv[0] + c[1]*Pv[1])
    d2 = float((Pv - c)[0]**2 + (Pv - c)[1]**2)
    P("  r=%s b=%s w=%s : 1-c.P = %.10f (>0) ; eta = %+.10f (|eta|<pi/2: %s) ; |c| = %.10f"
      % (rr, bb, ww, float(den), float(e), abs(e) < mp.pi/2, float(mp.sqrt(c[0]**2 + c[1]**2))))
P("")
P("uniform |c| bound:  |c|^2 = 1 + r^2 - 2 r sin(2b + asin r), and b in (acos(r)/2, acos(r)]")
P("  gives 2b + asin r in (pi/2, pi - asin r], hence sin(2b+asin r) in [sin(asin r), 1) = (r, 1]")
P("  wait: 2b+asin r in (pi/2, pi-asin r) => sin in (r, 1]  =>  |c|^2 in [(1-r)^2, 1-r^2).")
for (rr, bb) in [('0.38', '0.6'), ('0.38', '1.0'), ('0.38', '1.18'), ('0.375', '0.6'), ('0.375', '1.20')]:
    ss, c, P1, Pv = geom(rr, bb, '0.3')
    mod = float(mp.sqrt(c[0]**2 + c[1]**2))
    P("  r=%s b=%s : |c| = %.10f , 1-r = %.10f , s = %.10f , bound holds: %s"
      % (rr, bb, mod, float(1 - mp.mpf(rr)), float(mp.sqrt(1 - mp.mpf(rr)**2)),
         (1 - mp.mpf(rr)) < mod < mp.sqrt(1 - mp.mpf(rr)**2)))
P("")
P("denominator bound: 1 - c.P >= 1 - |c| > 1 - s  with s = sqrt(1-r^2);")
P("  on r in [3/8, 19/50]: min of (1-s) at r=3/8: 1 - sqrt(1-9/64) = 1 - sqrt(55)/8 = %.10f"
  % float(1 - mp.sqrt(55)/8))
P("  exact comparison 1 - sqrt(55)/8 > 1/14  <=>  13/14 > sqrt(55)/8  <=>  (13*8/14)^2 > 55")
P("    <=>  (52/7)^2 > 55  <=>  2704/49 > 55  <=>  2704 > 2695    TRUE  [exact rationals]")
P("  => 1 - c.P > 1/14 > 0 uniformly for r in [3/8,19/50], b in (acos(r)/2, acos(r)].")
P("  and d^2 = |P-c|^2 < (1+s)^2 <= (1+sqrt(55)/8)^2 = %.6f < 4, so"
  % float((1 + mp.sqrt(55)/8)**2))
P("  alpha' = (1-c.P)/d^2 > (1/14)/4 = 1/56 > 0  (monotone in w; identity from previous round).")

import pathlib
outp = pathlib.Path(__file__).resolve().parent.parent / 'out' / 'p32_c849_identities.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
