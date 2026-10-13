# -*- coding: utf-8 -*-
"""Uniform ridge-geometry feasibility on r in [3/8,19/50]: rigorous rational proof check.

norm/(2r) = 1 - r cos2T - 2 s sinT cosD   (T=b1+b2, D=b1-b2)     [lead's form]
hub-norm condition  <=>  cosD >= f(v), v = sinT, f(v) = (1-r+2rv^2)/(2sv)
f convex on v>0 => sup over v in (2rs,1] = max(f(2rs), f(1))
cosD >= sqrt((1+r)/2) =: c0   (crude bound from |D| < acos(r)/2)
Need: max(f(2rs),f(1)) <= c0 for all r in [3/8,19/50].
"""
import sympy as sp
from fractions import Fraction as F
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

r, v, T, D = sp.symbols('r v T D', real=True)
s_ = sp.sqrt(1-r**2)
# lead's form of norm/(2r) equals my -Phi
norm2r = 1 - r*sp.cos(2*T) - 2*s_*sp.sin(T)*sp.cos(D)
myform = (1 - r) + 2*r*sp.sin(T)**2 - 2*s_*sp.sin(T)*sp.cos(D)
P("(A) IDENTITY: norm/(2r) == (1-r) + 2r sin^2T - 2s sinT cosD :",
  sp.simplify(sp.expand_trig(norm2r - myform)) == 0)
P("    (both equal -Phi with Phi = 2s sinT cosD - 2r sin^2T - (1-r))")
P("")
P("(B) threshold: condition cosD >= f(v), f(v) = (1-r+2rv^2)/(2 s v)")
f = (1-r+2*r*v**2)/(2*s_*v)
P("    f''(v) = (1-r)/(s v^3) > 0 :", sp.simplify(sp.diff(f, v, 2) - (1-r)/(s_*v**3)) == 0,
  "  => f convex on v>0 => sup on (2rs,1] <= max(f(2rs), f(1))")
P("")
P("(C) endpoint 1: f(1) <= c0 = sqrt((1+r)/2)  <=>  r <= 1/2   [exact]")
P("    f(1)/c0 = 1/sqrt(2(1-r)) <= 1/sqrt(1.24) = %.6f < 1  for r <= 19/50"
  % (1/(1.24)**0.5))
P("")
P("(D) endpoint 2: need 1 - r + 8r^3(1-r^2) <= 4r(1-r^2) sqrt((1+r)/2)")
lam = 1 - r + 8*r**3*(1-r**2)
P("    LHS is increasing on [3/8,19/50]: 24r^2 - 40r^4 >= 24(3/8)^2 - 40(19/50)^4 = %.6f > 1"
  % (24*F(9, 64) - 40*F(19, 50)**4))
LHSmax = F(31, 50) + 8*F(19, 50)**3 - 8*F(19, 50)**5
P("    => LHS <= 1 - 19/50 + 8(19/50)^3 - 8(19/50)^5 = %s = %.8f"
  % (LHSmax, float(LHSmax)))
RHSmin = 4*F(3, 8)*(1-F(19, 50)**2)*sp.sqrt(F(11, 16))
P("    RHS >= 4(3/8)(1-(19/50)^2) sqrt(11/16) = 6417 sqrt(11)/20000 = %.8f"
  % float(6417*sp.sqrt(11)/20000))
lhsnum, lhsden = LHSmax.numerator*20000, LHSmax.denominator
# exact integer comparison:  LHSmax*20000 < 6417*sqrt(11)*312500000
L = lhsnum*312500000  # hmm: compare LHSmax < 6417 sqrt11/20000  <=>  LHSmax*20000 < 6417 sqrt11
# do it cleanly: LHSmax * 20000 < 6417 sqrt(11) * 312500000 ... use squaring
a = sp.Integer(LHSmax.numerator)*20000
b_ = sp.Integer(LHSmax.denominator)
P("    exact comparison: %s < 6417 sqrt(11)  <=>  %s^2 < 6417^2 * 11 * %s^2  : %s"
  % (sp.nsimplify(LHSmax*20000), a, b_,
     a**2 < 6417**2*11*b_**2))
P("    (both sides positive, so squaring is legitimate; the inequality is a strict integer one)")
P("")
P("(E) numeric sanity of the sup of f against c0 over r")
import mpmath as mp
mp.mp.dps = 25
P("%-8s %-12s %-12s %-12s %-12s" % ("r", "f(2rs)", "f(1)", "c0", "max f / c0"))
for rr in ['0.375', '0.376', '0.378', '0.38']:
    rv = mp.mpf(rr); sv = mp.sqrt(1-rv**2)
    f1 = (1-rv+2*rv)/(2*sv); f2 = (1-rv+2*rv*(2*rv*sv)**2)/(2*sv*2*rv*sv)
    c0 = mp.sqrt((1+rv)/2)
    P("%-8s %-12s %-12s %-12s %-12s" % (rr, mp.nstr(f2, 8), mp.nstr(f1, 8), mp.nstr(c0, 8),
                                        mp.nstr(max(f1, f2)/c0, 8)))
P("")
P("CONCLUSION: max(f(2rs),f(1)) <= c0 holds strictly for every r in [3/8,19/50], hence")
P("cosD >= c0 >= max f(v) >= f(v) and the hub-norm condition norm <= 0 holds STRICTLY")
P("for every r in [3/8,19/50] and every b1,b2 in (acos(r)/2, acos(r)].  Ridge geometry")
P("feasibility is therefore automatic; only the objective-side conditions (obtuse")
P("arguments and the two branch derivative signs) remain box-specific.")
P("")
P("MARGIN: f(2rs)/c0 ~ 0.9237 at r=3/8 (worst endpoint), i.e. ~7.6% slack; the crude")
P("rational route gives LHS <= %.8f < %.8f <= RHS, a strict margin of %.6f."
  % (float(LHSmax), float(6417*sp.sqrt(11)/20000), float(6417*sp.sqrt(11)/20000) - float(LHSmax)))

import pathlib
outp = pathlib.Path(__file__).resolve().parent.parent / 'out' / 'p35_ridge_uniform.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
