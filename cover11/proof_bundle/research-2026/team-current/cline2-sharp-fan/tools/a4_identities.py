# -*- coding: utf-8 -*-
"""A4 completion: machine-verify the four UNSQUARED derivative identities of the sector
atom (as used by `grad` in lead/interval_patch_fibers.py), by differentiating the atan2
expressions explicitly (no atan2 survives) and reducing the resulting polynomial
identities modulo the two geometric constraints.  Fast, exact, no trig simplify.
"""
import sympy as sp

P1x, P1y, cx, cy, cw, sw = sp.symbols('P1x P1y cx cy cw sw', real=True)
p1 = sp.Matrix([P1x, P1y]); c = sp.Matrix([cx, cy])
Pv = sp.Matrix([cw*P1x + sw*P1y, -sw*P1x + cw*P1y])          # P(w) = R(-w) P1
Pp = sp.Matrix([-sw*P1x + cw*P1y, -cw*P1x - sw*P1y])         # dP/dw
def cr(u, v): return sp.expand(u[0]*v[1] - u[1]*v[0])
def dt(u, v): return sp.expand(u[0]*v[0] + u[1]*v[1])
v0 = Pv - c; v1 = p1 - c
dd = dt(v0, v0); p_ = dt(c, Pv)
orient = cr(v0, v1); dot1 = dt(v0, v1)
orientp = cr(Pp, v1); dot1p = dt(Pp, v1)
chord = p1 - Pv; back = c - Pv
lc = cr(chord, back); dotL = dt(chord, back)
lcp = cr(-Pp, back) + cr(chord, -Pp)          # chord' = -Pp, back' = -Pp
dotLp = dt(-Pp, back) + dt(chord, -Pp)

# constraints: P1 on the unit circle ; |P1 - c| = r
def reduce_mod(e):
    e = sp.expand(e)
    d1sq = sp.expand((P1x-cx)**2 + (P1y-cy)**2)
    for _ in range(6):
        e = sp.expand(e.subs(P1x**2, 1 - P1y**2)).subs(cw**2, 1 - sw**2)
        e = sp.expand(e)
    return sp.factor(sp.expand(e))

lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

P("=== A4 identities (each checked as an exact polynomial identity modulo constraints) ===")
# id0: P' = -J P  (clockwise motion)
JP = sp.Matrix([-Pv[1], Pv[0]])
P("id0  dP/dw + J P == 0 :", sp.expand(Pp + JP) == sp.zeros(2, 1))

# id1: alpha' = (1 - c.P)/dd     where alpha = atan2(orient, dot1)
#      (orient' dot1 - orient dot1') / (orient^2 + dot1^2) == (1 - p)/dd
num1 = sp.expand(sp.expand(orientp*dot1 - orient*dot1p)*dd - (1 - p_)*(orient**2 + dot1**2))
P("id1  alpha' == (1 - c.P)/d^2 :", reduce_mod(num1) == 0)

# id2: (triangle area)' + (1-cos w)/2 == (1 - c.P)/2  i.e.  orient' == cos w - 1 + c.P
P("id2  (orient/2 + (w-sin w)/2)' == (1 - c.P)/2 :",
  reduce_mod(orientp - (cw - p_)) == 0)

# id3: (u^2)' == -2 cross(c,P)/R0^2 ,  u^2 = dd/R0^2
P("id3  (u^2)' == -2 cross(c,P)/R0^2 :", reduce_mod(dt(v0, Pp) + cr(c, Pv)) == 0)

# id4: (L + w/2)' == 1 - alpha' , i.e.  L' == 1/2 - alpha'
#      L' = (lc' dotL - lc dotLp)/(lc^2 + dotL^2)
alphap = sp.expand((orientp*dot1 - orient*dot1p)/(orient**2 + dot1**2))
lhs = sp.expand(lcp*dotL - lc*dotLp - (sp.Rational(1,2) - alphap)*(lc**2 + dotL**2))
den = sp.expand(orient**2 + dot1**2)
lhs_clear = sp.expand(sp.expand(sp.together(lhs))*den)
P("id4  (L + w/2)' == 1 - alpha' :", reduce_mod(lhs_clear) == 0)

# id5: the assembled derivative equals the code's `grad` expression
mu, h, d, dl, R0 = sp.symbols('mu h d dl R0', real=True)
up = dt(v0, Pp)/(sp.sqrt(dd)*R0)                    # u' = d'/R0 = (v0.Pp)/(|v0| R0)
Fp = (sp.expand(orientp/2 + (1 - cw)/2) - mu*alphap
      - d*2*dt(v0, Pp)/R0**2 - dl*dt(v0, Pp)/(sp.sqrt(dd)*R0) + h*sp.expand(lcp*dotL - lc*dotLp)/(lc**2 + dotL**2))
grad = ((1 - p_)*(sp.Rational(1,2) + (-mu - h)/dd) + h + (2*d + dl*R0/sp.sqrt(dd))*(cr(c, Pv))/R0**2)
diff = sp.expand(sp.together(sp.expand(Fp - grad))*(sp.sqrt(dd)))
P("id5  assembled F' == grad formula :", reduce_mod(diff) == 0)

P("")
P("Each line prints True only if the difference is the zero polynomial after")
P("  (i) expanding, (ii) substituting P1x^2 -> 1-P1y^2 (P1 on the unit circle) and")
P("  (iii) cw^2 -> 1-sw^2 (cos^2+sin^2=1).  |P1-c| = r is NOT needed: the denominators")
P("  dd, d1^2 appear only through the cleared products, so the identities hold for ANY")
P("  centre c, in particular for the switch-saturated chart centre.")

import pathlib
outp = pathlib.Path(__file__).resolve().parent.parent / 'out' / 'p31_a4_identities.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
