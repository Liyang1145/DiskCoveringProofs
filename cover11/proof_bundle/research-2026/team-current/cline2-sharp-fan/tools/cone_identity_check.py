# -*- coding: utf-8 -*-
"""Independent check of the lead's structural identity:
   T=b1+b2, D=b1-b2, eps=delta-D, A=b2-eps, B=b1+eps, face args = T -+ eps.
   min sin(T+-eps) = sinT cos eps - |cosT sin eps| = sin(beta-|eps|), beta=min(T,pi-T).
   cap: H <= 2r sin(beta-|eps|) <=> |eps| + asin(H/2r) <= beta ; ridge eps=0 maximises it.
   Also: no face argument leaves (0,pi) under feasibility; active-face flip.
"""
import sympy as sp
import mpmath as mp
mp.mp.dps = 30
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

T, e, r = sp.symbols('T epsilon r', real=True)
P("=" * 78)
P("(1) the two-argument identity")
P("=" * 78)
b = sp.symbols('beta', positive=True)
# right-hand side with sin(beta)=sin T, cos(beta)=|cos T| : split by sign of cos T
lhs = sp.sin(T-e)
rhs_acute = sp.sin(T)*sp.cos(e) - sp.cos(T)*sp.sin(abs(e))     # cos T >= 0
rhs_obtuse = sp.sin(T)*sp.cos(e) + sp.cos(T)*sp.sin(abs(e))    # cos T <= 0  (cos beta = -cos T)
P("  sin(T-eps) - [sinT cos eps - cosT sin|eps|] :",
  sp.simplify(sp.expand_trig(lhs - rhs_acute).rewrite(sp.cos)) if True else None)
P("  symbolic form: min(sin(T+eps),sin(T-eps)) = sinT cos eps - |cosT sin eps|")
P("  and sinT cos eps - |cosT| sin|eps| = sin(beta-|eps|) with sin beta = sinT, cos beta = |cosT|")
P("  beta = min(T, pi-T) if T in (0,pi).  Checked numerically below over many (T,eps).")
P("")
P("%-10s %-10s %-14s %-14s %-14s" % ("T", "eps", "min sin", "sinTcos-|cosT sin|", "sin(beta-|eps|)"))
for (Tv, ev) in [('1.0', '0.3'), ('1.0', '-0.7'), ('2.0', '0.5'), ('2.0', '-0.9'),
                 ('0.3', '0.25'), ('2.9', '0.05'), ('1.5', '0.4'), ('2.5', '-1.0'), ('0.5', '-1.2')]:
    T_ = mp.mpf(Tv); e_ = mp.mpf(ev)
    a = mp.sin(T_+e_); b_ = mp.sin(T_-e_)
    m1 = a if a < b_ else b_
    m2 = mp.sin(T_)*mp.cos(e_) - abs(mp.cos(T_)*mp.sin(e_))
    beta = T_ if T_ <= mp.pi/2 else mp.pi - T_
    m3 = mp.sin(beta - abs(e_))
    P("%-10s %-10s %-14s %-14s %-14s" % (Tv, ev, mp.nstr(m1, 10), mp.nstr(m2, 10), mp.nstr(m3, 10)))
P("  (three columns agree; note the identity holds for |eps| <= pi, not only |eps| < pi/2)")
P("")
P("=" * 78)
P("(2) chart reparametrisation: A=b2-eps, B=b1+eps, face args = T-+eps")
P("=" * 78)
b1, b2, d = sp.symbols('b1 b2 delta', positive=True)
D_ = b1-b2; e_ = d - D_
P("  A - (b2-eps) :", sp.simplify((b1-d) - (b2 - e_)))
P("  B - (b1+eps) :", sp.simplify((b2+d) - (b1 + e_)))
P("  b1+A - (T-eps):", sp.simplify((b1 + (b1-d)) - ((b1+b2) - e_)))
P("  b2+B - (T+eps):", sp.simplify((b2 + (b2+d)) - ((b1+b2) + e_)))
P("  eps range from A,B>0 :  eps < b2  and  eps > -b1   => |eps| < max(b1,b2)")
P("")
P("=" * 78)
P("(3) cap, cone and ridge maximality")
P("=" * 78)
P("  cap(eps) := min(2r sin(T+eps), 2r sin(T-eps)) = 2r sin(beta-|eps|)")
P("  => cap is even in eps and DECREASING in |eps|: maximised at eps=0 (the ridge),")
P("     with cap(0) = 2r sin beta = min(2r sinT, 2r sin(pi-T)) = min(h1,h2) at the ridge.")
P("  nonempty fiber with H>0 requires 0 < H <= cap(eps), so beta-|eps| > 0, i.e. |eps| < beta;")
P("  equivalently, with u := asin(H/(2r)) in (0, pi/2):  |eps| + u <= beta   (LINEAR cone).")
P("  beta <= pi/2, so beta-|eps| in [0,pi/2] and asin is monotone there: equivalence exact.")
P("")
P("  numeric: cap(eps)/(2r) vs sin(beta-|eps|) for a legal tuple")
P("  %-10s %-10s %-14s %-14s" % ("T", "eps", "min(sin(T-+eps))", "sin(beta-|eps|)"))
for (Tv, ev) in [('1.19', '0.0'), ('1.19', '0.1'), ('1.19', '-0.15'), ('2.37', '0.1'),
                 ('2.37', '-0.1'), ('2.30', '0.0')]:
    T_ = mp.mpf(Tv); e_ = mp.mpf(ev)
    a = mp.sin(T_+e_); b_ = mp.sin(T_-e_); m1 = a if a < b_ else b_
    beta = T_ if T_ <= mp.pi/2 else mp.pi - T_
    P("  %-10s %-10s %-14s %-14s" % (Tv, ev, mp.nstr(m1, 12), mp.nstr(mp.sin(beta-abs(e_)), 12)))
P("")
P("=" * 78)
P("(4) active-face flip, and no argument leaves (0,pi) under feasibility")
P("=" * 78)
P("  sin(T-eps) < sin(T+eps)  <=>  cosT sin eps > 0.  So the ACTIVE face is")
P("     the (b1+A)=T-eps face  iff eps cosT > 0, i.e. for eps>0 when T<pi/2 (acute)")
P("     and for eps<0 when T>pi/2 (obtuse): the active face flips at T=pi/2, and both")
P("     branches give the same cap, so the cap statement is global (no obtuse hypothesis).")
P("  missing args: A,B are angles at c2, so A,B in (0,pi); then T-eps = b1+A in (0,2pi) and")
P("     T+eps = b2+B in (0,2pi); a NONEMPTY fiber requires both face uppers > 0, i.e.")
P("     sin(T-eps) > 0 and sin(T+eps) > 0, which pins both arguments into (0,pi).")
for (Tv, ev) in [('1.19', ''), ('2.37', '')]:
    T_ = mp.mpf(Tv)
    b_ = T_ if T_ <= mp.pi/2 else mp.pi - T_
    P("     e.g. T=%s: beta=%.6f, cap>0 iff |eps|<beta; cap/(2r) = sin(beta-|eps|) >= 0" % (Tv, float(b_)))
P("")
P("RESIDUAL (not linear): in (u,eps) the other C848 constraints are")
P("   separation:  sin u >= |sin(D+eps)|   (with H = 2r sin u),")
P("   hub-norm:    4r^2 sin^2 u - 4rs cos(D+eps) sin u + 2r(1-r) <= 0.")
P("So the FACE CAP is the linear triangle |eps|+u<=beta; the fiber is that triangle cut by")
P("the two trigonometric strips above.  The ridge (eps=0, u=beta) sits on the triangle vertex.")

import pathlib
outp = pathlib.Path(__file__).resolve().parent.parent / 'out' / 'p36_cone_identity.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
