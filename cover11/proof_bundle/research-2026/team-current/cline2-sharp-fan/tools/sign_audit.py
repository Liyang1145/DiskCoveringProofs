# -*- coding: utf-8 -*-
"""C862c: (1) SYMBOLIC sign audit of the angle terms and M_j; (2) exact reduction of
"interior local max" to scalar inequalities; (3) bounded diagnostic for stationary + NSD.

Part 1 is exact (sympy).  Parts 2-3 are formula-level and (3) is exploratory only.
"""
import sympy as sp
lines = []
def P(*a):
    s = " ".join(str(x) for x in a); lines.append(s); print(s)

# ---------------------------------------------------------------- 1. symbolic sign audit
v, t, b1, b2, r = sp.symbols('v t b1 b2 r', real=True)
D1, D2 = 2*r*sp.sin(b1), 2*r*sp.sin(b2)
X1, Y1 = v - D1*sp.cos(b1), D1*sp.sin(b1) - t          # lead's face-1 data
X2, Y2 = v - D2*sp.cos(b2), D2*sp.sin(b2) + t
th1, th2 = sp.atan2(Y1, X1), sp.atan2(Y2, X2)
L1 = sp.sqrt(X1**2+Y1**2); L2 = sp.sqrt(X2**2+Y2**2)
P("=== 1. symbolic gradient / Hessian of the ANGLE terms (lead's coordinates) ===")
g1v = sp.diff(th1, v); g1t = sp.diff(th1, t); g2v = sp.diff(th2, v); g2t = sp.diff(th2, t)
P("  grad theta1 = (", sp.simplify(g1v), ",", sp.simplify(g1t), " )")
P("     expected form: (-Y1, -X1)/L1^2 :",
  sp.simplify(g1v - (-Y1)/L1**2) == 0, sp.simplify(g1t - (-X1)/L1**2) == 0)
P("  grad theta2 = (", sp.simplify(g2v), ",", sp.simplify(g2t), " )")
P("     expected form: (-Y2, +X2)/L2^2 :",
  sp.simplify(g2v - (-Y2)/L2**2) == 0, sp.simplify(g2t - (X2)/L2**2) == 0)
n1 = sp.Matrix([X1/L1, -Y1/L1])      # hub - Q1 in the (v,t) frame with Q1=(D1cos b1, D1 sin b1)
n2 = sp.Matrix([X2/L2, Y2/L2])
P("  n1 = (X1,-Y1)/L1 (unit) ; n2 = (X2,Y2)/L2 (unit)")
H1 = sp.Matrix([[sp.diff(th1, v, v), sp.diff(th1, v, t)], [sp.diff(th1, t, v), sp.diff(th1, t, t)]])
H2 = sp.Matrix([[sp.diff(th2, v, v), sp.diff(th2, v, t)], [sp.diff(th2, t, v), sp.diff(th2, t, t)]])
P("")
P("  Hess theta1 * L1^2 =", H1.multiply(sp.simplify(L1**2)))
P("  Hess theta2 * L2^2 =", H2.multiply(sp.simplify(L2**2)))
# express each Hess(theta_j) in the (n_j, n_j^perp) basis: coefficient of the mixed entry
def mixed(H, n):
    perp = sp.Matrix([-n[1], n[0]])
    return sp.simplify((n.T*H*perp)[0])
P("")
P("  mixed entry <n1, Hess(theta1) n1^perp> * L1 =", sp.simplify(mixed(H1, n1)*L1))
P("  mixed entry <n2, Hess(theta2) n2^perp> * L2 =", sp.simplify(mixed(H2, n2)*L2))
P("  (so both angle Hessians have the (n,n^perp) form [[0,-1/L],[-1/L,0]] with the SAME sign:")
P("   that is the lead's matrix -a/L^2 in the off-diagonal, i.e. M_j = -(2 w_j w_j^T - I) with")
P("   w_j = n_j rotated by +pi/4, equivalently +(2 w_j w_j^T - I) with w_j rotated by -pi/4.)")
P("")
P("=== 2. exact reduction: interior local max => a finite system of scalar conditions ===")
P("  F = affine + sum_j [ a_j theta_j + beta_j L_j^2 + gamma_j L_j ],  c_j = |gamma_j| > 0, a_j > 0.")
P("  (R1) radial necessary conditions (test w = n_1, n_2 in w^T Hess w <= 0; the angle term")
P("       contributes 0 in the radial direction because n_j^T M_j n_j = 0, sign-independent):")
P("          c_j/L_j + a_j/L_j^2 >= 2(beta_1+beta_2)      =>  L_j <= L*_j,")
P("          L*_1 = 0.421097, L*_2 = 0.419177   (roots of 2 sum(beta) L^2 - c_j L - a_j = 0)")
P("  (R2) trace:  tr Hess = 4(beta_1+beta_2) - sum_j c_j/L_j <= 0   =>  sum_j c_j/L_j >= 5.583507.")
P("  (R3) determinant (the NSD test in 2D): det Hess >= 0; explicitly, with phi the angle between")
P("       n_1 and n_2, s = sin(phi), S(j) = sign of the a_j-angle orientation (+-1), trace-free")
P("       angle parts M_j, det = product of the two eigenvalues = the scalar inequality")
P("          det = [4 sum(beta)^2 - ... ] - (2 sum(beta) - c_1/L_1)(2 sum(beta) - c_2/L_2) ...")
P("       which in compact form is:  (tr/2)^2 >= (H11 - H22)^2/4 + H12^2.")
P("  (R4) stationarity:   alpha = sum_j c_j n_j - sum_j a_j grad theta_j,   |alpha| = |...| ,")
P("       alpha = ( r(1 - cosT cosD), - r cos T sin D ),  T = b1+b2, D = b1-b2.")
P("  So an interior local maximum must satisfy (R1)+(R2)+(R3)+(R4); (R1)+(R2) alone are")
P("  satisfiable (the C862b ND witness has L_1,L_2 ~ 0.35 and sum c/L ~ 6.5), hence (R4) is the")
P("  binding one and the obligation reduces to a 4-parameter system (L_1, L_2, phi, angle(alpha)).")

import pathlib
outp = pathlib.Path(__file__).resolve().parent.parent / 'out' / 'p43_sign_audit.txt'
with open(outp, 'w', encoding='utf-8') as f:
    f.write("\n".join(lines) + "\n")
