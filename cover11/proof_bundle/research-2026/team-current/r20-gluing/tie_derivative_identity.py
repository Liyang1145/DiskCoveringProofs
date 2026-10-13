# -*- coding: utf-8 -*-
"""tie_derivative_identity.py — ANALYTIC (symbolic) verification of the tie-radius derivative.

Sites c, c' ; U = (cos th, sin th) on the unit circle is the tie point: |U-c| = |U-c'| = rho.
Total derivative along a free motion of c (with c' fixed) keeps the tie: U moves as U(th(c,c')).
Claim:
    grad_c rho = u * A,   A = <u',t>/<u-u',t>,      t = (-sin th, cos th),
    grad_c' rho = u' * B,  B = <u,t>/<u-u',t>,     u = (U-c)/rho, u' = (U-c')/rho,
so the fixed-switch split must use (A,B) (normalized alpha = A/(A+B), 1-alpha = B/(A+B)), not halves.
"""
import sympy as sp

cx, cy, ex, ey, th = sp.symbols('cx cy ex ey th', real=True)
U = sp.Matrix([sp.cos(th), sp.sin(th)])
c = sp.Matrix([cx, cy])
cp = sp.Matrix([ex, ey])
t = sp.Matrix([-sp.sin(th), sp.cos(th)])

F = (U - c).dot(U - c) - (U - cp).dot(U - cp)          # tie condition = 0
Fth = sp.simplify(sp.diff(F, th))
rho = sp.sqrt(sp.expand((U - c).dot(U - c)))
# d th / d cx = -(dF/dcx)/(dF/dth)
for var, idx in (('cx', 0), ('cy', 1)):
    dFd = sp.diff(F, c[idx])
    dthd = -dFd / Fth
    dRho = sp.diff(rho, c[idx]) + sp.diff(rho, th) * dthd
    print('d rho / d %s  (total, tie preserved) = %s' % (var, sp.simplify(dRho)))
# predicted form A * u
den = (U - c).dot(t) - (U - cp).dot(t)                  # <u,u'-wise>; note: den = (U-c-(U-cp)).t
den = (c - cp).dot(t) * (-1)
A = ((U - cp).dot(t)) / den
u = (U - c) / rho
print('\npredicted A*u :  A = <U-cp,t>/<c-cp,t> = %s' % sp.simplify(A))
chk = [sp.simplify(sp.diff(rho, c[i]) + sp.diff(rho, th) * (-sp.diff(F, c[i]) / Fth) - A * u[i])
       for i in (0, 1)]
print('check (grad_c rho - A u) =', chk)
print('zero? ->', [sp.simplify(sp.together(z)) == 0 for z in chk])

# numeric instance on the candidate-like geometry: c at radius .75, c' the mirror across the ray of U
import math
th0 = 0.7
U0 = sp.Matrix([sp.cos(th0), sp.sin(th0)])
c0 = sp.Matrix([sp.Rational(3, 4) * sp.cos(th0 - 0.25), sp.Rational(3, 4) * sp.sin(th0 - 0.25)])
# mirror of c0 in the line through the origin and U0:
n = U0
proj = n * (c0.dot(n) / n.dot(n))
cp0 = (2 * proj - c0)
rho0 = sp.sqrt(sp.expand((U0 - c0).dot(U0 - c0)))
u0 = (U0 - c0) / rho0
up0 = (U0 - cp0) / sp.sqrt(sp.expand((U0 - cp0).dot(U0 - cp0)))
t0 = sp.Matrix([-sp.sin(th0), sp.cos(th0)])
A0 = sp.simplify((U0 - cp0).dot(t0) / (c0 - cp0).dot(t0))
B0 = sp.simplify((U0 - c0).dot(t0) / ((cp0 - c0).dot(t0)))
print('\nnumeric: A = %.9f  B = %.9f  alpha = A/(A+B) = %.9f  (half-half = 0.5)'
      % (float(A0), float(B0), float(A0 / (A0 + B0))))
print('equal radii at the tie:  |U-c| = %.9f, |U-cp| = %.9f'
      % (float(rho0), float(sp.sqrt(sp.expand((U0 - cp0).dot(U0 - cp0))))))
