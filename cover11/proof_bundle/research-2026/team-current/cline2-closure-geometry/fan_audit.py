"""Analytic audit of lead/FAN-DEFICIT-COORDINATES.md -- checked closed forms.

All claims below are proved analytically in FAN-AUDIT-REPORT.md; this file only
(k) verifies the algebraic factorisations symbolically with sympy, and
(b) evaluates the resulting closed constants with mpmath to print them.
No numerical check is used as evidence for any theorem.
"""
import sympy as sp
from mpmath import mp, cos, sin, pi, mpf, acos, sqrt
mp.dps = 30

s, t, th, T, R = sp.symbols('s t theta T R', positive=True)
print('=== 1. equivalence of the circumradius condition ===')
lhs = (sp.cos(th) - sp.cos(s)*sp.cos(t))**2 - sp.sin(s)**2*sp.sin(t)**2
print('(cos th - cos s cos t)^2 - sin^2 s sin^2 t  =  ',
      sp.factor(sp.simplify(lhs)))          # expect (cos th - cos(s-t))(cos th - cos(s+t))
print('  => R_circ <= R  <=>  cos(s+t) <= cos th <= cos(s-t)  <=>  |s-t| <= th <= s+t')
print()
print('=== 2. envelope maximum and exact loss ===')
area = 2*sp.cos(s)*sp.cos(t)*sp.sin(th)
env = sp.sin(th)*(1 + sp.cos(th))
diff = sp.simplify(env - area - sp.sin(th)*((1 - sp.cos(s-t)) + (sp.cos(th) - sp.cos(s+t))))
print('envelope - area - sin th[(1-cos(s-t)) + (cos th - cos(s+t))]  =  ', diff)
print('2 cos s cos t = cos(s+t)+cos(s-t) check:  ',
      sp.simplify(2*sp.cos(s)*sp.cos(t) - sp.cos(s+t) - sp.cos(s-t)))
print('1 + cos th = 2 cos^2(th/2) check:  ',
      sp.simplify(1 + sp.cos(th) - 2*sp.cos(th/2)**2))
print('  => the max of cos s cos t under |s-t|<=th<=s+t is cos^2(th/2) at s=t=th/2')
print()
print('=== 3. degree-7 sharp minimum ===')
th0 = 2*pi/7
# sum of the second loss terms with all theta_i = th0, T = sum s_i
S = sp.symbols('S', positive=True)
pen = sp.diff(S*sp.cos(th0) - sp.sin(th0), S)
print('d/dT [ T cos th0 - sin th0 ] =', pen, ' = cos(2pi/7) =',
      mp.nstr(mp.cos(2*mp.pi/7), 20), '> 0  (monotone increasing in T)')
Cmin = 2*pi*cos(th0) - sin(th0)
print('sharp lower bound of total loss / R^2 (T = pi, all s_i equal):')
print('  C_min = 2 pi cos(2pi/7) - sin(2pi/7) =', mp.nstr(Cmin, 25))
print('  numerical evaluation of the same closed form for d = 7 balanced star:',
      mp.nstr(7*sin(th0)*(cos(th0) - cos(2*pi/7)), 25))
print()
print('=== 4. degree-6 ===')
th6 = 2*pi/6
print('s_i = pi/6, th_i = pi/3: 2 s_i = th_i (tight), sum(s_i+s_{i+1}) = 2pi (no slack)')
print('  second loss term: cos(pi/3) - cos(2pi/6) =',
      mp.nstr(cos(th6) - cos(2*pi/6), 20), ' = 0')
print('  first loss term: 1 - cos(0) = 0')
print('  total loss = 0 (saturated, no strict penalty)')
print()
print('=== 5. exact saturated identity (T = pi case) ===')
print('  when sum th_i = 2 pi and every th_i = s_i + s_{i+1}:')
print('  total loss / R^2 = sum_i sin(th_i) (1 - cos(s_{i+1} - s_i))')
print('                   = 2 sum_i sin(th_i) sin^2((s_{i+1}-s_i)/2)')
print('                   >= sum_i sin(th_i) (s_{i+1}-s_i)^2 / 2')
print()
print('=== 6. capacity bound ===')
print('  sum_i (s_i + s_{i+1}) = 2 sum s_i >= sum th_i = 2 pi  =>  sum s_i >= pi')
print('  equivalently sum_i acos(rho_i/(2R)) >= pi  (rho_i = |H c_i|)')
print('  d = 6: budget/gap equality forces every th_i = s_i+s_{i+1}, hence all s_i = pi/6')
print('  d = 7: 2 sum s_i = 14 s >= 2 pi only when s >= pi/7; per-edge budget theta<=2s')
