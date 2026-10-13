"""root-cc2 DIAGNOSTIC: resolve the contradictions the lead raised.

Disputed items:
  (1) claim C1160: is r^2 -(A-z)^2 == r^2 - z^2 identically? (lead says NO)
  (2) claim C1161: which circle-circle intersection lies on S^1 for the D2 family?
      the lead says the LOWER point (0.3083,0.5111) has norm ~0.596, and the UPPER
      (0.618759,0.785581) has norm 1.
  (3) F's algebraic form: sum of two non-negative terms, or "two squares MINUS det^2"?
Everything printed here is recomputed from scratch with mpmath at 60 digits.
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z0, C0, r0 = [mp.mpf(s) for s in scout['z_c_r']]
# exact literals of the old hprec point (strings, mpf built AFTER mp.dps is set)
hp = json.loads((HERE.parents[4] / 'research-2026/session2/type14/out/hprec_sol.json').read_text())

def n(x, k=25):
    return mp.nstr(x, k)

def geom(z, c, r):
    s = mp.sqrt(1 - r*r); A = (s + z)/2
    t = r + mp.sqrt(r*r - z*z)
    B = r + mp.sqrt(r*r - (A - z)**2)
    D = 1 - mp.sqrt(r*r - c*c)
    return s, A, B, c, D, t

s, A, B, C, D, t = geom(z0, C0, r0)
P = lambda *a: print(*a)
P('=' * 78)
P('(1) the two radicands at the lead root')
P('   z                 = %s' % n(z0))
P('   s = sqrt(1-r^2)   = %s' % n(s))
P('   A = (s+z)/2       = %s' % n(A))
P('   A - z             = %s' % n(A - z0))
P('   r - sqrt(r^2-z^2) = %s' % n(r0 - mp.sqrt(r0*r0 - z0*z0)))
P('   r^2 - z^2                 = %s' % n(r0*r0 - z0*z0))
P('   r^2 - (A-z)^2             = %s' % n(r0*r0 - (A - z0)**2))
P('   difference                = %s' % n((r0*r0 - (A - z0)**2) - (r0*r0 - z0*z0)))
P('   sympy identity            = -(s-z)(s+3z)/4 = %s' % n(-(s - z0)*(s + 3*z0)/4))
P('   B = r + sqrt(r^2-(A-z)^2) = %s' % n(B))
P('   t = r + sqrt(r^2-z^2)     = %s' % n(t))
P('   => radicands DIFFER: %s' % (abs((r0*r0 - (A - z0)**2) - (r0*r0 - z0*z0)) > mp.mpf('1e-20')))

P('')
P('=' * 78)
P('(2) the two circle-circle intersections of the radius-r circles about S1,S2')
P('   S1 = (A,B)   = (%s, %s)' % (n(A), n(B)))
P('   S2 = (C,D)   = (%s, %s)' % (n(C), n(D)))
mid = ((A + C)/2, (B + D)/2)
u = (C - A, D - B)
nu = mp.sqrt(u[0]**2 + u[1]**2)
h = mp.sqrt(r0*r0 - (nu/2)**2)
nperp = (-u[1]/nu, u[0]/nu)
p_plus = (mid[0] + h*nperp[0], mid[1] + h*nperp[1])
p_minus = (mid[0] - h*nperp[0], mid[1] - h*nperp[1])
for nm, p in (('plus ', p_plus), ('minus', p_minus)):
    P('   %s intersection = (%s, %s)  |p| = %s   |p-S1| = %s'
      % (nm, n(p[0]), n(p[1]), n(mp.sqrt(p[0]**2 + p[1]**2)),
         n(mp.sqrt((p[0]-A)**2 + (p[1]-B)**2))))
P('   r = %s' % n(r0))
# lead's linear-solve point
v1 = (1 + A*A + B*B - r0*r0)/2
v2 = (1 + C*C + D*D - r0*r0)/2
det = A*D - B*C
p_lin = ((v1*D - v2*B)/det, (A*v2 - C*v1)/det)
P('   lead linear solve p1 = (%s, %s)  |p1| = %s  |p1-S1| = %s'
  % (n(p_lin[0]), n(p_lin[1]), n(mp.sqrt(p_lin[0]**2 + p_lin[1]**2)),
     n(mp.sqrt((p_lin[0]-A)**2 + (p_lin[1]-B)**2))))
P('   which intersection does the linear solve reproduce? plus=%s minus=%s'
  % (abs(p_lin[0]-p_plus[0]) < mp.mpf('1e-30'), abs(p_lin[0]-p_minus[0]) < mp.mpf('1e-30')))
P('   hprec qpts[0] = %s' % str(hp['qpts'][0])[:60])

P('')
P('=' * 78)
P('(3) algebraic form of the lead F')
E = (p_lin[0]**2 + p_lin[1]**2 - 1)**2 + ((p_lin[0]-A)**2 + (p_lin[1]-B)**2 - r0*r0)
P('   lead F definition (as coded)      = %s' % n(E))
P('   = (|p|^2-1)^2 + (|p-S1|^2-r^2)   [sum of a square and a difference]')
P('   |p1|^2 - 1        = %s' % n(p_lin[0]**2 + p_lin[1]**2 - 1))
P('   |p1-S1|^2 - r^2   = %s' % n((p_lin[0]-A)**2 + (p_lin[1]-B)**2 - r0*r0))
P('   F as (|p|^2-1)^2 + (|p-S1|^2-r^2) is what lead/root_scout.py codes;')
P('   it is NOT "sum of two non-negative terms" and NOT a difference of two squares.')
# the "two intersections minus det^2" alternative
alt = (1 + A*A + B*B - r0*r0)/2*D - (1 + C*C + D*D - r0*r0)/2*B
P('   alternative F_alt = (v1*D - v2*B)^2 + (A*v2 - C*v1)^2 - det^2 = %s'
  % n((v1*D - v2*B)**2 + (A*v2 - C*v1)**2 - det*det))

P('')
P('=' * 78)
P('(4) does the lead F vanish at the root, and is the "lower" point on S^1?')
P('   |p_plus|^2 - 1  = %s' % n(p_plus[0]**2 + p_plus[1]**2 - 1))
P('   |p_minus|^2 - 1 = %s' % n(p_minus[0]**2 + p_minus[1]**2 - 1))
P('   |p_lin|^2 - 1   = %s' % n(p_lin[0]**2 + p_lin[1]**2 - 1))
