"""root-cc2: verify the identities that the lead's ROOT-ATTAINMENT argument uses.

Symbolic simplification of nested-radical expressions timed out, so these are checked
by 120-digit evaluation at the root plus exact structural checks:

  (I1)  F_lead = det^2 * e   with e = |p|^2 - 1                (exact identity)
  (I2)  G_lead = l1 * (l2 l3 - cross^2)   vs   G_mine = l1 l2 l3 - 4 r^2 cross^2
  (I3)  |p - A|^2 - r^2 = e  and  |p - C|^2 - r^2 = e          (both = e)
  (I4)  the two "cross" conventions differ by a sign only
  (I5)  F=0 and G=0 at the root; det != 0; p on S^1; |p-A| = |p-C| = r
"""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 120
HERE = Path(__file__).resolve().parent
NCG = HERE.parents[2]
scout = json.loads((NCG / 'lead' / 'root-scout.json').read_text())
z, C, r = [mp.mpf(s) for s in scout['z_c_r']]

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

s = mp.sqrt(1 - r*r); a = (s + z)/2
t = r + mp.sqrt(r*r - z*z)
b = r + mp.sqrt(r*r - (a - z)**2)
d = 1 - mp.sqrt(r*r - C*C)
v1 = (1 + a*a + b*b - r*r)/2
v2 = (1 + C*C + d*d - r*r)/2
det = a*d - b*C
px = (v1*d - v2*b)/det
py = (a*v2 - C*v1)/det
e = px*px + py*py - 1

F_lead = (v1*d - v2*b)**2 + (a*v2 - C*v1)**2 - det**2
F_expand = det*det*e
P('(I1) F_lead vs det^2 * e')
P('     F_lead            = %s' % mp.nstr(F_lead, 20))
P('     det^2 * e         = %s' % mp.nstr(F_expand, 20))
P('     difference        = %s' % mp.nstr(F_lead - F_expand, 6))
P('     relative          = %s' % mp.nstr((F_lead - F_expand)/F_lead, 6))
P('     det = %s ; e = %s' % (mp.nstr(det, 20), mp.nstr(e, 20)))

cross_lead = (C - a)*(t - b) + (d - b)*a
cross_mine = (C - a)*(t - b) - (d - b)*(-a)
P('')
P('(I4) cross conventions')
P('     cross_lead - cross_mine = %s' % mp.nstr(cross_lead - cross_mine, 6))
P('     cross_lead + cross_mine = %s (needs to equal 2(C-a)(t-b) = %s)'
  % (mp.nstr(cross_lead + cross_mine, 20), mp.nstr(2*(C-a)*(t-b), 20)))

l1 = (a - C)**2 + (b - d)**2
l2 = C*C + (d - t)**2
l3 = a*a + (b - t)**2
G_lead = l1*(r*r - (a - z)**2)*(r*r - z*z) - 4*r*r*cross_lead**2
G_mine = l1*l2*l3 - 4*r*r*cross_mine**2
P('')
P('(I2) G conventions')
P('     G_lead = %s' % mp.nstr(G_lead, 20))
P('     G_mine = %s' % mp.nstr(G_mine, 20))
P('     G_mine - G_lead = %s' % mp.nstr(G_mine - G_lead, 6))
P('     (G_mine - G_lead)/cross^2 = %s   [expect 4r^2 - 1 = %s]'
  % (mp.nstr((G_mine - G_lead)/cross_lead**2, 20), mp.nstr(4*r*r - 1, 20)))
P('     l2*l3 - (r^2-(a-z)^2)(r^2-z^2) = %s' % mp.nstr(l2*l3 - (r*r - (a - z)**2)*(r*r - z*z), 20))
P('     cross^2 = %s' % mp.nstr(cross_lead**2, 20))

P('')
P('(I3)/(I5) contact identities at the root')
P('     |p|^2 - 1                = %s' % mp.nstr(px*px + py*py - 1, 12))
P('     |p-A|^2 - r^2            = %s' % mp.nstr((px-a)**2 + (py-b)**2 - r*r, 12))
P('     |p-C|^2 - r^2            = %s' % mp.nstr((px-C)**2 + (py-d)**2 - r*r, 12))
P('     p·A - v1                 = %s' % mp.nstr(px*a + py*b - v1, 4))
P('     p·C - v2                 = %s' % mp.nstr(px*C + py*d - v2, 4))
P('     F_lead                   = %s' % mp.nstr(F_lead, 12))
P('     G_lead                   = %s' % mp.nstr(G_lead, 12))
P('     det                      = %s' % mp.nstr(det, 20))

(HERE.parent / 'evidence' / 'verif06_identities.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written] evidence/verif06_identities.txt')
