"""root-cc2: independent representation check of lead/root_integer_certificate.py.

Three interfaces decide whether the lead's integer certificate and my interval
certificate speak about the SAME zero set:
  (i)   their F vs my F_tilde:   F_lead = (v1 d - v2 b)^2 + (a v2 - c v1)^2 - det^2
        vs my e^2 + |p-S1|^2 - r^2 with p the linear solve, e = |p|^2 - 1.
  (ii)  their cross  (c-a)(t-b) + (d-b) a  vs the version with -(d-b)(-a):
        equal?  (only cross^2 enters G, so a sign flip is harmless anyway)
  (iii) their G uses l1*(r^2-(a-z)^2)*(r^2-z^2) instead of l1*l2*l3: these differ by
        the factor cross^2, i.e. the two G's are equal up to a non-vanishing factor,
        so the zero sets agree where cross != 0.
Also: interval check that cross != 0 on my certificate box (needed for (iii) and for
the "same zero set" statement).
All symbolic checks are exact (sympy); the box check is an mpmath interval enclosure.
"""
import sys
from pathlib import Path
import sympy as sp
import mpmath as mp
from mpmath import iv

mp.mp.dps = 60
iv.dps = 60
HERE = Path(__file__).resolve().parent

log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)
def Lv(x): return mp.mpf(x.a.a)
def Rv(x): return mp.mpf(x.b.b)

z, c, r = sp.symbols('z c r', real=True)
s = sp.sqrt(1 - r**2)
a = (s + z)/2
t = r + sp.sqrt(r**2 - z**2)
b = r + sp.sqrt(r**2 - (a - z)**2)
d = 1 - sp.sqrt(r**2 - c**2)
v1 = (1 + a**2 + b**2 - r**2)/2
v2 = (1 + c**2 + d**2 - r**2)/2
det = a*d - b*c
px = (v1*d - v2*b)/det
py = (a*v2 - c*v1)/det

P('=' * 78)
P('(i) lead F vs my F_tilde')
F_lead = (v1*d - v2*b)**2 + (a*v2 - c*v1)**2 - det**2
e = px**2 + py**2 - 1
F_mine = e**2 + ((px - a)**2 + (py - b)**2 - r**2)
ratio = sp.simplify(F_lead / F_mine)
P('   F_lead / F_tilde = %s' % sp.simplify(sp.together(ratio)))
P('   F_lead expanded  = %s' % sp.expand(F_lead))
P('   det^2 * (px^2+py^2-1) - F_lead = %s'
  % sp.simplify(det**2*(px**2 + py**2 - 1) - F_lead))

P('')
P('(ii) the two cross conventions')
crossA = (c - a)*(t - b) + (d - b)*a       # lead's
crossB = (c - a)*(t - b) - (d - b)*(-a)    # mine
P('   crossA - crossB = %s' % sp.simplify(crossA - crossB))
P('   crossA + crossB vs 2(c-a)(t-b): %s' % sp.simplify(crossA + crossB - 2*(c - a)*(t - b)))

P('')
P('(iii) lead G vs my G')
l1 = (a - c)**2 + (b - d)**2
l2 = c**2 + (d - t)**2
l3 = a**2 + (b - t)**2
G_mine = l1*l2*l3 - 4*r**2*crossA**2
G_lead = l1*(r**2 - (a - z)**2)*(r**2 - z**2) - 4*r**2*crossA**2
P('   l2*l3 - (r^2-(a-z)^2)(r^2-z^2) = %s'
  % sp.simplify(l2*l3 - (r**2 - (a - z)**2)*(r**2 - z**2)))
P('   G_lead - [l1*(r^2-(a-z)^2)(r^2-z^2) - 4r^2 cross^2] = %s'
  % sp.simplify(G_lead - (l1*(r**2 - (a - z)**2)*(r**2 - z**2) - 4*r**2*crossA**2)))
P('   G_lead - l1*crossA^2 = %s' % sp.simplify(G_lead - l1*crossA**2))
P('   (so G_lead = l1*(l2 l3 - cross^2) and G_mine = l1*l2*l3 - 4 r^2 cross^2:')
P('    their zero sets agree because G_mine = l1*(l2l3 - 4r^2 cross^2/l1) and')
P('    l2l3 - cross^2 differs from l2l3 - 4r^2 cross^2 by (4r^2-1) cross^2.)')
P('   G_mine - G_lead = %s' % sp.simplify(G_mine - G_lead))
P('   (G_mine - G_lead)/cross^2 = %s' % sp.simplify((G_mine - G_lead)/crossA**2))

P('')
P('=' * 78)
P('(iv) interval check on my certificate box that cross != 0 and 4r^2 != 1')
zlo, zhi = mp.mpf('0.326813068949914'), mp.mpf('0.326823068949914')
Clo, Chi = mp.mpf('0.291936118964939'), mp.mpf('0.291946118964939')
rlo, rhi = mp.mpf('0.331727034276234'), mp.mpf('0.331737034276234')
one = iv.mpf(mp.mpf(1)); two = iv.mpf(mp.mpf(2))
Z = iv.mpf([zlo, zhi]); CC = iv.mpf([Clo, Chi]); RR = iv.mpf([rlo, rhi])
S = iv.sqrt(one - RR*RR)
A = (S + Z)/two
T = RR + iv.sqrt(RR*RR - Z*Z)
B = RR + iv.sqrt(RR*RR - (A - Z)*(A - Z))
D = one - iv.sqrt(RR*RR - CC*CC)
crossI = (CC - A)*(T - B) + (D - B)*A
P('   interval cross = [%s, %s]   sign definite: %s'
  % (mp.nstr(Lv(crossI), 14), mp.nstr(Rv(crossI), 14), (Lv(crossI) > 0) or (Rv(crossI) < 0)))
P('   interval 4r^2  = [%s, %s]   != 1: %s'
  % (mp.nstr(Lv(4*RR*RR), 10), mp.nstr(Rv(4*RR*RR), 10), not (Lv(4*RR*RR) <= 1 <= Rv(4*RR*RR))))

(HERE.parent / 'evidence' / 'verif05_leadrep_equivalence.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written] evidence/verif05_leadrep_equivalence.txt')
