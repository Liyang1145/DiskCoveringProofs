"""cline2-coupled-factors R16V: locate and fix the G'' discrepancy by validating each
second-derivative piece separately against finite differences.

Pieces of G'' = d2V/ddelta2:
   hub      : H'' k + 2 H' k' + H k''
   on-face  : (2 beta e + gamma) e'' + 2 beta (e')^2
   off-face : (2 beta e + gamma) e'' + 2 beta (e')^2 + 2 a phi'
with e = sqrt(Q)/(2R), e' = Q'/(4 R sqrt(Q)), e'' = Q''/(4 R sqrt(Q)) - (Q')^2/(8 R Q^{3/2}).
"""
import math, sys
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
sys.path.insert(0, str(P))
from r16S_g2_legal import face1_data, RR, TWO

print('=== per-piece validation at a legal point (0.375,1.05,1.05,0.0) ===')
r, b1, b2, dl = 0.375, 1.05, 1.05, 0.0
r_i, b1_i, b2_i, d_i = [iv.mpf(repr(x)) for x in (r, b1, b2, dl)]
q0 = face1_data(r_i, b1_i, b2_i, d_i)
h = iv.mpf('1e-3')
qp = face1_data(r_i, b1_i, b2_i, d_i+h)
qm = face1_data(r_i, b1_i, b2_i, d_i-h)

print('  e2   analytic:', float(q0['e2'].a))
print('  e2\'  analytic:', float(q0['e2p'].a), ' FD:',
      float(((qp['e2']-qm['e2'])/(2*h)).a))
print('  e2\'\' analytic:', float(q0['e2pp'].a), ' FD of e2\':',
      float(((qp['e2p']-qm['e2p'])/(2*h)).a))
print('  G\'   analytic:', float(q0['G1'].a), ' FD of G:',
      float(((qp['G']-qm['G'])/(2*h)).a))
print('  G\'\'  analytic:', float(q0['G2'].a), ' FD of G\':',
      float(((qp['G1']-qm['G1'])/(2*h)).a))
gap = float(((qp['G1']-qm['G1'])/(2*h)).a) - float(q0['G2'].a)
print(f'  gap = {gap:+.9f}')

# what correction to the 2*beta*(e')^2 coefficient would close it?
beta2 = float(iv.mpf('-0.86525597').a) if False else -0.86525597
e2p = float(q0['e2p'].a)
print(f'  if the off-face quadratic coefficient were 2*beta2*(e\' )^2 = '
      f'{2*beta2*e2p*e2p:+.9f}')
print(f'  with coefficient 4*beta2*(e\')^2 = {4*beta2*e2p*e2p:+.9f}')
print(f'  gap / (beta2 e2p^2) = {gap/(beta2*e2p*e2p):+.6f}   '
      f'(would be -2 if the coefficient should be 4 instead of 2)')

print('\n=== recompute with the corrected off-face coefficient (4 beta e\'^2) ===')


def G2_fixed(r, b1, b2, dl):
    q = face1_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    if q is None:
        return None
    # rebuild the off-face part with the corrected coefficient
    beta2 = -0.86525597
    e2p = float(q['e2p'].a)
    e2pp = float(q['e2pp'].a)
    off_old = (2*beta2*float(q['e2'].a)+(-0.86525597))*e2pp+2*beta2*e2p*e2p
    off_new = (2*beta2*float(q['e2'].a)+(-0.86525597))*e2pp+4*beta2*e2p*e2p
    return float(q['G2'].a)-off_old+off_new


h2 = iv.mpf('1e-3')
fd2 = float(((qp['G1']-qm['G1'])/(2*h2)).a)
print(f'  analytic (corrected) = {G2_fixed(r,b1,b2,dl):+.9f}')
print(f'  FD of G\'            = {fd2:+.9f}')
print(f'  remaining gap        = {fd2-G2_fixed(r,b1,b2,dl):+.2e}')
