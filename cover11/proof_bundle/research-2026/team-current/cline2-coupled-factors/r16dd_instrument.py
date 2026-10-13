import sys
from mpmath import iv
from pathlib import Path
P = Path(r'research-2026/team-current/cline2-coupled-factors')
sys.path.insert(0, str(P))
iv.dps = 30
from r16S_g2_legal import face1_data, RR, TWO, BE1, GA1, BE2, GA2, XX1, XX2, C0

r, b1, b2, d0 = 0.375, 1.05, 1.05, 0.0
ri, b1i, b2i, di = iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(d0))
q = face1_data(ri, b1i, b2i, di)
print('code off-face pieces:')
for k in ['e2', 'e2p', 'e2pp', 'phi2', 'phi2p', 'Q']:
    print(f'   {k:6s} = {float(q[k].a):.17f}')
print()
print('reference (closed form, mpmath 40dps):')
print('   e2    = 0.85600976209935880')
print("   e2'   = 0.98680722875461378")
print("   e2''  = 0.01667366401438181")
print("   phi2' = -1.00969220919971500")
print()
off2_code = ((TWO*BE2*q['e2']+GA2)*q['e2pp']+TWO*BE2*q['e2p']*q['e2p']+TWO*XX2*q['phi2p'])
print('code off2  =', float(off2_code.a))
print('reference  = 0.8086333878459614')
print()
print('terms:')
print('   (2 BE2 e2 + GA2) e2pp =', float(((TWO*BE2*q['e2']+GA2)*q['e2pp']).a))
print('   2 BE2 (e2p)^2         =', float((TWO*BE2*q['e2p']*q['e2p']).a))
print('   2 XX2 phi2p           =', float((TWO*XX2*q['phi2p']).a))
print()
print('check: 2 BE2 =', float((TWO*BE2).a), ' BE2 =', float(BE2.a), ' XX2 =', float(XX2.a))
