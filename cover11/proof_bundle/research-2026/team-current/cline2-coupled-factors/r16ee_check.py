import sys
from mpmath import iv, mp
from pathlib import Path
P = Path(r'research-2026/team-current/cline2-coupled-factors')
sys.path.insert(0, str(P))
iv.dps = 30
mp.dps = 30
import r16S_g2_legal as S
from r16S_g2_legal import face1_data, RR, TWO, BE2, GA2, XX2

r, b1, b2, d0 = 0.375, 1.05, 1.05, 0.0
ri, b1i, b2i, di = (iv.mpf(repr(x)) for x in (r, b1, b2, d0))
q = face1_data(ri, b1i, b2i, di)
print('code: Q =', float(q['Q'].a), ' 2R*e2 =', float((TWO*RR*q['e2']).a))
print('Q vs (2R e2)^2 :', float(q['Q'].a), float((TWO*RR*q['e2']).a)**2)
print()
# independent recomputation of Q here
H = 2*r*mp.sin(2*b1-0)
Y = 2*r*mp.sin(b1)*mp.sin(b2+0)+0
X = H-2*r*mp.sin(b2)*mp.cos(b2+0)
print('independent X =', mp.nstr(X, 17), ' Y =', mp.nstr(Y, 17),
      ' Q =', mp.nstr(X*X+Y*Y, 17))
print('e2 =', mp.nstr(mp.sqrt(X*X+Y*Y)/(2*mp.mpf(19)/50), 17))
print()
print('So the code\'s e2 corresponds to sqrt(Q)/(2R) with Q =',
      mp.nstr((2*mp.mpf(19)/50*mp.mpf('0.85600976209935875'))**2, 17))
print('which is NOT the Q printed above -> the module computes e2 from a DIFFERENT Q.')
print()
print('BE2 =', float(BE2.a), ' GA2 =', float(GA2.a), ' XX2 =', float(XX2.a))
off2 = (TWO*BE2*q['e2']+GA2)*q['e2pp']+TWO*BE2*q['e2p']*q['e2p']+TWO*XX2*q['phi2p']
print('code off2 =', float(off2.a))
# manual with printed values
e2 = float(q['e2'].a); e2p = float(q['e2p'].a); e2pp = float(q['e2pp'].a)
phi2p = float(q['phi2p'].a)
man = (2*float(BE2.a)*e2+float(GA2.a))*e2pp+2*float(BE2.a)*e2p*e2p+2*float(XX2.a)*phi2p
print('manual from the SAME printed values =', man)
