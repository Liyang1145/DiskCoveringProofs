"""cline2-coupled-factors R16W: isolate the 0.066 gap by piecewise FD comparison."""
import sys, math
from pathlib import Path
from mpmath import iv
iv.dps = 30
sys.path.insert(0, str(Path(__file__).parent))
from r16S_g2_legal import RR, TWO

r, b1, b2 = 0.375, 1.05, 1.05


def pieces(dl):
    r_i, b1_i, b2_i, d_i = iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl))
    A = b1_i-d_i; B = b2_i+d_i
    H = TWO*r_i*iv.sin(TWO*b1_i-d_i)
    Hp = -TWO*r_i*iv.cos(TWO*b1_i-d_i)
    k = r_i*(iv.sin(b1_i)*iv.sin(A)+iv.sin(b2_i)*iv.sin(B))
    e1 = r_i*iv.sin(A)/RR
    e2 = None
    Y = TWO*r_i*iv.sin(b2_i)*iv.sin(B)
    X = H-TWO*r_i*iv.sin(b2_i)*iv.cos(B)
    Q = X*X+Y*Y
    sq = iv.sqrt(Q)
    e2 = sq/(TWO*RR)
    return H, Hp, k, e1, e2, X, Y, Q, sq


h = iv.mpf('1e-4')
d0 = 0.0
H0, Hp0, k0, e10, e20, X0, Y0, Q0, sq0 = pieces(d0)
Hp_, Hpp_, kp_, e1p_, e2p_, _, _, _, _ = pieces(d0+float(h))
Hm_, Hpm_, km_, e1m_, e2m_, _, _, _, _ = pieces(d0-float(h))
hub2_an = float(-H0).__float__()*0  # placeholder
# hub second derivative, analytic vs FD of the hub product H*k
hub_an = float(((-H0)*k0+TWO*Hp0*((-1)*r_i := 0 or 0)).a) if False else None
rr = iv.mpf(repr(r)); b1i = iv.mpf(repr(b1)); b2i = iv.mpf(repr(b2))
A0 = b1i-iv.mpf(repr(d0)); B0 = b2i+iv.mpf(repr(d0))
k1 = rr*(-iv.sin(b1i)*iv.cos(A0)+iv.sin(b2i)*iv.cos(B0))
k2 = -rr*(iv.sin(b1i)*iv.sin(A0)+iv.sin(b2i)*iv.sin(B0))
Hpp = -H0
hub2 = Hpp*k0+TWO*Hp0*k1+H0*k2
hub_fd = ((Hp_*kp_)-2*(H0*k0)+(Hm_*km_))/(h*h)
print('hub term  analytic:', float(hub2.a), ' FD:', float(hub_fd.a))
print('   (kp_/km_ recomputed below properly)')

# proper FD for the hub product
def hubval(dl):
    H, Hp, k, e1, e2, X, Y, Q, sq = pieces(dl)
    return H*k


hfd = 1e-4
hub_fd2 = (hubval(d0+hfd)-2*hubval(d0)+hubval(d0-hfd))/(hfd*hfd)
print('   hub FD (float):', hub_fd2, ' vs analytic', float(hub2.a),
      ' gap', hub_fd2-float(hub2.a))

# on-face piece
def onval(dl):
    H, Hp, k, e1, e2, X, Y, Q, sq = pieces(dl)
    return e1


on_fd = (onval(d0+hfd)-2*onval(d0)+onval(d0-hfd))/(hfd*hfd)
e1pp_an = -r*math.sin(b1-d0)/float(RR)
print('on-face e1\'\' analytic:', e1pp_an, ' FD:', on_fd)

# off-face pieces
def offvals(dl):
    H, Hp, k, e1, e2, X, Y, Q, sq = pieces(dl)
    return e2, float(Q), float(sq)


e2p0 = (offvals(d0+hfd)[0]-offvals(d0-hfd)[0])/(2*hfd)
e2pp_fd = (offvals(d0+hfd)[0]-2*offvals(d0)[0]+offvals(d0-hfd)[0])/(hfd*hfd)
print("off-face e2' FD:", e2p0, " e2'' FD:", e2pp_fd)
BETA2 = -0.86525597
print('2 beta2 (e2\')^2 =', 2*BETA2*e2p0*e2p0)
print('4 beta2 (e2\')^2 =', 4*BETA2*e2p0*e2p0)
print('term (2 beta2 e2 + gamma2) e2\'\' =', (2*BETA2*float(e20.a)+BETA2)*e2pp_fd)
print()
print('total analytic pieces: hub', float(hub2.a),
      '+ on-face', (2*(-0.405431351)*float(e10.a)+(-0.870277865))*e1pp_an
      + 2*(-0.405431351)*(r*math.cos(b1-d0)/float(RR))**2,
      '+ off-face', (2*BETA2*float(e20.a)+BETA2)*e2pp_fd+2*BETA2*e2p0*e2p0
      + 2*0.013306528*float((X0*TWO*rr*iv.sin(b2i)*iv.cos(B0)
                            -Y0*(Hp0+TWO*rr*iv.sin(b2i)*iv.sin(B0))).a/Q0)
      )
print('vs FD of the full G1: 0.3002587324154301 at this point')
