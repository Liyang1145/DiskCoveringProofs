"""cline2-coupled-factors R16aa: decompose the off-face second difference to locate the gap."""
from mpmath import mp
mp.dps = 40
R = mp.mpf(19)/50
r, b1, b2 = mp.mpf('0.375'), mp.mpf('1.05'), mp.mpf('1.05')
B2c, G2c, A2c = mp.mpf('0.400827103'), mp.mpf('-0.86525597'), mp.mpf('0.013306528')


def pieces(d):
    A = b1-d; B = b2+d
    H = 2*r*mp.sin(2*b1-d)
    Y = 2*r*mp.sin(b2)*mp.sin(B)
    X = H-2*r*mp.sin(b2)*mp.cos(B)
    Q = X*X+Y*Y
    e2 = mp.sqrt(Q)/(2*R)
    phi = mp.atan2(Y, X)
    return e2, phi, X, Y, Q


h = mp.mpf('1e-4')
d0 = mp.mpf(0)
e2p = (pieces(d0+h)[0]-2*pieces(d0)[0]+pieces(d0-h)[0])/(h*h)   # e2''
phip = (pieces(d0+h)[1]-2*pieces(d0)[1]+pieces(d0-h)[1])/(h*h)   # phi''
e2 = pieces(d0)[0]; phi = pieces(d0)[1]
e2_fd1 = (pieces(d0+h)[0]-pieces(d0-h)[0])/(2*h)
phi_fd1 = (pieces(d0+h)[1]-pieces(d0-h)[1])/(2*h)
print('e2   =', mp.nstr(e2, 15))
print("e2'  =", mp.nstr(e2_fd1, 15), "  e2''  =", mp.nstr(e2p, 15))
print("phi' =", mp.nstr(phi_fd1, 15), "  phi'' =", mp.nstr(phip, 15))
print()
print('parts of the off second difference:')
print('  2 B2c (e2\')^2          =', mp.nstr(2*B2c*e2_fd1**2, 15))
print('  (2 B2c e2 + G2c) e2\'\'  =', mp.nstr((2*B2c*e2+G2c)*e2p, 15))
print('  A2c phi\'\'             =', mp.nstr(A2c*phip, 15))
print('  sum                    =', mp.nstr(2*B2c*e2_fd1**2+(2*B2c*e2+G2c)*e2p+A2c*phip, 15))


def offval(d):
    e2, phi, X, Y, Q = pieces(d)
    return B2c*e2*e2+G2c*e2+A2c*phi


print('  off piece FD direct    =', mp.nstr((offval(d0+h)-2*offval(d0)+offval(d0-h))/(h*h), 15))
print()
# suspected missing term: d/ddelta of (2 B2c e2 + G2c) is 2 B2c e2', so the correct
# second derivative of B2c e2^2 + G2c e2 is 2 B2c (e2')^2 * 2 ... let's just print both
print('  candidate with coefficient 4 on (e2\')^2:',
      mp.nstr(4*B2c*e2_fd1**2+(2*B2c*e2+G2c)*e2p+A2c*phip, 15))
