"""cline2-coupled-factors R17L2: verify W'' term by term (each piece differenced alone)."""
import json
from pathlib import Path
from mpmath import mp
mp.dps = 50
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: mp.mpf(f'{zJ[i]:.9f}') for i in range(len(zJ))}
R = mp.mpf(19)/50
r = mp.mpf('0.379'); b = mp.mpf('1.10'); w0 = mp.mpf('0.1914')
x0 = 2*b-mp.pi/2+mp.asin(r)
mu, h, d, l = Z[1], Z[112], Z[34], Z[96]


def X(w):
    return -mp.sin(w)+r*mp.sin(x0+w)


def Pp(w):
    return mp.cos(w)-r*mp.cos(x0+w)


def A(w):
    return mp.atan2(X(w), 1-Pp(w))


def U(w):
    Y = 1-Pp(w)
    return mp.sqrt(X(w)**2+Y*Y)/R


def fd(f, h):
    return (f(w0+h)-2*f(w0)+f(w0-h))/(h*h)


hh = mp.mpf('1e-3')
fd_x = fd(X, hh)/2
fd_a = fd(A, hh)
fd_u = fd(U, hh)
fd_u2 = fd(lambda w: U(w)**2, hh)
print('term-by-term second derivatives at w0 = 0.1914 (h = 1e-3):')
print('   x/2  : FD =', mp.nstr(fd_x, 16))
print('   a    : FD =', mp.nstr(fd_a, 16))
print('   u    : FD =', mp.nstr(fd_u, 16))
print('   u^2  : FD =', mp.nstr(fd_u2, 16))
print()
print('   W = x/2 + (mu+h)a - d u^2 - l u  (w-dependent part)')
print('   => W" = (x/2)" + (mu+h) a" - d (u^2)" - l u"')
assembled = fd_x+(mu+h)*fd_a-d*fd_u2-l*fd_u
print('   assembled from the FD pieces =', mp.nstr(assembled, 16))


def Wval(w):
    Y = 1-Pp(w)
    q = X(w)**2+Y*Y
    return (-r*mp.sqrt(1-r*r)*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+X(w)/2
            +(mu+h)*mp.atan2(X(w), Y)-d*q/R**2-l*mp.sqrt(q)/R)


print('   direct FD of W               =', mp.nstr(fd(Wval, hh), 16))
print()
x = X(w0); Yv = 1-Pp(w0)
x1 = -mp.cos(w0)+r*mp.cos(x0+w0)
x2 = mp.sin(w0)-r*mp.sin(x0+w0)
Yp = -x
Ypp = -x1
rho = x*x+Yv*Yv
rho1 = 2*(x*x1+Yv*Yp)
g = x1*Yv-x*Yp
gp = x2*Yv-x*Ypp
a2_closed = gp/rho-g*rho1/(rho*rho)
print('closed-form pieces:')
print('   x"/2 =', mp.nstr(x2/2, 16), '   (FD gave', mp.nstr(fd_x, 16)+')')
print('   a"   =', mp.nstr(a2_closed, 16), '   (FD gave', mp.nstr(fd_a, 16)+')')
print('   rel diff for a":', mp.nstr(abs(a2_closed-fd_a)/abs(fd_a), 6))
print('   coefficients mu+h =', mp.nstr(mu+h, 12), ' d =', mp.nstr(d, 12),
      ' l =', mp.nstr(l, 12))
