"""cline2-coupled-factors R17L: verify W'' term by term, each piece differenced on its own."""
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


hstep = mp.mpf('1e-3')
print('term-by-term second derivative (FD of each piece at h=1e-3):')
fd_x = (X(w0+hstep)-2*X(w0)+X(w0-hstep))/hstep**2/2
print(f'  x/2        : analytic x\'\'/2 = {-X(w0)/2:.15f}   FD = {mp.nstr(fd_x,15)}')
fd_a = (A(w0+hstep)-2*A(w0)+A(w0-hstep))/hstep**2
print(f'  a          : analytic a\'\'   = (below)        FD = {mp.nstr(fd_a,15)}')
fd_u = (U(w0+hstep)-2*U(w0)+U(w0-hstep))/hstep**2
print(f'  u          : FD u\'\'        = {mp.nstr(fd_u,15)}')
fd_u2 = (U(w0+hstep)**2-2*U(w0)**2+U(w0-hstep)**2)/hstep**2
print(f'  u^2        : FD (u^2)\'\'    = {mp.nstr(fd_u2,15)}')
print()
print('  so W\'\' = x\'\'/2 + (mu+h)*a\'\' - d*(u^2)\'\' - l*u\'\'  [note: -d(u^2)\'\' = -2d(u\'^2+uu\'\')]')
W2_direct = fd_x+(mu+h)*fd_a-d*fd_u2-l*fd_u
print(f'     assembled from FDs = {mp.nstr(W2_direct,16)}')
h2 = mp.mpf('1e-3')
def Wval(w):
    Y = 1-Pp(w)
    q = X(w)**2+Y*Y
    return (-r*mp.sqrt(1-r*r)*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+X(w)/2
            +(mu+h)*mp.atan2(X(w), Y)-d*q/R**2-l*mp.sqrt(q)/R)
fd_W = (Wval(w0+h2)-2*Wval(w0)+Wval(w0-h2))/h2**2
print(f'     direct FD of W      = {mp.nstr(fd_W,16)}')
print()
print('  now the closed-form pieces:')
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
print(f'     a\'\' closed = {mp.nstr(a2_closed,16)}   FD = {mp.nstr(fd_a,16)}   '
      f'rel diff = {mp.nstr(abs(a2_closed-fd_a)/abs(fd_a),4)}')
print(f'     x\'\'/2 = {mp.nstr(x2/2,16)}   FD = {mp.nstr(fd_x,16)}')
print(f'     coefficients: mu+h = {mp.nstr(mu+h,12)}  d = {mp.nstr(d,12)}  l = {mp.nstr(l,12)}')
print()
print('  check the u-part coefficients against the definition W-part = -d u^2 - l u:')
print(f'     -d*(u^2)\'\' = {-d*fd_u2:.15f}   (from FD)')
print(f'     -l*u\'\'      = {-l*fd_u:.15f}   (from FD)')
