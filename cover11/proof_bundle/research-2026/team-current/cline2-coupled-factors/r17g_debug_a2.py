"""cline2-coupled-factors R17g: resolve the factor-2 in a'' with a transparent numeric test."""
from mpmath import mp
mp.dps = 40

r = mp.mpf('0.379'); b = mp.mpf('1.10')
phi = mp.asin(r)
x0 = 2*b-mp.pi/2+phi


def parts(w):
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    return p, x


def a_of(w):
    p, x = parts(w)
    return mp.atan2(x, 1-p)


w0 = mp.mpf('0.1914')
h = mp.mpf('1e-3')
a_p = a_of(w0+h); a_0 = a_of(w0); a_m = a_of(w0-h)
fd2 = (a_p-2*a_0+a_m)/(h*h)
p, x = parts(w0)
p1 = -mp.sin(w0)+r*mp.sin(x0+w0)
p2 = -mp.cos(w0)+r*mp.cos(x0+w0)
x1 = -mp.cos(w0)+r*mp.cos(x0+w0)
x2 = mp.sin(w0)-r*mp.sin(x0+w0)
Y = 1-p; Yp = -p1; Ypp = -p2
rho = x*x+Y*Y
rho1 = 2*(x*x1+Y*Yp)
print(f'w0={float(w0)}  x={mp.nstr(x,12)} Y={mp.nstr(Y,12)} rho={mp.nstr(rho,12)}')
print(f'  x\'={mp.nstr(x1,12)} x\'\'={mp.nstr(x2,12)} Y\'={mp.nstr(Yp,12)} Y\'\'={mp.nstr(Ypp,12)}')
print(f'  rho={mp.nstr(rho,12)} rho\'={mp.nstr(rho1,12)}')
print()
g = x1*Y-x*Yp
gp = x2*Y-x*Ypp
print(f'  a\' = g/rho   with g={mp.nstr(g,12)}')
a1 = g/rho
a1_fd = (a_p-a_m)/(2*h)
print(f'     closed a\'={mp.nstr(a1,16)}   FD a\'={mp.nstr(a1_fd,16)}   '
      f'diff={mp.nstr(abs(a1-a1_fd),4)}')
print()
print('  a\'\' via three candidate expressions:')
c1 = gp/rho-g*rho1/(rho*rho)
c2 = (gp*rho-g*rho1)/(rho*rho)
print(f'     c1 = gp/rho - g rho\'/rho^2 = {mp.nstr(c1,16)}')
print(f'     c2 = (gp rho - g rho\')/rho^2 = {mp.nstr(c2,16)}   (identical: {c1==c2})')
print(f'     FD a\'\' = {mp.nstr(fd2,16)}')
print(f'     ratio c1/FD = {mp.nstr(c1/fd2,10)}')
print()
print('  check rho\' : rho = x^2+Y^2 so rho\' = 2(x x\' + Y Y\')')
print(f'     direct FD of rho: ', end='')
pp, xx = parts(w0+h); Yp2 = 1-pp; rho_p = xx*xx+Yp2*Yp2
pp, xx = parts(w0-h); Yp2 = 1-pp; rho_m = xx*xx+Yp2*Yp2
print(f'{(rho_p-rho_m)/(2*h)}')
print(f'     formula: {mp.nstr(rho1,16)}')
print()
print('  check gp by FD of g:')
def g_of(w):
    p, x = parts(w)
    ph2 = mp.asin(r); x02 = 2*b-mp.pi/2+ph2
    p1_ = -mp.sin(w)+r*mp.sin(x02+w)
    Y_ = 1-p
    return p1_*Y_-x*(-p1_)
gp_fd = (g_of(w0+h)-g_of(w0-h))/(2*h)
print(f'     FD gp={mp.nstr(gp_fd,16)}   formula gp={mp.nstr(gp,16)}   '
      f'diff={mp.nstr(abs(gp_fd-gp),4)}')
print()
print('  DIRECT arctan derivative check: d/dw atan2(x,Y) = (x\'Y - xY\')/(x^2+Y^2)')
print(f'     a\' from FD           = {mp.nstr(a1_fd,16)}')
print(f'     (x\'Y - xY\')/rho      = {mp.nstr((x1*Y-x*Yp)/rho,16)}')
