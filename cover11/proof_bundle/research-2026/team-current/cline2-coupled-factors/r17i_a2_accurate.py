"""cline2-coupled-factors R17i: high-accuracy a'' and W'' by tiny-step difference."""
from mpmath import mp
mp.dps = 50

r = mp.mpf('0.379'); b = mp.mpf('1.10')
phi = mp.asin(r)
x0 = 2*b-mp.pi/2+phi
w0 = mp.mpf('0.1914')


def a_of(w):
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    return mp.atan2(x, 1-p)


print("a'' by successive refinement (the sequence should stabilise):")
prev = None
for hh in ['1e-3', '5e-4', '2.5e-4', '1.25e-4', '6.25e-5', '3.125e-5']:
    h = mp.mpf(hh)
    v = (a_of(w0+h)-2*a_of(w0)+a_of(w0-h))/(h*h)
    ch = '' if prev is None else f'   change {mp.nstr(v-prev,4)}'
    print(f'   h={hh:9s} a\'\' = {mp.nstr(v,20)}{ch}')
    prev = v
print()
print('closed-form candidates:')
p = mp.cos(w0)-r*mp.cos(x0+w0)
x = -mp.sin(w0)+r*mp.sin(x0+w0)
p1 = -mp.sin(w0)+r*mp.sin(x0+w0)
p2 = -mp.cos(w0)+r*mp.cos(x0+w0)
x1 = -mp.cos(w0)+r*mp.cos(x0+w0)
x2 = mp.sin(w0)-r*mp.sin(x0+w0)
Y = 1-p; Yp = -p1; Ypp = -p2
rho = x*x+Y*Y
rho1 = 2*(x*x1+Y*Yp)
g = x1*Y-x*Yp
gp = x2*Y-x*Ypp
print(f'   x={mp.nstr(x,14)} Y={mp.nstr(Y,14)} rho={mp.nstr(rho,14)}')
print(f'   x\'={mp.nstr(x1,14)} x\'\'={mp.nstr(x2,14)} Y\'={mp.nstr(Yp,14)} Y\'\'={mp.nstr(Ypp,14)}')
print(f'   g = x\'Y - xY\' = {mp.nstr(g,16)}')
print(f'   gp = x\'\'Y - xY\'\' = {mp.nstr(gp,16)}')
print(f'   rho\' = {mp.nstr(rho1,16)}')
print(f'   candidate (gp rho - g rho\')/rho^2 = {mp.nstr((gp*rho-g*rho1)/(rho*rho),18)}')
print()
print('  NOTE on gp: gp = d/dw[x\']*Y + x\'*Y\' - d/dw[x]*Y\' - x*Y\'\'')
print(f'     d/dw[x\'] = x\'\' = {mp.nstr(x2,14)} ;  x\'*Y\' = {mp.nstr(x1*Yp,14)}')
print(f'     d/dw[x]*Y\' = x\'*Y\' = {mp.nstr(x1*Yp,14)}  (they cancel!)')
print(f'     so gp = x\'\'*Y - x*Y\'\' = {mp.nstr(x2*Y-x*Ypp,16)}')
print()
print('  BUT: g = x\'*Y - x*Y\', so dg/dw = x\'\'Y + x\'Y\' - x\'Y\' - xY\'\' = x\'\'Y - xY\'\'')
print('  which is what we used.  Check by differencing g directly at tiny h:')
for hh in ['1e-4', '1e-5', '1e-6']:
    h = mp.mpf(hh)
    def g_of(w):
        p = mp.cos(w)-r*mp.cos(x0+w)
        xx = -mp.sin(w)+r*mp.sin(x0+w)
        p1_ = -mp.sin(w)+r*mp.sin(x0+w)
        return p1_*(1-p)-xx*(-p1_)
    v = (g_of(w0+h)-g_of(w0-h))/(2*h)
    print(f'     h={hh}: g\' = {mp.nstr(v,20)}')
