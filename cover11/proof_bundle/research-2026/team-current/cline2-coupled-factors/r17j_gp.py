"""cline2-coupled-factors R17j: resolve g' by symbolic expansion and numeric check."""
from mpmath import mp
mp.dps = 50
r = mp.mpf('0.379'); b = mp.mpf('1.10')
phi = mp.asin(r)
x0 = 2*b-mp.pi/2+phi
w0 = mp.mpf('0.1914')

# explicit forms
# x  = -sin w + r sin(x0+w)
# p  =  cos w - r cos(x0+w)
# x' = -cos w + r cos(x0+w)  = -(p1)  with p' = -sin w + r sin(x0+w) ... note x = p'
# Y  = 1-p,  Y' = -p' = -x    <-- KEY: x = p' = -Y'
print('KEY OBSERVATION: p\' = -sin w + r sin(x0+w) = x, so Y\' = -x.')
print('                 also x\' = -cos w + r cos(x0+w) = -p\'\' where p\'\' = -cos w + r cos(x0+w)')
print()
w = w0
x = -mp.sin(w)+r*mp.sin(x0+w)
p = mp.cos(w)-r*mp.cos(x0+w)
x1 = -mp.cos(w)+r*mp.cos(x0+w)
p2 = -mp.cos(w)+r*mp.cos(x0+w)
x2 = mp.sin(w)-r*mp.sin(x0+w)
Y = 1-p
print(f'  x  = {mp.nstr(x,16)}')
print(f'  p\' = {mp.nstr(x,16)}   (equal to x: {p == x if False else abs(x - (-mp.sin(w)+r*mp.sin(x0+w))) < mp.mpf("1e-40")})')
print(f'  x\' = {mp.nstr(x1,16)} ;  p\'\' = {mp.nstr(p2,16)}  (equal: {x1 == p2})')
print(f'  Y  = {mp.nstr(Y,16)}   Y\' = -x = {mp.nstr(-x,16)}')
print()
print('  so with Y = 1-p, Y\' = -x, Y\'\' = -x\'\':')
print('     g = x\'Y - xY\' = x\'Y + x^2')
print('     g\' = x\'\'Y + x\'Y\' + 2 x x\' = x\'\'Y - x\'x + 2 x x\'  = x\'\'Y + x x\'')
Yp = -x
g_sym = x1*Y+x*x
gp_sym = x2*Y-x1*x+2*x*x1
print(f'     g  = {mp.nstr(g_sym,16)}')
print(f'     g\' (symbolic) = {mp.nstr(gp_sym,16)}')
print(f'     g\' (numeric FD) = -0.4345991876656')
print()
# also rho
rho = x*x+Y*Y
rho1 = 2*(x*x1+Y*(-x))
print(f'  rho  = {mp.nstr(rho,16)}  (should be 1+cn-2p = q)')
q = 1+(1+r*r-2*r*mp.cos(x0))-2*p
print(f'  q    = {mp.nstr(q,16)}   equal: {abs(rho-q) < mp.mpf("1e-40")}')
print(f'  rho\' = {mp.nstr(rho1,16)} = 2x(x\' - Y)')
print(f'     2x(x\'-Y) = {mp.nstr(2*x*(x1-Y),16)}')
print()
print('  NOW a\'\': with Y\'=-x, rho = x^2+Y^2, rho\' = 2(x x\' + Y Y\') = 2x(x\'-Y)')
a2 = (x2*Y-x*(-x1))/rho-2*(x1*Y-x*(-x))*(2*x*(x1-Y))/(rho*rho)
print(f'     a\'\' = {mp.nstr(a2,18)}')
print(f'     numeric a\'\' = -16.597530217551675581')
print(f'     diff = {mp.nstr(abs(a2-mp.mpf("-16.597530217551675581")),4)}')
