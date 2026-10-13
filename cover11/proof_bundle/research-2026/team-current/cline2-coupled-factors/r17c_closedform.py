"""cline2-coupled-factors R17c: validate the closed-form W'' by Richardson extrapolation,
then state the c^T H c structure and the majorant constants.
"""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 40
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: mp.mpf(f'{zJ[i]:.9f}') for i in range(len(zJ))}
R = mp.mpf(19)/50


def consts(j):
    return ((Z[1], Z[112], Z[34], Z[96]) if j == 0 else (Z[3], Z[115], Z[39], Z[101]))


def geom(r, b, w):
    s = mp.sqrt(1-r*r); ph = mp.asin(r)
    x0 = 2*b-mp.pi/2+ph
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    return s, ph, x0, p, x


def Wval(r, b, w, j):
    mu, h, d, l = consts(j)
    s, ph, x0, p, x = geom(r, b, w)
    cn = 1+r*r-2*r*mp.cos(x0)
    q = 1+cn-2*p
    a = mp.atan2(x, 1-p)
    u = mp.sqrt(q)/R
    return -r*s*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+x/2+(mu+h)*a-d*u*u-l*u


def closed_W2(r, b, w, j):
    mu, h, d, l = consts(j)
    s, ph, x0, p, x = geom(r, b, w)
    p1 = -mp.sin(w)+r*mp.sin(x0+w)
    p2 = -mp.cos(w)+r*mp.cos(x0+w)
    p3 = mp.sin(w)-r*mp.sin(x0+w)
    x1 = -mp.cos(w)+r*mp.cos(x0+w)
    x2 = mp.sin(w)-r*mp.sin(x0+w)
    x3 = mp.cos(w)-r*mp.cos(x0+w)
    num, num1, num2, num3 = x, x1, x2, x3
    den, den1, den2, den3 = 1-p, -p1, -p2, -p3
    g1 = num1*den-num*den1
    g2 = num2*den-num*den2
    g3 = num3*den-num*den3
    rho = num*num+den*den
    rho1 = 2*(num*num1+den*den1)
    rho2 = 2*(num1*num1+num*num2+den1*den1+den*den2)
    a2 = (g2*rho-g1*rho1)/(rho*rho)
    cn = 1+r*r-2*r*mp.cos(x0)
    q = 1+cn-2*p
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -p1/(R*sq)
    u2 = -p2/(R*sq)+p1*p1/(R*q*sq)
    return x2/2+(mu+h)*a2-2*d*(u1*u1+u*u2)-l*u2, dict(q=q, rho=rho, a2=a2, u1=u1, u2=u2)


print('=== Richardson validation of the closed form ===')
for (j, r, b, w) in [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                     (1, mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35')),
                     (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679'))]:
    cl, info = closed_W2(r, b, w, j)
    vals = {}
    for hh in ['1e-2', '5e-3', '2.5e-3']:
        h = mp.mpf(hh)
        vals[hh] = (Wval(r, b, w+h, j)-2*Wval(r, b, w, j)+Wval(r, b, w-h, j))/(h*h)
    rich = (4*vals['2.5e-3']-vals['5e-3'])/3
    print(f'  j={j} r={float(r)} b={float(b)} w={float(w)}  (q={mp.nstr(info["q"],8)})')
    print(f'     closed W\'\' = {mp.nstr(cl,14)}')
    print(f'     FD 2.5e-3   = {mp.nstr(vals["2.5e-3"],14)}')
    print(f'     Richardson  = {mp.nstr(rich,14)}   rel diff = '
          f'{mp.nstr(abs(rich-cl)/max(abs(rich),mp.mpf(1e-30)),4)}')

print()
print('=== the structure c^T H c + g.X, term by term ===')
print('  W\'\'(w) =  x\'\'/2  +  (mu+h) a\'\'  -  2d (u\'^2 + u u\'\')  -  l u\'\'')
print('  with a = atan2(X, Y), X = x, Y = 1-p, rho = X^2+Y^2 = q,')
print('       a\'\' = (X\'\' Y - X Y\'\')/rho - 2 (X Y\' - Y X\') rho\'/rho^2')
print('       u = sqrt(q)/R, q = 1+cn-2p, q\' = -2p\', q\'\' = -2p\'\'')
print('       u\' = -p\'/(R sqrt q),  u\'\' = -p\'\'/(R sqrt q) + p\'^2/(R q^{3/2})')
print()
print('  Key: the a\'\' term carries 1/rho and 1/rho^2 factors, so it dominates when')
print('  q = rho -> 0, which is exactly the regime producing W\'\' > 0.')

print()
print('=== the majorant constants on the stated box ===')
print('  Bounds needed:  |p\'|, |p\'\'|, |x\'|, |x\'\'| <= ...  on')
print('     r in [.379,.37999], b in [acos(r)/2, 1.19], w in [0, Wmax(r,b)] (<= 0.79)')
for j in (0, 1):
    mu, h, d, l = consts(j)
    print(f'  j={j}: mu+h={mp.nstr(mu+h,10)}  2d={mp.nstr(2*d,10)}  l={mp.nstr(l,10)}  '
          f'R={R}')
    print(f'       |mu+h|={mp.nstr(abs(mu+h),10)}  |l|/R={mp.nstr(abs(l)/R,10)}')
print()
print('  with q >= q_min the a\'\' term is bounded by C/q_min^2; hence')
print('     W\'\'(w) <= (|x\'\'|/2 + |mu+h| C_1/q + 2d(u\'^2+|u||u\'\'|) + |l||u\'\'|)')
print('  and a valid quadratic majorant on any w-interval is')
print('     W(w) <= W(w0) + W\'(w0)(w-w0) + (kappa/2)(w-w0)^2 ,  kappa >= sup W\'\'.')
