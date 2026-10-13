"""cline2-coupled-factors R17f: settle a'' and W'' cleanly, then the rigorous sup bound.

a = atan2(x, Y), Y = 1-p, rho = x^2+Y^2 = q.  With primes = d/dw:
    a'  = (x' Y - x Y')/rho
    a'' = (x'' Y - x Y'')/rho - 2 (x' Y - x Y')(x x' + Y Y')/rho^2
(no other conventions).  Verified against a high-precision Taylor extraction of a alone.
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


def data(r, b, w):
    s = mp.sqrt(1-r*r); ph = mp.asin(r)
    x0 = 2*b-mp.pi/2+ph
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    p1 = -mp.sin(w)+r*mp.sin(x0+w)
    p2 = -mp.cos(w)+r*mp.cos(x0+w)
    x1 = -mp.cos(w)+r*mp.cos(x0+w)
    x2 = mp.sin(w)-r*mp.sin(x0+w)
    return dict(s=s, x0=x0, p=p, x=x, p1=p1, p2=p2, x1=x1, x2=x2,
                Y=1-p, Yp=-p1, Ypp=-p2)


def a2_formula(d):
    x, Y = d['x'], d['Y']
    rho = x*x+Y*Y
    num = d['x2']*Y-x*d['Ypp']
    cross = d['x1']*Y-x*d['Yp']
    rho1 = 2*(x*d['x1']+Y*d['Yp'])
    return num/rho-2*cross*rho1/(rho*rho), rho, num, cross, rho1


print('=== a\'\' : closed formula vs Taylor extraction of a alone ===')
for (r, b, w0) in [(mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                   (mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
                   (mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35'))]:
    d = data(r, b, w0)
    cl, rho, num, cross, rho1 = a2_formula(d)
    # Taylor of a alone, small step
    def af(wv):
        dd = data(r, b, wv)
        return mp.atan2(dd['x'], dd['Y'])
    best = None
    for hh in ['1e-2', '5e-3', '2.5e-3']:
        h = mp.mpf(hh)
        v = (af(w0+h)-2*af(w0)+af(w0-h))/(h*h)
        if best is None:
            best = (vv := {}) or {}
        best[hh] = v
    rich = (4*best['2.5e-3']-best['5e-3'])/3
    print(f'  r={float(r)} b={float(b)} w={float(w0)} q=rho={mp.nstr(rho,10)}')
    print(f'     closed a\'\' = {mp.nstr(cl,16)}')
    print(f'     Taylor a\'\' = {mp.nstr(rich,16)}      rel diff = '
          f'{mp.nstr(abs(rich-cl)/abs(rich),4)}')
    print(f'     pieces: num={mp.nstr(num,12)} cross={mp.nstr(cross,12)} '
          f'rho1={mp.nstr(rho1,12)}')

print()
print('=== W\'\' : closed form with the settled a\'\' ===')
print('   W = -r s sin^2 b + (1/2-mu)w + x/2 + (mu+h)a - d u^2 - l u,  u = sqrt(q)/R')
print('   u\' = -p\'/(R sqrt q);   u\'\' = -p\'\'/(R sqrt q) + p\'^2/(R q^{3/2})')
print('   W\'\' = x\'\'/2 + (mu+h)a\'\' - 2d(u\'^2 + u u\'\') - l u\'\'')


def W2(r, b, w, j):
    mu, h, d, l = consts(j)
    dd = data(r, b, w)
    a2, rho, _, _, _ = a2_formula(dd)
    q = rho
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -dd['p1']/(R*sq)
    u2 = -dd['p2']/(R*sq)+dd['p1']*dd['p1']/(R*q*sq)
    return dd['x2']/2+(mu+h)*a2-2*d*(u1*u1+u*u2)-l*u2, dict(sq=sq, u=u, u1=u1, u2=u2,
                                                            a2=a2, q=q)


for (j, r, b, w0) in [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                      (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
                      (1, mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35'))]:
    cl, info = W2(r, b, w0, j)

    def Wv(w):
        mu, h, d, l = consts(j)
        dd = data(r, b, w)
        q = dd['x']*dd['x']+dd['Y']*dd['Y']
        a = mp.atan2(dd['x'], dd['Y'])
        u = mp.sqrt(q)/R
        return -r*dd['s']*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+dd['x']/2+(mu+h)*a-d*u*u-l*u
    vs = {}
    for hh in ['1e-4', '5e-5', '2.5e-5']:
        h = mp.mpf(hh)
        vs[hh] = (Wv(w0+h)-2*Wv(w0)+Wv(w0-h))/(h*h)
    rich = (4*vs['2.5e-5']-vs['5e-5'])/3
    print(f'  j={j} r={float(r)} b={float(b)} w={float(w0)}: closed W\'\'={mp.nstr(cl,16)}  '
          f'Richardson={mp.nstr(rich,16)}  rel diff={mp.nstr(abs(rich-cl)/abs(rich),4)}')
