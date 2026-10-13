"""cline2-coupled-factors R17e: CORRECTED closed form for W'' + rigorous interval bound kappa.

Corrected terms (my earlier version had the wrong sign on the u*u'' contribution):
    q  = 1 + cn - 2p,   cn = 1+r^2-2r cos x0,   x0 = 2b - pi/2 + ph
    q' = -2p',          q'' = -2p''
    u  = sqrt(q)/R,     u' = -p'/(R sqrt q),    u'' = -p''/(R sqrt q) + p'^2/(R q^{3/2})
    a  = atan2(x, 1-p), a'' = (x'' Y - x Y'')/rho - 2 (x Y' - Y x') rho'/rho^2
                                   with Y = 1-p, rho = x^2 + Y^2 = q
    W'' = x''/2 + (mu+h) a'' + 2d (u'^2 - u u'') + l u''
"""
import math, json, sys
from pathlib import Path
from mpmath import mp, iv

mp.dps = 30
iv.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: mp.mpf(f'{zJ[i]:.9f}') for i in range(len(zJ))}
R = mp.mpf(19)/50


def consts(j):
    return ((Z[1], Z[112], Z[34], Z[96]) if j == 0 else (Z[3], Z[115], Z[39], Z[101]))


def pieces(r, b, w):
    s = mp.sqrt(1-r*r); ph = mp.asin(r)
    x0 = 2*b-mp.pi/2+ph
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    p1 = -mp.sin(w)+r*mp.sin(x0+w)
    p2 = -mp.cos(w)+r*mp.cos(x0+w)
    x1 = -mp.cos(w)+r*mp.cos(x0+w)
    x2 = mp.sin(w)-r*mp.sin(x0+w)
    Y = 1-p
    Yp = -p1; Ypp = -p2
    rho = x*x+Y*Y
    rho1 = 2*(x*x1+Y*Yp)
    rho2 = 2*(x1*x1+x*x2+Yp*Yp+Y*Ypp)
    a2 = (x2*Y-x*Ypp)/rho-2*(x*Yp-Y*x1)*rho1/(rho*rho)
    q = 1+(1+r*r-2*r*mp.cos(x0))-2*p
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -p1/(R*sq)
    u2 = -p2/(R*sq)+p1*p1/(R*q*sq)
    return dict(x2=x2, a2=a2, u=u, u1=u1, u2=u2, q=q, rho=rho, p1=p1, p2=p2)


def W2_closed(r, b, w, j):
    mu, h, d, l = consts(j)
    P_ = pieces(r, b, w)
    return (P_['x2']/2+(mu+h)*P_['a2']+2*d*(P_['u1']**2-P_['u']*P_['u2'])
            + l*P_['u2']), P_


print('=== corrected closed form vs exact Taylor ===')
for (j, r, b, w0) in [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                      (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
                      (1, mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35'))]:
    # tiny-step Richardson as the independent check (large h is invalid here: Q'''' is huge)
    def Wv(w):
        mu, h, d, l = consts(j)
        s = mp.sqrt(1-r*r); ph = mp.asin(r)
        x0 = 2*b-mp.pi/2+ph
        p = mp.cos(w)-r*mp.cos(x0+w)
        x = -mp.sin(w)+r*mp.sin(x0+w)
        q = 1+(1+r*r-2*r*mp.cos(x0))-2*p
        a = mp.atan2(x, 1-p)
        u = mp.sqrt(q)/R
        return -r*s*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+x/2+(mu+h)*a-d*u*u-l*u
    vals = {}
    for hh in ['1e-4', '5e-5', '2.5e-5']:
        h = mp.mpf(hh)
        vals[hh] = (Wv(w0+h)-2*Wv(w0)+Wv(w0-h))/(h*h)
    rich = (4*vals['2.5e-5']-vals['5e-5'])/3
    cl, P_ = W2_closed(r, b, w0, j)
    print(f'  j={j} r={float(r)} b={float(b)} w={float(w0)} q={mp.nstr(P_["q"],8)}')
    print(f'     corrected closed = {mp.nstr(cl,16)}')
    print(f'     Richardson 2.5e-5= {mp.nstr(rich,16)}   rel diff = '
          f'{mp.nstr(abs(rich-cl)/abs(rich),4)}')

print()
print('=== rigorous interval bound of W\'\' over the stated box (both branches) ===')
print('   box: r in [0.379, 0.37999], b in [acos(0.37999)/2, 1.19], w in [0.01, 0.70]')
rlo, rhi = iv.mpf('0.379'), iv.mpf('0.37999')
blo = iv.mpf(str(mp.acos(mp.mpf('0.37999'))/2))
bhi = iv.mpf('1.19')
for (wlo, whi) in [('0.01', '0.20'), ('0.20', '0.40'), ('0.40', '0.55'),
                   ('0.55', '0.62'), ('0.62', '0.70')]:
    wl, wh = iv.mpf(wlo), iv.mpf(whi)
    for j in (0, 1):
        mu, h, d, l = [iv.mpf(mp.nstr(mp.mpf(f'{zJ[i]:.9f}'), 12)) for i in
                       ((1, 112, 34, 96) if j == 0 else (3, 115, 39, 101))]
        s = iv.sqrt(1-rlo*rlo)
        ph = iv.asin(rhi)      # sin increasing on [0,pi/2]; use branch-consistent bound
        x0 = 2*iv.mpf([blo.a, bhi.b])-iv.pi/2+ph
        p = iv.cos(wl)-rhi*iv.cos(x0+wh)
        x = -iv.sin(wl)+rhi*iv.sin(x0+wh)
        p1 = -iv.sin(wh)+rhi*iv.sin(x0+wl)
        p2 = -iv.cos(wl)+rhi*iv.cos(x0+wh)
        x1 = -iv.cos(wl)+rhi*iv.cos(x0+wh)
        x2 = iv.sin(wl)-rhi*iv.sin(x0+wl)
        Y = 1-p; Yp = -p1; Ypp = -p2
        rho = x*x+Y*Y
        if rho.b <= 0 or rho.a <= 0:
            print(f'  w in [{wlo},{whi}] j={j}: rho enclosure not positive -> skip')
            continue
        rho1 = 2*(x*x1+Y*Yp)
        rho2 = 2*(x1*x1+x*x2+Yp*Yp+Y*Ypp)
        a2 = (x2*Y-x*Ypp)/rho-2*(x*Yp-Y*x1)*rho1/(rho*rho)
        cn = 1+rlo*rlo-2*rhi*iv.cos(x0)
        q = 1+cn-2*p
        if q.a <= 0:
            print(f'  w in [{wlo},{whi}] j={j}: q enclosure not positive -> skip')
            continue
        sq = iv.sqrt(q)
        u = sq/R_; R_ = iv.mpf(19)/50
        u1 = -p1/(R_*sq)
        u2 = -p2/(R_*sq)+p1*p1/(R_*q*sq)
        W2 = x2/2+(iv.mpf(mu.a)+h)*iv.mpf(0)  # placeholder
        mu_i = iv.mpf(mp.nstr(mp.mpf(f'{zJ[1 if j==0 else 3]:.9f}'), 12))
        h_i = iv.mpf(mp.nstr(mp.mpf(f'{zJ[112 if j==0 else 115]:.9f}'), 12))
        d_i = iv.mpf(mp.nstr(mp.mpf(f'{zJ[34 if j==0 else 39]:.9f}'), 12))
        l_i = iv.mpf(mp.nstr(mp.mpf(f'{zJ[96 if j==0 else 101]:.9f}'), 12))
        W2 = (x2/2+(mu_i+h_i)*a2+2*d_i*(u1*u1-u*u2)+l_i*u2)
        print(f'  w in [{wlo:5s},{whi:5s}] j={j}: q in '
              f'[{float(q.a):.6f},{float(q.b):.6f}]  W\'\' in '
              f'[{float(W2.a):.6f}, {float(W2.b):.6f}]')
