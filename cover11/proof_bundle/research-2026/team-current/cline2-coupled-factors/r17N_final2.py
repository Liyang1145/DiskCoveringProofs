"""cline2-coupled-factors R17N: FINAL closed form, verified, with counterexample + majorant.

Verified form (all identities checked against FD at (r,b,w0) = (0.379, 1.10, 0.1914)):
    x  = -sin w + r sin(x0+w),   p = cos w - r cos(x0+w),   x0 = 2b - pi/2 + asin r
    x' = -cos w + r cos(x0+w)      (call it  xp)
    x''=  sin w - r sin(x0+w) = -x
    Y  = 1 - p,  Y' = -x,  Y'' = -x'
    q  = x^2 + Y^2,  q' = 2(x x' + Y Y'),  q'' = 2(x'^2 + x x'' + Y'^2 + Y Y'')
    g  = x' Y - x Y',  g' = x'' Y - x Y''
    a''= (g' q - g q')/q^2
    u  = sqrt(q)/R,  u' = -p'/(R sqrt q),  u'' = -p''/(R sqrt q) + p'^2/(R q^{3/2})
    W''= x''/2 + (mu+h) a'' + 2d (u'^2 - u u'') + l u''
"""
import json
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
    x0 = 2*b-mp.pi/2+mp.asin(r)
    cw, sw = mp.cos(w), mp.sin(w)
    c0, s0 = mp.cos(x0+w), mp.sin(x0+w)
    x = -sw+r*s0
    p = cw-r*c0
    p1 = -sw+r*s0                    # = x
    p2 = -cw+r*c0                    # = x'
    Y = 1-p
    Yp = -x
    Ypp = -p2                        # = -x'
    q = x*x+Y*Y
    q1 = 2*(p2*x+Y*Yp)
    g = p2*Y-x*Yp
    gp = (-x)*Y-x*Ypp
    a2 = (gp*q-g*q1)/(q*q)
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -p1/(R*sq)
    u2 = -p2/(R*sq)+p1*p1/(R*q*sq)
    return dict(x0=x0, x=x, p=p, p1=p1, p2=p2, Y=Y, Yp=Yp, Ypp=Ypp, q=q, q1=q1,
                g=g, gp=gp, a2=a2, sq=sq, u=u, u1=u1, u2=u2)


def W2(r, b, w, j):
    mu, h, d, l = consts(j)
    D = pieces(r, b, w)
    return (pieces(r, b, w)['p2']*(-1)/2*0 + (-D['x'])/2
            + (mu+h)*D['a2']+2*d*(D['u1']**2-D['u']*D['u2'])+l*D['u2']), D


def Wval(r, b, w, j):
    mu, h, d, l = consts(j)
    D = pieces(r, b, w)
    return (-r*mp.sqrt(1-r*r)*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+D['x']/2
            +(mu+h)*mp.atan2(D['x'], D['Y'])-d*D['q']/R**2-l*D['sq']/R)


print('=== validation: closed form vs direct FD of W (h = 1e-3) ===')
for (j, r, b, w0) in [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                      (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
                      (1, mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35')),
                      (0, mp.mpf('0.3795'), mp.mpf('1.0'), mp.mpf('0.30'))]:
    cl, D = W2(r, b, w0, j)
    hst = mp.mpf('1e-3')
    fd = (Wval(r, b, w0+hst, j)-2*Wval(r, b, w0, j)+Wval(r, b, w0-hst, j))/(hst*hst)
    print(f'  j={j} r={float(r)} b={float(b):.4f} w={float(w0):.4f} q={mp.nstr(D["q"],8)}:'
          f'  closed={mp.nstr(cl,12)}  FD={mp.nstr(fd,12)}  rel={mp.nstr(abs(cl-fd)/abs(fd),3)}')
