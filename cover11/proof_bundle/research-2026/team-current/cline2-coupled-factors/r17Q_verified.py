"""cline2-coupled-factors R17Q: FINAL, written directly from the verified identities.

Lead's width function (lead/joint_boundary_jet.py:7-14):
    x0 = 2b - pi/2 + asin r
    p  = cos w - r cos(x0+w)        p' = x        p'' = x'
    x  = -sin w + r sin(x0+w)       x' = xp       x'' = -x
    cn = 1 + r^2 - 2r cos x0        q  = 1 + cn - 2p = x^2 + (1-p)^2
    u  = sqrt(q)/R                  a = atan2(x, 1-p)
    W  = -r sqrt(1-r^2) sin^2 b + (1/2 - mu) w + x/2 + (mu+h) a - d u^2 - l u

Constants (9-decimal frozen z): j=0 (z1,z112,z34,z96), j=1 (z3,z115,z39,z101).
Deriving W'' with the identities above (Y := 1-p, Y' = -x, Y'' = -x'):
    q'  = -2p' = -2x ;  q'' = -2p'' = -2x'      [because q = 1+cn-2p]
    u'  = -p'/(R sqrt q) = -x/(R sqrt q)
    u'' = -p''/(R sqrt q) + p'^2/(R q^{3/2}) = -x'/(R sqrt q) + x^2/(R q^{3/2})
    a'  = (x'Y - xY')/q = (x'Y + x^2)/q
    a'' = (x''Y - xY'')/q - (x'Y - xY') q'/q^2
    W'' = x''/2 + (mu+h) a'' - 2d (u'^2 + u u'') - l u''
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: mp.mpf(f'{zJ[i]:.9f}') for i in range(len(zJ))}
R = mp.mpf(19)/50


def consts(j):
    return ((Z[1], Z[112], Z[34], Z[96]) if j == 0 else (Z[3], Z[115], Z[39], Z[101]))


def Wval(r, b, w, j):
    mu, h, d, l = consts(j)
    s = mp.sqrt(1-r*r)
    x0 = 2*b-mp.pi/2+mp.asin(r)
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    q = 1+(1+r*r-2*r*mp.cos(x0))-2*p
    a = mp.atan2(x, 1-p)
    u = mp.sqrt(q)/R
    return -r*s*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+x/2+(mu+h)*a-d*u*u-l*u


def W2(r, b, w, j):
    mu, h, d, l = consts(j)
    x0 = 2*b-mp.pi/2+mp.asin(r)
    c0 = mp.cos(x0+w); s0 = mp.sin(x0+w)
    cw = mp.cos(w); sw = mp.sin(w)
    p = cw-r*c0
    x = -sw+r*s0
    xp = -cw+r*c0                 # x'
    xpp = -x                      # x''
    pp = xp                       # p''
    p1 = x                        # p'
    Y = 1-p
    q = 1+(1+r*r-2*r*c0*0+0)-2*p
    q = x*x+Y*Y
    q1 = -2*p1                    # q' = -2p'
    q2 = -2*pp                    # q'' = -2p''
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -p1/(R*sq)
    u2 = -pp/(R*sq)-p1*p1/(R*q*sq)
    g = xp*Y-x*(-x)               # x'Y - xY'  with Y'=-x
    gp = xpp*Y-x*(-xp)            # x''Y - xY'' with Y''=-x'
    a2 = gp/q-g*q1/(q*q)
    val = xpp/2+(mu+h)*a2-2*d*(u1*u1+u*u2)-l*u2
    return val, dict(q=q, q1=q1, q2=q2, u=u, u1=u1, u2=u2, a2=a2, x=x, xp=xp, xpp=xpp,
                     p=p, p1=p1, pp=pp, Y=Y, g=g, gp=gp)


def check(r, b, w0, j, h):
    cl, D = W2(r, b, w0, j)
    fd = (Wval(r, b, w0+h, j)-2*Wval(r, b, w0, j)+Wval(r, b, w0-h, j))/(h*h)
    return cl, fd, D


print('=== VALIDATION, three independent routes at (0.379, 1.10, 0.1914) ===')
r, b, w0 = mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')
cl, fd, D = check(r, b, w0, 0, mp.mpf('1e-3'))
print(f'   closed form        = {mp.nstr(cl,16)}')
print(f'   direct FD of W     = {mp.nstr(fd,16)}')
print(f'   piecewise FD route = 2.426746802058497  (r17L2, each term differenced alone)')
print(f'   pieces: q={mp.nstr(D["q"],10)} q\'={mp.nstr(D["q1"],10)} q\'\'={mp.nstr(D["q2"],10)}')
print(f'           u\'={mp.nstr(D["u1"],10)} u\'\'={mp.nstr(D["u2"],10)} a\'\'={mp.nstr(D["a2"],10)}')
print()
print('=== VALIDATION over a spread of points (both branches) ===')
good = 0
tot = 0
for (j, rv, bv, wv) in [(0, '0.379', '1.10', '0.1914'), (0, '0.379', '0.95', '0.1679'),
                        (1, '0.37999', '1.19', '0.35'), (0, '0.3795', '1.00', '0.30'),
                        (1, '0.379', '1.05', '0.25'), (0, '0.37999', '0.90', '0.40'),
                        (1, '0.3795', '1.10', '0.20')]:
    r, b, w0 = mp.mpf(rv), mp.mpf(bv), mp.mpf(wv)
    cl, fd, D = check(r, b, w0, j, mp.mpf('1e-3'))
    rel = abs(cl-fd)/abs(fd)
    tot += 1
    if rel < mp.mpf('5e-6'):
        good += 1
    print(f'  j={j} r={rv} b={bv} w={wv}: closed={mp.nstr(cl,12)} FD={mp.nstr(fd,12)} '
          f'rel={mp.nstr(rel,3)}')
print(f'  validated {good}/{tot}')
