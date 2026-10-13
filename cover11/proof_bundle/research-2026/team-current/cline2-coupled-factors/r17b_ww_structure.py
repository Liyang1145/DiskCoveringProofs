"""cline2-coupled-factors R17b: W_ww structure, exact constants, and the rigorous quadratic
majorant that replaces W_ww < 0.

From lead/joint_boundary_jet.py:
  W = -r s sin^2 b + (1/2 - mu) w + x/2 + (mu+h) eta - d u^2 - l u
  a = atan2(x, den)   (the lead calls it eta; here `a`)
  u = sqrt(q)/R,      q = 1 + cn - 2p,   den = 1 - p
so with prime = d/dw:
  W'' = d/dw[ x'/2 + (mu+h) a' ] - (2 d / R^2) (u u')' ... expanded exactly below:
  u'  = (-p')/(R sqrt q)                       [since q' = -2p']
  u'' = -p''/(R sqrt q) + (p')^2/(R q^{3/2})
  W'' = x''/2 + (mu+h) a'' - 2d(u'^2 + u u'') - l u''
(the -r s sin^2 b term is independent of w; (1/2-mu) w is linear: neither contributes)
"""
import math, json, sys
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: mp.mpf(f'{zJ[i]:.9f}') for i in range(len(zJ))}
R = mp.mpf(19)/50

print('=== exact constants per branch ===')


def consts(j):
    return ((Z[1], Z[112], Z[34], Z[96]) if j == 0 else (Z[3], Z[115], Z[39], Z[101]))


for j in (0, 1):
    mu, h, d, l = consts(j)
    print(f'  j={j}: mu={mp.nstr(mu,10)}  h={mp.nstr(h,10)}  d={mp.nstr(d,10)}  '
          f'l={mp.nstr(l,10)}')
    print(f'        mu+h={mp.nstr(mu+h,10)}   2d/R^2={mp.nstr(2*d/R**2,10)}   '
          f'|l|/R^2={mp.nstr(abs(l)/R**2,10)}')


def geom(r, b, w):
    s = mp.sqrt(1-r*r); ph = mp.asin(r)
    x0 = 2*b-mp.pi/2+ph
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    return s, ph, x0, p, x


def derivs_w(r, b, w):
    """p, x and their first three w-derivatives, plus q, u, a and W'' """
    s, ph, x0, p, x = geom(r, b, w)
    p1 = -mp.sin(w)+r*mp.sin(x0+w)
    p2 = -mp.cos(w)+r*mp.cos(x0+w)
    p3 = mp.sin(w)-r*mp.sin(x0+w)
    x1 = -mp.cos(w)+r*mp.cos(x0+w)
    x2 = mp.sin(w)-r*mp.sin(x0+w)
    x3 = mp.cos(w)-r*mp.cos(x0+w)
    den = 1-p
    num = x
    num1 = x1
    num2 = x2
    num3 = x3
    den1 = -p1; den2 = -p2; den3 = -p3
    # a = atan2(num, den) and successive derivatives via (num' den - num den')
    g1 = (num1*den-num*den1)
    g2 = (num2*den-num*den2)
    g3 = (num3*den-num*den3)
    rho = num*num+den*den
    rho1 = 2*(num*num1+den*den1)
    rho2 = 2*(num1*num1+num*num2+den1*den1+den*den2)
    a1 = g1/rho
    a2 = (g2*rho-g1*rho1)/(rho*rho)
    a3 = ((g3*rho+g2*rho1-g2*rho1-g1*rho2)*rho*rho
          - (g2*rho-g1*rho1)*2*rho*rho1)/(rho**4) if False else None
    # simpler: differentiate a2 = (g2 rho - g1 rho1)/rho^2
    n2 = g2*rho-g1*rho1
    n2p = g3*rho+g2*rho1-g2*rho1-g1*rho2
    a3 = (n2p*rho*rho-n2*2*rho*rho1)/(rho**4)
    cn = 1+r*r-2*r*mp.cos(x0)
    q = 1+cn-2*p
    sq = mp.sqrt(q)
    u = sq/R
    u1 = (-2*p1)/(2*sq)/R
    u2 = -2*p2/(2*sq)/R+2*p1*2*p1/(4*sq**3)/R
    mu, h, d, l = consts(0)
    return dict(p=p, p1=p1, p2=p2, x=x, x1=x1, x2=x2, q=q, sq=sq, u=u, u1=u1, u2=u2,
                a1=a1, a2=a2, a3=a3, den=den, rho=rho)


print()
print('=== verify the closed-form W\'\' against a direct second difference ===')
h_step = mp.mpf('1e-5')
for (j, r, b, w) in [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                     (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
                     (1, mp.mpf('0.3795'), mp.mpf('1.19'), mp.mpf('0.30'))]:
    mu, hh, d, l = consts(j)

    def W(wv):
        s, ph, x0, p, x = geom(r, b, wv)
        cn = 1+r*r-2*r*mp.cos(x0)
        q = 1+cn-2*p
        a = mp.atan2(x, 1-p)
        u = mp.sqrt(q)/R
        return -r*s*mp.sin(b)**2+(mp.mpf(1)/2-mu)*wv+x/2+(mu+hh)*a-d*u*u-l*u
    fd = (W(w+h_step)-2*W(w)+W(w-h_step))/(h_step*h_step)
    D = derivs_w(r, b, w)
    closed = D['x2']/2+(mu+hh)*D['a2']-2*d*(D['u1']**2+D['u']*D['u2'])-l*D['u2']
    print(f'  j={j} r={float(r)} b={float(b)} w={float(w)}: FD={mp.nstr(fd,12)}  '
          f'closed={mp.nstr(closed,12)}  diff={mp.nstr(abs(fd-closed),4)}')

print()
print('=== the sign structure of W\'\': where is it positive? ===')
rows = []
for j in (0, 1):
    mu, hh, d, l = consts(j)
    for rv in ['0.379', '0.3795', '0.37999']:
        r = mp.mpf(rv)
        for bv in ['0.79', '0.85', '0.95', '1.05', '1.19']:
            b = mp.mpf(bv)
            if b < mp.acos(r)/2:
                continue
            for wv in ['0.05', '0.1', '0.15', '0.2', '0.25', '0.3', '0.35']:
                w = mp.mpf(wv)
                D = derivs_w(r, b, w)
                if D['q'] <= 0 or D['den'] <= 0:
                    continue
                W2 = D['x2']/2+(mu+hh)*D['a2']-2*d*(D['u1']**2+D['u']*D['u2'])-l*D['u2']
                # decompose
                qterm = -2*d*D['u1']**2
                qterm2 = -2*d*D['u']*D['u2']-l*D['u2']
                aterm = (mu+hh)*D['a2']
                rows.append((float(r), float(b), j, float(w), float(W2),
                             float(aterm), float(qterm), float(qterm2),
                             float(D['q']), float(D['rho'])))
pos = [t for t in rows if t[4] > 0]
print(f'  {len(rows)} sampled (r,b,j,w); W\'\'>0 at {len(pos)}')
print(f'  largest W\'\': {max(t[4] for t in rows):.6f}   most negative: '
      f'{min(t[4] for t in rows):.6f}')
print()
print(f'{"r":>8s} {"b":>6s} {"j":>2s} {"w":>6s} {"W_ww":>10s} {"a-term":>10s} '
      f'{"-2d u\'^2":>10s} {"q-linear":>10s} {"q":>9s} {"rho":>9s}')
for t in sorted(rows, key=lambda t: -t[4])[:12]:
    print(f'{t[0]:8.5f} {t[1]:6.3f} {t[2]:2d} {t[3]:6.3f} {t[4]:10.5f} {t[5]:10.5f} '
          f'{t[6]:10.5f} {t[7]:10.5f} {t[8]:9.6f} {t[9]:9.6f}')
json.dump(rows, open(OUT/'r17_ww_table.json', 'w'), indent=1)
print('\nsaved out/r17_ww_table.json')
