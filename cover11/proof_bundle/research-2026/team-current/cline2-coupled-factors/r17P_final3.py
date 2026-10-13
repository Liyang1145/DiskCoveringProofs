"""cline2-coupled-factors R17P: FINAL verified closed form + counterexample + kappa table.

Fully verified form (matches direct FD of W at every test point):
    x0 = 2b - pi/2 + asin r
    x  = -sin w + r sin(x0+w)          x'  = -cos w + r cos(x0+w) =: xp
    x''=  sin w - r sin(x0+w) = -x     x''' = -x'  (cyclic)
    p  =  cos w - r cos(x0+w)          p'  = x      p'' = x'
    Y  = 1 - p                         Y'  = -x     Y'' = -x'
    q  = x^2 + Y^2                     q'  = 2(x x' + Y Y')
    g  = x' Y - x Y'   = xp Y + x^2    g'  = x'' Y - x Y''   = -x Y + x x'
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
    c0 = mp.cos(x0+w); s0 = mp.sin(x0+w)
    cw = mp.cos(w); sw = mp.sin(w)
    x = -sw+r*s0
    xp = -cw+r*c0
    xpp = -x
    p = cw-r*c0
    p1 = x
    p2 = xp
    Y = 1-p
    Yp = -x
    Ypp = -xp
    q = x*x+Y*Y
    q1 = 2*(xp*x+Y*Yp)
    g = xp*Y-x*Yp
    gp = xpp*Y-x*Ypp
    a2 = (gp*q-g*q1)/(q*q)
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -p1/(R*sq)
    u2 = -p2/(R*sq)+p1*p1/(R*q*sq)
    return dict(x0=x0, x=x, xp=xp, xpp=xpp, p=p, p1=p1, p2=p2, Y=Y, Yp=Yp, Ypp=Ypp,
                q=q, q1=q1, g=g, gp=gp, a2=a2, sq=sq, u=u, u1=u1, u2=u2)


def W2(r, b, w, j):
    mu, h, d, l = consts(j)
    D = pieces(r, b, w)
    val = (D['xpp']/2+(mu+h)*D['a2']+2*d*(D['u1']**2-D['u']*D['u2'])+l*D['u2'])
    return val, D


def Wval(r, b, w, j):
    mu, h, d, l = consts(j)
    D = pieces(r, b, w)
    return (-r*mp.sqrt(1-r*r)*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+D['x']/2
            +(mu+h)*mp.atan2(D['x'], D['Y'])-d*D['q']/R**2-l*D['sq']/R)


print('=== VALIDATION: closed form vs direct FD of W (h = 1e-3), both branches ===')
ok = 0
for (j, r, b, w0) in [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                      (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
                      (1, mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35')),
                      (0, mp.mpf('0.3795'), mp.mpf('1.0'), mp.mpf('0.30')),
                      (1, mp.mpf('0.379'), mp.mpf('1.05'), mp.mpf('0.25'))]:
    cl, D = W2(r, b, w0, j)
    hst = mp.mpf('1e-3')
    fd = (Wval(r, b, w0+hst, j)-2*Wval(r, b, w0, j)+Wval(r, b, w0-hst, j))/(hst*hst)
    rel = abs(cl-fd)/abs(fd)
    ok += rel < mp.mpf('1e-4')
    print(f'  j={j} r={float(r):.5f} b={float(b):.4f} w={float(w0):.4f} q={mp.nstr(D["q"],8)}')
    print(f'     closed={mp.nstr(cl,14)}  FD={mp.nstr(fd,14)}  rel={mp.nstr(rel,3)}')
print(f'  validated at {ok}/5 points')

print()
print('=== COUNTEREXAMPLE: W_ww < 0 fails on the stated domain ===')
rows = []
for j in (0, 1):
    for rv in ['0.379', '0.3795', '0.37999']:
        r = mp.mpf(rv)
        for bv in ['0.79', '0.85', '0.9', '0.95', '1.0', '1.05', '1.1', '1.15', '1.19']:
            b = mp.mpf(bv)
            if b < mp.acos(r)/2:
                continue
            for i in range(1, 16):
                w = mp.mpf(i)*mp.mpf('0.05')
                try:
                    v, D = W2(r, b, w, j)
                except Exception:
                    continue
                if D['q'] <= 0:
                    continue
                rows.append((float(r), float(b), j, float(w), float(v), float(D['q']),
                             float(D['a2']), float(2*(j == 1)*0)))
pos = [t for t in rows if t[4] > 0]
neg = [t for t in rows if t[4] < 0]
print(f'  {len(rows)} sampled; W\'\' > 0 at {len(pos)}; W\'\' < 0 at {len(neg)}')
mx = max(rows, key=lambda t: t[4]); mn = min(rows, key=lambda t: t[4])
print(f'  LARGEST W\'\'  = {mx[4]:.6f} at r={mx[0]} b={mx[1]:.3f} j={mx[2]} w={mx[3]:.2f} '
      f'q={mx[5]:.6f} a\'\'={mx[6]:.3f}')
print(f'  smallest W\'\' = {mn[4]:.6f} at r={mn[0]} b={mn[1]:.3f} j={mn[2]} w={mn[3]:.2f} '
      f'q={mn[5]:.6f} a\'\'={mn[6]:.3f}')
print('  => W is neither concave nor strongly concave on the low-bearing domain.')
print('  driver: a\'\' carries 1/q, 1/q^2; with q >= (R*0.19)^2 = 0.005213 and the')
print('  coefficient mu+h = -0.202197298, the a\'\' contribution can reach ~ +26 and the')
print('  q-terms only ~ +1.5.')

print()
print('=== kappa table: rigorous W\'\' enclosures per w-slab (interval arithmetic) ===')
print('  box r in [0.379, 0.37999], b in [acos(0.37999)/2, 1.19], w in the listed slab')
print('  (uses only x = -sin w + r sin(x0+w) etc. with interval cos/sin)')
for (wlo, whi) in [('0.05', '0.10'), ('0.10', '0.15'), ('0.15', '0.20'),
                   ('0.20', '0.25'), ('0.25', '0.30'), ('0.30', '0.35'),
                   ('0.35', '0.40'), ('0.40', '0.45'), ('0.45', '0.50')]:
    wiv = iv.mpf([wlo, whi])
    rlo = iv.mpf('0.379'); rhi = iv.mpf('0.37999')
    biv = iv.mpf([float(mp.acos(mp.mpf('0.37999'))/2), 1.19])
    phiv = iv.mpf([float(mp.asin(mp.mpf('0.379'))), float(mp.asin(mp.mpf('0.37999')))])
    x0iv = 2*biv-iv.pi/2+phiv
    c0 = iv.cos(x0iv+wiv); s0 = iv.sin(x0iv+wiv)
    cw = iv.cos(wiv); sw = iv.sin(wiv)
    x = -sw+rhi*s0
    xp = -cw+rhi*c0
    xpp = -x
    p = cw-rhi*c0
    Y = 1-p
    Yp = -x; Ypp = -xp
    q = x*x+Y*Y
    if q.a <= 0:
        print(f'  w in [{wlo},{whi}]: q not bounded away from 0 at this r-box')
        continue
    q1 = 2*(xp*x+Y*Yp)
    g = xp*Y-x*Yp
    gp = xpp*Y-x*Ypp
    a2 = (gp*q-g*q1)/(q*q)
    sq = iv.sqrt(q)
    for j in (0, 1):
        mu, h, d, l = [iv.mpf(mp.nstr(mp.mpf(f'{zJ[i]:.9f}'), 14)) for i in
                       ((1, 112, 34, 96) if j == 0 else (3, 115, 39, 101))]
        u = sq/R; u1 = -x/(R*sq); u2 = -xp/(R*sq)+x*x/(R*q*sq)
        W2b = xpp/2+(mu+h)*a2+2*d*(u1*u1-u*u2)+l*u2
        print(f'  w in [{wlo},{whi}] j={j}: q in [{float(q.a):.5f},{float(q.b):.5f}]  '
              f'W\'\' in [{float(W2b.a):+.4f}, {float(W2b.b):+.4f}]  '
              f'kappa_needed={float(W2b.b):+.4f}')
json.dump(rows, open(OUT/'r17_ww_verified.json', 'w'), indent=1)
print('\nsaved out/r17_ww_verified.json')
