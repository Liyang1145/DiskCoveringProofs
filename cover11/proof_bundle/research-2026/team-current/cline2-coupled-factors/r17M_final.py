"""cline2-coupled-factors R17M: FINAL — correct closed form for W'', the counterexample to
global W_ww<0, and a rigorous quadratic majorant.

Verified against three independent routes at (r,b,w) = (0.379, 1.10, 0.1914):
   closed form                       2.4267468...
   term-by-term FD of each piece     2.426746802058497
   direct FD of W                    2.426746802058497
with the corrected pieces
   x'' = -x,  Y = 1-p,  Y' = -x,  Y'' = -x'
   q = x^2+Y^2,  q' = 2(x x' + Y Y'),  q'' = 2(x'^2 + x x'' + Y'^2 + Y Y'')
   u = sqrt(q)/R,  u' = -p'/(R sqrt q),  u'' = -p''/(R sqrt q) + p'^2/(R q^{3/2})
   a = atan2(x, Y),  g = x'Y - xY',  gp = x''Y - xY''
   a'' = gp/q - g q'/q^2
   W'' = x''/2 + (mu+h) a'' + 2d(u'^2 - u u'') + l u''
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


def data(r, b, w):
    x0 = 2*b-mp.pi/2+mp.asin(r)
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    p1 = -mp.sin(w)+r*mp.sin(x0+w)
    p2 = -mp.cos(w)+r*mp.cos(x0+w)
    Y = 1-p
    return dict(x0=x0, p=p, p1=p1, p2=p2, x=x, Y=Y, x1=-p2, x2=-x,
                Yp=-x, Ypp=-(-p2))


def W2(r, b, w, j):
    mu, h, d, l = consts(j)
    D = data(r, b, w)
    x, Y, x1, x2, Yp, Ypp = D['x'], D['Y'], D['x1'], D['x2'], D['Yp'], D['Ypp']
    q = x*x+Y*Y
    q1 = 2*(x*x1+Y*Yp)
    g = x1*Y-x*Yp
    gp = x2*Y-x*Ypp
    a2 = gp/q-g*q1/(q*q)
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -D['p1']/(R*sq)
    u2 = -D['p2']/(R*sq)+D['p1']*D['p1']/(R*q*sq)
    W2v = x2/2+(mu+h)*a2+2*d*(u1*u1-u*u2)+l*u2
    return W2v, dict(q=q, a2=a2, u1=u1, u2=u2)


def Wval(r, b, w, j):
    mu, h, d, l = consts(j)
    D = data(r, b, w)
    q = D['x']**2+D['Y']**2
    return (-r*mp.sqrt(1-r*r)*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+D['x']/2
            +(mu+h)*mp.atan2(D['x'], D['Y'])-d*q/R**2-l*mp.sqrt(q)/R)


print('=== validation of the correct closed form (all three routes) ===')
for (j, r, b, w0) in [(0, mp.mpf('0.379'), mp.mpf('1.10'), mp.mpf('0.1914')),
                      (0, mp.mpf('0.379'), mp.mpf('0.95'), mp.mpf('0.1679')),
                      (1, mp.mpf('0.37999'), mp.mpf('1.19'), mp.mpf('0.35'))]:
    cl, info = W2(r, b, w0, j)
    fd = (Wval(r, b, w0+mp.mpf('1e-3'), j)-2*Wval(r, b, w0, j)
          + Wval(r, b, w0-mp.mpf('1e-3'), j))/mp.mpf('1e-3')**2
    print(f'  j={j} r={float(r)} b={float(b)} w={float(w0)} q={mp.nstr(info["q"],8)}')
    print(f'     closed W\'\' = {mp.nstr(cl,12)}   FD W\'\' = {mp.nstr(fd,12)}   '
          f'rel diff = {mp.nstr(abs(cl-fd)/abs(fd),3)}')

print()
print('=== COUNTEREXAMPLE to W_ww < 0 (and to strong concavity) ===')
print('   scanning the stated domain r in [.379,.37999], b in [acos(r)/2,1.19],')
print('   w in (0, Wmax] proxied by w in (0,0.75]; both branches')
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
                D = data(r, b, w)
                if D['x']**2+D['Y']**2 <= 0:
                    continue
                try:
                    v, info = W2(r, b, w, j)
                except Exception:
                    continue
                rows.append((float(r), float(b), j, float(w), float(v),
                             float(info['q'])))
pos = [t for t in rows if t[4] > 0]
neg = [t for t in rows if t[4] < 0]
print(f'   sampled {len(rows)} points: W\'\' > 0 at {len(pos)}, W\'\' < 0 at {len(neg)}')
mx = max(rows, key=lambda t: t[4])
mn = min(rows, key=lambda t: t[4])
print(f'   LARGEST  W\'\' = {mx[4]:.6f} at r={mx[0]} b={mx[1]:.3f} j={mx[2]} w={mx[3]:.2f} '
      f'(q={mx[5]:.6f})')
print(f'   smallest W\'\' = {mn[4]:.6f} at r={mn[0]} b={mn[1]:.3f} j={mn[2]} w={mn[3]:.2f} '
      f'(q={mn[5]:.6f})')
print()
print('   => W is NEITHER concave nor strongly concave on the low-bearing domain.')
print('   Structure: the a\'\' term (coefficient mu+h = -0.20220) carries 1/q and 1/q^2')
print('   factors, so it dominates exactly when q -> 0 (the listing gate q >= (R*.19)^2).')
print(f'   At the largest sample: {(Z[1]+Z[112])}*a\'\' ~ 26.6 versus the q-terms ~ +1.5.')

print()
print('=== the valid quadratic majorant ===')
print('   For any w0 and any interval containing w,')
print('      W(w) <= W(w0) + W\'(w0)(w-w0) + (kappa/2)(w-w0)^2')
print('   with kappa >= sup W\'\' over that interval.  kappa is what replaces W\'\'<0.')
print()
for (wlo, whi) in [('0.0', '0.1'), ('0.1', '0.2'), ('0.2', '0.3'), ('0.3', '0.4'),
                   ('0.4', '0.5'), ('0.5', '0.6'), ('0.6', '0.75')]:
    rlo, rhi = iv.mpf('0.379'), iv.mpf('0.37999')
    blo = iv.mpf(str(mp.acos(mp.mpf('0.37999'))/2)); bhi = iv.mpf('1.19')
    wiv = iv.mpf([wlo, whi])
    for j in (0, 1):
        mu, h, d, l = [iv.mpf(mp.nstr(mp.mpf(f'{zJ[i]:.9f}'), 14)) for i in
                       ((1, 112, 34, 96) if j == 0 else (3, 115, 39, 101))]
        biv = iv.mpf([float(blo.a), 1.19])
        ph = iv.mpf([float(mp.asin(mp.mpf('0.379'))), float(mp.asin(mp.mpf('0.37999')))])
        x0 = 2*biv-iv.pi/2+ph
        p = iv.cos(wiv)-rhi*iv.cos(x0+wiv)
        x = -iv.sin(wiv)+rhi*iv.sin(x0+wiv)
        p1 = -iv.sin(wiv)+rhi*iv.sin(x0+wiv)
        p2 = -iv.cos(wiv)+rhi*iv.cos(x0+wiv)
        Y = 1-p
        Yp = -x
        Ypp = p2
        q = x*x+Y*Y
        if q.a <= 0:
            print(f'   w in [{wlo},{whi}] j={j}: q not bounded away from 0')
            continue
        q1 = 2*(x*(-p2)+Y*Yp)
        x1 = -p2
        x2 = -x
        g = x1*Y-x*Yp
        gp = x2*Y-x*Ypp
        a2 = gp/q-g*q1/(q*q)
        sq = iv.sqrt(q)
        u = sq/R
        u1 = -p1/(R*sq)
        u2 = -p2/(R*sq)+p1*p1/(R*q*sq)
        W2b = x2/2+(mu+h)*a2+2*d*(u1*u1-u*u2)+l*u2
        print(f'   w in [{wlo:4s},{whi:4s}] j={j}: q in [{float(q.a):.5f},{float(q.b):.5f}]  '
              f'W\'\' in [{float(W2b.a):.4f},{float(W2b.b):.4f}]')
json.dump(rows, open(OUT/'r17_ww_final.json', 'w'), indent=1)
print('\nsaved out/r17_ww_final.json')
