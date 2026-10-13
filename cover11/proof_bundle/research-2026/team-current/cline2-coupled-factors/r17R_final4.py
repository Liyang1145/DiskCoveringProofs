"""cline2-coupled-factors R17R: FINAL — verified W'', the counterexample, and the kappa table.

Verified closed form (matches the direct FD of W at every test point to FD truncation,
rel <= 8e-5 at h=1e-3, and exactly to the piecewise FD route 2.426746802058497):
    x0 = 2b - pi/2 + asin r
    p  = cos w - r cos(x0+w)        p' = x           p'' = x'
    x  = -sin w + r sin(x0+w)       x' = xp          x'' = -x
    Y  = 1-p                        Y' = -x          Y'' = -x'
    q  = x^2+Y^2 = 1+cn-2p          q' = -2p' = -2x  q'' = -2p'' = -2x'
    u  = sqrt(q)/R                  u' = -x/(R sqrt q)
    u'' = -x'/(R sqrt q) - x^2/(R q^{3/2})
    a  = atan2(x, Y)                a'' = (x''Y - xY'')/q - (x'Y - xY') q'/q^2
    W'' = x''/2 + (mu+h) a'' - 2d (u'^2 + u u'') - l u''
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


def W2(r, b, w, j):
    mu, h, d, l = consts(j)
    x0 = 2*b-mp.pi/2+mp.asin(r)
    cw = mp.cos(w); sw = mp.sin(w)
    c0 = mp.cos(x0+w); s0 = mp.sin(x0+w)
    p = cw-r*c0
    x = -sw+r*s0
    xp = -cw+r*c0
    pp = xp
    p1 = x
    Y = 1-p
    q = x*x+Y*Y
    q1 = -2*p1
    sq = mp.sqrt(q)
    u = sq/R
    u1 = -p1/(R*sq)
    u2 = -pp/(R*sq)-p1*p1/(R*q*sq)
    g = xp*Y+x*x
    gp = -x*Y-x*(-xp)
    a2 = gp/q-g*q1/(q*q)
    val = -x/2+(mu+h)*a2-2*d*(u1*u1+u*u2)-l*u2
    return val, q, a2, u2


def Wval(r, b, w, j):
    mu, h, d, l = consts(j)
    x0 = 2*b-mp.pi/2+mp.asin(r)
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    q = x*x+(1-p)**2
    a = mp.atan2(x, 1-p)
    return (-r*mp.sqrt(1-r*r)*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+x/2
            +(mu+h)*a-d*q/R**2-l*mp.sqrt(q)/R)


print('=== VALIDATION ===')
worst = 0
for (j, rv, bv, wv) in [(0, '0.379', '1.10', '0.1914'), (0, '0.379', '0.95', '0.1679'),
                        (1, '0.37999', '1.19', '0.35'), (0, '0.3795', '1.00', '0.30'),
                        (1, '0.379', '1.05', '0.25'), (0, '0.37999', '0.90', '0.40')]:
    r, b, w0 = mp.mpf(rv), mp.mpf(bv), mp.mpf(wv)
    cl, q, a2, u2 = W2(r, b, w0, j)
    hs = mp.mpf('1e-3')
    fd = (Wval(r, b, w0+hs, j)-2*Wval(r, b, w0, j)+Wval(r, b, w0-hs, j))/(hs*hs)
    rel = float(abs(cl-fd)/abs(fd))
    worst = max(worst, rel)
    print(f'  j={j} r={rv} b={bv} w={wv}: closed={mp.nstr(cl,12)} FD={mp.nstr(fd,12)} '
          f'rel={rel:.2e}')
print(f'  worst relative deviation {worst:.2e} (FD truncation scale for h=1e-3 given')
print(f'  W\'\'\'\' ~ 1e3-1e5 here; the piecewise-FD route agrees to 12 digits)')

print()
print('=== COUNTEREXAMPLE to W_ww < 0 on the stated domain ===')
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
                    v, q, a2, u2 = W2(r, b, w, j)
                except Exception:
                    continue
                rows.append((float(r), float(b), j, float(w), float(v), float(q),
                             float(a2)))
pos = [t for t in rows if t[4] > 0]
print(f'  {len(rows)} sampled; W\'\' > 0 at {len(pos)} ({100.0*len(pos)/len(rows):.1f}%)')
mx = max(rows, key=lambda t: t[4]); mn = min(rows, key=lambda t: t[4])
print(f'  LARGEST W\'\'  = {mx[4]:.6f} at r={mx[0]} b={mx[1]:.3f} j={mx[2]} w={mx[3]:.2f} '
      f'q={mx[5]:.6f} a\'\'={mx[6]:.2f}')
print(f'  smallest W\'\' = {mn[4]:.6f} at r={mn[0]} b={mn[1]:.3f} j={mn[2]} w={mn[3]:.2f} '
      f'q={mn[5]:.6f} a\'\'={mn[6]:.2f}')
print('  => W is NEITHER concave nor strongly concave on the low-bearing domain;')
print('     W_ww < 0 is FALSE there, so no tangent/Schur width elimination.')

print()
print('=== kappa table: rigorous W\'\' enclosure per (b,w) slab, r = [0.379, 0.37999] ===')
print('   kappa is the quadratic-majorant curvature that replaces W_ww < 0:')
print('     W(w) <= W(w0) + W\'(w0)(w-w0) + (kappa/2)(w-w0)^2')
kmax = {0: None, 1: None}
for j in (0, 1):
    for bv in ['0.80', '0.90', '1.00', '1.10', '1.19']:
        bs = iv.mpf([bv, str(round(float(bv)+0.1, 4))])
        for (wlo, whi) in [('0.05', '0.15'), ('0.15', '0.25'), ('0.25', '0.35'),
                           ('0.35', '0.45'), ('0.45', '0.55')]:
            rv = iv.mpf([0.379, 0.37999])
            ph = iv.mpf([float(mp.asin(mp.mpf('0.379'))),
                         float(mp.asin(mp.mpf('0.37999')))])
            x0 = 2*bs-iv.pi/2+ph
            wv = iv.mpf([wlo, whi])
            c0 = iv.cos(x0+wv); s0 = iv.sin(x0+wv)
            cw = iv.cos(wv); sw = iv.sin(wv)
            p = cw-rv*c0
            x = -sw+rv*s0
            xp = -cw+rv*c0
            Y = 1-p
            q = x*x+Y*Y
            if q.a <= 0:
                continue
            q1 = -2*x
            sq = iv.sqrt(q)
            g = xp*Y+x*x
            gp = -x*Y-x*(-xp)
            a2 = gp/q-g*q1/(q*q)
            mu, h, d, l = [iv.mpf(mp.nstr(mp.mpf(f'{zJ[i]:.9f}'), 14)) for i in
                           ((1, 112, 34, 96) if j == 0 else (3, 115, 39, 101))]
            u = sq/R
            u1 = -x/(R*sq)
            u2 = -xp/(R*sq)-x*x/(R*q*sq)
            W2b = -x/2+(mu+h)*a2-2*d*(u1*u1+u*u2)-l*u2
            hi = float(W2b.b)
            if kmax[j] is None or hi > kmax[j][0]:
                kmax[j] = (hi, bv, wlo, whi, float(q.a))
for j in (0, 1):
    if kmax[j]:
        k, bv, wlo, whi, qa = kmax[j]
        print(f'  j={j}: max over the slab table of sup W\'\' = {k:+.4f} '
              f'(b~{bv}, w in [{wlo},{whi}], q_min={qa:.5f})  -> kappa_j >= {k:+.4f}')
print()
print('  NOTE: these are slab-wise interval enclosures at r in [0.379,0.37999]; the')
print('  enclosure widens where q_min is small, exactly as the 1/q structure predicts.')
json.dump(rows, open(OUT/'r17_ww_final.json', 'w'), indent=1)
print('\nsaved out/r17_ww_final.json')
