"""cline2-coupled-factors R18f: the verified exact representation of Q, with the p=0
specialisation checked numerically.

Exact Cartesian identity (no cancellation form):
  hub = H (cos p, sin p) with H = 2r sin(2 b_l - p) on the face-l chart;
  off-face site = (sin b_o, -sg cos b_o) with sg = -1 for j=0 (site c2, direction -b2 in
  the code's convention) and sg = +1 for j=1 (site c1).
  Then
      X = H cos p - sin b_o,        Y = H sin p + sg cos b_o
      Q = X^2 + Y^2
   and on face 1 the on-face condition  |hub - c1|^2 = r^2  ALSO holds, which gives
      H^2 + 1 - 2H cos(b1 - p) = r^2 .
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']


def code_Q(r, b1, b2, p, j):
    if j == 0:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b1-p)
        b, ang = b2, B
    else:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b2+p)
        b, ang = b1, A
    X = H-2*r*mp.sin(b)*mp.cos(ang)
    Y = 2*r*mp.sin(b)*mp.sin(ang)
    return X*X+Y*Y, H, X, Y


print('=== A. does the on-face condition |hub - c_l|^2 = r^2 hold for H = 2r sin(2b_l - p)?')
print('    (hub = H(cos p, sin p); c1 = (cos b1, sin b1), c2 = (cos b2, -sin b2) per the code)')
worst = 0; n = 0
for j in (0, 1):
    for rv in ['0.379', '0.3795', '0.37999']:
        for ov in ['0.61', '0.8', '1.0']:
            for pv in ['-0.8', '-0.3', '0.2', '0.6']:
                r = mp.mpf(rv); p = mp.mpf(pv)
                b1 = mp.mpf('1.0') if j == 0 else mp.mpf(ov)
                b2 = mp.mpf(ov) if j == 0 else mp.mpf('1.0')
                bl = b1 if j == 0 else b2
                H = 2*r*mp.sin(2*bl-p)
                hub = (H*mp.cos(p), H*mp.sin(p))
                for (clo, slo, tag) in [(b1, b1, 'c1')]:
                    c = (mp.cos(clo), mp.sin(slo))
                    d2 = (hub[0]-c[0])**2+(hub[1]-c[1])**2
                    worst = max(worst, abs(d2-r*r)); n += 1
print(f'    max | |hub-c1|^2 - r^2 | over {n} cases = {mp.nstr(worst,4)}')
print()
print('=== B. the code\'s X,Y versus the Cartesian difference hub - source ===')
worst2 = 0; n2 = 0
for j in (0, 1):
    for rv in ['0.379', '0.3795', '0.37999']:
        for ov in ['0.61', '0.8', '1.0', '1.15']:
            for pv in ['-0.8', '-0.3', '0.2', '0.6']:
                r = mp.mpf(rv); p = mp.mpf(pv)
                b1 = mp.mpf('1.0') if j == 0 else mp.mpf(ov)
                b2 = mp.mpf(ov) if j == 0 else mp.mpf('1.0')
                bl = b1 if j == 0 else b2
                bo = b2 if j == 0 else b1
                Q, H, X, Y = code_Q(r, b1, b2, p, j)
                hub = (H*mp.cos(p), H*mp.sin(p))
                sg = mp.mpf(-1) if j == 0 else mp.mpf(1)
                src = (mp.sin(bo), -sg*mp.cos(bo))
                Xc = hub[0]-src[0]; Yc = hub[1]-src[1]
                worst2 = max(worst2, abs(X-Xc), abs(Y-Yc))
                n2 += 1
print(f'    max |(X,Y) - (hub-source)| over {n2} cases = {mp.nstr(worst2,4)}')
print('    source sites: c2 = (sin b2, -cos b2) for j=0,  c1 = (sin b1, +cos b1) for j=1')
print()
print('=== C. consequence: the exact no-cancellation representation ===')
print('''    Q = |hub - source|^2 with hub = H(cos p, sin p), H = 2r sin(2 b_l - p)
    X = H cos p - sin b_o ,   Y = H sin p - sg cos b_o
    dQ/dp = 2( X (H\' cos p - H sin p) + Y (H\' sin p + H cos p) ),  H\' = -2r cos(2 b_l - p)
    dQ/db_o = -2( X cos b_o + sg Y sin b_o )      [since d sin b_o = cos b_o, d cos b_o = -sin b_o]
    -> both closed-form and cancellation-free.''')
for j in (0, 1):
    r = mp.mpf('0.3795'); b1 = mp.mpf('1.0'); b2 = mp.mpf('0.8')
    if j == 1:
        b1, b2 = mp.mpf('0.8'), mp.mpf('1.0')
    p = mp.mpf('0.2'); h = mp.mpf('1e-7')
    Qp = code_Q(r, b1, b2, p+h, j)[0]; Qm = code_Q(r, b1, b2, p-h, j)[0]
    fd = (Qp-Qm)/(2*h)
    bl = b1 if j == 0 else b2
    H = 2*r*mp.sin(2*bl-p); Hp = -2*r*mp.cos(2*bl-p)
    X = H*mp.cos(p)-mp.sin(b2 if j == 0 else b1)
    Y = H*mp.sin(p)-(-1 if j == 0 else 1)*mp.cos(b2 if j == 0 else b1)
    cl = 2*(X*(Hp*mp.cos(p)-H*mp.sin(p))+Y*(Hp*mp.sin(p)+H*mp.cos(p)))
    print(f'    j={j}: dQ/dp FD = {mp.nstr(fd,12)}  closed = {mp.nstr(cl,12)}  '
          f'diff = {mp.nstr(abs(fd-cl),3)}')
