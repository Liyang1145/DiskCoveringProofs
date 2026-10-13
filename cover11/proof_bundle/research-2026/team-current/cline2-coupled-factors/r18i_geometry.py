"""cline2-coupled-factors R18i: pin the hub geometry empirically.
For the code's hub data (X,Y,H) on face chart j, test which of the natural points the hub
is equidistant-r from, and what Q measures.
"""
import json
from pathlib import Path
from mpmath import mp

mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']


def code(r, b1, b2, p, j):
    if j == 0:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b1-p); b, ang = b2, B
    else:
        A = b1-p; B = b2+p; H = 2*r*mp.sin(2*b2+p); b, ang = b1, A
    X = H-2*r*mp.sin(b)*mp.cos(ang)
    Y = 2*r*mp.sin(b)*mp.sin(ang)
    return dict(X=X, Y=Y, Q=X*X+Y*Y, H=H, b=b, ang=ang, A=A, B=B)


print('=== which polar point is the hub, and what is it r-away from? ===')
print('   Testing: for hub = H(cos p, sin p) and hub = (-H sin p, H cos p),')
print('   distances to c1 = (cos b1, sin b1) and c2 = (cos b2, -sin b2).')
r = mp.mpf('0.3795')
for (b1v, b2v, pv, j) in [('1.0', '0.8', '0.2', 0), ('0.8', '1.0', '0.2', 1),
                          ('1.0', '0.8', '-0.5', 0), ('1.15', '0.65', '0.4', 0)]:
    b1 = mp.mpf(b1v); b2 = mp.mpf(b2v); p = mp.mpf(pv)
    D = code(r, b1, b2, p, j)
    H = D['H']
    c1 = (mp.cos(b1), mp.sin(b1)); c2 = (mp.cos(b2), -mp.sin(b2))
    print(f'  j={j} b1={b1v} b2={b2v} p={pv}: H={mp.nstr(H,10)}')
    for tag, hub in [('H(cos p, sin p)', (H*mp.cos(p), H*mp.sin(p))),
                     ('(-H sin p, H cos p)', (-H*mp.sin(p), H*mp.cos(p))),
                     ('(H cos(b1-p), H sin(b1-p))',
                      (H*mp.cos(b1-p), H*mp.sin(b1-p)))]:
        d1 = mp.sqrt((hub[0]-c1[0])**2+(hub[1]-c1[1])**2)
        d2 = mp.sqrt((hub[0]-c2[0])**2+(hub[1]-c2[1])**2)
        print(f'     hub={tag:26s}: |hub-c1|-r={mp.nstr(d1-r,6)}  |hub-c2|-r={mp.nstr(d2-r,6)}')
    print(f'     Q = {mp.nstr(D["Q"],10)}   |hub-c1|^2 = '
          f'{mp.nstr((H*mp.cos(p)-mp.cos(b1))**2+(H*mp.sin(p)-mp.sin(b1))**2,10)}')
    print()

print('=== empirical: is Q = |hub - c_src|^2 for the source site, hub = H(cos p, sin p)? ===')
worst = 0; n = 0
for j in (0, 1):
    for rv in ['0.379', '0.3795', '0.37999']:
        for ov in ['0.61', '0.8', '1.0', '1.15']:
            for pv in ['-0.8', '-0.3', '0.2', '0.6']:
                r = mp.mpf(rv); p = mp.mpf(pv)
                b1 = mp.mpf('1.0') if j == 0 else mp.mpf(ov)
                b2 = mp.mpf(ov) if j == 0 else mp.mpf('1.0')
                D = code(r, b1, b2, p, j)
                H = D['H']; hub = (H*mp.cos(p), H*mp.sin(p))
                src = (mp.cos(b2), -mp.sin(b2)) if j == 0 else (mp.cos(b1), mp.sin(b1))
                diff = mp.sqrt((hub[0]-src[0])**2+(hub[1]-src[1])**2)
                worst = max(worst, abs(D['Q']-diff*diff)); n += 1
print(f'   max |Q - |hub-c_src|^2| = {mp.nstr(worst,4)} over {n} cases')
