"""cline2-coupled-factors R18g: identify p numerically from the code's X,Y.
Candidates: hub = H(cos p, sin p) or H(-sin p, cos p); source = (sin b, -cos b), (sin b, cos b),
or the disk-centre-like (-sin b, cos b) / (sin b, -cos b).
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
    return dict(X=X, Y=Y, H=H, b=b, ang=ang, A=A, B=B)


r = mp.mpf('0.3795'); b1 = mp.mpf('1.0'); b2 = mp.mpf('0.8'); p = mp.mpf('0.2')
for j in (0, 1):
    D = code(r, b1, b2, p, j)
    print(f'j={j}: X={mp.nstr(D["X"],12)}  Y={mp.nstr(D["Y"],12)}  H={mp.nstr(D["H"],12)}'
          f'  A={mp.nstr(D["A"],10)} B={mp.nstr(D["B"],10)} b={mp.nstr(D["b"],8)}')
    print(f'     X + 2r sin b cos ang = H = {mp.nstr(D["X"]+2*r*mp.sin(D["b"])*mp.cos(D["ang"]),12)}')
    print(f'     Y - 2r sin b sin ang = 0 ? {mp.nstr(D["Y"]-2*r*mp.sin(D["b"])*mp.sin(D["ang"]),4)}')

print()
print('=== candidate Cartesian identifications for hub and source ===')
cands = {
    'hub_H_cosp_sinp': lambda H, p, sg, b: (H*mp.cos(p), H*mp.sin(p)),
    'hub_H_-sinp_cosp': lambda H, p, sg, b: (-H*mp.sin(p), H*mp.cos(p)),
    'hub_2r_sinA_dir': lambda H, p, sg, b: None,
}
srcs = {
    'src_sin_cos_m': lambda b: (mp.sin(b), mp.cos(b)),
    'src_sin_cos_p': lambda b: (mp.sin(b), -mp.cos(b)),
    'src_cos_sin': lambda b: (mp.cos(b), mp.sin(b)),
    'src_-sin_cos': lambda b: (-mp.sin(b), mp.cos(b)),
}
for j in (0, 1):
    D = code(r, b1, b2, p, j)
    H = D['H']; b = D['b']
    print(f' j={j} (H={mp.nstr(H,8)}, b={mp.nstr(b,8)}):')
    for hn, hf in cands.items():
        if hf is None:
            continue
        hub = hf(H, p, 0, b)
        for sn, sf in srcs.items():
            src = sf(b)
            err = abs((hub[0]-src[0])-D['X'])+abs((hub[1]-src[1])-D['Y'])
            if err < mp.mpf('1e-8'):
                print(f'    MATCH: hub={hn}, source={sn}  (err {mp.nstr(err,3)})')
    # also test pure algebraic: is X^2+Y^2 equal to a simpler expression?
    print(f'    Q = {mp.nstr(D["X"]**2+D["Y"]**2,12)}')
    print(f'    H^2+1-2H sin b = {mp.nstr(H*H+1-2*H*mp.sin(b),12)}')
    print(f'    H^2+1-2H cos b = {mp.nstr(H*H+1-2*H*mp.cos(b),12)}')
    print(f'    H^2+4r^2 sin^2 b-4rH sin b sin ang = '
          f'{mp.nstr(H*H+4*r*r*mp.sin(b)**2-4*r*H*mp.sin(b)*mp.sin(D["ang"]),12)}')
