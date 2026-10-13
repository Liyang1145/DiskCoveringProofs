"""cline2-coupled-factors R17: width strong-concavity probe on the LEAD's width(r,b,w,j).

Objects read from lead/joint_boundary_jet.py:
  s = sqrt(1-r^2); ph = asin(r); x0 = 2b - pi/2 + ph
  p = cos(w) - r cos(x0+w);            x = -sin(w) + r sin(x0+w)
  cx = s - r sin2b;  cy = -2r sin^2 b
  px = s cos w - r sin w;  py = -s sin w - r cos w
  q = (px-cx)^2 + (py-cy)^2
  cn = 1 + r^2 - 2r cos(x0);  gap = 1 - sqrt(cn);  den = 1 - p
  u = sqrt(q)/R;   eta = atan2(x, den)
  W = -r s sin^2 b + (1/2 - mu) w + x/2 + (mu+h) eta - d u^2 - l u
with (mu,h,d,l) = (z1, z112, z34, z96) for j=0 and (z3, z115, z39, z101) for j=1,
R = 19/50.

Gates requested by the lead: r in [.379,.37999], b in [acos(r)/2, 1.19],
g <= w <= Wmax(r,b), endpoint  q >= (R*0.19)^2 = 0.0052132...
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
QGATE = (R*mp.mpf('0.19'))**2


def width(r, b, w, j):
    s = mp.sqrt(1-r*r); ph = mp.asin(r)
    x0 = 2*b-mp.pi/2+ph
    p = mp.cos(w)-r*mp.cos(x0+w)
    x = -mp.sin(w)+r*mp.sin(x0+w)
    cx = s-r*mp.sin(2*b); cy = -2*r*mp.sin(b)**2
    px = s*mp.cos(w)-r*mp.sin(w); py = -s*mp.sin(w)-r*mp.cos(w)
    q = (px-cx)**2+(py-cy)**2
    den = 1-p
    cn = 1+r*r-2*r*mp.cos(x0)
    gap = 1-mp.sqrt(cn)
    mu, h, d, l = ((Z[1], Z[112], Z[34], Z[96]) if j == 0
                   else (Z[3], Z[115], Z[39], Z[101]))
    u = mp.sqrt(q)/R
    eta = mp.atan2(x, den)
    W = -r*s*mp.sin(b)**2+(mp.mpf(1)/2-mu)*w+x/2+(mu+h)*eta-d*u*u-l*u
    return W, q, den, gap, cn


def Wmax(r, b):
    """the largest w with den = 1-p > 0 (lead's legal(): W = 2 atan2(X, D))"""
    ph = mp.pi/2-mp.atan2(mp.sqrt(1-r*r), r)
    x0 = 2*b-mp.pi/2+ph
    X = r*mp.sin(x0); D = 1-r*mp.cos(x0)
    if X < 0:
        return None
    return 2*mp.atan2(X, D)


print('=== 0. verify the q identity: q = 1 + cn - 2p ===')
for (r, b, w, j) in [(mp.mpf('0.3795'), mp.mpf('1.0'), mp.mpf('0.2'), 0),
                     (mp.mpf('0.3799'), mp.mpf('1.1'), mp.mpf('0.35'), 1),
                     (mp.mpf('0.379'), mp.mpf('1.19'), mp.mpf('0.15'), 0)]:
    W, q, den, gap, cn = width(r, b, w, j)
    ident = 1+cn-2*(1-den)
    print(f'  r={float(r):.5f} b={float(b):.3f} w={float(w):.3f} j={j}: '
          f'q={mp.nstr(q,12)}  1+cn-2p={mp.nstr(ident,12)}  diff={mp.nstr(abs(q-ident),4)}')

print()
print('=== 1. domain and gates ===')
wmin = None
for j in (0, 1):
    r = mp.mpf('0.3795')
    for b in [mp.acos(r)/2, mp.mpf('0.9'), mp.mpf('1.0'), mp.mpf('1.19')]:
        Wm = Wmax(r, b)
        if Wm is None:
            print(f'  j={j} r={float(r)} b={float(b):.4f}: Wmax undefined (X<0)')
            continue
        W0, q0, den0, gap0, cn0 = width(r, b, mp.mpf('0'), j)
        W1, q1, den1, gap1, cn1 = width(r, b, Wm, j)
        print(f'  j={j} r={float(r):.5f} b={float(b):.4f}: Wmax={float(Wm):.6f} '
              f'| at w=0: q={float(q0):.6f}({">=gate" if q0 >= QGATE else "<GATE"}) '
              f'gap={float(gap0):.6f} | at w=Wmax: q={float(q1):.6f} '
              f'den={float(den1):.3e}')

print()
print(f'  q gate = (R*0.19)^2 = {mp.nstr(QGATE,12)}')
print('  note: at w=Wmax the gate q >= gap^2 is what keeps u^2 bounded; the lead''s listed')
print('  condition is q >= (R*0.19)^2 at the endpoint.')

print()
print('=== 2. W_ww via exact second differences (mpmath, h=1e-4) ===')
h = mp.mpf('1e-4')
print(f'{"r":>8s} {"b":>7s} {"j":>2s} {"w":>8s} {"q":>12s} {"W_ww":>14s} {"-W_ww":>12s}')
rows = []
for j in (0, 1):
    for r in ['0.379', '0.3795', '0.37999']:
        for b in ['0.7900', '0.95', '1.10', '1.19']:
            rr = mp.mpf(r); bb = mp.mpf(b)
            if bb < mp.acos(rr)/2:
                continue
            Wm = Wmax(rr, bb)
            if Wm is None or Wm <= 0:
                continue
            for frac in ['0.25', '0.5', '0.75', '0.95']:
                w = Wm*mp.mpf(frac)
                if w < h*4:
                    continue
                Wp = width(rr, bb, w+h, j)[0]
                W0 = width(rr, bb, w, j)[0]
                Wm2 = width(rr, bb, w-h, j)[0]
                d2 = (Wp-2*W0+Wm2)/(h*h)
                q = width(rr, bb, w, j)[1]
                rows.append((float(rr), float(bb), j, float(w), float(q), float(d2)))
                print(f'{float(rr):8.5f} {float(bb):7.4f} {j:2d} {float(w):8.4f} '
                      f'{float(q):12.6f} {float(d2):14.6f} {float(-d2):12.6f}')
print()
pos = [t for t in rows if t[5] > 0]
neg = [t for t in rows if t[5] < 0]
print(f'  sampled points: {len(rows)};  W_ww < 0 at {len(neg)};  W_ww > 0 at {len(pos)}')
if pos:
    w = min(pos, key=lambda t: -t[5])
    print(f'  strongest VIOLATION of W_ww<0: W_ww={w[5]:+.6f} at '
          f'r={w[0]} b={w[1]:.4f} j={w[2]} w={w[3]:.4f} q={w[4]:.6f}')
json.dump(rows, open(OUT/'r17_ww_probe.json', 'w'), indent=1)
print('  saved out/r17_ww_probe.json')
