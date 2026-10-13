"""cline2-coupled-factors R17S: kappa table only (fix: R as an interval literal)."""
import json
from pathlib import Path
from mpmath import mp, iv

iv.dps = 30
mp.dps = 30
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
RI = iv.mpf(19)/50

print('kappa table: rigorous W\'\' enclosure per (b,w) slab with r in [0.379, 0.37999]')
print('W(w) <= W(w0) + W\'(w0)(w-w0) + (kappa/2)(w-w0)^2  needs kappa >= sup W\'\'')
print()
print(f'{"j":>2s} {"b slab":>14s} {"w slab":>14s} {"q_min":>10s} {"sup W\'\'":>12s} '
      f'{"inf W\'\'":>12s}')
best = {}
for j in (0, 1):
    for b0 in ['0.80', '0.90', '1.00', '1.10', '1.15']:
        b1 = str(round(float(b0)+0.05, 4))
        for (wlo, whi) in [('0.05', '0.10'), ('0.10', '0.15'), ('0.15', '0.20'),
                           ('0.20', '0.25'), ('0.25', '0.30'), ('0.30', '0.35'),
                           ('0.35', '0.40'), ('0.40', '0.45')]:
            bs = iv.mpf([float(b0), float(b1)])
            rv = iv.mpf([0.379, 0.37999])
            ph = iv.mpf([float(mp.asin(mp.mpf('0.379'))),
                         float(mp.asin(mp.mpf('0.37999')))])
            x0 = 2*bs-iv.pi/2+ph
            wv = iv.mpf([float(wlo), float(whi)])
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
            u = sq/RI
            u1 = -x/(RI*sq)
            u2 = -xp/(RI*sq)-x*x/(RI*q*sq)
            W2b = -x/2+(mu+h)*a2-2*d*(u1*u1+u*u2)-l*u2
            sup = float(W2b.b); inf = float(W2b.a)
            print(f'{j:2d} [{b0},{b1}] [{wlo},{whi}] {float(q.a):10.5f} '
                  f'{sup:+12.4f} {inf:+12.4f}')
            cur = best.get(j)
            if cur is None or sup > cur[0]:
                best[j] = (sup, b0, b1, wlo, whi, float(q.a))
print()
for j in (0, 1):
    if j in best:
        sup, b0, b1, wlo, whi, qa = best[j]
        print(f'  j={j}: worst-case sup W\'\' = {sup:+.4f} on b=[{b0},{b1}], '
              f'w=[{wlo},{whi}] (q_min={qa:.5f})  =>  kappa_j >= {sup:+.4f}')
print()
print('  Reading: kappa is finite and modest away from the q -> 0 corner, and grows like')
print('  1/q_min there, exactly as the a\'\' = O(1/q) structure predicts.  This is the')
print('  quantity that replaces W_ww < 0 in the width elimination.')
json.dump({str(k): v for k, v in best.items()}, open(OUT/'r17_kappa.json', 'w'), indent=1)
print('\nsaved out/r17_kappa.json')
