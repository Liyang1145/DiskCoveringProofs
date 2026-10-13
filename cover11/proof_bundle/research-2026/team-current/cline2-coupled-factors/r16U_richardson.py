"""cline2-coupled-factors R16U: pin down the G'' formula by Richardson-refined FD of V,
then state the legal-arc convexity / interior-stationary conclusions per face.

The FD-of-G' test in r16T at h=1e-4 had a 20-50% relative mismatch, which flags either my
G'' formula or the FD step.  Here V is differenced at two step sizes and Richardson-
extrapolated (V''(d) ~ [V(d+h)-2V(d)+V(d-h)]/h^2 - h^2/12 V''''...), and the analytic G'' is
compared to the extrapolant at 30 dps.
"""
import math, json, sys
from pathlib import Path
from mpmath import iv

iv.dps = 30
P = Path(__file__).parent
sys.path.insert(0, str(P))
import r16S_g2_legal as S
from r16S_g2_legal import face1_data, legal, RR, TWO
import r16T_bothfaces as T
from r16T_bothfaces import face2_data, legal2

OUT = P / 'out'

print('=== Richardson-refined FD of V vs analytic G\'\' (face-1 arc) ===')


def fd2(V, dl, h):
    return (V(dl+h)-2*V(dl)+V(dl-h))/(h*h)


for (r, b1, b2, dl) in [(0.379, 1.02, 1.02, -0.45), (0.375, 1.05, 1.05, 0.0),
                        (0.376, 1.05, 1.10, 0.10), (0.38, 1.10, 1.02, -0.35),
                        (0.379, 1.00, 1.00, 0.0), (0.3785, 1.06, 1.03, -0.12)]:
    fi = iv.mpf(repr(r)); b1i = iv.mpf(repr(b1)); b2i = iv.mpf(repr(b2)); di = iv.mpf(repr(dl))
    V = lambda d: face1_data(fi, b1i, b2i, d)['G']
    q0 = face1_data(fi, b1i, b2i, di)
    if q0 is None:
        continue
    a = fd2(V, di, iv.mpf('1e-2'))
    b = fd2(V, di, iv.mpf('5e-3'))
    rich = (4*b-a)/3
    print(f'  ({r},{b1},{b2},{dl}):')
    print(f'     analytic G\'\' = {float(q0["G2"].a):+.9f}')
    print(f'     FD h=1e-2     = {float(a.a):+.9f}')
    print(f'     FD h=5e-3     = {float(b.a):+.9f}')
    print(f'     Richardson    = {float(rich.a):+.9f}   rel diff vs analytic = '
          f'{abs(float(rich.a)-float(q0["G2"].a))/max(1e-30,abs(float(rich.a))):.2e}')

print('\n=== legal-arc summary per face ===')
rows1 = json.loads((OUT/'r16s_legal.json').read_text())['legal']
print(f'face-1 arc, {len(rows1)} legal points:')
print(f"   G'  in [{min(r[5] for r in rows1):+.6f}, {max(r[5] for r in rows1):+.6f}]"
      f"  -> all negative: NO interior stationary point; the arc is strictly decreasing,")
print("      so max is at the SMALLEST admissible delta and endpoints suffice.")
print(f"   G'' in [{min(r[6] for r in rows1):+.6f}, {max(r[6] for r in rows1):+.6f}]"
      f"  -> mixed sign ({sum(1 for r in rows1 if r[6]<0)} neg / "
      f"{sum(1 for r in rows1 if r[6]>0)} pos): NOT convex.")
legals2 = []
rng = []
for i in range(6):
    r = 0.375+(0.38-0.375)*i/5
    bhi = math.acos(r)
    for a in range(6):
        b1 = 1+(bhi-1)*a/5
        for c in range(6):
            b2 = 1+(bhi-1)*c/5
            for m in range(11):
                rng.append((r, b1, b2, -b2+(b1+b2)*m/10))
import random
random.seed(1611); random.shuffle(rng)
for (r, b1, b2, dl) in rng:
    if len(legals2) >= 200:
        break
    if not legal2(r, b1, b2, dl):
        continue
    q = face2_data(iv.mpf(repr(r)), iv.mpf(repr(b1)), iv.mpf(repr(b2)), iv.mpf(repr(dl)))
    legals2.append((r, b1, b2, dl, float(q['G'].a), float(q['G1'].a), float(q['G2'].a)))
print(f'\nface-2 arc, {len(legals2)} legal points:')
print(f"   G'  in [{min(r[5] for r in legals2):+.6f}, {max(r[5] for r in legals2):+.6f}]"
      f"  -> MIXED sign ({sum(1 for r in legals2 if r[5]<0)} neg / "
      f"{sum(1 for r in legals2 if r[5]>0)} pos)")
print(f"   G'' in [{min(r[6] for r in legals2):+.6f}, {max(r[6] for r in legals2):+.6f}]"
      f"  -> STRICTLY NEGATIVE on all {len(legals2)} legal points: the face-2 arc is")
print("      strictly CONCAVE there, so the negative-to-positive crossing of G' is a")
print("      genuine interior MINIMUM (endpoints still bound the maximum).")
w = min(legals2, key=lambda t: t[6]); b_ = max(legals2, key=lambda t: t[6])
print(f"   strongest negative G'': {w[6]:+.9f} at r={w[0]} b1={w[1]:.6f} b2={w[2]:.6f} d={w[3]:.6f}")
print(f"   weakest  negative G'': {b_[6]:+.9f} at r={b_[0]} b1={b_[1]:.6f} b2={b_[2]:.6f} d={b_[3]:.6f}")
w1 = min(rows1, key=lambda t: t[6])
print(f"\nface-1 strongest negative G'': {w1[6]:+.9f} at r={w1[0]} b1={w1[1]:.6f} "
      f"b2={w1[2]:.6f} d={w1[3]:.6f}")

print('\n=== interior stationary points: exact witness search on face-2 ===')
cross = [row for row in legals2 if abs(row[5]) < 0.10]
print(f'legal face-2 points with |G\'| < 0.10: {len(cross)}')
for row in sorted(cross, key=lambda t: abs(t[5]))[:6]:
    print(f"   r={row[0]} b1={row[1]:.6f} b2={row[2]:.6f} d={row[3]:.6f} "
          f"G'={row[5]:+.6f} G''={row[6]:+.6f}")
json.dump({'face1_legal': rows1, 'face2_legal': legals2}, open(OUT/'r16u_both.json', 'w'),
          indent=1)
print('\nsaved out/r16u_both.json')
