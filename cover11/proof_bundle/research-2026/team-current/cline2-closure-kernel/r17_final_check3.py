"""R17 final: (1) assembled bound vs the certificate, (2) source/coefficient pins,
(3) broad random+local numeric search for the ridge maximum to test the certificate's validity
(expected to stay below; the certificate, not the search, is the evidence).
"""
import json, math, random, sys, hashlib
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))
import os
os.chdir(LEAD)
import numpy as np

cert = json.loads((LEAD / 'ridge_tangent_certificate.json').read_text())
print('=== certificate ===')
print('scope   :', cert['scope'])
print('upper   :', cert['upper'])
print('domain  :', cert['domain'])
for row in cert['components']:
    print(f"  j={row['j']}: upper={row['upper']:.9f} count={row['count']} live={row['live']}")
print('coeff sha256:', cert['coefficient_sha256'][:16], '...')
print('\n=== pins ===')
for name, declared in cert['source_sha256'].items():
    p = LEAD / name
    if not p.exists():
        print(f'  {name}: ABSENT'); continue
    actual = hashlib.sha256(p.read_bytes()).hexdigest()
    print(f'  {name:26s} declared={declared[:12]} actual={actual[:12]} '
          f'{"OK" if actual == declared else "MISMATCH"}')
fj = LEAD / 'joint_nested_frozen.json'
print(f'  joint_nested_frozen.json  actual={{hashlib.sha256(fj.read_bytes()).hexdigest()[:12]}}')

print('\n=== assembly check ===')
import re
nums = [float(x) for x in re.findall(r'-?\d+\.\d+(?:[eE][-+]?\d+)?', cert['constant'])]
c_lo, c_hi = min(nums), max(nums)
csum = sum(r['upper'] for r in cert['components'])
print(f'  constant interval = [{c_lo:.9f}, {c_hi:.9f}]')
print(f'  components sum    = {csum:.9f}')
print(f'  constant_lo+sum   = {c_lo + csum:.9f}   certificate upper = {cert["upper"]}')
print(f'  target 28.107045  -> margin = {28.107045 - cert["upper"]:.9f}')

print('\n=== numeric search for the ridge maximum (validity test only) ===')
b_hi = math.acos(0.375)
r_lo, r_hi = 0.379, 0.37999
w_lo, w_hi = 0.04644456359141745, 0.7795925929485212
z = json.loads(fj.read_text())['z']
z = [float(v) for v in z]
R0 = 0.38


def G_float(r, b1, b2, w1, w3):
    """float re-implementation of patch_smooth_jet.objective restricted to the ridge H=2r sin(b1+b2),
    using only terms that depend on (r,b1,b2,w1,w3) - the delta terms vanish at delta=b1-b2?"""
    # For this validity test use the lead's own module instead (interval), to avoid re-deriving.
    return None


from mpmath import iv
iv.dps = 30
import patch_ridge_jet as old
from interval_joint_patch import I


def val(r, b1, b2, w1, w3):
    H = 2 * r * math.sin(b1 + b2)
    box = [I(str(r)), I(str(b1)), I(str(b2)), I(str(b1 - b2)),
           I(str(w1)), I(str(w3)), I(str(H))]
    v = old.objective(box)
    return float(v.b)


rng = random.Random(20260925)
best = (-1e18, None)
N = 4000
for _ in range(N):
    r = r_lo + (r_hi - r_lo) * rng.random()
    b1 = 1 + (b_hi - 1) * rng.random()
    b2 = 1 + (b_hi - 1) * rng.random()
    w1 = w_lo + (w_hi - w_lo) * rng.random()
    w3 = w_lo + (w_hi - w_lo) * rng.random()
    try:
        g = val(r, b1, b2, w1, w3)
    except Exception:
        continue
    if g > best[0]:
        best = (g, (r, b1, b2, w1, w3))
print(f'  random {N}: best = {best[0]:.9f} at {tuple(round(x,6) for x in best[1])}')

# local polish
x = np.array(best[1])
step = np.array([(r_hi - r_lo) / 8, (b_hi - 1) / 8, (b_hi - 1) / 8,
                 (w_hi - w_lo) / 8, (w_hi - w_lo) / 8])
for it in range(60):
    improved = False
    for k in range(5):
        for s in (+1, -1):
            y = x.copy()
            y[k] = min(max(y[k] + s * step[k], [r_lo, 1, 1, w_lo, w_lo][k]),
                       [r_hi, b_hi, b_hi, w_hi, w_hi][k])
            try:
                g = val(*y)
            except Exception:
                continue
            if g > best[0]:
                best = (g, tuple(y)); x = y; improved = True
    if not improved:
        step *= 0.5
print(f'  polished: best = {best[0]:.9f} at {tuple(round(x,6) for x in best[1])}')
print(f'\n  certificate = {cert["upper"]:.9f}')
print(f'  certificate - best_found = {cert["upper"] - best[0]:+.9f}  (>=0: no counterexample)')
print(f'  best_found vs target 28.107045: {best[0] < 28.107045}')
