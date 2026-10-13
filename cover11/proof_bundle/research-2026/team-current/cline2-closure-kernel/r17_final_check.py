"""R17 final: (a) how certify_ridge_tangent assembles the bound, (b) pointwise scan of the TRUE
ridge objective vs the certificate's per-component bounds.

Sign convention confirmed: h = -sin2T is CONCAVE on T in [2, 2acos(0.375)] (h'' = 4 sin2T < 0,
min -4, max -3.027); the tangent line lies ABOVE h (max residual -7.8e-13 <= 0), and the kernel's
gap = r^2 [tangent - h] >= 0. A valid upper bound on G therefore SUBTRACTS the gap.
"""
import json, math, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))
import os
os.chdir(LEAD)

print('=== (a) assembly in certify_ridge_tangent.py ===')
src = (LEAD / 'certify_ridge_tangent.py').read_text(encoding='utf-8', errors='replace')
for i, line in enumerate(src.splitlines(), 1):
    if any(w in line for w in ('gap', 'constant', 'upper', 'total', 'sum', 'result')):
        print(f'  {i:3d}| {line.strip()}')

print('\n=== certificate components and constant ===')
cert = json.loads((LEAD / 'ridge_tangent_certificate.json').read_text())
const = cert['constant']
print('  constant interval:', const)
c_lo, c_hi = float(const[0]), float(const[1])
comps = cert['components']
csum = sum(row['upper'] for row in comps)
print(f'  component uppers: {[row["upper"] for row in comps]}  sum={csum:.9f}')
print(f'  constant(lo) + components = {c_lo + csum:.9f}')
print(f'  certificate upper         = {cert["upper"]}')
print(f'  target 28.107045; margin = {28.107045 - cert["upper"]:.9f}')

print('\n=== (b) pointwise TRUE ridge objective vs certificate ===')
from mpmath import iv
iv.dps = 30
import patch_ridge_jet as old
from interval_joint_patch import I

rng_r = [0.379 + 0.00099 * k / 60 for k in range(61)]
b_hi = math.acos(0.375)
mx = (-1e18, None)
N = 60
for r in rng_r:
    for i in range(N + 1):
        b1 = 1 + (b_hi - 1) * i / N
        for j in range(N + 1):
            b2 = 1 + (b_hi - 1) * j / N
            for k in range(11):
                w1 = 0.04644456359141745 + (0.7795925929485212 - 0.04644456359141745) * k / 10
                for m in range(11):
                    w3 = 0.04644456359141745 + (0.7795925929485212 - 0.04644456359141745) * m / 10
                    H = 2 * r * math.sin(b1 + b2)
                    box = [I(str(r)), I(str(b1)), I(str(b2)), I(str(b1 - b2)),
                           I(str(w1)), I(str(w3)), I(str(H))]
                    v = old.objective(box).v
                    if float(v.b) > mx[0]:
                        mx = (float(v.b), (r, b1, b2, w1, w3))
print(f'  scanned {len(rng_r)}x{N}x{N}x11x11 points; max TRUE ridge objective = {mx[0]:.9f}')
print(f'  attained near {tuple(round(x, 6) for x in mx[1])}')
print(f'  certificate upper = {cert["upper"]}')
print(f'  certificate - true_max = {cert["upper"] - mx[0]:+.9f}  '
      f'(positive = valid upper bound)')
print(f'  true_max vs target 28.107045: {mx[0]:.9f} < 28.107045 -> {mx[0] < 28.107045}')
