"""R17 final v2: parse the certificate constant, assemble the bound, and scan the TRUE ridge
objective pointwise to test the certificate's validity."""
import json, math, re, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))
import os
os.chdir(LEAD)

cert = json.loads((LEAD / 'ridge_tangent_certificate.json').read_text())
raw = cert['constant']
nums = [float(x) for x in re.findall(r'-?\d+\.?\d*(?:[eE][-+]?\d+)?', raw)]
print('constant raw =', raw[:60], '...')
print('parsed numbers:', nums)
c_lo, c_hi = min(nums), max(nums)
comps = cert['components']
csum = sum(row['upper'] for row in comps)
print(f'component uppers: {[round(row["upper"], 9) for row in comps]} sum={csum:.9f}')
print(f'assembled = constant + sum(components)')
print(f'   using constant lo: {c_lo + csum:.9f}')
print(f'   using constant hi: {c_hi + csum:.9f}')
print(f'certificate upper  : {cert["upper"]}')
print(f'target             : 28.107045   margin = {28.107045 - cert["upper"]:.9f}')
print(f'tau fixed at 87/40 = {87/40}')

from mpmath import iv
iv.dps = 30
import patch_ridge_jet as old
from interval_joint_patch import I

b_hi = math.acos(0.375)
print(f'\n=== pointwise scan of the TRUE ridge objective (patch_ridge_jet) ===')
print(f'r in [0.379, 0.37999], b1,b2 in [1, {b_hi:.9f}], w1,w3 in [0.0464, 0.7796]')
mx = (-1e18, None)
Nr, Nb, Nw = 41, 41, 9
for ir in range(Nr):
    r = 0.379 + (0.37999 - 0.379) * ir / (Nr - 1)
    for i in range(Nb):
        b1 = 1 + (b_hi - 1) * i / (Nb - 1)
        for j in range(Nb if i % 4 == 0 else 1):
            b2 = 1 + (b_hi - 1) * j / (Nb - 1) if i % 4 == 0 else b1
            for k in range(Nw):
                w1 = 0.04644456359141745 + (0.7795925929485212 - 0.04644456359141745) * k / (Nw - 1)
                for m in (range(Nw) if i % 4 == 0 else [k]):
                    w3 = 0.04644456359141745 + (0.7795925929485212 - 0.04644456359141745) * m / (Nw - 1)
                    H = 2 * r * math.sin(b1 + b2)
                    box = [I(str(r)), I(str(b1)), I(str(b2)), I(str(b1 - b2)),
                           I(str(w1)), I(str(w3)), I(str(H))]
                    v = old.objective(box).v
                    if float(v.b) > mx[0]:
                        mx = (float(v.b), (r, b1, b2, w1, w3))
print(f'  scanned points; max TRUE ridge objective = {mx[0]:.9f}')
print(f'  attained near (r,b1,b2,w1,w3) = {tuple(round(x, 6) for x in mx[1])}')
print(f'  certificate upper            = {cert["upper"]}')
print(f'  certificate - true_max       = {cert["upper"] - mx[0]:+.9f}   '
      f'(>=0 => certificate is a valid upper bound over the ridge)')
print(f'  true_max vs 28.107045        : {mx[0] < 28.107045}')
