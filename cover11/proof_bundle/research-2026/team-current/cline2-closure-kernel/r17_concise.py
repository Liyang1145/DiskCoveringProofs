"""R17 concise verification: (1) decomposition identity at many points (lead modules),
(2) coarse numeric search for any point where the true ridge objective exceeds the certificate
28.10690059505904. Uses .v to unwrap the Jet."""
import json, math, random, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))
import os
os.chdir(LEAD)
from mpmath import iv
iv.dps = 30
import patch_ridge_jet as old
import ridge_tangent_jet as tj
from interval_joint_patch import I

CERT = 28.10690059505904
TAU = float(tj.TAU.a)
b_hi = math.acos(0.375)
r_lo, r_hi = 0.379, 0.37999
w_lo, w_hi = 0.04644456359141745, 0.7795925929485212


def ridge_old(r, b1, b2, w1, w3):
    H = 2 * r * math.sin(b1 + b2)
    box = [I(r, r), I(b1, b1), I(b2, b2), I(b1 - b2, b1 - b2),
           I(w1, w1), I(w3, w3), I(H, H)]
    return float(old.objective(box).v.b)


def split(r, b1, b2, w1, w3):
    c = tj.constant(I(r, r)).v
    c0, _ = tj.component([I(r, r), I(b1, b1), I(w1, w1)], 0)
    c1, _ = tj.component([I(r, r), I(b2, b2), I(w3, w3)], 1)
    T = b1 + b2
    gap = r * r * (-math.sin(2 * TAU) - 2 * math.cos(2 * TAU) * (T - TAU) + math.sin(2 * T))
    return float((c + c0.v + c1.v).b), float(c.a) + float(c0.v.a) + float(c1.v.a), gap


print('=== (1) decomposition identity: old ridge vs constant+components-gap ===')
rng = random.Random(4242)
worst = 0.0
maxgap = 0.0
maxgap_pt = None
n = 0
for _ in range(60):
    r = r_lo + (r_hi - r_lo) * rng.random()
    b1 = 1 + (b_hi - 1) * rng.random()
    b2 = 1 + (b_hi - 1) * rng.random()
    w1 = w_lo + (w_hi - w_lo) * rng.random()
    w3 = w_lo + (w_hi - w_lo) * rng.random()
    try:
        a = ridge_old(r, b1, b2, w1, w3)
        hi, lo, gap = split(r, b1, b2, w1, w3)
    except Exception as e:
        print('   skip', type(e).__name__); continue
    n += 1
    d = abs((lo - gap) - a)
    worst = max(worst, d)
    if gap > maxgap:
        maxgap, maxgap_pt = gap, (r, b1, b2)
print(f'  {n} points; worst |(const+components-gap) - old_ridge| = {worst:.3e}')
print(f'  max gap over sample = {maxgap:.9f} at r,b1,b2 = {tuple(round(x,6) for x in maxgap_pt)}')

print('\n=== (2) search for any point with true ridge objective ABOVE the certificate ===')
best = (-1e18, None)
nok = 0
for _ in range(6000):
    p = (r_lo + (r_hi - r_lo) * rng.random(),
         1 + (b_hi - 1) * rng.random(), 1 + (b_hi - 1) * rng.random(),
         w_lo + (w_hi - w_lo) * rng.random(), w_lo + (w_hi - w_lo) * rng.random())
    try:
        g = ridge_old(*p)
    except Exception:
        continue
    nok += 1
    if g > best[0]:
        best = (g, p)
print(f'  {nok} ok evaluations; best = {best[0]:.9f} at {tuple(round(x,6) for x in best[1])}')
print(f'  certificate - best = {CERT - best[0]:+.9f}  (>= 0: no counterexample found)')
print(f'  best vs target 28.107045: {best[0] < 28.107045}')
print(f'  (numeric only; the certificate is the evidence, per the lead)')
