"""R17 numeric validity search (fixed): random + polish over the ridge domain using the lead's own
objective. Purpose: look for a point where the true ridge objective EXCEEDS the certificate's
28.10690059505904. The certificate, not this search, is the evidence."""
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
from interval_joint_patch import I

cert = json.loads((LEAD / 'ridge_tangent_certificate.json').read_text())
CERT = cert['upper']
b_hi = math.acos(0.375)
r_lo, r_hi = 0.379, 0.37999
w_lo, w_hi = 0.04644456359141745, 0.7795925929485212
print(f'certificate upper = {CERT:.9f}')
print(f'domain r=[{r_lo},{r_hi}], b=[1,{b_hi:.9f}], w=[{w_lo:.6f},{w_hi:.6f}]')

errs = {}


def val(r, b1, b2, w1, w3):
    H = 2 * r * math.sin(b1 + b2)
    box = [I(str(r)), I(str(b1)), I(str(b2)), I(str(b1 - b2)),
           I(str(w1)), I(str(w3)), I(str(H))]
    v = old.objective(box)
    return float(v.b)


pts = []
rng = random.Random(99)
for _ in range(3000):
    pts.append((r_lo + (r_hi - r_lo) * rng.random(),
                1 + (b_hi - 1) * rng.random(), 1 + (b_hi - 1) * rng.random(),
                w_lo + (w_hi - w_lo) * rng.random(), w_lo + (w_hi - w_lo) * rng.random()))
# structured extremes: b1,b2 at their boundary, w at boundary, r at boundary
for r in (r_lo, 0.5 * (r_lo + r_hi), r_hi):
    for b1 in (1.0, 1.1, b_hi):
        for b2 in (1.0, 1.1, b_hi):
            for w1 in (w_lo, 0.5 * (w_lo + w_hi), w_hi):
                for w3 in (w_lo, 0.5 * (w_lo + w_hi), w_hi):
                    pts.append((r, b1, b2, w1, w3))

best = (-1e18, None)
nok = 0
for p in pts:
    try:
        g = val(*p)
    except Exception as e:
        errs[type(e).__name__] = errs.get(type(e).__name__, 0) + 1
        continue
    nok += 1
    if g > best[0]:
        best = (g, p)
print(f'evaluated {nok} points ok; exceptions: {errs}')
print(f'best found = {best[0]:.9f} at {tuple(round(x,6) for x in best[1])}')
print(f'certificate - best = {CERT - best[0]:+.9f}   (>=0 => no numeric counterexample)')

# coordinate polish from the best
x = list(best[1])
step = [(r_hi - r_lo) / 4, (b_hi - 1) / 4, (b_hi - 1) / 4,
        (w_hi - w_lo) / 4, (w_hi - w_lo) / 4]
lo = [r_lo, 1.0, 1.0, w_lo, w_lo]
hi = [r_hi, b_hi, b_hi, w_hi, w_hi]
for it in range(80):
    improved = False
    for k in range(5):
        for s in (+1, -1):
            y = list(x)
            y[k] = min(max(y[k] + s * step[k], lo[k]), hi[k])
            try:
                g = val(*y)
            except Exception:
                continue
            if g > best[0]:
                best = (g, tuple(y)); x = list(y); improved = True
    if not improved:
        step = [s * 0.5 for s in step]
print(f'polished best = {best[0]:.9f} at {tuple(round(v,6) for v in best[1])}')
print(f'certificate - polished = {CERT - best[0]:+.9f}')
print(f'polished vs target 28.107045: {best[0] < 28.107045}')
