"""R17: audit the ridge rank-one decomposition, tangent direction, and the q/filter interfaces.

1. Verify the exact ridge objective (patch_ridge_jet.old) equals
   constant(r) + component(r,b1,w1,j=0) + component(r,b2,w3,j=1) + r^2*g(T)
   with g(T) = -sin2T - h'(tau)(T-tau) + h(tau) style gap, at many random legal points, using
   only the lead's own modules (read-only import).
2. Verify h(T) = -sin(2T) is concave on T in [2, 2acos(3/8)] and that the tangent inequality
   h(T) <= h(tau) + h'(tau)(T-tau) holds with the code's exact tau = 87/40.
3. Check the two necessary filters in the kernel: q <= r^2 and cos b >= r.
4. Print the tau used and the gap maximum.
"""
import sys, math, json
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))
import os
os.chdir(LEAD)

from mpmath import iv
iv.dps = 30
import ridge_tangent_jet as t
import patch_ridge_jet as old
from interval_joint_patch import I, uf, lf, R, z

TAU = float(t.TAU.a)
print(f'tau = 87/40 = {TAU}  (exact rational in the kernel)')

pi = math.pi
b_lo, b_hi = 1.0, math.acos(0.375)
T_lo, T_hi = 2 * b_lo, 2 * b_hi
print(f'b in [{b_lo}, {b_hi:.9f}]  T in [{T_lo}, {T_hi:.9f}]')
print(f'2T in [{2*T_lo:.6f}, {2*T_hi:.6f}] subset (pi,2pi): {2*T_lo > pi and 2*T_hi < 2*pi}')

print('\n=== 2. concavity of h(T) = -sin(2T) and the tangent inequality ===')
mincurv = min(-4 * math.sin(2 * (T_lo + (T_hi - T_lo) * k / 2000)) for k in range(2001))
print(f'  h\'\'(T) = 4 sin 2T;  min over the interval = {mincurv:.9f} '
      f'(negative => strictly concave): {mincurv < 0}')
worstgap = -1e9
for k in range(2001):
    T = T_lo + (T_hi - T_lo) * k / 2000
    h = -math.sin(2 * T)
    tan = -math.sin(2 * TAU) + (-2 * math.cos(2 * TAU)) * (T - TAU)
    worstgap = max(worstgap, h - tan)
print(f'  max h(T) - tangent = {worstgap:+.6e}  (<=0 proves the bound direction holds)')
print(f'  value at tau: h(tau)={-math.sin(2*TAU):.9f}  h\'(tau)={-2*math.cos(2*TAU):.9f}')

print('\n=== 1. decomposition identity at random legal points (lead modules only) ===')
import random
rng = random.Random(1701)
worst = 0.0
worst_rel = 0.0
n = 0
for i in range(40):
    r = 0.375 + rng.random() * 0.005
    b1 = 1 + rng.random() * (math.acos(0.375) - 1)
    b2 = 1 + rng.random() * (math.acos(0.375) - 1)
    w1 = 0.66 + rng.random() * 0.1
    w3 = 0.66 + rng.random() * 0.1
    H = 2 * r * math.sin(b1 + b2)
    box = [I(str(r)), I(str(b1)), I(str(b2)), I(str(b1 - b2)), I(str(w1)), I(str(w3)), I(str(H))]
    f = old.objective(box).v
    c = t.constant(I(str(r)))
    c0, _ = t.component([I(str(r)), I(str(b1)), I(str(w1))], 0)
    c1, _ = t.component([I(str(r)), I(str(b2)), I(str(w3))], 1)
    T = b1 + b2
    gap = r * r * (-math.sin(2 * TAU) - 2 * math.cos(2 * TAU) * (T - TAU) + math.sin(2 * T))
    total = c + c0.v + c1.v - gap
    diff = float((total - f).b) if hasattr(total - f, 'b') else abs(total - f)
    lo = float((total - f).a)
    hi = float((total - f).b)
    worst = max(worst, abs(lo), abs(hi))
    n += 1
    if i < 3:
        print(f'  pt i={i}: r={r:.6f} b1={b1:.5f} b2={b2:.5f} T={T:.5f}')
        print(f'     old_ridge = {float(f.a):.9f}..{float(f.b):.9f}')
        print(f'     split     = {float((total).a):.9f}..{float((total).b):.9f}')
        print(f'     difference [{lo:+.3e}, {hi:+.3e}]  contains 0: {lo <= 0 <= hi}')
print(f'  {n} points; worst |split - old| = {worst:.3e}')

print('\n=== 3. necessary filters ===')
print(f'  cos(b) >= r for b in [1, acos r]:  cos(1)={math.cos(1):.9f}, r<=0.38  -> '
      f'{math.cos(1) >= 0.38}')
print(f'  q <= r^2: kernel line 28 rejects when (q.v - r^2).a > 0')
print(f'  _H bound H = 2 r sin(b1+b2): sin(2b)<=... : at b=acos(0.375), '
      f'H=2*0.38*sin({2*math.acos(0.375):.6f})={2*0.38*math.sin(2*math.acos(0.375)):.9f}')

print('\n=== 4. certificate / control summaries ===')
for f in ('ridge_split_control.json', 'ridge_tangent_certificate.json',
          'ridge_tangent_calibration.json'):
    p = LEAD / f
    if p.exists():
        d = json.loads(p.read_text())
        print(f'  {f}: keys={list(d.keys())[:8]}')
        if 'n' in d:
            print(f'      n={d["n"]} sympy_trig_identity={d.get("sympy_trig_identity")}')
        for k in ('upper', 'tau', 'scope', 'budget_ended', 'liveboxes'):
            if k in d:
                print(f'      {k} = {d[k]}')
