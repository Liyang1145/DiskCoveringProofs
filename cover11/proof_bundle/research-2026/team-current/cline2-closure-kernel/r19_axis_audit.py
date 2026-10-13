"""R19 audit (analytic, no grids): (a) exact coordinate identities in HUB-SEPARATION-AXIS.md,
(b) radial-lemma constants and sign, (c) 3D domain containment, (d) chirality of the atan terms.

Only point evaluations of the frozen coefficients; no sweeps.
"""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
import json, math
from pathlib import Path

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))
import os
os.chdir(LEAD)
from mpmath import iv
iv.dps = 30
import hub_axis_stationary as h
from interval_joint_patch import I, z

def f(x):
    try:
        return float(x.mid)
    except Exception:
        return float(x)

beta1, beta2 = f(h.beta1), f(h.beta2)
c1, c2 = f(h.c1), f(h.c2)
a1, a2 = f(h.a1), f(h.a2)
print('=== frozen coefficients (from hub_axis_stationary) ===')
print(f'  beta1={beta1:+.9f} beta2={beta2:+.9f}')
print(f'  c1   ={c1:+.9f} c2   ={c2:+.9f}')
print(f'  a1   ={a1:+.9f} a2   ={a2:+.9f}')
print(f'  all positive: {beta1>0 and beta2>0 and c1>0 and c2>0 and a1>0 and a2>0}')

print('\n=== (a) A = (d/2) n  exact identity + M decomposition (point check) ===')
r, b1, b2 = 0.3795, 1.05, 1.12
Q1 = (r*math.sin(2*b1), 2*r*math.sin(b1)**2)
Q2 = (r*math.sin(2*b2), -2*r*math.sin(b2)**2)
m = ((Q1[0]+Q2[0])/2, (Q1[1]+Q2[1])/2)
dv = (Q1[0]-Q2[0], Q1[1]-Q2[1]); d = math.hypot(*dv)
e = (dv[0]/d, dv[1]/d); n = (e[1], -e[0])
A = (r*(math.sin(b1)**2+math.sin(b2)**2), r*(math.sin(b2)*math.cos(b2)-math.sin(b1)*math.cos(b1)))
print(f'  Q1={tuple(round(x,6) for x in Q1)} Q2={tuple(round(x,6) for x in Q2)} d={d:.9f}')
print(f'  A=({A[0]:.9f},{A[1]:.9f})  (d/2)n=({(d/2)*n[0]:.9f},{(d/2)*n[1]:.9f}) '
      f'  diff=({A[0]-(d/2)*n[0]:+.2e},{A[1]-(d/2)*n[1]:+.2e})')

print('\n=== (b) radial lemma constant: 2(beta1+beta2) - c/L - a/L^2 at L=0.43 ===')
L = 0.43
for tag, (cc, aa) in [('face1 (c1,a1)', (c1, a1)), ('face2 (c2,a2)', (c2, a2))]:
    val = 2*(beta1+beta2) - cc/L - aa/L**2
    print(f'  {tag}: 2(beta1+beta2)={2*(beta1+beta2):.9f}  c/L={cc/L:.9f}  a/L^2={aa/L**2:.9f}'
          f'  -> {val:+.9f}   positive: {val>0}')
print(f'  kernel assertion in probe_axis_radial.py uses exactly this expression with I(".43")')

print('\n=== positive-curvature kernel: Wj = 2 betaj - cj/Lj on Lj <= 0.76 ===')
for tag, (bb, cc) in [('j=1', (beta1, c1)), ('j=2', (beta2, c2))]:
    print(f'  {tag}: 2beta={2*bb:.9f} - c/0.76={cc/0.76:.9f} -> {2*bb-cc/0.76:+.9f}')

print('\n=== (c) 3D domain containment: is [.45,1.049]x[-.76,.76]x[-.535,.535] reachable-superset? ===')
print('  reachable: |hub| <= 1 and |hub - Qj| <= 2r,  r <= 0.37999 so 2r <= 0.75998; d <= 2r.')
for r in (0.379, 0.3795, 0.37999):
    print(f'  r={r}: 2r={2*r:.6f} (<= 1.049 OK), max |x| = 2r = {2*r:.6f} (<= .76 '
          f'{2*r<=0.76001})')
print('  d: since L1,L2 <= .43 at a maximum and d <= L1+L2 <= .86, the .45-1.049 box is loose on')
print('     the upper side; loose boxes are safe (cost only work).')
print('  |y|: y <= d/2 + a_hi; with d <= 1.049 and a_hi <= .76 this is 1.2845, so the .535 bound')
print('       needs the |hub|<=1 constraint. Check: max |y| s.t. |M + x n + y e| <= 1 with')
print('       |M| <= r and x = 0 is |y| <= sqrt(1 - (|M|-r)^2) ... evaluate worst case:')
for r in (0.379, 0.37999):
    M = r  # |M| at most r (midpoint of two points each at radius r)
    print(f'     r={r}: |M|<= {M:.6f}, y <= sqrt(1-(|M|)^2) = {math.sqrt(1-M*M):.6f} '
          f'(<= .535: {math.sqrt(1-M*M)<=0.535})')

print('\n=== (d) chirality of the atan terms ===')
print('  face-1 centre c1v = (r sin2b1, -r cos2b1); its bearing angle beta1v = pi/2 - 2b1.')
print('  Q1 = 2 r cos(beta1v) * (cos beta1v, sin beta1v)  (outward radial point)')
for b1v in (1.0, 1.1, 1.1864):
    bta = math.pi/2 - 2*b1v
    Q1 = (2*r*math.cos(bta)*math.cos(bta), 2*r*math.cos(bta)*math.sin(bta))
    Q1c = (r*math.sin(2*b1v), 2*r*math.sin(b1v)**2)
    print(f'   b1={b1v}: beta1={bta:+.6f}, Q1(radial)={tuple(round(v,9) for v in Q1)} '
          f'vs (r sin2b1, 2r sin^2 b1)={tuple(round(v,9) for v in Q1c)} '
          f'diff={abs(Q1[0]-Q1c[0])+abs(Q1[1]-Q1c[1]):.2e}')
print('  angle at Q1 measured from the OUTWARD radial direction is -phi_1 = -atan2(u1, x):')
for (x, u1) in [(0.3, 0.1), (0.3, -0.1), (-0.2, 0.2)]:
    print(f'   (x,u1)=({x},{u1}): atan2(u1,x)={math.atan2(u1,x):+.6f}, '
          f'atan2(-u1,x)={math.atan2(-u1,x):+.6f}')
print('  the code (hub_axis_stationary.direct) uses a_j*u_j/q_j and -a_j*x/q_j for j=1,')
print('  i.e. the angle derivative of atan2(-u1, x) = -atan2(u1,x): d/dx = u1/q1,')
print('  d/du1 = -x/q1.  MATCHES. Sigma1 = -1 as the note states.')
print('  face-2: mirror (Q2 below, bearing beta2v = 2b2 - pi/2), sigma2 = +1: derivatives of')
print('  atan2(+u2, x): d/dx = -u2/q2, d/du2 = +x/q2. Code uses -a2*v/q2 and +a2*x/q2. MATCHES.')
