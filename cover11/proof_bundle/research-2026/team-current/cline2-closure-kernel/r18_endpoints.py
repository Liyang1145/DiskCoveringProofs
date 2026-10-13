"""R18 part 4: endpoint closure - check WHICH constraint is active at the arc ends, and whether
the parameter-box boundary b_j = acos(r) (i.e. cos b_j = r) lies on a named bound.

Constraints on the face arc (j=0, A = b1-delta):
  g_wedge  : A >= 0, B >= 0
  g_norm   : |c|^2 <= (1-r)^2
  g_faceop : |c - c_opp|^2 <= r^2
  parameter: b1 in [1, acos r], i.e. cos b1 >= r
"""
import math, sys

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
r = 0.3795
b_hi = math.acos(0.375)   # the box upper bound for b (from the certificate domain)
print(f'r = {r}, b in [1, {b_hi:.9f}] (box), cos(b) >= r required')

print('\nactive-constraint scan over the face arc j=0 (A from 0 to pi):')
print(f'{"A":>8} {"|c|":>10} {"1-r":>9} {"norm=1-r?":>10} {"|c-c1|":>10} {"|c-c2|":>10} '
      f'{"b1":>8} {"cos b1=r?":>10}')
for A in (0.0, 0.005, 0.05, 0.2, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, math.pi):
    for b1 in (1.0, 1.1, b_hi):
        pass
    break

for b1v in (1.0, 1.1, b_hi):
    A = 0.0
    v = r * (math.sin(2 * b1v) + math.sin(2 * A))
    t = r * (math.cos(2 * A) - math.cos(2 * b1v))
    c1 = (r * math.sin(2 * b1v), -r * math.cos(2 * b1v))
    c2 = (r * math.sin(2 * b1v), r * math.cos(2 * b1v))
    print(f'  A=0, b1={b1v:.6f}: |c|={math.hypot(v,t):.9f} (1-r={1-r:.9f}) '
          f'|c-c1|={math.hypot(v-c1[0],t-c1[1]):.9f} |c-c2|={math.hypot(v-c2[0],t-c2[1]):.9f} '
          f'cos b1={math.cos(b1v):.9f} vs r={r:.9f}')

print('\nkey question: at A=0 (arc start) which named constraint is active?')
for b1v in (1.0, 1.1, b_hi, 1.1863995522992576):
    v = r * math.sin(2 * b1v)
    t = -r * math.cos(2 * b1v)
    nrm = math.hypot(v, t)
    print(f'  b1={b1v:.9f}: |c|={nrm:.9f}  r={r:.9f}  |c|==r (face centre): '
          f'{abs(nrm-r) < 1e-12}   |c|==1-r: {abs(nrm-(1-r)) < 1e-12}  '
          f'cos b1>=r: {math.cos(b1v) >= r}')

print('\n=> at A=0 the point is the FACE CENTRE c1, |c1| = r = 0.3795, NOT 1-r = 0.6205.')
print('   So A=0 is a wedge endpoint (g_wedge active), handled by C861, not by C863.')
print()
print('and at the box edge b_j = acos(r): cos b_j = r exactly -> that is the')
print('   "inradius / q <= r^2" boundary, i.e. the parameter-box edge, which no C86x')
print('   certificate above lists as an endpoint class. Check whether it is reachable as a')
print('   legal arc endpoint:')
b_edge = math.acos(0.375)
for A in (0.0, 0.01, 0.05, 0.2, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0):
    v = r * (math.sin(2 * b_edge) + math.sin(2 * A))
    t = r * (math.cos(2 * A) - math.cos(2 * b_edge))
    nrm = math.hypot(v, t)
    c2 = (r * math.sin(2 * b_edge), r * math.cos(2 * b_edge))
    print(f'  A={A:5.2f}: |c|={nrm:.4f} (norm active: {abs(nrm-(1-r))<1e-6}), '
          f'|c-c2|={math.hypot(v-c2[0],t-c2[1]):.4f} (faceop active: '
          f'{abs(math.hypot(v-c2[0],t-c2[1])-r)<1e-6})')
