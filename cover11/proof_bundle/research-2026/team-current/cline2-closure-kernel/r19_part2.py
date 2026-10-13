"""R19 part 2: (i) is |y| <= .535 implied by the reachable set? (ii) A = (d/2) n at the point
where d is extreme; (iii) the Q1 bearing-angle derivation done correctly."""
import math, sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

r = 0.37999

print('=== (i) reachable |y| ===')
print('state: hub = M + x n + y e, |M| <= r, |x n + y e| = sqrt(x^2+y^2) <= |hub| + |M| <= 1 + r')
print('  crude: |y| <= 1 + r = %.6f' % (1 + r))
print('  better (x=0, hub on the unit circle, M perpendicular to e):')
print('    |hub|^2 = |M|^2 + y^2 + 2 y (M.e); with M.e = 0 (M perpendicular => M along n):')
print('    y^2 = 1 - |M|^2 <= 1 - 0 = 1   =>  |y| <= 1')
print('  with the face cap |x| <= 2r and any M with |M| <= r:')
best = 0.0
arg = None
for i in range(-200, 201):
    ye = i / 1000.0                      # y
    for j in range(-200, 201):
        xe = j / 1000.0                  # x
        for k in range(0, 101):
            Mv = r * k / 100.0
            for sgn in (1, -1):
                # worst orientation: M along e
                hx = Mv * sgn + ye                # e-component carries M and y
                hy = xe                          # n-component carries x
                if math.hypot(hx, hy) <= 1 + 1e-12 and abs(xe) <= 2 * r + 1e-12:
                    if abs(ye) > best:
                        best, arg = abs(ye), (xe, ye, Mv)
print(f'  numeric sup |y| over the reachable set (coarse): {best:.4f}  at {arg}')
print('  => the geometric constraint alone does NOT give |y| <= .535')

print('\n=== (ii) A = (d/2) n at the extreme separation d ===')
for (b1, b2) in [(1.0, 1.0), (1.1864, 1.0), (1.0, 1.1864), (1.1864, 1.1864)]:
    Q1 = (r * math.sin(2 * b1), 2 * r * math.sin(b1) ** 2)
    Q2 = (r * math.sin(2 * b2), -2 * r * math.sin(b2) ** 2)
    dv = (Q1[0] - Q2[0], Q1[1] - Q2[1])
    d = math.hypot(*dv)
    e = (dv[0] / d, dv[1] / d)
    n = (e[1], -e[0])
    A = (r * (math.sin(b1) ** 2 + math.sin(b2) ** 2),
         r * (math.sin(b2) * math.cos(b2) - math.sin(b1) * math.cos(b1)))
    lhs = (A[0] - (d / 2) * n[0], A[1] - (d / 2) * n[1])
    print(f'  b1={b1:.4f} b2={b2:.4f}: d={d:.9f}  |A|={math.hypot(*A):.9f}  '
          f'd/2={d/2:.9f}  residual=({lhs[0]:+.2e},{lhs[1]:+.2e})')

print('\n=== (iii) Q1 bearing angle done correctly ===')
b1 = 1.05
cx, cy = r * math.sin(2 * b1), -r * math.cos(2 * b1)
print(f'  c1 = (r sin2b1, -r cos2b1) = ({cx:.9f},{cy:.9f}); |c1| = {math.hypot(cx,cy):.9f} = r')
print(f'  its bearing angle = atan2(cy, cx) = {math.atan2(cy, cx):+.9f} rad'
      f' ; pi/2 - 2b1 = {math.pi/2 - 2*b1:+.9f}')
Q1 = (r * math.sin(2 * b1), 2 * r * math.sin(b1) ** 2)
print(f'  Q1 = (r sin2b1, 2r sin^2 b1) = ({Q1[0]:.9f},{Q1[1]:.9f}); |Q1| = {math.hypot(*Q1):.9f}')
print(f'  Q1 in the e/n frame relative to M: u1 = y - d/2 with Q1 = M + (d/2) e')
print('  => Q1 = M + (d/2) e exactly, so at Q1 one has x=0, y=+d/2, u1=y-d/2=0, q1 = 0^2+0^2 = 0')
print('  => Q1 is the POLE (L1=0) of the axis chart, as expected: the chart is centred on Q1.')
print('  (my earlier "radial point 2r cos(beta1v)(...)" formula used the wrong face;')
print('   Q1 is a point of the OTHER face circle, at distance 2r cos(b1 + A) ... see below)')
for A in (0.0, 0.5, 1.0):
    X = (r * (math.sin(2 * b1) + math.sin(2 * A)), r * (math.cos(2 * A) - math.cos(2 * b1)))
    print(f'   face-1 arc point A={A}: ({X[0]:.9f},{X[1]:.9f}) |X|={math.hypot(*X):.9f} '
          f'|X-Q1|={math.hypot(X[0]-Q1[0], X[1]-Q1[1]):.9f} |X-Q2|={math.hypot(X[0]-Q2[0], X[1]-Q2[1]):.9f}')
