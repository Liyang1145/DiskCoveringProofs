"""R18 correction: exact evaluation of the code's Taylor expression, and the endpoint geometry."""
import sys
sys.stdout.reconfigure(encoding='utf-8', errors='replace')

f = lambda T: -0.5 * (T - 2.175) ** 2 + 10.0
mid = 2.20
dstar = 2.175
print('parabola f(T) = -0.5 (T-2.175)^2 + 10')
print(f'  f(mid=2.20) = {f(mid):.12f}')
print(f'  f(d*=2.175) = {f(dstar):.12f}')
print(f'  (m-d*)^2    = {(mid-dstar)**2:.12f}')
print(f'  f\'\'(xi) = -1 exactly')
print()
print('code line 29:  centered = am.v - a.h*(x3-mid)^2/2')
print('  am.v    = f(mid) = %.12f' % f(mid))
print('  a.h     = interval bound on f\'\' ; the code keeps boxes with a.h.b <= 0, so a sound')
print('            centred value uses a.h = lower endpoint = -1 (more negative => safer direction)')
for hval, tag in [(-1.0, 'a.h = -1 (exact f\'\')'), (-1.0, 'a.h = a.h.a with a.h.b<=0 -> at most -1')]:
    centered = f(mid) - hval * (mid - dstar) ** 2 / 2
    print(f'  a.h = {hval:+.3f}: centered = {centered:.12f}   ({tag})')
print()
print('exact identity about the stationary point:  f(m) = f(d*) + 0.5 f\'\'(xi)(m-d*)^2')
print(f'  9.9996875 + 0.5*(-1)*(0.000625) = {9.9996875 + 0.5*(-1)*0.000625:.12f}')
print(f'  => code f(d*) = f(m) - 0.5 f\'\'(xi)(m-d*)^2 = {9.9996875 - 0.5*(-1)*0.000625:.12f}')
print('  my earlier 9.9993750 came from using |f\'\'| with a sign flip - arithmetically wrong.')
print()
print('=> R18 (1) WITHDRAWN: the Taylor block is algebraically correct.')

print()
print('=' * 70)
print('(4) endpoint geometry: A = 0 on the delta-arc')
print('=' * 70)
import math
for r in (0.379, 0.3795, 0.37999):
    for b1 in (1.0, 1.1, math.acos(0.375)):
        Q1 = (r * math.sin(2 * b1), 2 * r * math.sin(b1) ** 2)
        Di = (r * math.sin(2 * b1), -r * math.cos(2 * b1))
        print(f'  r={r:.5f} b1={b1:.6f}:')
        print(f'     |Q1| = {math.hypot(*Q1):.9f}   (2 r sin^2 b1 = {Q1[1]:.9f})')
        print(f'     |Di| = {math.hypot(*Di):.9f}   (r = {r})')
        print(f'     Q1 == Di ? {abs(Q1[0]-Di[0])<1e-15 and abs(Q1[1]-Di[1])<1e-15}')
print()
print('  so the A=0 point is Q1 = (r sin2b1, 2r sin^2 b1), NOT the face centre Di.')
print('  my earlier scan plotted t = -r cos 2b1 = the centre; corrected here per the lead.')
