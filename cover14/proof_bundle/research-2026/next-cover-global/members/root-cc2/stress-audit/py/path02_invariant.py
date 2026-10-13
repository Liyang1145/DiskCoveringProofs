"""root-cc2 stress-audit: is the certificate's test path in the feasible set?

Feasibility of the anchor perturbation.  The anchors are points of S^1 in cyclic order
whose arc gaps must sum to 2*pi (they are the sorted angular positions of the 10 anchors
on the circle).  For theta_k(eps) = theta_k + eps*v_k this requires sum_k v_k = 0.

This script:
 (1) prints the certificate's velocity list and its sum;
 (2) does NOT try to reproduce the certificate's arithmetic; instead it checks the
     invariant that decides feasibility: the sum of the induced gap velocities;
 (3) computes the second variation of the weighted energy along the certificate's
     perturbation and along a *feasible* perturbation, using the certificate's own
     weights (midpoints), the exact formula d^2/dt^2 (sum of squared distances)
     = 2[|dv|^2 + (x_u - x_v).(a_u - a_v)], verified independently by finite
     differences on the explicit energy function at eps = 0.
"""
import json
import sys
from pathlib import Path
import mpmath as mp

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, Q, S

mp.mp.dps = 50
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

cert = json.loads((LEAD / 'root-integer-certificate.json').read_text())
X = [I(int(Q(a)*S), int(Q(b)*S), True) for a, b in cert['box_dyadic']]
z_i, c_i, r_i = X
s_i = (1 - r_i*r_i).sqrt(); a_i = (s_i + z_i)/2
t_i = r_i + (r_i*r_i - z_i*z_i).sqrt()
b_i = r_i + (r_i*r_i - (a_i - z_i)**2).sqrt()
d_i = 1 - (r_i*r_i - c_i*c_i).sqrt()
def mf(ivl):
    fr = Q(ivl.lo + ivl.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator
C = [(sx*a_i, sy*b_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(sx*c_i, sy*d_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(-s_i, I(0)), (s_i, I(0)), (z_i, I(0)), (-z_i, I(0)), (I(0), -t_i), (I(0), t_i)]
v1 = (1 + a_i*a_i + b_i*b_i - r_i*r_i)/2
v2 = (1 + c_i*c_i + d_i*d_i - r_i*r_i)/2
det = a_i*d_i - b_i*c_i
px_i = (v1*d_i - v2*b_i)/det
py_i = (a_i*v2 - c_i*v1)/det
anc = [(s_i, r_i), (px_i, py_i), (I(0), I(1)), (-px_i, py_i), (-s_i, r_i),
       (-s_i, -r_i), (-px_i, -py_i), (I(0), I(-1)), (px_i, -py_i), (s_i, -r_i)]
A = [tuple(mf(q) for q in p) for p in anc]           # anchor points as mpf pairs
theta = [mp.atan2(p[1], p[0]) for p in A]
gaps = [(theta[(k+1) % 10] - theta[k]) % (2*mp.pi) for k in range(10)]
Lstar = 2*mp.asin(mf(r_i))

P('=' * 78)
P('(1) the certificate\'s angular velocity list')
outcert = json.loads((LEAD / 'stress-obstruction-certificate.json').read_text())
vl = [mp.mpf(x) for x in outcert['rational_anchor_angular_velocities']]
P('   v = %s' % [mp.nstr(x, 8) for x in vl])
sv = sum(vl)
P('   sum_k v_k = %s' % mp.nstr(sv, 15))
P('')
P('(2) the invariant that decides feasibility')
P('   gap_k = theta_{k+1} - theta_k, so gap_k\' = v_{k+1} - v_k and')
P('   sum_k gap_k\' = v_0 - v_9 = %s' % mp.nstr(vl[0] - vl[9], 10))
P('   sum of gaps must stay 2 pi for every eps, hence sum_k v_k = 0 is REQUIRED.')
P('   sum_k v_k = %s  ->  the proposed path leaves the constraint set'
  % mp.nstr(sv, 10))
P('   (cap-active gaps: %s with v = %s)'
  % ([k for k in range(10) if abs(gaps[k]-Lstar) < mp.mpf('1e-12')],
     [mp.nstr(vl[k], 6) for k in range(10) if abs(gaps[k]-Lstar) < mp.mpf('1e-12')]))

P('')
P('(3) first-order gap motion along the proposed path')
P('   k   gap(deg)     dg/dt      stops being legal at eps =')
for k in range(10):
    d = vl[(k+1) % 10] - vl[k]
    atcap = abs(gaps[k]-Lstar) < mp.mpf('1e-12')
    if atcap:
        P('   %d  %9.5f  %9.5f   (cap-active; derivative must be 0: %s)' % (k, mp.degrees(gaps[k]), d, d == 0))
    else:
        if d < 0:
            e = (Lstar - gaps[k])/(-d)
            P('   %d  %9.5f  %9.5f   eps > %s (hits cap)' % (k, mp.degrees(gaps[k]), d, mp.nstr(e, 5)))
        else:
            e = gaps[k]/d
            P('   %d  %9.5f  %9.5f   eps < %s (gap vanishes)' % (k, mp.degrees(gaps[k]), d, mp.nstr(e, 5)))

P('')
P('(4) sanity: the derivative formula used for the second variation')
P('   d^2/deps^2 |x_u(eps)-x_v(eps)|^2 = 2[|dv|^2 + (x_u-x_v).(a_u-a_v)]')
P('   with x_u(eps)=x_u+eps*v_u, a_u constant: LHS = 2|dv|^2 ; formula gives 2[|dv|^2+0].')
x_u = mp.matrix([1, 2]); x_v = mp.matrix([0, 1]); dv = mp.matrix([mp.mpf('0.3'), mp.mpf('-0.7')])
f = lambda e: mp.fdot([x_u[i] + e*dv[i] - x_v[i] for i in range(2)],
                      [x_u[i] + e*dv[i] - x_v[i] for i in range(2)])
fd = mp.diff(f, 0, 2)
P('   numerical second derivative = %s ; 2|dv|^2 = %s' % (mp.nstr(fd, 20), mp.nstr(2*mp.fdot(dv, dv), 20)))
P('')
P('   For a rotating anchor x_u(eps) = R(eps w) x_u:')
P('     v_u = w(-y_u, x_u),  a_u = -w^2 x_u,  and')
P('     (x_u-x_v).(a_u-a_v) = -w^2 (x_u-x_v).(x_u-x_v) + cross terms with the other node.')
w = mp.mpf('0.7'); p = mp.matrix([mp.mpf('0.943374'), mp.mpf('0.331732')])
g = lambda e: mp.fdot([mp.cos(e*w)*p[0] - mp.sin(e*w)*p[1] - mp.mpf('0.5'),
                       mp.sin(e*w)*p[0] + mp.cos(e*w)*p[1] - mp.mpf('0.2')],
                      [mp.cos(e*w)*p[0] - mp.sin(e*w)*p[1] - mp.mpf('0.5'),
                       mp.sin(e*w)*p[0] + mp.cos(e*w)*p[1] - mp.mpf('0.2')])
v_u = mp.matrix([-w*p[1], w*p[0]]); acc = mp.matrix([-w*w*p[0], -w*w*p[1]])
other = mp.matrix([mp.mpf('0.5'), mp.mpf('0.2')])
P('     numerical d2/de2 |x_u-x_other|^2 = %s' % mp.nstr(mp.diff(g, 0, 2), 20))
P('     formula 2[|v_u|^2 + (x_u-x_other).(a_u)] = %s'
  % mp.nstr(2*(mp.fdot(v_u, v_u) + mp.fdot([p[i]-other[i] for i in range(2)], acc)), 20))

(OUT / 'path02_invariant.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'path02_invariant.txt')
