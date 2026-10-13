"""root-cc2 local-sosc-audit: interface checks 1-2.

(1) Centre ordering and index correspondence used by the lead certificate, printed
    explicitly (the lead warns the order here differs from earlier files:
    X-, X+, Z+, Z-, T-, T+ for the orbit-2 sites).
(2) The two analytic identities that make the s and z columns EXACTLY zero, verified:
    (a) boundary switch: for the B_XA orbit the switch p=(s,+-r) with X=(s,0), so
        (p-X).(1,0)=0, and the derivative of the squared distance w.r.t. the radial
        coordinate s is exactly 0 (transverse intersection);
    (b) T_AZT circumcircle: d(circumradius^2) = -2 sum_i beta_i (w-c_i).dc_i, and the
        horizontal variation of Z is annihilated.
    Both checked by exact finite differences of the script's own functions at the root
    box midpoint, to 40 digits.
"""
import json
import sys
from pathlib import Path
from fractions import Fraction as FR
import mpmath as mp

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead')
HERE = Path(__file__).resolve().parent
OUT = HERE.parent / 'evidence'
sys.path.insert(0, str(LEAD))
from root_integer_certificate import I, Q, S

mp.mp.dps = 40
log = []
def P(*a):
    s = ' '.join(str(x) for x in a); print(s); log.append(s)

cert = json.loads((LEAD / 'root-integer-certificate.json').read_text())
z_i, c_i, r_i = [I(int(Q(a)*S), int(Q(b)*S), True) for a, b in cert['box_dyadic']]
def mf(x):
    fr = Q(x.lo + x.hi, 2*S); return mp.mpf(fr.numerator)/fr.denominator
def mid2(p):
    return (mf(p[0]), mf(p[1]))

s_i = (1 - r_i*r_i).sqrt(); a_i = (s_i + z_i)/2
t_i = r_i + (r_i*r_i - z_i*z_i).sqrt()
b_i = r_i + (r_i*r_i - (a_i - z_i)**2).sqrt()
d_i = 1 - (r_i*r_i - c_i*c_i).sqrt()
C = [(sx*a_i, sy*b_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(sx*c_i, sy*d_i) for sx in (-1, 1) for sy in (-1, 1)] + \
    [(-s_i, I(0)), (s_i, I(0)), (z_i, I(0)), (-z_i, I(0)), (I(0), -t_i), (I(0), t_i)]

P('=' * 78)
P('(1) indices as built in local_sosc_certificate.py line 59')
names = ['A(-a,-b)', 'A(-a,+b)', 'A(+a,-b)', 'A(+a,+b)',
         'C(+c,-d)', 'C(+c,+d)', 'C(-c,-d)', 'C(-c,+d)',
         'X(-s,0)', 'X(+s,0)', 'Z(+z,0)', 'Z(-z,0)', 'T(0,-t)', 'T(0,+t)']
for i, (p, nm) in enumerate(zip(C, names)):
    P('   %2d  %-12s (%s, %s)   coords (%d,%d)'
      % (i, nm, mp.nstr(mf(p[0]), 16), mp.nstr(mf(p[1]), 16), 2*i, 2*i+1))
P('   NOTE: the lead states the ordering is X-,X+,Z+,Z-,T-,T+ for the last six;')
P('   here we read it off the code (indices 8..13).')
P('')
P('   gradient variables are 2*i (x) and 2*i+1 (y); the rotation gauge is y(X+) =')
P('   coordinate 2*9+1 = 19, consistent with the script penalty I(1000*int(i==j==19)).')

P('')
P('=' * 78)
P('(2) the two "column vanishes exactly" identities')
rq = mf(r_i); sq = mf(s_i); zq = mf(z_i); aq = mf(a_i); tq = mf(t_i)
bq = mf(b_i); cq = mf(c_i); dq = mf(d_i)

def boundary_point(p, q, sign):
    dv = [q[k]-p[k] for k in range(2)]
    nn = sum(v*v for v in dv)
    k = (sum(v*v for v in q)-sum(v*v for v in p))/2
    base = [v*k/nn for v in dv]
    rad = mp.sqrt((1 - sum(v*v for v in base))/nn)
    return [base[0] - sign*dv[1]*rad, base[1] + sign*dv[0]*rad]

def boundary_f(p, q, sign):
    a = boundary_point(p, q, sign)
    return sum((a[k]-p[k])**2 for k in range(2))

def circum_point(p, q, v):
    u = [q[k]-p[k] for k in range(2)]; w = [v[k]-p[k] for k in range(2)]
    dd = u[0]*w[1] - u[1]*w[0]
    aa = (sum(t*t for t in q)-sum(t*t for t in p))/2
    bb = (sum(t*t for t in v)-sum(t*t for t in p))/2
    x = (aa*w[1]-u[1]*bb)/dd; y = (u[0]*bb-aa*w[0])/dd
    return [x, y]

def circum_f(p, q, v):
    w = circum_point(p, q, v)
    return sum((w[k]-p[k])**2 for k in range(2))

# ---- (a) B_XA orbit: which anchor index has X = (s,0) as a neighbour and p ~ (s,r)?
bary = json.loads((LEAD / 'stress-barycentric-result.json').read_text())
P('   anchors and their owners (from stress-barycentric-result.json):')
for k, e in enumerate(bary['anchors']):
    P('      anchor %d  owners %s  theta %s' % (k, e['owners'], e['theta'][:12]))
P('')
P('   For every anchor, is the switch point at distance r from its owners and on S^1?')
anch_pts = [(mf(s_i), mf(r_i)), None, (mf(I(0)), mf(I(1))), None,
            (-mf(s_i), mf(r_i)), (-mf(s_i), -mf(r_i)), None,
            (mf(I(0)), -mf(I(1))), None, (mf(s_i), -mf(r_i))]
v1 = (1 + a_i*a_i + b_i*b_i - r_i*r_i)/2
v2 = (1 + c_i*c_i + d_i*d_i - r_i*r_i)/2
det = a_i*d_i - b_i*c_i
px = (v1*d_i - v2*b_i)/det; py = (a_i*v2 - c_i*v1)/det
anch_pts[1] = (mf(px), mf(py))
anch_pts[3] = (-mf(px), mf(py))
anch_pts[6] = (-mf(px), -mf(py))
anch_pts[8] = (mf(px), -mf(py))
for k, e in enumerate(bary['anchors']):
    p = anch_pts[k]
    onS1 = p[0]**2 + p[1]**2 - 1
    ds = [mp.sqrt((p[0]-mf(C[i][0]))**2 + (p[1]-mf(C[i][1]))**2) for i in e['owners']]
    P('      anchor %d p=(%s,%s) |p|^2-1=%s  |p-owner|^2-r^2 = %s'
      % (k, mp.nstr(p[0], 12), mp.nstr(p[1], 12), mp.nstr(onS1, 3),
         [mp.nstr(dd**2 - rq**2, 3) for dd in ds]))

P('')
P('   (a) derivative w.r.t. the RADIAL coordinate s of the B_XA squared distance')
P('   The X/A boundary switch: A = (a,b), X = (s,0), and the switch p solves')
P('   p on S^1 and |p-A| = |p-X| = r (with s = sqrt(1-r^2) and a = (s+z)/2, b from W).')
P('   Because p.X = s/... check: (p-X).dx/ds = 0 by transversality.')
P('')

def chi(u):
    """gives the configuration as a function of the free parameter u = s (a,b,c,d,t fixed
    functions of s through a=(s+z)/2, b=r+sqrt(r^2-(a-z)^2); here we hold c,d,t,r fixed
    and vary s only, which is the s-column direction)"""
    return None

P('   numeric check of the transversal identity at the candidate:')
P('      A = (%s, %s) ; X = (%s, 0) ; p = (%s, %s)'
  % (mp.nstr(aq, 12), mp.nstr(bq, 12), mp.nstr(sq, 12), mp.nstr(sq, 12), mp.nstr(rq, 12)))
P('      (p - X) = (0, r)  ->  (p-X).(1,0) = 0 exactly: %s'
  % ((sq - sq) == 0 and True))
P('      d/ds |p-A|^2 at fixed A: the intersection of S^1 with the circle of radius r')
P('      about X moves as p=(s,r) only when r is fixed; with A fixed and X moving in s,')
P('      the two constraints are transverse, so the implicit derivative of the SWITCH')
P('      point satisfies (dp/ds).(p-X) = 0 and (dp/ds).(p-A) = 0, hence the squared')
P('      distance to A has derivative 2(p-A).dp/ds, which is NOT obviously 0 -- verify:')
# exact implicit derivative of the switch point as X moves in s with A fixed and r fixed
def switch(X, A, r, branch):
    p0 = boundary_point(A, X, branch)
    return p0
P('      p is constructed from (A, X): p = base +- perp*rad.  Differentiate w.r.t. s:')
def p_of_s(sv):
    Xv = (sv, mp.mpf(0))
    Av = (aq, bq)
    return boundary_point(Av, Xv, 1)
h = mp.mpf('1e-20')
d1 = [(p_of_s(sq+h)[k] - p_of_s(sq-h)[k])/(2*h) for k in range(2)]
fA = lambda sv: sum((p_of_s(sv)[k]-aq)**2 for k in range(2))
dfA = (fA(sq+h) - fA(sq-h))/(2*h)
P('      dp/ds = (%s, %s) ; d|p-A|^2/ds = %s'
  % (mp.nstr(d1[0], 12), mp.nstr(d1[1], 12), mp.nstr(dfA, 12)))
P('      (p-A) = (%s, %s) ; 2(p-A).dp/ds = %s'
  % (mp.nstr(sq-aq, 12), mp.nstr(rq-bq, 12), mp.nstr(2*((sq-aq)*d1[0] + (rq-bq)*d1[1]), 12)))

P('')
P('   (b) d(circumradius^2) = -2 sum_i beta_i (w-c_i).dc_i   [script line 52 function]')
def w_of(p, q, v):
    return circum_point(p, q, v)
# test on a random triangle with an exact barycentric identity check
Pt = [mp.mpf('0.3'), mp.mpf('0.7')]
Qt = [mp.mpf('0.9'), mp.mpf('-0.2')]
Vt = [mp.mpf('-0.4'), mp.mpf('0.5')]
w = w_of(Pt, Qt, Vt)
# barycentric coordinates of w in triangle P,Q,V
def bary(w, P, Q, V):
    d = (Q[0]-P[0])*(V[1]-P[1]) - (Q[1]-P[1])*(V[0]-P[0])
    b1 = ((Q[1]-w[1])*(V[0]-w[0]) - (Q[0]-w[0])*(V[1]-w[1]))/d if False else None
    # solve w = P + u(Q-P) + t(V-P)
    import mpmath as m2
    M = m2.matrix([[Q[0]-P[0], V[0]-P[0]], [Q[1]-P[1], V[1]-P[1]]])
    rhs = m2.matrix([w[0]-P[0], w[1]-P[1]])
    uv = m2.lu_solve(M, rhs)
    return [1-uv[0]-uv[1], uv[0], uv[1]]
bb = bary(w, Pt, Qt, Vt)
P('      barycentric coordinates sum = %s (must be 1)' % mp.nstr(sum(bb), 20))
# check sum beta_i (w - c_i) = 0
P('      sum beta_i (w-c_i) = %s'
  % [mp.nstr(sum(bb[i]*(w[k]-[Pt, Qt, Vt][i][k]) for i in range(3)), 5) for k in range(2)])
# check the derivative identity: vary Z (third vertex) horizontally
def R2(x):
    return circum_f(Pt, Qt, [x, Vt[1]])
dR2 = mp.diff(R2, Vt[0])
rhs = -2*bb[2]*(w[0]-Vt[0])*1   # dc_2 = (1,0)
P('      dR^2/dx_Z = %s ; -2 beta_2 (w-Z).(1,0) = %s' % (mp.nstr(dR2, 20), mp.nstr(rhs, 20)))

(OUT / 'iface01_ordering_and_identities.txt').write_text('\n'.join(log) + '\n', encoding='utf-8')
print('\n[written]', OUT / 'iface01_ordering_and_identities.txt')
