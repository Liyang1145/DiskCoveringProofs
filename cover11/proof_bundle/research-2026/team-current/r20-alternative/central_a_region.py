"""central_a_region.py  (r20-alternative; sole write, no child)

Lead obligation: with the NOMINAL rings fixed, study the b-eliminated 2D a-region
    A(a) = K_A  cap  { b-fiber nonempty },  b-fiber = K_B cap D_0(a) cap D_4(a) cap B_open(0,rho),
and decide whether `a` can be removed by direct quantifier elimination / finite boundary
candidates.  Deliver: minimal polynomial variables / degree / domain / degeneracies; test
convexity; try an exact counterexample.

  [S] sympy rationalisation: with the rings fixed the only non-constant radicals are the two
      central circle branches k_i(a) = sqrt(r^2 - |a-c_i|^2/4); after clearing the positive
      denominators s_i = |a-c_i| every condition is POLYNOMIAL in (x,y,k0,k1,s0,s1) with
      k_i^2 = r^2 - s_i^2/4 and s_i^2 = |a-c_i|^2.
  [E] EXACT rational counterexample to convexity (the crescent shape the clauses inherit).
  [N] bounded nominal probe (numeric; bounded, no grid).
"""
import json
import itertools
from fractions import Fraction as F
from pathlib import Path

import sympy as sp

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
rep = {'kind': 'structural study of the 2D a-region after b-elimination (nominal rings fixed)'}

# ======================================================================================
# [S] rationalised a-conditions
# ======================================================================================
x, y, r = sp.symbols('x y r', positive=True)
a = sp.Matrix([x, y])
c0 = sp.Matrix([sp.symbols('c0x'), sp.symbols('c0y')])
c4 = sp.Matrix([sp.symbols('c4x'), sp.symbols('c4y')])
pk = sp.Matrix([sp.symbols('p1'), sp.symbols('p2')])
k0, k1 = sp.symbols('k0 k1', positive=True)
s0, s1 = sp.symbols('s0 s1', positive=True)
gens = (x, y, k0, k1, s0, s1)
DOT = lambda P, Q: sp.expand(P.dot(Q))
m0, m4 = (a + c0) / 2, (a + c4) / 2
u0 = sp.Matrix([-(c0 - a)[1], (c0 - a)[0]])
u1 = sp.Matrix([-(c4 - a)[1], (c4 - a)[0]])
rel = [(k0**2, r**2 - s0**2 / 4), (k1**2, r**2 - s1**2 / 4)]
L0 = sp.expand(((DOT(m0 - pk, m0 - pk) + k0**2) * s0 + 2 * k0 * DOT(m0 - pk, u0)).subs(rel))
L1 = sp.expand(((DOT(m4 - pk, m4 - pk) + k1**2) * s1 + 2 * k1 * DOT(m4 - pk, u1)).subs(rel))
L01 = sp.expand(((DOT(m0 - m4, m0 - m4) + k0**2 + k1**2) * s0 * s1
                 + 2 * k0 * DOT(m0 - m4, u0) * s1 - 2 * k1 * DOT(m0 - m4, u1) * s0
                 - 2 * k0 * k1 * DOT(u0, u1)).subs(rel))
cross = lambda P, Q: sp.expand(P[0] * Q[1] - P[1] * Q[0])
Xc = sp.expand((cross(m0 - m4, pk - m0) * s0 * s1
                + k0 * cross(u0, pk - m0) * s1 + k0 * cross(m0 - m4, u0) * s1
                - k1 * cross(u1, pk - m0) * s0 - k0 * k1 * cross(u1, u0)).subs(rel))
rep['S1_variables'] = ('a=(x,y) in K_A (convex ring-only disk intersection); the only '
                       'non-constant radicals are k_i(a)=sqrt(r^2-|a-c_i|^2/4), i=0,4; with '
                       's_i=|a-c_i| the relations are k_i^2=r^2-s_i^2/4, s_i^2=|a-c_i|^2, s_i>0')
rep['S2_q_form'] = ('q_i(a) = (a+c_i)/2 + k_i * perp(c_i-a)/|c_i-a|; branch = side of the '
                    'reference b-point (orientation preserved; the C894-retracted half-plane '
                    'direction is NOT used)')
def tdeg(e, gs):
    """total degree in gs, tolerant of non-polynomial dependence in other generators"""
    e = sp.expand(e)
    tot = 0
    for g in gs:
        try:
            tot += int(sp.degree(e, g))
        except Exception:
            tot += 0
    return tot


rep['S3_degrees_cleared_(x,y,k0,k1,s0,s1)'] = {
    'a2*s0    = |q0-p|^2 s0': str(tdeg(L0, (x, y, k0, s0))),
    'b2*s1    = |q4-p|^2 s1': str(tdeg(L1, (x, y, k1, s1))),
    'c2*s0*s1 = |q0-q4|^2 s0 s1': str(tdeg(L01, (x, y, k0, k1, s0, s1))),
    'X*s0*s1  = cross s0 s1': str(tdeg(Xc, (x, y, k0, k1, s0, s1)))}
rep['S4_rationalisation'] = (
    'a2=L0/s0, b2=L1/s1, c2=L01/(s0 s1), X=Xc/(s0 s1), all s_i>0. Then max(a2,b2,c2)>4r^2 <=> '
    'max(L0 s1, L1 s0, L01) > 4 r^2 s0 s1 (degree <=4); the acuteness comparisons multiply the '
    'same way; the acute-product clause a2 b2 c2 > 4 r^2 X^2 becomes L0 L1 L01 > 4 r^2 Xc^2 '
    '(degree <=10). So every a-condition is POLYNOMIAL in (x,y,k0,k1,s0,s1) after clearing '
    'positive denominators, subject to two quadratic relations: quantifier elimination exists in '
    'principle, at the price of a 1-dimensional boundary (see [E]).')
rep['S5_domain_and_degeneracies'] = [
    'domain: a in K_A = B(0,1-r) cap cap_{j in {4..8}} B(p_j,r) (convex) with k_i >= 0 and the '
    'branch side sign det(c_i-a, b_ref-a) != 0',
    'k_i = 0 <=> |a-c_i| = 2r: the two circle branches coalesce; the rho-argument does NOT exclude '
    'this boundary (rho >= r does not contradict rho <= r) -- such tuples are excluded by the '
    'STRICT G bound instead (q_near = q_far = m)',
    's_i = 0 <=> a = c_i: central face triangle degenerates (circumradius undefined)',
    'branch failure: det(c_i-a, b_ref-a) = 0 (a collinear with c_i and b_ref)',
    'loss region: the single-disk clause is EXACT only where K_B misses the distal disk (a '
    'certified (H2) box); outside it the clause set changes',
    'the clauses contain crescent-type "exactly one of two disks" parts, which are curved (see [E]): '
    'no finite POINT candidate set decides the region']

# ======================================================================================
# [E] exact rational counterexample to convexity
# ======================================================================================
def g(p, q, rr):
    return (p[0] - q[0])**2 + (p[1] - q[1])**2 - rr**2


rE = F(1)
qE, qE2 = (F(0), F(4, 5)), (F(0), -F(4, 5))
pts = {'q_plus': qE, 'q_minus': qE2, 'midpoint': (F(0), F(0))}
tab = {}
for name, p in pts.items():
    gg = (g(p, qE, rE), g(p, qE2, rE))
    tab[name] = {'g_plus': str(gg[0]), 'g_minus': str(gg[1]), 'in_crescent': gg[0] * gg[1] <= 0}
rep['E_exact_convexity_counterexample'] = {
    'data': ("r=1, A=(-3/5,0), C=(3/5,0); the two radius-1 circle centres through A,C are "
             "q=(0,4/5), q'=(0,-4/5): |q-A|=|q-C|=|q'-A|=|q'-C|=1 exactly"),
    'readings': tab,
    'verdict': ("q and q' are crescent points ((g_plus,g_minus)=(-1,39/25) resp. (39/25,-1)); "
                "their midpoint (0,0) has both g=-9/25<0, i.e. lies in the OPEN lens which the "
                "crescent excludes.  Crescent is NOT convex -- exactly, rational data."),
    'consequence': ("clauses of this shape appear verbatim in the b-fiber relaxation (H1-H6: "
                    "'in exactly one of two disks', two moving disks disjoint, min-norm vs the "
                    "open norm ball). Hence the a-region is a Boolean combination of CURVED "
                    "pieces: the boundary is 1-dimensional; no finite set of POINT candidates "
                    "decides it (3-element witnesses alone cannot make `a` finite).")}

# ======================================================================================
# [N] bounded nominal probe
# ======================================================================================
import mpmath as mp
mp.mp.dps = 50
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(v[0]), 10**17), F(int(v[1]), 10**17)) for v in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
FAN_A, FAN_B, CENTRAL = [4, 5, 6, 7, 8], [0, 1, 2, 3], [0, 4]
R_UB = F(3799838531198387090485182, 10**25)
Mp = lambda fr: mp.mpf(fr.numerator) / mp.mpf(fr.denominator)
ring = [mp.matrix([Mp(p[0]), Mp(p[1])]) for p in [Pf[i] for i in NEW2RAW_RINGS]]
rI = Mp(R_UB)
hA = mp.matrix([Mp(Pf[0][0]), Mp(Pf[0][1])])
hB = mp.matrix([Mp(Pf[2][0]), Mp(Pf[2][1])])
nrm = lambda u: mp.sqrt(u[0]**2 + u[1]**2)


def pin(i):
    A_, B_ = ring[i], ring[(i + 1) % 9]
    m_ = (A_ + B_) / 2
    d_ = nrm(B_ - A_)
    n_ = mp.matrix([(B_[1] - A_[1]) / d_, -(B_[0] - A_[0]) / d_])
    k_ = mp.sqrt(rI * rI - d_ * d_ / 4)
    p1, p2 = m_ + k_ * n_, m_ - k_ * n_
    return p1 if nrm(p1) < nrm(p2) else p2


pins = {i: pin(i) for i in range(9)}


def disk_center(A_, C_, side_point):
    m_ = (A_ + C_) / 2
    d_ = nrm(C_ - A_)
    n_ = mp.matrix([-(C_[1] - A_[1]) / d_, (C_[0] - A_[0]) / d_])   # perp(u), same convention
    k_ = mp.sqrt(rI * rI - d_ * d_ / 4)                             # as the interval kernel
    qp, qm = m_ + k_ * n_, m_ - k_ * n_
    s = (C_ - A_)[0] * (side_point - A_)[1] - (C_ - A_)[1] * (side_point - A_)[0]
    return qp if s > 0 else qm


def in_K_A(a_):
    return nrm(a_) < 1 - rI and all(nrm(a_ - pins[j]) <= rI for j in FAN_A)


def fiber_minnorm(a_, tol=mp.mpf('1e-30')):
    rho = 1 - rI
    ds = [(pins[j], rI) for j in FAN_B]
    for i in CENTRAL:
        ds.append((disk_center(a_, ring[i], hB), rI))
    cands = [mp.matrix([0, 0])]
    for c_, rr_ in ds:
        if nrm(c_) > rr_:
            cands.append(c_ * (rr_ / nrm(c_)))
    for (c1, r1), (c2, r2) in itertools.combinations(ds, 2):
        d_ = nrm(c2 - c1)
        if d_ > r1 + r2 or d_ < abs(r1 - r2) or d_ == 0:
            continue
        aa = (r1 * r1 - r2 * r2 + d_ * d_) / (2 * d_)
        hh2 = r1 * r1 - aa * aa
        if hh2 < 0:
            continue
        hh = mp.sqrt(hh2)
        e_ = (c2 - c1) / d_
        n_ = mp.matrix([-e_[1], e_[0]])
        cands.append(c1 + aa * e_ + hh * n_)
        cands.append(c1 + aa * e_ - hh * n_)
    best = None
    for z in cands:
        if all(nrm(z - c_) <= rr_ + tol for c_, rr_ in ds):
            nz = nrm(z)
            if nz < rho + tol and (best is None or nz < best):
                best = nz
    return best


probe = {'hA_in_K_A': bool(in_K_A(hA)),
         'hA_fiber_minnorm': (lambda z: None if z is None else str(z))(fiber_minnorm(hA))}
rays = {}
for nm, dvec in (('+x', (1, 0)), ('-x', (-1, 0)), ('+y', (0, 1)), ('-y', (0, -1))):
    last_ok = None
    for t in (1e-06, 1e-05, 0.0001, 0.001, 0.005, 0.01, 0.02, 0.04, 0.08, 0.15):
        a_ = hA + mp.mpf(t) * mp.matrix(dvec)
        if in_K_A(a_) and fiber_minnorm(a_) is not None:
            last_ok = t
        else:
            break
    rays[nm] = last_ok
probe['fiber_nonempty_extent_along_rays'] = rays
rep['N_nominal_probe'] = probe

(OUT / 'central_a_region.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
for k in ('S3_degrees_cleared_(x,y,k0,k1,s0,s1)', 'S4_rationalisation'):
    print(k, '=', rep[k])
print('E readings:', json.dumps(rep['E_exact_convexity_counterexample']['readings']))
print('E verdict:', rep['E_exact_convexity_counterexample']['verdict'][:190])
print('N probe:', json.dumps(probe, indent=1))
