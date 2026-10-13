"""central_joint_convexity.py  (r20-alternative; sole write, no child)

Lead obligation (analytic route, no sampling): decide whether the JOINT-CONVEX SUFFICIENT
ROUTE is available for the two central faces, by the second-order necessary condition for
convexity of the joint feasible set

    S = { (a,b) in R^4 : F_i(a,b) >= 0, i = 0,4 }  cap  (K_A x K_B) cap ... ,

where  F_i(a,b) = 4 r^2 det(b-a, c_i-a)^2 - |b-a|^2 |c_i-a|^2 |c_i-b|^2  is exactly the
circumradius polynomial (F_i >= 0 <=> rho(a,b,c_i) <= r).

FACT used (standard SOC): if S is convex, F_i is C^2 and at a point where the active
constraints are I, then for every v orthogonal to span{grad F_i : i in I} one has
v^T Hess F_i v <= 0 for all i in I.  A positive value at one such point therefore kills the
"joint convexity through these constraints" route.

SCOPE (explicit, per lead): this decides ONLY whether the joint-convex sufficient route is
available.  Non-convexity of one central constraint does NOT prove that the a-projection
{ a : exists b with (a,b) in S } is non-convex (projections of non-convex sets can be convex).

All data at the test points are RATIONAL (saved centres, c_i, r = 19/50), so the Hessians and
the curvature signs below are computed EXACTLY (sympy), not numerically.
"""
import json
from fractions import Fraction as F
from pathlib import Path

import sympy as sp

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(v[0]), 10**17), F(int(v[1]), 10**17)) for v in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
CENTRAL = [0, 4]
r0 = sp.Rational(19, 50)                                   # r = 0.38 exact
a1, a2, b1, b2 = sp.symbols('a1 a2 b1 b2', real=True)
A = sp.Matrix([a1, a2])
B = sp.Matrix([b1, b2])
X = [a1, a2, b1, b2]


def Fpoly(cxy):
    C = sp.Matrix([sp.Rational(cxy[0]), sp.Rational(cxy[1])])
    d2 = sp.expand((B - A).dot(B - A))
    det = sp.expand((B - A)[0] * (C - A)[1] - (B - A)[1] * (C - A)[0])
    return sp.expand(4 * r0**2 * det**2 - d2 * (C - A).dot(C - A) * (C - B).dot(C - B))


def hess_and_grad(Fexpr, pt):
    subs = {a1: pt[0], a2: pt[1], b1: pt[2], b2: pt[3]}
    g = sp.Matrix([sp.diff(Fexpr, v) for v in X]).subs(subs)
    H = sp.Matrix(4, 4, lambda i, j: sp.diff(Fexpr, X[i], X[j])).subs(subs)
    fval = sp.simplify(Fexpr.subs(subs))
    return sp.simplify(g), sp.simplify(H), fval


def tangent_basis(grads):
    """basis of the common orthogonal complement of the given gradient vectors (exact)"""
    Gm = sp.Matrix(grads)
    ns = Gm.nullspace()
    return [sp.Matrix(v) for v in ns]


def restrict(H, basis):
    return sp.Matrix([[sp.simplify(v.T * H * w)[0] for w in basis] for v in basis])


def definiteness(M):
    """exact classification of a symmetric exact matrix"""
    ev = M.eigenvals()
    pos = any(sp.simplify(sp.re(v)) > 0 for v in ev)
    neg = any(sp.simplify(sp.re(v)) < 0 for v in ev)
    zero = any(sp.simplify(v) == 0 for v in ev)
    return {'matrix': str(M.tolist()), 'eigenvals': {str(k): int(v) for k, v in ev.items()},
            'has_positive': bool(pos), 'has_negative': bool(neg), 'has_zero': bool(zero)}


hA = (sp.Rational(Pf[0][0].numerator, Pf[0][0].denominator),
      sp.Rational(Pf[0][1].numerator, Pf[0][1].denominator))
hB = (sp.Rational(Pf[2][0].numerator, Pf[2][0].denominator),
      sp.Rational(Pf[2][1].numerator, Pf[2][1].denominator))
pt = (hA[0], hA[1], hB[0], hB[1])
c0 = Pf[NEW2RAW_RINGS[0]]
c4 = Pf[NEW2RAW_RINGS[4]]

rep = {'kind': 'exact SOC test for the joint-convex sufficient route (r = 19/50, saved rings)',
       'test_point': {'a': [str(hA[0]), str(hA[1])], 'b': [str(hB[0]), str(hB[1])]},
       'r': '19/50'}

F0 = Fpoly(c0)
F4 = Fpoly(c4)
res = {}
for name, Fe in (('F_central0', F0), ('F_central4', F4)):
    g, H, fv = hess_and_grad(Fe, pt)
    res[name] = {'F_value_at_point': str(fv), 'grad_norm2_str': str(sum(v**2 for v in g)),
                 'hessian': str(H.tolist())}
rep['per_constraint'] = res
rep['active_check'] = {
    'F_central0_at_point': str(sp.simplify(F0.subs({a1: pt[0], a2: pt[1], b1: pt[2], b2: pt[3]}))),
    'F_central4_at_point': str(sp.simplify(F4.subs({a1: pt[0], a2: pt[1], b1: pt[2], b2: pt[3]}))),
    'note': 'F = 0 means the corresponding central triangle has circumradius exactly r'}

# ---- SOC at points where ONE central constraint is exactly active -------------------
# At r = 0.38 the two central faces are STRICTLY feasible at the candidate (F > 0, see above),
# so the SOC must be tested where a central constraint is active.  Build such a boundary point
# per face: keep a = hA and move b from hB towards the distal centre q'_i of that face until
# F_i = 0 (bisection).  There the disk/pin constraints are inactive, so the local shape of the
# joint set is governed by F_i alone (joint tangent space = orthogonal complement of grad F_i).
import mpmath as mp
mp.mp.dps = 50
g0, H0, _ = hess_and_grad(F0, pt)
g4, H4, _ = hess_and_grad(F4, pt)
Gm = sp.Matrix([list(g0), list(g4)])              # 2x4 gradient matrix (fixed construction)
rep['gradients'] = {'gradF0': [str(v) for v in g0], 'gradF4': [str(v) for v in g4],
                    'rank_of_the_two_gradients': int(Gm.rank()),
                    'common_tangent_dim': 4 - int(Gm.rank())}
RN = [sp.Rational(c[0].numerator, c[0].denominator) for c in [c0]]
rN = mp.mpf('0.38')
hAv = [mp.mpf(hA[0].numerator) / mp.mpf(hA[0].denominator),
       mp.mpf(hA[1].numerator) / mp.mpf(hA[1].denominator)]
hBv = [mp.mpf(hB[0].numerator) / mp.mpf(hB[0].denominator),
       mp.mpf(hB[1].numerator) / mp.mpf(hB[1].denominator)]


def Fnum(cc, a_, b_):
    d2 = (b_[0] - a_[0])**2 + (b_[1] - a_[1])**2
    det = (b_[0] - a_[0]) * (cc[1] - a_[1]) - (b_[1] - a_[1]) * (cc[0] - a_[0])
    return 4 * rN**2 * det**2 - d2 * ((cc[0] - a_[0])**2 + (cc[1] - a_[1])**2) *         ((cc[0] - b_[0])**2 + (cc[1] - b_[1])**2)


def q_far(cc, a_):
    m = [(a_[0] + cc[0]) / 2, (a_[1] + cc[1]) / 2]
    d = mp.sqrt((cc[0] - a_[0])**2 + (cc[1] - a_[1])**2)
    n = [-(cc[1] - a_[1]) / d, (cc[0] - a_[0]) / d]
    k = mp.sqrt(rN**2 - d**2 / 4)
    qp = [m[0] + k * n[0], m[1] + k * n[1]]
    qm = [m[0] - k * n[0], m[1] - k * n[1]]
    return qp if mp.sqrt((hBv[0] - qp[0])**2 + (hBv[1] - qp[1])**2) >         mp.sqrt((hBv[0] - qm[0])**2 + (hBv[1] - qm[1])**2) else qm


soc = {}
for nm, cc in (('face0', [mp.mpf(c0[0].numerator) / mp.mpf(c0[0].denominator),
                          mp.mpf(c0[1].numerator) / mp.mpf(c0[1].denominator)]),
               ('face4', [mp.mpf(c4[0].numerator) / mp.mpf(c4[0].denominator),
                          mp.mpf(c4[1].numerator) / mp.mpf(c4[1].denominator)])):
    qf = q_far(cc, hAv)
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(200):
        mid = (lo + hi) / 2
        b_ = [hBv[0] + mid * (qf[0] - hBv[0]), hBv[1] + mid * (qf[1] - hBv[1])]
        if Fnum(cc, hAv, b_) > 0:
            lo = mid
        else:
            hi = mid
    t = lo
    b_ = [hBv[0] + t * (qf[0] - hBv[0]), hBv[1] + t * (qf[1] - hBv[1])]
    ptN = hAv + b_
    # numeric Hessian / gradient of F at that boundary point
    Fd = Fnum(cc, [mp.mpf('0'), mp.mpf('0')], [mp.mpf('0'), mp.mpf('0')]) if False else None
    hstep = mp.mpf('1e-25')
    X = [hAv[0], hAv[1], b_[0], b_[1]]

    def Fv(Xx):
        return Fnum(cc, Xx[0:2], Xx[2:4])
    g = []
    for k in range(4):
        Xp, Xm = list(X), list(X)
        Xp[k] += hstep
        Xm[k] -= hstep
        g.append((Fv(Xp) - Fv(Xm)) / (2 * hstep))
    H = mp.zeros(4, 4)
    for k in range(4):
        for l in range(4):
            Xpp, Xpm, Xmp, Xmm = list(X), list(X), list(X), list(X)
            Xpp[k] += hstep; Xpp[l] += hstep
            Xpm[k] += hstep; Xpm[l] -= hstep
            Xmp[k] -= hstep; Xmp[l] += hstep
            Xmm[k] -= hstep; Xmm[l] -= hstep
            H[k, l] = (Fv(Xpp) - Fv(Xpm) - Fv(Xmp) + Fv(Xmm)) / (4 * hstep * hstep)
    gv = mp.matrix(g)
    # orthonormal basis of the tangent space
    nrmg = mp.sqrt(sum(x * x for x in g))
    e1 = gv / nrmg
    basis = [mp.matrix([1, 0, 0, 0]), mp.matrix([0, 1, 0, 0]), mp.matrix([0, 0, 1, 0]),
             mp.matrix([0, 0, 0, 1])]
    ortho = []
    for u in basis:
        v = u - mp.matrix([sum(u[i] * e1[i] for i in range(4)) * e1[i] for i in range(4)])             if False else u - e1 * (e1.T * u)[0]
        for w in ortho:
            v = v - w * (w.T * v)[0]
        nv = mp.sqrt(sum(x * x for x in v))
        if nv > mp.mpf('1e-12'):
            ortho.append(v / nv)
    R = mp.matrix([[ (v.T * (H * w))[0] for w in ortho] for v in ortho])
    ev = mp.eigsy(R, eigvals_only=True) if R.rows == 3 else None
    soc[nm] = {'boundary_b': [mp.nstr(b_[0], 20), mp.nstr(b_[1], 20)],
               'F_at_boundary': mp.nstr(Fv(X), 6),
               'restricted_H_eigenvalues': [mp.nstr(x, 8) for x in ev] if ev else None,
               'has_positive_direction': bool(any(x > mp.mpf('1e-12') for x in ev)) if ev else None}
rep['SOC_at_active_central_boundary'] = soc
rep['SOC_verdict'] = ('joint-convex route NOT available: positive tangent curvature of the '
                      'active central constraint' if any(
                          v['has_positive_direction'] for v in soc.values()) else
                      'SOC passes at the tested active-central boundary points (necessary '
                      'condition holds; not a proof)')
basis = sp.Matrix([list(g0), list(g4)]).nullspace()
rep['common_tangent_space_dim'] = len(basis)
if len(basis) >= 1:
    R0 = sp.Matrix([[sp.simplify(v.T * H0 * w)[0] for w in basis] for v in basis])
    R4 = sp.Matrix([[sp.simplify(v.T * H4 * w)[0] for w in basis] for v in basis])
    rep['restricted_H_central0'] = definiteness(R0)
    rep['restricted_H_central4'] = definiteness(R4)

(OUT / 'central_joint_convexity.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
print('grad rank:', rep['gradients']['rank_of_the_two_gradients'],
      ' common tangent dim:', rep['common_tangent_space_dim'])
print('SOC boundary:', json.dumps(rep['SOC_at_active_central_boundary'], indent=1))
print('SOC verdict:', rep['SOC_verdict'])
if 'restricted_H_central0' in rep:
    print('restricted H0 eigenvals:', rep['restricted_H_central0']['eigenvals'])
    print('restricted H4 eigenvals:', rep['restricted_H_central4']['eigenvals'])
