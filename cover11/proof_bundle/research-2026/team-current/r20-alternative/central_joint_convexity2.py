"""central_joint_convexity2.py  (r20-alternative; sole write, no child)

Decisive SOC test (fixing the flaw of central_joint_convexity.py: its F_i-boundary points had
b OUTSIDE K_B, so they said nothing about the JOINT set).

Here the test point lies ON the boundary of the JOINT set: start from the candidate (hA, hB),
keep a = hA, and move b ALONG the central circle boundary  b(theta) = q_0 + r * Rot(theta)(hB-q_0)
so that |b - q_0| = r stays TIGHT (F_0 = 0 exactly) while the four chain-pin constraints and the
other central disk slacken.  At such a point the only (near-)active constraints are F_0 = 0 and
the (now inactive) others, so the joint tangent space is (essentially) the orthogonal complement
of grad F_0, and

    if  v^T Hess F_0 v > 0  for some tangent v   =>   the joint set is NOT convex there
    (SOC violated), hence the "joint-convex sufficient route" is NOT available.

Scope: this decides the joint-convex route only.  Non-convexity of a single central constraint
does NOT prove the a-projection is non-convex (projections of non-convex sets may be convex).
"""
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

mp.mp.dps = 50
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(v[0]), 10**17), F(int(v[1]), 10**17)) for v in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
FAN_A, FAN_B, CENTRAL = [4, 5, 6, 7, 8], [0, 1, 2, 3], [0, 4]
r = mp.mpf('0.38')
Mp = lambda fr: mp.mpf(fr.numerator) / mp.mpf(fr.denominator)
ring = [mp.matrix([Mp(p[0]), Mp(p[1])]) for p in [Pf[i] for i in NEW2RAW_RINGS]]
hA = mp.matrix([Mp(Pf[0][0]), Mp(Pf[0][1])])
hB = mp.matrix([Mp(Pf[2][0]), Mp(Pf[2][1])])
nrm = lambda u: mp.sqrt(u[0]**2 + u[1]**2)


def pin(i):
    A_, B_ = ring[i], ring[(i + 1) % 9]
    m_ = (A_ + B_) / 2
    d_ = nrm(B_ - A_)
    n_ = mp.matrix([-(B_[1] - A_[1]) / d_, (B_[0] - A_[0]) / d_])
    k_ = mp.sqrt(r * r - d_ * d_ / 4)
    p1, p2 = m_ + k_ * n_, m_ - k_ * n_
    return p1 if nrm(p1) < nrm(p2) else p2


pins = {i: pin(i) for i in range(9)}


def centers(a_, i):
    C_ = ring[i]
    m_ = (a_ + C_) / 2
    d_ = nrm(C_ - a_)
    n_ = mp.matrix([-(C_[1] - a_[1]) / d_, (C_[0] - a_[0]) / d_])
    k_ = mp.sqrt(r * r - d_ * d_ / 4)
    return m_ + k_ * n_, m_ - k_ * n_


def Fnum(cc, a_, b_):
    d2 = (b_[0] - a_[0])**2 + (b_[1] - a_[1])**2
    det = (b_[0] - a_[0]) * (cc[1] - a_[1]) - (b_[1] - a_[1]) * (cc[0] - a_[0])
    return 4 * r * r * det**2 - d2 * ((cc[0] - a_[0])**2 + (cc[1] - a_[1])**2) * \
        ((cc[0] - b_[0])**2 + (cc[1] - b_[1])**2)


rep = {'kind': 'SOC test ON the joint-set boundary (central circle kept tight, pins slackened)',
       'r': '0.38', 'a': [mp.nstr(hA[0], 20), mp.nstr(hA[1], 20)]}
tests = []
for i in CENTRAL:
    qp, qm = centers(hA, i)
    # near centre = the one at distance r from hB (branch-correct)
    qnear, qfar = (qp, qm) if abs(nrm(hB - qp) - r) < abs(nrm(hB - qm) - r) else (qm, qp)
    v = hB - qnear
    for th in (mp.mpf('0.02'), mp.mpf('0.05'), mp.mpf('0.1')):
        cth, sth = mp.cos(th), mp.sin(th)
        b_ = qnear + mp.matrix([cth * v[0] - sth * v[1], sth * v[0] + cth * v[1]])
        X = [hA[0], hA[1], b_[0], b_[1]]
        F_here = Fnum(ring[i], hA, b_)
        # slack of the other constraints
        pin_slack = min(r - nrm(b_ - pins[j]) for j in FAN_B)
        norm_slack = (1 - r) - nrm(b_)
        other = [j for j in CENTRAL if j != i][0]
        F_other = Fnum(ring[other], hA, b_)
        # numeric gradient / Hessian of F_i at this point
        hstep = mp.mpf('1e-20')

        def Fv(Xx):
            return Fnum(ring[i], mp.matrix(Xx[0:2]), mp.matrix(Xx[2:4]))
        g = [(Fv(list(mp.matrix(X) + hstep * mp.matrix([1 if k == t else 0 for k in range(4)]))) -
              Fv(list(mp.matrix(X) - hstep * mp.matrix([1 if k == t else 0 for k in range(4)])))) /
             (2 * hstep) for t in range(4)]
        H = mp.zeros(4, 4)
        for k in range(4):
            for l in range(4):
                dk = mp.matrix([1 if k == t else 0 for t in range(4)])
                dl = mp.matrix([1 if l == t else 0 for t in range(4)])
                X0 = mp.matrix(X)
                H[k, l] = (Fv(list(X0 + hstep * dk + hstep * dl)) -
                           Fv(list(X0 + hstep * dk - hstep * dl)) -
                           Fv(list(X0 - hstep * dk + hstep * dl)) +
                           Fv(list(X0 - hstep * dk - hstep * dl))) / (4 * hstep * hstep)
        gv = mp.matrix(g)
        e1 = gv / mp.sqrt(sum(x * x for x in g))
        basis = []
        for k in range(4):
            u = mp.matrix([1 if t == k else 0 for t in range(4)])
            w = u - e1 * (e1.T * u)[0]
            for ww in basis:
                w = w - ww * (ww.T * w)[0]
            nw = mp.sqrt(sum(x * x for x in w))
            if nw > mp.mpf('1e-10'):
                basis.append(w / nw)
        R = mp.matrix([[(vv.T * (H * ww))[0] for ww in basis] for vv in basis])
        ev = mp.eigsy(R, eigvals_only=True)
        tests.append({'face': i, 'theta': mp.nstr(th, 4),
                      'b': [mp.nstr(b_[0], 18), mp.nstr(b_[1], 18)],
                      'F_i_at_point': mp.nstr(F_here, 6),
                      '_pin_slack': pin_slack, '_norm_slack': norm_slack,
                      '_F_other': F_other,
                      'pin_slack_min': mp.nstr(pin_slack, 6),
                      'norm_slack': mp.nstr(norm_slack, 6),
                      'F_other_face': mp.nstr(F_other, 6),
                      'restricted_H_eigenvalues': [mp.nstr(x, 8) for x in ev],
                      'has_positive_direction': bool(any(x > mp.mpf('1e-10') for x in ev))})
rep['tests'] = tests
dec = [t for t in tests if t['_pin_slack'] > 0 and t['_norm_slack'] > 0 and t['_F_other'] > 0]
rep['decisive_points'] = len(dec)
rep['verdict'] = ('joint-convex sufficient route NOT available: positive tangent curvature of the '
                  'active central constraint at a joint-boundary point where all other constraints '
                  'are slack' if any(t['has_positive_direction'] for t in dec) else
                  'no positive direction at the decisive points (necessary condition passes; '
                  'not a convexity proof)')
rep['scope'] = ('decides the joint-convex sufficient route only; does NOT prove the a-projection '
                'non-convex (projection of a non-convex set can be convex)')
(OUT / 'central_joint_convexity.json').write_text(json.dumps(rep, indent=2), encoding='utf-8')
print(json.dumps(rep, indent=1))
