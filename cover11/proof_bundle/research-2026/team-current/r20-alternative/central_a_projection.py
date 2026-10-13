"""central_a_projection.py  (r20-alternative, v2; sole write, no child)

Lead obligation (revised): at r = 0.38 (C904 window) with the SAVED rings fixed, K_A should have
a TRUE interior (r - R* ~ 1.6e-5).  Compute K_A's analytic boundary/deepest candidates, ASSERT a
strict feasible margin > 0, then use <= 20 probes to decide fixed-rings a-projection convexity
(counterexample decision only).

Conditions stated BEFORE deriving (lead):
  F := K_B cap B(0,rho)  (ring-only convex, fixed).
  For fixed b, the branch-disk condition b in D_i(a) = B(q_i(a), r) is equivalent to the exact
  crescent constraint rho(a,b,c_i) <= r only on a region that avoids the distal disk:
      for all b in R:  R cap B(q'_i(a), r) = empty   =>   the two agree on R.
  The converse is NOT automatic (C894's retracted half-plane direction must not be used).
  Here R := K_B cap B(b_B, eps_B) with eps_B = sqrt(r^2 - |p_0 p_3|^2/4) (variance identity with
  rational weights 1/2,1/2 on two chain pins), and the distal check is verified per probe.

Deliberately NOT claimed: any certificate from the 3.9e-62 nominal margin, and any statement that
the nominal b is a min-norm corner derived from a numerical equality.
"""
import json
import itertools
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
Pf = [(F(int(v[0]), 10**17), F(int(v[1]), 10**17)) for v in raw['centers_scaled_1e17']]
NEW2RAW_RINGS = [5, 7, 1, 8, 6, 4, 9, 10, 3]
FAN_A, FAN_B, CENTRAL = [4, 5, 6, 7, 8], [0, 1, 2, 3], [0, 4]
R_T = mp.mpf('0.38')                      # C904 window test radius (exactly 19/50)
Mp = lambda fr: mp.mpf(fr.numerator) / mp.mpf(fr.denominator)
ring = [mp.matrix([Mp(p[0]), Mp(p[1])]) for p in [Pf[i] for i in NEW2RAW_RINGS]]
hA = mp.matrix([Mp(Pf[0][0]), Mp(Pf[0][1])])
hB = mp.matrix([Mp(Pf[2][0]), Mp(Pf[2][1])])
nrm = lambda u: mp.sqrt(u[0]**2 + u[1]**2)


def pin(i, r):
    A_, B_ = ring[i], ring[(i + 1) % 9]
    m_ = (A_ + B_) / 2
    d_ = nrm(B_ - A_)
    n_ = mp.matrix([-(B_[1] - A_[1]) / d_, (B_[0] - A_[0]) / d_])
    k_ = mp.sqrt(r * r - d_ * d_ / 4)
    p1, p2 = m_ + k_ * n_, m_ - k_ * n_
    return p1 if nrm(p1) < nrm(p2) else p2


pins = {i: pin(i, R_T) for i in range(9)}
KA_disks = [(mp.matrix([0, 0]), 1 - R_T)] + [(pins[j], R_T) for j in FAN_A]
KB_disks = [(mp.matrix([0, 0]), 1 - R_T)] + [(pins[j], R_T) for j in FAN_B]
bB = (pins[0] + pins[3]) / 2
epsB = mp.sqrt(max(mp.mpf(0), R_T * R_T - (nrm(pins[0] - pins[3]) / 2)**2))


def disk_int_witness(ds, tol=mp.mpf('1e-35')):
    """finite-candidate decision for an intersection of disks: 0, projections of 0 on each
    circle, and circle-circle intersections; returns (max_min_slack, z) or None"""
    cands = [mp.matrix([0, 0])]
    for c_, rr_ in ds:
        if nrm(c_) > rr_:
            cands.append(c_ * (rr_ / nrm(c_)))
    for (P, rp), (Q, rq) in itertools.combinations(ds, 2):
        d_ = nrm(Q - P)
        if d_ == 0 or d_ > rp + rq:
            continue
        aa = (rp * rp - rq * rq + d_ * d_) / (2 * d_)
        hh2 = rp * rp - aa * aa
        if hh2 < 0:
            continue
        hh = mp.sqrt(hh2)
        e_ = (Q - P) / d_
        n_ = mp.matrix([-e_[1], e_[0]])
        cands += [P + aa * e_ + hh * n_, P + aa * e_ - hh * n_]
    best = None
    for z in cands:
        m = min(rr_ - nrm(z - c_) for c_, rr_ in ds)
        if m >= -tol and (best is None or m > best[0]):
            best = (m, z)
    return best


# ---- deepest point of K_A at r = 0.38 (bisection on a uniform tightening) -----------
assert disk_int_witness(KA_disks) is not None, 'K_A empty at r=0.38'
lo, hi = mp.mpf(0), mp.mpf('0.02')
for _ in range(80):
    mid = (lo + hi) / 2
    if disk_int_witness([(c_, rr_ - mid) for c_, rr_ in KA_disks]) is not None:
        lo = mid
    else:
        hi = mid
t_star = lo
w = disk_int_witness([(c_, rr_ - t_star / 2) for c_, rr_ in KA_disks])
z0, margin = w[1], w[0]
res = {'r_test': mp.nstr(R_T, 12),
       'K_A_deepest_uniform_margin_t_star': mp.nstr(t_star, 10),
       'K_A_interior_witness': [mp.nstr(z0[0], 18), mp.nstr(z0[1], 18)],
       'K_A_witness_min_slack': mp.nstr(margin, 10),
       'assert_strict_interior(margin>0)': bool(margin > 0),
       'hA_min_slack_in_K_A': mp.nstr(min(rr_ - nrm(hA - c_) for c_, rr_ in KA_disks), 8),
       'eps_B': mp.nstr(epsB, 12)}
assert margin > 0


def two_centers(a_, i):
    C_ = ring[i]
    m_ = (a_ + C_) / 2
    d_ = nrm(C_ - a_)
    n_ = mp.matrix([-(C_[1] - a_[1]) / d_, (C_[0] - a_[0]) / d_])
    k_ = mp.sqrt(R_T * R_T - d_ * d_ / 4)
    return m_ + k_ * n_, m_ - k_ * n_


def distal_condition(a_):
    """stated extra condition: R = K_B cap B(bB, epsB) avoids both distal disks.
    clearance_i = |bB - q'_i(a)| - epsB - r  > 0."""
    clr = None
    for i in CENTRAL:
        qp, qm = two_centers(a_, i)
        qfar = qp if nrm(bB - qp) > nrm(bB - qm) else qm
        c = nrm(bB - qfar) - epsB - R_T
        clr = c if clr is None else min(clr, c)
    return clr


def disk_center(a_, C_):
    m_ = (a_ + C_) / 2
    d_ = nrm(C_ - a_)
    n_ = mp.matrix([-(C_[1] - a_[1]) / d_, (C_[0] - a_[0]) / d_])
    k_ = mp.sqrt(R_T * R_T - d_ * d_ / 4)
    qp, qm = m_ + k_ * n_, m_ - k_ * n_
    s = (C_ - a_)[0] * (bB - a_)[1] - (C_ - a_)[1] * (bB - a_)[0]
    return qp if s > 0 else qm


def fiber_witness(a_):
    ds = list(KB_disks) + [(disk_center(a_, ring[i]), R_T) for i in CENTRAL]
    return disk_int_witness(ds)


def in_KA(a_):
    return min(rr_ - nrm(a_ - c_) for c_, rr_ in KA_disks) >= -mp.mpf('1e-30')


# ---- <= 20 probes ------------------------------------------------------------------
probes = [z0]
step = margin / 3
for k in range(8):
    th = mp.pi * k / 4
    probes.append(z0 + step * mp.matrix([mp.cos(th), mp.sin(th)]))
probes.append(hA)
probes = probes[:20]
res['probes'] = []
feas = []
for idx, a_ in enumerate(probes):
    ok = in_KA(a_)
    dc = distal_condition(a_) if ok else None
    fw = fiber_witness(a_) if ok else None
    e = {'idx': idx, 'a': [mp.nstr(a_[0], 16), mp.nstr(a_[1], 16)], 'in_K_A': bool(ok),
         'distal_clearance': (None if dc is None else mp.nstr(dc, 6)),
         'distal_condition_ok': (None if dc is None else bool(dc > 0)),
         'fiber': 'nonempty' if fw is not None else ('empty' if ok else '-')}
    if fw is not None:
        e['b'] = [mp.nstr(fw[1][0], 16), mp.nstr(fw[1][1], 16)]
        e['b_margin'] = mp.nstr(fw[0], 6)
        if dc is not None and dc > 0:
            feas.append((idx, a_))
    res['probes'].append(e)
conv = []
for (i1, a1), (i2, a2) in itertools.combinations(feas, 2):
    am = (a1 + a2) / 2
    ok = in_KA(am)
    fw = fiber_witness(am) if ok else None
    e = {'pair': [i1, i2], 'mid_in_K_A': bool(ok), 'mid_fiber': 'nonempty' if fw else 'empty'}
    if ok and fw is None:
        ds = list(KB_disks) + [(disk_center(am, ring[i]), R_T) for i in CENTRAL]
        for (u, v) in itertools.combinations(range(len(ds)), 2):
            sep = nrm(ds[u][0] - ds[v][0]) - ds[u][1] - ds[v][1]
            if sep > mp.mpf('1e-35'):
                e['empty_certificate'] = {'pair_separation': [u, v], 'margin': mp.nstr(sep, 6)}
                break
    conv.append(e)
res['convexity_probes'] = conv
res['verdict'] = ('counterexample found' if any(x['mid_fiber'] == 'empty' and x['mid_in_K_A']
                                                for x in conv)
                  else 'no counterexample among probes (convexity NOT proved)')
(OUT / 'central_a_projection.json').write_text(json.dumps(res, indent=2), encoding='utf-8')
print(json.dumps({k: v for k, v in res.items() if k not in ('probes', 'convexity_probes')},
                 indent=1))
print('probes:', [(p['idx'], p['in_K_A'], p['fiber'], p['distal_condition_ok'])
                  for p in res['probes']])
print('n_feasible_with_distal:', len(feas), ' convexity_probes:', json.dumps(conv))
