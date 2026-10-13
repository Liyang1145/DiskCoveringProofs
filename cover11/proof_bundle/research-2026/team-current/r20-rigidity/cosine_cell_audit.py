"""r20-rigidity: corrected independent kernel audit of the cosine-envelope cell (node 26).

Fixes after lead source audit (same class of missing asserts as C914):
 * the whole-arc Taylor check runs in INTERVAL arithmetic (iv.cos/iv.sin with I(F(...)) inputs),
   comparing lo(bound) >= hi(exact target): mp scalars at high precision are not a certificate;
 * arcs are taken from MY interval vertex ranges and expanded to enclose the stored decimal
   endpoints, so no inward contraction can occur;
 * all bearing quantities are HARD-ASSERTED: len(alpha)==len(edges), 36 weights, pair order,
   Schur residual exactly zero, sum(beta)==1 and min(beta)>=0, per-pair gamma sum 1 and >=0,
   recorded pair weight == derived mixture weight, every minorant proved, radius lower > 0.38;
 * the final radius is a lower endpoint of an iv.sqrt (same interval object as the energy bound);
 * no PASS is reported before these asserts pass.
Writes cosine_cell_audit.json/.log.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
mp.iv.dps = 45
R20 = Path(__file__).resolve().parent
LEAD = R20.parent / 'lead'
cert = json.loads((LEAD / 'cosine_envelope_cell_certificate.json').read_text(encoding='utf-8'))
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


def Q(x):
    if isinstance(x, F):
        return mp.mpf(x.numerator) / x.denominator
    if isinstance(x, mp.mpf):
        return x
    return mp.mpf(str(x))


def I(x):
    x = F(x)
    return mp.iv.mpf(x.numerator) / x.denominator


faces = [[9, k, k + 1] for k in range(4)] + [[10, k, (k + 1) % 9] for k in range(4, 9)] \
        + [[9, 10, 0], [9, 10, 4]]
edges = []
for s in range(9):
    edges.extend([(9 + s, s), (9 + s, (s - 1) % 9)])
for j, fa in enumerate(faces):
    edges.extend((9 + s, 20 + j) for s in fa)
pairs = [(i, j) for i in range(9) for j in range(i + 1, 9)]
assert len(pairs) == 36
say('[K0] rebuilt carrying graph: %d edges ; 36 anchor pairs' % len(edges))
L = 2 * mp.iv.atan2(I(F(19, 50)), mp.iv.sqrt(1 - I(F(19, 50)) ** 2))
D = 9 * L - 2 * mp.iv.pi
assert D > 0
row = cert['rows'][0]
say('[K1] cell %s ; stored radius lower (DIFFERENT object) = %s' % (row['cell'], row['radius_lower']))

# ---------------- (S) exact Schur identity, hard-asserted
def schur_residual(alpha_strs, weights):
    al = [F(x) for x in alpha_strs]
    assert len(al) == len(edges), 'len(alpha) != len(edges) (%d vs %d)' % (len(al), len(edges))
    assert sum(al) == 1 and min(al) > 0, 'alpha not a positive probability vector'
    assert len(weights) == 36, 'weights != 36'
    assert [(int(a), int(b)) for a, b, _ in weights] == pairs, 'pair order mismatch'
    assert min(F(w) for _, _, w in weights) > 0, 'non-positive Schur weight'
    n31 = 31
    Lm = [[F(0)] * n31 for _ in range(n31)]
    for (vv, ww), a in zip(edges, al):
        Lm[vv][vv] += a
        Lm[ww][ww] += a
        Lm[vv][ww] -= a
        Lm[ww][vv] -= a
    M = [[F(0)] * 9 for _ in range(9)]
    for (i, j, w) in weights:
        M[i][j] = -F(w)
        M[j][i] = -F(w)
    for i in range(9):
        M[i][i] = -sum(M[i][j] for j in range(9) if j != i)
    nf = 22
    A = [[Lm[9 + i][9 + j] for j in range(nf)] + [Lm[9 + i][j] for j in range(9)] for i in range(nf)]
    for c in range(nf):
        pr = next(r for r in range(c, nf) if A[r][c] != 0)
        A[c], A[pr] = A[pr], A[c]
        pc = A[c][c]
        A[c] = [x / pc for x in A[c]]
        for r in range(nf):
            if r != c and A[r][c] != 0:
                fac = A[r][c]
                A[r] = [x - fac * y for x, y in zip(A[r], A[c])]
    Y = [[A[i][nf + j] for j in range(9)] for i in range(nf)]
    worst = F(0)
    for i in range(9):
        for j in range(9):
            acc = Lm[i][j] - sum(Lm[i][9 + a] * Y[a][j] for a in range(nf))
            worst = max(worst, abs(acc - M[i][j]))
    return worst


worst_schur = max(schur_residual(f['alpha'], f['weights']) for f in cert['fields'])
assert worst_schur == 0, 'Schur residual not exactly zero'
say('[K2] ASSERTED (exact Fraction): for all %d fields alpha is a positive probability vector with'
    ' %d entries, the 36 pairs are in order, all weights positive, and the Schur residual'
    ' |Laa - M - Laf Lff^-1 Lfa| is EXACTLY ZERO' % (len(cert['fields']), len(edges)))

# ---------------- (M) whole-arc minorants, INTERVAL Taylor bound
def dyadic(t):
    sign, man, exp, bc = t
    return F((-1 if sign else 1) * man) * (F(2) ** exp)


def endpoint_frac_lo(x):
    """EXACT lower Fraction of an interval (raw dyadic endpoint, no padding)."""
    return dyadic(x._mpi_[0])


def endpoint_frac_hi(x):
    """EXACT upper Fraction of an interval (raw dyadic endpoint, no padding)."""
    return dyadic(x._mpi_[1])


def taylor_ok(aF, bF, sF, tgtF, depth=0, maxdepth=80):
    """Prove h >= tgtF on [aF, bF] for h(z) = 1 - cos z - (sF) z, with aF,bF,sF,tgtF exact
    Fractions; every arithmetic step below is interval, recursion keeps Fractions."""
    mF = (aF + bF) / 2
    rF = (bF - aF) / 2
    mv, rv = I(mF), I(rF)
    s_iv = I(sF)
    hm = 1 - mp.iv.cos(mv) - s_iv * mv
    hp = mp.iv.sin(mv) - s_iv
    bound_iv = hm - abs(hp) * rv - rv ** 2 / 2
    if bound_iv >= I(tgtF):
        return depth
    if depth >= maxdepth or rF < F(1, 10 ** 40):
        return None
    dl = taylor_ok(aF, mF, sF, tgtF, depth + 1, maxdepth)
    dr = taylor_ok(mF, bF, sF, tgtF, depth + 1, maxdepth)
    return None if (dl is None or dr is None) else max(dl, dr)


v = [[F(x) for x in r] for r in row['vertices']]


def zz_of(y):
    return [(i - j) * L - D * I(sum(y[:i]) - sum(y[:j])) for (i, j) in pairs]


zall = [zz_of(y) for y in v]
worst_depth, nlines, ok_all = 0, 0, True
for rec_idx, rec in enumerate(row['minorants']):
    i, j = rec['pair']
    assert (i, j) == pairs[rec_idx], 'minorant pair order mismatch'
    zs = [z[rec_idx] for z in zall]
    aF = min([F(rec['arc'][0])] + [endpoint_frac_lo(z) for z in zs])
    bF = max([F(rec['arc'][1])] + [endpoint_frac_hi(z) for z in zs])
    # certified containment (evidence at 40+ dps): the Fraction arc encloses every vertex interval
    for z in zs:
        assert I(aF) <= z, 'arc lower Fraction does not enclose a vertex interval'
        assert I(bF) >= z, 'arc upper Fraction does not enclose a vertex interval'
    assert sum(F(ent['gamma']) for ent in rec['lines']) == 1, 'gamma not summing to 1'
    assert min(F(ent['gamma']) for ent in rec['lines']) >= 0, 'gamma negative'
    for ent in rec['lines']:
        sF = F(ent['slope'])
        assert -1 <= sF <= 1, 'slope outside [-1,1]'
        tgtF = F(ent['intercept_lower']) - F(1, 10 ** 6)      # EXACT shifted target
        nlines += 1
        dd = taylor_ok(aF, bF, sF, tgtF)
        if dd is None:
            ok_all = False
            say('     FAIL minorant pair %s slope %s' % (rec['pair'], ent['slope']))
        else:
            worst_depth = max(worst_depth, dd)
assert ok_all, 'a whole-arc minorant could not be proved'
say('[K3] ASSERTED: all %d minorant lines proved on EXACT Fraction arcs (raw dyadic endpoints, no'
    ' padding, containing every vertex interval) by full-interval Taylor; worst depth %d; exact'
    ' target = intercept - 1/10^6' % (nlines, worst_depth))

# ---------------- (V) SAME object: intercepts shifted by -1e-6, iv.sqrt lower endpoint
beta = [F(x) for x in row['beta']]
assert sum(beta) == 1 and min(beta) >= 0, 'beta is not a probability vector'
W = [sum(beta[f] * F(cert['fields'][f]['weights'][k][2]) * 2 for f in range(len(cert['fields'])))
     for k in range(36)]
assert min(W) >= 0, 'derived mixture weight negative'
vals = [mp.iv.mpf(0) for _ in range(9)]
for rec_idx, rec in enumerate(row['minorants']):
    i, j = rec['pair']
    assert F(rec['weight']) == W[rec_idx], 'recorded pair weight != derived mixture weight'
    for ent in rec['lines']:
        s_ = I(F(ent['slope']))
        gF = F(ent['gamma'])
        c_ = I(F(ent['intercept_lower'])) - mp.iv.mpf(1) / 10 ** 6
        for t, y in enumerate(v):
            z = (i - j) * L - D * I(sum(y[:i]) - sum(y[:j]))
            vals[t] = vals[t] + I(W[rec_idx] * gF) * (s_ * z + c_)
lb_iv = min(vals, key=lambda x: x.a)
rad_iv = mp.iv.sqrt(lb_iv)
say('[K4] my own interval vertex bound, intercepts shifted by -1e-6 (same object as [K3]):'
    ' energy lower = %s ; radius lower = %s' % (mp.nstr(mp.mpf(lb_iv.a), 18),
                                                mp.nstr(mp.mpf(rad_iv.a), 18)))
assert rad_iv > I(F(19, 50)), 'shifted-bound radius not above 0.38 (iv compare)'
say('[K5] ASSERTED: shifted-bound radius lower > 0.38 (stored 0.38441171... refers to the'
    ' unshifted object; the two are NOT the same quantity)')
OUT = {'cell': row['cell'], 'schur_residual_exactly_zero': bool(worst_schur == 0), 'n_edges': len(edges),
       'n_pairs': 36, 'n_minorant_lines': nlines, 'minorant_target': 'intercept - 1e-6',
       'worst_subdivision_depth': worst_depth, 'arcs_expanded': True,
       'energy_lower_shifted': mp.nstr(mp.mpf(lb_iv.a), 20),
       'radius_lower_shifted': mp.nstr(mp.mpf(rad_iv.a), 20),
       'radius_lower_shifted_gt_0_38': bool(rad_iv > I(F(19, 50))),
       'stored_radius_lower_unshifted_object': row['radius_lower'],
       'scope': 'kernel audit: exact Schur identity, interval whole-arc minorants, mixture weights,'
                ' own interval vertex bound with the 1e-6-shifted intercepts; not the modelling step,'
                ' not the cell coverage, not global',
       'repro': 'py -3 -B -X utf8 cosine_cell_audit.py'}
(R20 / 'cosine_cell_audit.json').write_text(json.dumps(OUT, indent=2))
(R20 / 'cosine_cell_audit.log').write_text('\n'.join(REP) + '\n')
say('written cosine_cell_audit.json / .log')
