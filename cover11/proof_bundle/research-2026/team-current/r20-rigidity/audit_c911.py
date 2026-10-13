"""r20-rigidity: INDEPENDENT instrument audit of C911 (uniform sector certificate).

Scope: read the lead's artifacts only (no writes outside r20-rigidity, no subagents). The original
solver is NOT used. What is recomputed here, from scratch:

  (1) the canonical 31-node graph from the written description (9 anchors 0..8, 11 sites 9..19,
      11 auxiliary face nodes 20..30; site-anchor edges (9+s, s), (9+s, (s-1) mod 9); 11 faces x 3
      edges to the auxiliary node), then a comparison with the edges stored in the certificate;
  (2) the incidence/divergence of the STORED rational forces at all 22 free nodes, in exact Fraction
      arithmetic (independent of the lead's balancing code and traversal);
  (3) the coordinate l1 norm and the norm bound sum_e ||p_e|| < 1 in interval arithmetic;
  (4) each anchor's support minimum by a DIFFERENT expression: the exact minimum of
      g(t) = a cos t + d sin t on [-h, h] is min( g(-h), g(h), -R * [phi + pi in [-h,h]] ) with
      R = sqrt(a^2+d^2), phi = atan2(d, a) -- i.e. the interior critical point is included instead of
      the lead's linearised endpoint forms;
  (5) the angle-0 fixation (theta0 = 0 exactly, term = a_0) and a diagnostic of what the bound would
      become if |theta_0| <= h were allowed (why the fixation is load bearing).

Exact rational arithmetic is used wherever the quantities are rational; only cos/sin/sqrt are
interval-evaluated. Prints PASS/FAIL of each algebraic check, but the audit claim rests on the printed
identities, not on a script PASS.

Writes audit_c911.json (and the human-readable C911-AUDIT.md is written separately).
"""
import json
from pathlib import Path
from fractions import Fraction as F
import mpmath as mp

mp.mp.dps = 70
mp.iv.dps = 60
R20 = Path(__file__).resolve().parent
LEAD = R20.parent / 'lead'
cert = json.loads((LEAD / 'uniform_sector_certificate.json').read_text(encoding='utf-8'))
REP = []


def say(s):
    print(s, flush=True)
    REP.append(s)


# ---------------------------------------------------------------- (1) graph from the description
faces_audit = [[9, k, k + 1] for k in range(4)] + [[10, k, (k + 1) % 9] for k in range(4, 9)] \
              + [[9, 10, 0], [9, 10, 4]]
edges_audit = []
for s in range(9):
    edges_audit.extend([(9 + s, s), (9 + s, (s - 1) % 9)])
for j, face in enumerate(faces_audit):
    edges_audit.extend((9 + s, 20 + j) for s in face)
edges_stored = [tuple(e) for e in cert['edges']]
faces_stored = cert['faces']
say('[A1] graph rebuilt from the description: %d edges, %d faces' % (len(edges_audit), len(faces_audit)))
say('     identical to the stored edge list (order included): %s' % (edges_audit == edges_stored))
say('     identical to the stored face list: %s' % (faces_audit == faces_stored))
deg = [0] * 31
for v, w in edges_audit:
    deg[v] += 1
    deg[w] += 1
say('     degrees: anchors %s ; sites %s ; auxiliaries %s'
    % (sorted(set(deg[0:9])), sorted(set(deg[9:20])), sorted(set(deg[20:31]))))

# ---------------------------------------------------------------- (2) exact divergence of stored forces
p = [[F(v) for v in row] for row in cert['forces_rational']]
say('[A2] stored rational forces read: %d edges ; normalization B = %s' % (len(p), cert['normalization_rational']))
assert len(p) == 51


def balances(pp):
    b = [[F(0), F(0)] for _ in range(31)]
    for (v, w), q in zip(edges_audit, pp):
        for k in range(2):
            b[v][k] += q[k]
            b[w][k] -= q[k]
    return b


b = balances(p)
free = b[9:]
say('     divergence at the 22 free nodes: all exactly zero = %s (max |.| = %s)'
    % (all(x == 0 for row in free for x in row), max((abs(x) for row in free for x in row), default=0)))
# the 9 anchor divergences (these are the support terms l_i)
say('     anchor divergences l_i = (b[0..8]) in exact rationals:')
for i in range(9):
    say('        i=%d  l = (%s, %s)' % (i, b[i][0], b[i][1]))

# ---------------------------------------------------------------- (3) norm bound, interval
def I(q):
    return mp.iv.mpf(q.numerator) / q.denominator


norm = sum(mp.iv.sqrt(sum(I(v) ** 2 for v in row)) for row in p)
say('[A3] interval norm sum_e ||p_e|| = [%s, %s] ; < 1 : %s'
    % (mp.nstr(mp.mpf(norm.a), 20), mp.nstr(mp.mpf(norm.b), 20), bool(norm < 1)))
l1 = sum(sum(abs(v) for v in row) for row in p)
say('     coordinate l1 = %s (diagnostic only, unused by the certificate)' % mp.nstr(mp.mpf(l1.numerator) / l1.denominator, 20))

# ---------------------------------------------------------------- (4) support minimums, other expression
h = mp.iv.mpf(1) / 50
terms, diag = [], []
PI_LO_ = mp.mpf(mp.iv.pi.a)
for i in range(9):
    th = 2 * mp.iv.pi * i / 9
    n = (mp.iv.cos(th), mp.iv.sin(th))
    tan = (-n[1], n[0])
    a = sum(I(b[i][k]) * n[k] for k in range(2))
    d = sum(I(b[i][k]) * tan[k] for k in range(2))
    if i == 0:
        term = a                                   # theta0 fixed: exact, no h
        kind = 'fixed theta0 -> a_0'
    elif b[i][0] == 0 and b[i][1] == 0:
        term = mp.iv.mpf(0)                        # zero l_i handled exactly (Fraction zero)
        kind = 'zero l_i (exact Fractions)'
    else:
        gh = a * mp.iv.cos(h) + d * mp.iv.sin(h)
        gm = a * mp.iv.cos(h) - abs(d) * mp.iv.sin(h)
        R = mp.iv.sqrt(a * a + d * d)
        a_lo, a_hi = mp.mpf(a.a), mp.mpf(a.b)
        h_hi = mp.mpf(h.b)
        # g(t) = a cos t + d sin t has its MAXIMUM at t = phi (= atan2(d,a), where cos(t-phi)=1) and
        # its interior MINIMUM at t = phi + pi, value -R.  The minimum lies in [-h,h] only if
        # |phi| >= pi - h; for a > 0 we have |phi| < pi/2, so it is excluded as soon as h < pi/2.
        # Certified exclusion only; otherwise -R MUST be included (three-state, no straddling drop).
        excl = bool(a_lo > 0 and h_hi < PI_LO_ / 2)
        assert h_hi < PI_LO_ / 2, \
            'h must be < iv.pi/2 (threshold taken from iv.pi); h.hi = %s' % mp.nstr(h_hi, 20)
        assert abs(h_hi - mp.mpf('0.02')) < mp.mpf('1e-15'), 'h is 1/50 (interval) as declared'
        if not excl:
            say('     i=%d: exclusion of the interior minimum NOT provable (a=[%s,%s]) -> '
                'conservatively including -R' % (i, mp.nstr(a_lo, 12), mp.nstr(a_hi, 12)))
        cand = [mp.mpf(gh.a), mp.mpf(gm.a)]
        if not excl:
            cand.append(-mp.mpf(R.b))
        term = mp.iv.mpf(min(cand))
        kind = 'no interior min (a.lo>0, h<=0.02<pi/2)' if excl else 'conservative: -R included'

    terms.append(term)
    diag.append((i, kind, mp.nstr(mp.mpf(term.a), 18), mp.nstr(mp.mpf(term.b), 18)))
say('[A4] support minimums (independent expression; interior-minimum branch certified or conservative):')
for i, kind, la, lb in diag:
    say('     i=%d  %-24s lower=[%s, %s]' % (i, kind, la, lb))
lb = sum(terms)
say('[A5] total lower bound interval = [%s, %s] ; > 39/100 : %s'
    % (mp.nstr(mp.mpf(lb.a), 20), mp.nstr(mp.mpf(lb.b), 20), bool(lb > mp.iv.mpf(39) / 100)))
say('     (lead reported lower_interval_diagnostic = %s)' % (cert['lower_interval_diagnostic'],))
# hard asserts (lead: logged booleans do not stop a silent failure)
assert edges_audit == edges_stored, 'graph identity failed'
assert faces_audit == faces_stored, 'face identity failed'
assert all(x == 0 for row in free for x in row), 'free-node divergence not exactly zero'
assert norm < 1, 'dual feasibility norm bound failed'
assert lb > mp.iv.mpf(39) / 100, 'total lower bound does not exceed 39/100'
say('[A5b] hard asserts passed: graph identity, exact free divergence zero, norm < 1, bound > 39/100')

# ---------------------------------------------------------------- (5) angle-0 fixation diagnostic
say('[A6] angle-0 fixation: theta0 = 0 exactly, i=0 term = a_0 = %s' % mp.nstr(mp.mpf(terms[0].a), 18))
b0 = b[0]
a0 = I(b0[0])
d0 = I(b0[1])
free0 = a0 * mp.iv.cos(h) - abs(d0) * mp.iv.sin(h)
say('     if |theta0| <= h were allowed instead, i=0 would contribute at most [%s, %s]'
    % (mp.nstr(mp.mpf(free0.a), 18), mp.nstr(mp.mpf(free0.b), 18)))
say('     loss = lower bound would be [%s, %s] which is still > 39/100 : %s'
    % (mp.nstr(mp.mpf((lb - terms[0] + free0).a), 18), mp.nstr(mp.mpf((lb - terms[0] + free0).b), 18),
       bool(lb - terms[0] + free0 > mp.iv.mpf(39) / 100)))

OUT = {'scope': cert['scope'], 'graph_identical_to_stored': edges_audit == edges_stored,
       'faces_identical_to_stored': faces_audit == faces_stored,
       'free_divergence_all_zero': all(x == 0 for row in free for x in row),
       'anchor_divergences': [[str(b[i][0]), str(b[i][1])] for i in range(9)],
       'norm_interval': [mp.nstr(mp.mpf(norm.a), 20), mp.nstr(mp.mpf(norm.b), 20)],
       'norm_lt_one': bool(norm < 1),
       'support_kinds': [k for _, k, _, _ in diag],
       'lower_interval_independent': [mp.nstr(mp.mpf(lb.a), 20), mp.nstr(mp.mpf(lb.b), 20)],
       'lower_gt_39_100': bool(lb > mp.iv.mpf(39) / 100),
       'angle0_fixed': True,
       'angle0_relaxed_still_above': bool(lb - terms[0] + free0 > mp.iv.mpf(39) / 100),
       'status': 'instrument audit; the algebraic identities printed in the log are the evidence, not '
                 'the PASS flags',
       'repro': 'py -3 -B -X utf8 audit_c911.py'}
(R20 / 'audit_c911.json').write_text(json.dumps(OUT, indent=2))
(R20 / 'audit_c911.log').write_text('\n'.join(REP) + '\n')
say('\nwritten audit_c911.json / .log')
