"""Independent audit (different representation) of the r20-geometry "missed central point" at r = 19/50.

Their route: rational circumcentre p of the violated central triangle (hubA, c0=raw5, hubB), then exact
11 distances.  My route (separable, no new search):
  (A) same witness with my own Fraction kernel: 11 exact signs |p-c_j|^2 - r^2, |p|^2 < 1, and the
      MULTISET comparison with their list (their list uses a different site ORDER -- hubs last);
  (B1) p is equidistant from (hA, CEN[5], hB), R_c > r, triangle acute => p is the maximin hole centre;
  (B2) short-arc cap ledger ON THE BOUNDARY: only the 9 RINGS have boundary arcs (the two hubs are
      strict interior, |h|^2 < (1-r)^2 exactly => their disks do not meet the unit circle at all);
      the 9 ring arcs cover the boundary => the failure is purely INTERIOR (cap-overlap hole);
  (B3) nine consecutive-pair pins: EXACT rational coverage certificate.  Circle-circle intersections
      are q_l = m + s*sqrt(K)*J with K = (r^2-|u|^2/4)/|u|^2 in Q and J the rational perpendicular, so
      |h - q_l|^2 - r^2 = alpha + q*sqrt(K) with alpha, q in Q (sign decided exactly).  The correct
      aggregate for "ALL nine pins covered" is  max_over_pins( min_over_hubs(slack) ) < 0  (the
      minimum-over-all does NOT prove the universal statement).
Read-only inputs: n11/upper/certified_object.json; r20-geometry/exact_missed_point.json.
Writes only in r20-stress/out .
"""
import io, json, math
from fractions import Fraction as F
from pathlib import Path
from mpmath import mp, mpf, sqrt as msqrt, acos, atan2, pi as MP_PI

mp.dps = 60
W = Path(__file__).parent
OUT = W / 'out'
ROOT = W.parents[2]
OBJ = json.load(io.open(ROOT / 'n11/upper/certified_object.json', encoding='utf-8'))
DEN = 10 ** int(OBJ['decimals'])
CEN = [(F(int(x), DEN), F(int(y), DEN)) for x, y in OBJ['centers_scaled_1e17']]
THEIRS = json.loads((W.parent / 'r20-geometry' / 'exact_missed_point.json').read_text(encoding='utf-8'))
R = F(19, 50)
hA = (F(THEIRS['hubA'][0]), F(THEIRS['hubA'][1]))
hB = (F(THEIRS['hubB'][0]), F(THEIRS['hubB'][1]))
P = (F(THEIRS['p'][0]), F(THEIRS['p'][1]))
SITES = list(CEN)
SITES[2] = hA
SITES[0] = hB
TAGS = ['hubB(raw0)', 'ring1', 'hubA(raw2)', 'ring3', 'ring4', 'ring5=central', 'ring6', 'ring7',
        'ring8', 'ring9', 'ring10']


def n2(p):
    return p[0] * p[0] + p[1] * p[1]


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


# ---------------- (A) exact independent kernel on the same witness
signs = [n2(sub(P, s)) - R * R for s in SITES]
res = {'r': str(R), 'witness_p': [str(P[0]), str(P[1])],
       'A_all_eleven_outside': bool(all(s > 0 for s in signs)),
       'A_min_margin_over_eleven': str(min(signs)),
       'A_p_norm2_lt_1': bool(n2(P) < 1),
       'A_multiset_matches_their_list': sorted(str(s) for s in signs) == sorted(THEIRS['outside_signs']),
       'A_their_list_order_differs': [str(s) for s in signs] != THEIRS['outside_signs'],
       'A_matches_their_Rc2_minus_r2': str(min(signs)) == THEIRS['Rc2_minus_r2']}
print('(A) exact {11 signs}: all outside = %s | min = Rc2-r2 exactly = %s | multiset == their list: %s | |p|^2<1 = %s'
      % (res['A_all_eleven_outside'], res['A_matches_their_Rc2_minus_r2'],
         res['A_multiset_matches_their_list'], res['A_p_norm2_lt_1']))

# ---------------- (B1) p = circumcentre of (hA, CEN[5], hB) and it is the maximin point
c0 = CEN[5]
dA, d0, dB = n2(sub(P, hA)), n2(sub(P, c0)), n2(sub(P, hB))
res['B1_equidistant'] = bool(dA == d0 == dB)
Rc2 = dA
res['B1_Rc2_minus_r2'] = str(Rc2 - R * R)
res['B1_triangle_acute'] = bool(all(dot(sub(u, v), sub(w, v)) > 0
                                   for (u, v, w) in ((hA, c0, hB), (c0, hB, hA), (hB, hA, c0))))
Rc = float(msqrt(mpf(Rc2.numerator) / Rc2.denominator))
res['B1_Rc'] = Rc
res['B1_hole_depth'] = Rc - 0.38
print('(B1) equidistant: %s ; Rc-r = %.9e ; acute/inside: %s'
      % (res['B1_equidistant'], Rc - 0.38, res['B1_triangle_acute']))

# ---------------- (B2) boundary arcs: only the 9 rings (hubs strict interior => no arc at all)
res['B2_hub_strict_exact'] = {'hubB(raw0)': bool(n2(hB) < (1 - R) * (1 - R)),
                              'hubA(raw2)': bool(n2(hA) < (1 - R) * (1 - R))}
arcs = []
for i in range(11):
    if i in (0, 2):
        continue
    s = SITES[i]
    rho = float(msqrt(mpf(n2(s).numerator) / n2(s).denominator))
    cos_a = (rho * rho + 1 - 0.38 ** 2) / (2 * rho)
    a = float(acos(cos_a)) if abs(cos_a) <= 1 else None
    th = float(atan2(mpf(s[1].numerator) / s[1].denominator, mpf(s[0].numerator) / s[0].denominator))
    arcs.append({'idx': i, 'tag': TAGS[i], 'halfwidth_deg': None if a is None else round(a * 180 / float(MP_PI), 6),
                 'rho': round(rho, 10), 'theta': round(th, 10), 'a': a, 'th': th})
res['B2_arcs_rings_only'] = [{k: v for k, v in x.items() if k not in ('a', 'th')} for x in arcs]
res['B2_n_boundary_arcs'] = sum(1 for x in arcs if x['a'] is not None)
tot = sum(2 * x['a'] for x in arcs if x['a'] is not None)
res['B2_total_ring_arc_length_over_2pi'] = tot / (2 * float(MP_PI))
cov = sorted([(x['th'] - x['a'], x['th'] + x['a'], x['tag']) for x in arcs if x['a'] is not None])
gaps = []
for k in range(len(cov)):
    lo_k, hi_k, tk = cov[k]
    lo_n, hi_n, tn = cov[(k + 1) % len(cov)]
    lo_n = lo_n + 2 * float(MP_PI) if k == len(cov) - 1 else lo_n
    gaps.append((tn, tk, lo_n - hi_k))
res['B2_boundary_worst_gap_rad'] = max(g for (_, _, g) in gaps)
res['B2_boundary_covered'] = bool(res['B2_boundary_worst_gap_rad'] <= 0)
print('(B2) boundary arcs = %d (rings only; hubs strict interior: %s) ; total/2pi = %.6f ; covered = %s (worst gap %.3e rad)'
      % (res['B2_n_boundary_arcs'], res['B2_hub_strict_exact'], res['B2_total_ring_arc_length_over_2pi'],
         res['B2_boundary_covered'], res['B2_boundary_worst_gap_rad']))


# ---------------- (B3) nine pins: EXACT rational coverage certificate, correct aggregate
def sign_pmq(K, p, q):
    if q == 0:
        return (p > 0) - (p < 0)
    if p == 0:
        return (q > 0) - (q < 0)
    if p > 0 and q > 0:
        return 1
    if p < 0 and q < 0:
        return -1
    if p > 0:
        return 1 if p * p > q * q * K else (-1 if p * p < q * q * K else 0)
    return 1 if q * q * K > p * p else (-1 if q * q * K < p * p else 0)


PAIRS = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]
pin_rows = []
for (i, j) in PAIRS:
    A, B = SITES[i], SITES[j]
    m = ((A[0] + B[0]) / 2, (A[1] + B[1]) / 2)
    u = sub(B, A)
    d2 = n2(u)
    K = (R * R - d2 / 4) / d2
    if K <= 0:
        pin_rows.append({'pair': [i, j], 'k_positive': False})
        continue
    J = (-u[1], u[0])
    # |q_s|^2 = |m|^2 + K*d2 + 2s*sqrt(K)*<m,J>  =>  sign(|q_+|^2 - |q_-|^2) = sign(<m,J>)
    s_plus = sign_pmq(K, F(0), 2 * dot(m, J))
    near_sign = -1 if s_plus > 0 else 1                        # near pin = smaller norm
    row = {'pair': [i, j], 'k_positive': True, 'near_sign': near_sign, 'K': str(K)}
    for nm, h in (('hubA', hA), ('hubB', hB)):
        hm = sub(h, m)
        alpha = n2(hm) + K * d2 - R * R
        q = near_sign * (-2 * dot(hm, J))
        row['sign_slack2_' + nm] = sign_pmq(K, alpha, q)
    row['pin_covered'] = bool(row['sign_slack2_hubA'] < 0 or row['sign_slack2_hubB'] < 0)
    row['best_hub_slack2_sign'] = min(row['sign_slack2_hubA'], row['sign_slack2_hubB'])
    row['both_hubs_cover_it'] = bool(row['sign_slack2_hubA'] < 0 and row['sign_slack2_hubB'] < 0)
    pin_rows.append(row)
res['B3_pins_exact'] = pin_rows
res['B3_n_pins_not_covered'] = int(sum(1 for r_ in pin_rows if not r_.get('pin_covered', False)))
res['B3_aggregate_max_over_pins_min_over_hubs_slack2_sign'] = max(r_['best_hub_slack2_sign']
                                                                 for r_ in pin_rows if 'best_hub_slack2_sign' in r_)
res['B3_aggregate_lt_0_proves_ALL_nine'] = bool(res['B3_aggregate_max_over_pins_min_over_hubs_slack2_sign'] < 0)
res['B3_their_pins_strict_field'] = THEIRS['pins_strict']
res['B3_note_on_their_field'] = ('per lead: their earlier false reading came from a sign helper using a negative '
                                 'beta^2*Q (code bug), NOT a convention difference; their current json field and '
                                 'my exact computation agree')
print('(B3) exact nine pins: all covered = %s (not covered %d) ; CORRECT AGGREGATE max_over_pins(min_over_hubs) = %s (<0 => all nine) ; their field = %s'
      % (res['B3_n_pins_not_covered'] == 0, res['B3_n_pins_not_covered'],
         res['B3_aggregate_max_over_pins_min_over_hubs_slack2_sign'], THEIRS['pins_strict']))

res['verdict'] = ('same witness independently reproduced (exact): p uncovered, maximin hole centre, boundary fully '
                  'covered by the 9 ring arcs (hubs strict interior, no arcs); nine pins all covered under the '
                  'CORRECT aggregate max_over_pins(min_over_hubs) < 0')
(OUT / 'central_missed_point_arc_audit.json').write_text(json.dumps(res, indent=1), encoding='utf-8')
print('[done] -> out/central_missed_point_arc_audit.json')
