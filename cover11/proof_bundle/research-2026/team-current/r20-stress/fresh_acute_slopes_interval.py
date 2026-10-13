"""FRESH interval kernel (my only obligation per lead): interval acuteness of the C891-root faces and
opposite tangential distance slopes at the nine boundary ties, WITH MARGINS.

Provenance discipline (lead): the interval centers are built from the SAME source-level construction as
lead/check_tc_root_geometry.py (read and mirrored here: repaired_tc_krawczyk.json box -> u -> z=u[:7],
r=z[6], a4=pi-2*sum(z[:4]), a=[z0,z1,z2,z3,a4,z3,z2,z1,z0], rho[k]=cos(a_k)-sqrt(r^2-sin^2 a_k),
theta recurrence, c = 9 rings + hubs (z4,0),(z5,0), tie B[k]=(cos(th_k+a_k), sin(th_k+a_k))).
No use of any previous JSON reading as if it were interval: every number below is computed here in
mpmath.iv (dps=50, same as the lead's file).  Float midpoints are used ONLY to print orientation, never
as a certificate.

Outputs (writes only in r20-stress/out):
  * per-face acuteness margins: min over the three vertex-angle dot products of the interval LOWER bound
    (acuteness certifies the circumcentre barycentrics are positive: beta = (sin2A:sin2B:sin2C));
  * per-tie tangential slopes: the two angular derivatives <u_i, J B_k> at the tie for the two adjacent
    sites, as intervals, with sign and a lower bound on |value| for each -> "opposite, each away from 0".
"""
from pathlib import Path
import json, sys
from mpmath import mp, iv

mp.dps = 60
iv.dps = 50
W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'
cert = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())['certificate']
rad = float.fromhex(cert['radius_hex'])
u = [iv.mpf(float.fromhex(v)) + iv.mpf([-rad, rad]) for v in cert['center_hex']]
z = u[:7]
r = z[6]
a4 = iv.pi - 2 * sum(z[:4])
a = [z[0], z[1], z[2], z[3], a4, z[3], z[2], z[1], z[0]]
rho = [iv.cos(v) - iv.sqrt(r * r - iv.sin(v) ** 2) for v in a]
th = [iv.mpf(0)] * 9
for k in range(5, 9):
    th[k] = th[k - 1] + a[k - 1] + a[k]
for k in range(3, -1, -1):
    th[k] = th[k + 1] - (a[k] + a[k + 1])
c = [(rho[k] * iv.cos(th[k]), rho[k] * iv.sin(th[k])) for k in range(9)] + [(z[4], iv.mpf(0)), (z[5], iv.mpf(0))]
B = [(iv.cos(th[k] + a[k]), iv.sin(th[k] + a[k])) for k in range(9)]
FACES = [[2, 9, 10], [6, 9, 10]] + [[k, (k + 1) % 9, 9 if 2 <= k <= 5 else 10] for k in range(9)]


def LO(x):
    return mp.mpf(x.a)


def HI(x):
    return mp.mpf(x.b)


def mid(x):
    return (LO(x) + HI(x)) / 2


def dot(P, Q):
    return P[0] * Q[0] + P[1] * Q[1]


def sub(P, Q):
    return (P[0] - Q[0], P[1] - Q[1])


rows = []
worst_acute = mp.inf
n_margin_ok = 0
for f in FACES:
    A, Bv, C = c[f[0]], c[f[1]], c[f[2]]
    dots = [dot(sub(A, Bv), sub(C, Bv)), dot(sub(Bv, A), sub(C, A)), dot(sub(A, C), sub(Bv, C))]
    lb = min(LO(d) for d in dots)
    ok = lb > 0
    n_margin_ok += int(ok)
    worst_acute = min(worst_acute, lb)
    rows.append({'face': f, 'acute': bool(ok), 'acuteness_margin_lower': mp.nstr(lb, 12),
                 'circumcentre_barycentrics_positive': bool(ok)})
print('=== ACUTENESS (fresh interval kernel, dps=50) ===')
print('   faces: %d ; strictly acute with positive margin: %d ; worst vertex-angle dot lower bound = %s'
      % (len(FACES), n_margin_ok, mp.nstr(worst_acute, 12)))
print('   faces acute: %d/%d (the 9 active faces are a subset of these 11, so they are acute too)'
      % (n_margin_ok, len(FACES)))

print('   per-face (face, acute, margin):')
for row in rows:
    print('     %-14s %s  %s' % (row['face'], row['acute'], row['acuteness_margin_lower']))

tie_rows = []
both_ok = 0
THR = mp.mpf('0.51')      # conservative uniform threshold on |tangential slope| (lead)
for k in range(9):
    b = B[k]
    vals = []
    for i in (k, (k + 1) % 9):
        # lead's convention: direction (U - c)/norm; the distance angular derivative is the NEGATIVE of the
        # (c-U) form, so the opposite-sign property is unchanged.
        ux = b[0] - c[i][0]
        uy = b[1] - c[i][1]
        nrm = iv.sqrt(ux * ux + uy * uy)
        vals.append((ux * (-b[1]) + uy * b[0]) / nrm)
    # two-sided exhaustive sign decision from the RAW intervals (never LO-only; never min|endpoint| to prove
    # non-crossing: that requires the exhaustive HI<0 or LO>0 test used here).
    neg = [HI(v) < 0 for v in vals]
    pos = [LO(v) > 0 for v in vals]
    decidable = [bool(neg[i] or pos[i]) for i in (0, 1)]
    opposite = bool(decidable[0] and decidable[1] and ((neg[0] and pos[1]) or (pos[0] and neg[1])))
    # magnitude lower bound is valid ONLY because that interval was shown strictly one-sided above
    mag = [min(abs(LO(vals[i])), abs(HI(vals[i]))) if decidable[i] else mp.mpf(0) for i in (0, 1)]
    ok = bool(opposite and mag[0] >= THR and mag[1] >= THR)
    both_ok += int(ok)
    tie_rows.append({'tie': k, 'sites': [k, (k + 1) % 9],
                     'sign_decidable_two_sided': decidable,
                     'sites_neg': [bool(neg[0]), bool(neg[1])], 'sites_pos': [bool(pos[0]), bool(pos[1])],
                     'opposite_signs': opposite,
                     'abs_lower_bound_site_k': mp.nstr(mag[0], 12),
                     'abs_lower_bound_site_k1': mp.nstr(mag[1], 12),
                     'ge_threshold_0.51_both_sides': bool(mag[0] >= THR and mag[1] >= THR),
                     'criterion_ok': ok,
                     # nstr values below are DIAGNOSTIC only (they drop the directed rounding)
                     'slope_interval_site_k_diagnostic': [mp.nstr(LO(vals[0]), 12), mp.nstr(HI(vals[0]), 12)],
                     'slope_interval_site_k1_diagnostic': [mp.nstr(LO(vals[1]), 12), mp.nstr(HI(vals[1]), 12)]})
print('=== TIE TANGENTIAL SLOPES (criteria from RAW iv; nstr fields = diagnostic only) ===')
print('   ties with [two-sided decidable AND opposite signs AND both |slope| >= 0.51]: %d/9' % both_ok)
for row in tie_rows:
    print('     tie %d sites %s decidable=%s neg=%s pos=%s opposite=%s |.|>=%s/%s ok=%s'
          % (row['tie'], row['sites'], row['sign_decidable_two_sided'], row['sites_neg'], row['sites_pos'],
             row['opposite_signs'], row['abs_lower_bound_site_k'], row['abs_lower_bound_site_k1'],
             row['criterion_ok']))

out = {'scope': 'fresh mpmath.iv kernel (dps=50) on the repaired TC root box; interval centers built from '
                'the same source-level construction as lead/check_tc_root_geometry.py; no previous JSON reading '
                'is used as a certificate',
       'faces': rows, 'n_faces': len(FACES), 'n_acute_with_margin': int(n_margin_ok),
       'worst_acuteness_margin_lower': mp.nstr(worst_acute, 15),
       'ties': tie_rows, 'n_ties_opposite_and_away_from_zero': int(both_ok),
       'float_pilot_disclosure': 'mpmath.iv throughout; float() only for printing orientation'}
(OUT / 'fresh_acute_slopes_interval.json').write_text(json.dumps(out, indent=1), encoding='utf-8')
print('[done] -> out/fresh_acute_slopes_interval.json')
