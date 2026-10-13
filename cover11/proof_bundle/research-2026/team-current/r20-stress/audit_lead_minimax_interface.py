"""Brief independent audit of the lead's two interface notes (lead request, third round).

Inputs (READ-ONLY):
    ../lead/tc_symmetric_hessian.json                 (interval Gram certificate)
    ../lead/FINITE-MINIMAX-QUALITATIVE-SUFFICIENCY.md  (theorem + application requirements)
    ../lead/TC-SYMMETRIC-SECOND-VARIATION.md           (G = Z^T H Z, interface to physical 12D)
    ../lead/repaired_tc_krawczyk.json                  (the box, for the premise check below)

Two things are done here:
  (A) EXACT-RATIONAL re-verification of the finite arithmetic recorded in the lead's Hessian
      certificate: determinant recomputed from the Gram entries, Sylvester, det/trace > 1/4,
      and the display tuples being conservative.  Uses fractions.Fraction only (no floats for
      the decisions).
  (B) INTERVAL premise check on the same box (my instrument): the theorem needs every one of
      the 18 active branch functions to equal R at the root.  I evaluate the 9 face
      circumradii and the 9 boundary tie radii (switch waist legs) as intervals and compare
      them with the R interval.

Writes only in r20-stress/out .
"""
import os, sys, json
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from fractions import Fraction as Fr
from pathlib import Path
from mpmath import mp, iv, mpf

mp.dps = 60
iv.dps = 35
W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'


def F(s):
    return Fr(s)


# ------------------------------------------------------------------ (A) exact re-derivation
H = json.loads((LEAD / 'tc_symmetric_hessian.json').read_text(encoding='utf-8'))
G = [[[F(H['gram_exact'][i][j][0]), F(H['gram_exact'][i][j][1])] for j in range(2)] for i in range(2)]
DET = [F(H['det_exact'][0]), F(H['det_exact'][1])]
LAMLO = F(H['lambda_min_lower_exact'])


def mul(a, b):
    c = [x * y for x in a for y in b]
    return [min(c), max(c)]


def sub(a, b):
    return [a[0] - b[1], a[1] - b[0]]


def add(a, b):
    return [a[0] + b[0], a[1] + b[1]]


det_iv = sub(mul(G[0][0], G[1][1]), mul(G[0][1], G[1][0]))
trace_iv = add(G[0][0], G[1][1])
# det/trace  (trace > 0)
ratio_iv = [det_iv[0] / trace_iv[1], det_iv[1] / trace_iv[0]]
A = {}
A['det_recomputed_from_G'] = [str(det_iv[0]), str(det_iv[1])]
# the recorded det must CONTAIN the naive determinant enclosure of the recorded Gram box
A['naive_det_enclosure_inside_recorded'] = (DET[0] <= det_iv[0] and det_iv[1] <= DET[1])
A['recorded_minus_naive_lo'] = str(DET[0] - det_iv[0])
A['recorded_minus_naive_hi'] = str(DET[1] - det_iv[1])
A['det_interval_positive'] = DET[0] > 0
A['G00_positive'] = G[0][0][0] > 0
A['G11_positive'] = G[1][1][0] > 0
A['sylvester_PD'] = G[0][0][0] > 0 and DET[0] > 0
A['trace_positive'] = trace_iv[0] > 0
A['det_over_trace_min'] = str(ratio_iv[0])
A['det_over_trace_gt_quarter'] = ratio_iv[0] > Fr(1, 4)
A['recorded_lambda_min_lower'] = str(LAMLO)
A['lambda_min_lower_is_below_det_over_trace'] = LAMLO <= ratio_iv[0]
# display tuples must be conservative summaries of the exact intervals
disp_ok = True
for i in range(2):
    for j in range(2):
        lo, hi = H['gram_display'][i][j]
        if not (float(G[i][j][0]) >= lo - 1e-12 and float(G[i][j][1]) <= hi + 1e-12):
            disp_ok = False
A['gram_display_conservative'] = disp_ok
A['det_display_conservative'] = (float(DET[0]) >= H['det_display'][0] - 1e-12 and
                                 float(DET[1]) <= H['det_display'][1] + 1e-12)
# graph-basis structure: free coordinates (rows 4,5) are the identity
B = [[[F(v[0]), F(v[1])] for v in row] for row in H['basis_exact']]
A['basis_is_7x2'] = len(B) == 7 and all(len(r) == 2 for r in B)
A['basis_free_rows_identity'] = (B[4] == [[Fr(1), Fr(1)], [Fr(0), Fr(0)]] and
                                 B[5] == [[Fr(0), Fr(0)], [Fr(1), Fr(1)]])
A['gram_symmetric_bit_exact'] = (G[0][1] == G[1][0])
A['gram_offdiag_max_endpoint_diff'] = str(max(abs(G[0][1][k] - G[1][0][k]) for k in range(2)))
A['lead_pass_flag'] = H.get('pass')

# ------------------------------------------------------------------ (B) 18 branches = R at the root
sys.path.insert(0, str(W))
from weights_interface import root_box                                    # noqa: E402

BOX = root_box()
a04, y0, y1, R = BOX[0:4], BOX[4], BOX[5], BOX[6]
a4 = iv.pi - 2 * (a04[0] + a04[1] + a04[2] + a04[3])
Aa = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
SIN = [iv.sin(a) for a in Aa]
RHO = [iv.cos(Aa[k]) - iv.sqrt(R * R - SIN[k] * SIN[k]) for k in range(9)]
TH = [iv.mpf(0)] * 9
for k in range(5, 9):
    TH[k] = TH[k - 1] + Aa[k - 1] + Aa[k]
for k in range(3, -1, -1):
    TH[k] = TH[k + 1] - (Aa[k] + Aa[k + 1])
C = [(RHO[k] * iv.cos(TH[k]), RHO[k] * iv.sin(TH[k])) for k in range(9)]
HUB = [(y0, iv.mpf(0)), (y1, iv.mpf(0))]


def dist2(P, Q):
    return (P[0] - Q[0]) * (P[0] - Q[0]) + (P[1] - Q[1]) * (P[1] - Q[1])


def circumradius(Apt, Bpt, Cpt):
    la = iv.sqrt(dist2(Bpt, Cpt))
    lb = iv.sqrt(dist2(Apt, Cpt))
    lc = iv.sqrt(dist2(Apt, Bpt))
    cross = (Bpt[0] - Apt[0]) * (Cpt[1] - Apt[1]) - (Bpt[1] - Apt[1]) * (Cpt[0] - Apt[0])
    if not (mpf(cross.a) > 0 or mpf(cross.b) < 0):
        raise ValueError('degenerate triangle on the box')
    area2 = iv.sqrt(cross * cross)          # |cross| = 2*area
    return la * lb * lc / (2 * area2)       # circumradius = abc/(4*Area) = abc/(2|cross|)


FACES = [('fan', 1, 1), ('fan', 6, 1), ('fan', 2, 0), ('fan', 5, 0), ('fan', 3, 0),
         ('fan', 4, 0), ('fan', 8, 1), ('central', 6, 0), ('central', 2, 0)]
face_rows = []
for (kind, k, l) in FACES:
    if kind == 'fan':
        Apt, Bpt, Cpt = C[k], C[(k + 1) % 9], HUB[l]
    else:
        Apt, Bpt, Cpt = HUB[0], HUB[1], C[k]
    rr = circumradius(Apt, Bpt, Cpt)
    face_rows.append((('face %s(%d,%d)' % (kind, k, l)), rr))

tie_rows = []
for j in range(9):
    Pw = (iv.cos(TH[j] + Aa[j]), iv.sin(TH[j] + Aa[j]))     # tie point on the unit circle
    tie_rows.append(('tie gap%d' % j, iv.sqrt(dist2(C[j], Pw))))


def overlap(x, y):
    return not (mpf(x.b) < mpf(y.a) or mpf(y.b) < mpf(x.a))


def gap(x, y):
    if overlap(x, y):
        return mpf(0)
    return min(abs(mpf(x.a) - mpf(y.b)), abs(mpf(y.a) - mpf(x.b)))


B_rows = []
for nm, rr in face_rows + tie_rows:
    B_rows.append((nm, mpf(rr.a), mpf(rr.b), overlap(rr, R), gap(rr, R)))

B_ok = all(r[3] for r in B_rows)
# CAUTION (lead 2026-09-25): interval intersection with R is COMPATIBILITY ONLY, it is NOT a proof
# that the exact root has branch = R.  That equality is ANALYTIC (root F=0 + chart + positive
# conversion: Fin=0 & Fout>0 & y!=0 => rho_face=R ; g=0 => t_j=R).  What the interval run
# legitimately certifies is the POSITIVITY of the conversion factors plus consistency.
A['all_18_branch_intervals_compatible_with_R'] = B_ok
A['caliber_branch_row'] = ('compatibility only; "branch = R at the exact root" is analytic '
                           '(root F=0 + chart + positive conversion), NOT inferred from intersection')
WIW = None
try:
    from weights_interface import physical_weights
    WIW = physical_weights(BOX)
    A['conversion_Fout_positive'] = all(mpf(x.a) > 0 for x in WIW['F_out'])
    A['conversion_y_nonzero'] = all(not (mpf(x.a) <= 0 <= mpf(x.b)) for x in WIW['y_height'])
    A['weights_18_strictly_positive'] = (
        all(mpf(x.a) > 0 for x in WIW['face_weight_9']) and
        all(mpf(x.a) > 0 for x in WIW['tie_weight']))
except Exception as e:                     # pragma: no cover
    A['conversion_factor_check_error'] = repr(e)
A['max_branch_R_gap'] = str(max(r[4] for r in B_rows))

print('=== (A) exact-rational re-verification of lead/tc_symmetric_hessian.json ===')
for k in sorted(A):
    print('   %-42s %s' % (k, A[k]))
print()
print('=== (B) compatibility check on the box: 18 active branch intervals vs R ===')
print('    (intersection = compatibility ONLY; "branch = R at the exact root" is analytic:')
print('     root F=0 + chart + positive conversion (Fout>0, y!=0) => rho_face=R ; g=0 => t_j=R)')
for nm, lo, hi, ov, gp in B_rows:
    print('   %-18s [%s, %s]   overlaps R=%s  gap=%s'
          % (nm, mp.nstr(lo, 16), mp.nstr(hi, 16), ov, mp.nstr(gp, 3)))
print()
print('   R interval = [%s, %s]' % (mp.nstr(mpf(R.a), 20), mp.nstr(mpf(R.b), 20)))
print('   all 18 branch intervals compatible with R (compatibility, not equality):', B_ok)

out = dict(scope='brief independent audit of the lead minimax/second-variation interface; '
                 'exact-rational re-derivation of the recorded Gram determinant/Sylvester/'
                 'det-trace claims + box COMPATIBILITY check (branch intervals vs R) and '
                 'certification of the positive conversion factors on the same box; '
                 'NOTE: interval intersection does not prove branch=R, that is analytic',
           part_A_exact_recheck=A,
           part_B_branch_table=[[nm, mp.nstr(lo, 20), mp.nstr(hi, 20), bool(ov), mp.nstr(gp, 4)]
                                for nm, lo, hi, ov, gp in B_rows],
           R_interval=[mp.nstr(mpf(R.a), 25), mp.nstr(mpf(R.b), 25)])
(OUT / 'audit_lead_minimax_interface.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print('[done] -> out/audit_lead_minimax_interface.json')
