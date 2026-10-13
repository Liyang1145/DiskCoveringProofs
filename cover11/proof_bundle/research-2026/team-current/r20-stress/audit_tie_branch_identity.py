"""Bearing check A (lead's request): is the FROZEN TIEPICK branch really the C892 boundary tie?

r20-rigidity picks the tie sign per gap at the CENTRE by a numeric nearest-site criterion and then
freezes it for the whole box.  Numeric nearest choice does NOT by itself certify that the chosen
branch is the C892 boundary tie on the box.  This script certifies, on the whole lead box:

  A1  the chosen intersection p*_k coincides with the CHART tie unit vector
      P_k = (cos(theta_k + a_k), sin(theta_k + a_k))  :  sup |p* - P|^2 <= 1e-6
  A2  the OTHER intersection is separated from P_k    :  inf |p_other - P|^2 >= 1e-4
      (and the two intersections are separated: inf |p_+ - p_-|^2 > 0)
  A3  non-incident sites are strictly farther than R  :  inf (|p* - C_i|^2 - R^2) > 0.01  (i != k,k+1)
      and the incident sites tie                           :  0 in |p* - C_k|^2 - R^2, same for k+1
  A4  the TIEPICK criterion FAILS with margin at the other intersection (so the frozen choice is
      uniquely correct on the box):  min_{i not in pair} |p_other - C_i|  <  max(|p_other-C_k|,
      |p_other-C_{k+1}|) - 0.01

Construction copied from the audited file (unit circle intersected with the radical line of the two
disks: p . d = kap, |p| = 1), evaluated in interval arithmetic.  Read-only inputs; writes only in
r20-stress/out .
"""
import json, os
from pathlib import Path
from mpmath import mp, iv, mpf

mp.dps = 60
iv.dps = 35
W = Path(__file__).parent
OUT = W / 'out'
LEAD = W.parent / 'lead'
CERT = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text(encoding='utf-8'))
RAD = float.fromhex(CERT['certificate']['radius_hex'])
CH = [float.fromhex(v) for v in CERT['certificate']['center_hex']]

z = [iv.mpf(CH[i]) + iv.mpf([-RAD, RAD]) for i in range(7)]
a0, a1, a2, a3, y0, y1, R = z
a4 = iv.pi - 2 * (a0 + a1 + a2 + a3)
ak = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
SIN = [iv.sin(a) for a in ak]
RHO = [iv.cos(ak[k]) - iv.sqrt(R * R - SIN[k] * SIN[k]) for k in range(9)]
TH = [iv.mpf(0)] * 9
for k in range(5, 9):
    TH[k] = TH[k - 1] + ak[k - 1] + ak[k]
for k in range(3, -1, -1):
    TH[k] = TH[k + 1] - (ak[k] + ak[k + 1])
C = [(RHO[k] * iv.cos(TH[k]), RHO[k] * iv.sin(TH[k])) for k in range(9)]
SITE = C + [(y0, iv.mpf(0)), (y1, iv.mpf(0))]          # 9 rings + H0 + H1


def LO(x):
    return mpf(x.a)


def HI(x):
    return mpf(x.b)


def d2(P, Q):
    return (P[0] - Q[0]) * (P[0] - Q[0]) + (P[1] - Q[1]) * (P[1] - Q[1])


rows = []
all1 = all2 = all3 = all4 = True
min_noninc = None
min_other_margin = None
for k in range(9):
    ca, cb = SITE[k], SITE[(k + 1) % 9]
    dx, dy = cb[0] - ca[0], cb[1] - ca[1]
    D = dx * dx + dy * dy
    kap = ((cb[0] * cb[0] + cb[1] * cb[1]) - (ca[0] * ca[0] + ca[1] * ca[1])) / 2
    dl = iv.sqrt(D)
    a0x, a0y = (kap / D) * dx, (kap / D) * dy
    one_minus = 1 - (a0x * a0x + a0y * a0y)
    t = iv.sqrt(one_minus)
    cand = []
    for sgn in (1, -1):
        p = (a0x + sgn * t * (-dy / dl), a0y + sgn * t * (dx / dl))
        cand.append(p)
    Pchart = (iv.cos(TH[k] + ak[k]), iv.sin(TH[k] + ak[k]))
    dP = [d2(p, Pchart) for p in cand]
    i_ch = 0 if HI(dP[0]) <= HI(dP[1]) else 1
    p_star, p_oth = cand[i_ch], cand[1 - i_ch]
    A1 = bool(HI(dP[i_ch]) <= mpf('1e-6'))
    A2a = bool(LO(d2(p_oth, Pchart)) >= mpf('1e-4'))
    A2b = bool(LO(d2(cand[0], cand[1])) > 0)
    inci = sorted(d2(p_star, SITE[i]) - R * R for i in (k, (k + 1) % 9))
    tie_ok = all(LO(x) <= 0 <= HI(x) for x in inci)
    non = [(i, d2(p_star, SITE[i]) - R * R) for i in range(11) if i not in (k, (k + 1) % 9)]
    nmin = min(LO(x) for _, x in non)
    A3 = bool(tie_ok and nmin > mpf('0.01'))
    dd_oth = [iv.sqrt(d2(p_oth, SITE[i])) for i in range(11)]
    inci_d = max(LO(dd_oth[k]), LO(dd_oth[(k + 1) % 9]))
    non_d = min(HI(dd_oth[i]) for i in range(11) if i not in (k, (k + 1) % 9))
    other_margin = inci_d - non_d        # > 0  <=>  some non-incident site is strictly closer
    A4 = bool(other_margin > mpf('0.01'))
    all1 &= A1
    all2 &= (A2a and A2b)
    all3 &= A3
    all4 &= A4
    min_noninc = nmin if min_noninc is None else min(min_noninc, nmin)
    min_other_margin = other_margin if min_other_margin is None else min(min_other_margin, other_margin)
    rows.append(dict(gap=k, sgn_effective=int(1 if i_ch == 0 else -1),
                     dist2_chosen_to_chart=[mp.nstr(LO(dP[i_ch]), 6), mp.nstr(HI(dP[i_ch]), 6)],
                     dist2_other_to_chart=[mp.nstr(LO(dP[1 - i_ch]), 6), mp.nstr(HI(dP[1 - i_ch]), 6)],
                     sep_two_intersections=mp.nstr(LO(d2(cand[0], cand[1])), 6),
                     incident_contains_zero=bool(tie_ok), min_nonincident_margin=mp.nstr(nmin, 6),
                     other_branch_margin=mp.nstr(other_margin, 6),
                     A1=A1, A2=A2a and A2b, A3=A3, A4=A4))

base = Path('research-2026/team-current/r20-rigidity/r20_anti_block_interval.py')
import hashlib
snap = None
if base.exists():
    b = base.read_bytes()
    snap = dict(bytes=len(b), sha256=hashlib.sha256(b).hexdigest())

print('=== bearing check A: frozen TIEPICK branch = the C892 boundary tie? (whole box) ===')
print('box: lead Krawczyk radius %.3e ; r20-rigidity snapshot %s' % (RAD, snap))
for r in rows:
    print('  gap %d: A1 %s | A2 %s | A3 %s | A4 %s | d2(chosen,chart)=%s  d2(other,chart)=%s  '
          'non-incident margin >= %s  other-branch margin >= %s'
          % (r['gap'], r['A1'], r['A2'], r['A3'], r['A4'],
             r['dist2_chosen_to_chart'], r['dist2_other_to_chart'],
             r['min_nonincident_margin'], r['other_branch_margin']))
print()
print('ALL 9 gaps: A1 %s | A2 %s | A3 %s | A4 %s' % (all1, all2, all3, all4))
print('min non-incident margin    =', mp.nstr(min_noninc, 8))
print('min other-branch margin    =', mp.nstr(min_other_margin, 8))

# ---- bearing check B control: min(|lo|,|hi|) > 0 does NOT exclude zero crossing
x = iv.mpf([-1, 2])
ctl = dict(interval=str(x), min_abs_endpoint=mp.nstr(min(abs(LO(x)), abs(HI(x))), 6),
           contains_zero=bool(LO(x) <= 0 <= HI(x)),
           wrong_test_min_abs_gt_0=bool(min(abs(LO(x)), abs(HI(x))) > 0),
           exact_test_lo_gt_0_or_hi_lt_0=bool(LO(x) > 0 or HI(x) < 0))
print()
print('=== bearing check B control ===')
print('   interval %s : min(|lo|,|hi|) = %s > 0  -> %s ; contains 0 = %s ; exact test (lo>0 or hi<0) = %s'
      % (ctl['interval'], ctl['min_abs_endpoint'], ctl['wrong_test_min_abs_gt_0'],
         ctl['contains_zero'], ctl['exact_test_lo_gt_0_or_hi_lt_0']))

out = dict(scope='bearing check A: certify on the box that the frozen TIEPICK tie branch is the '
                 'C892 boundary tie (chart-angle unit vector), that the other intersection is '
                 'separated, that non-incident sites are >0.01 farther, and that the TIEPICK '
                 'criterion fails with margin at the other branch; plus check-B control on the '
                 'zero-crossing test.  Interval arithmetic on the lead box; conditional on the '
                 'lead Krawczyk box only.',
           snapshot_of_audited_code=snap, box_radius_hex=CERT['certificate']['radius_hex'],
           per_gap=rows, A1_all=all1, A2_all=all2, A3_all=all3, A4_all=all4,
           min_nonincident_margin=mp.nstr(min_noninc, 10),
           min_other_branch_margin=mp.nstr(min_other_margin, 10),
           check_B_control=ctl)
(OUT / 'audit_tie_branch_identity.json').write_text(json.dumps(out, indent=2), encoding='utf-8')
print('[done] -> out/audit_tie_branch_identity.json')
