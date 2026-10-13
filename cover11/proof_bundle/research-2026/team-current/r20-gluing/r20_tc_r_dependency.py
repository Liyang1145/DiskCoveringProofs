# -*- coding: utf-8 -*-
"""R20-TC-RDEP (r20-gluing, sole writer this round): the CORRECT dependency picture of the
symmetric-active tight family, replacing the withdrawn "2 angle-only equations + explicit R".

Scope: symmetric active family (mirror symmetry + the 5 active tight rows + boundary
saturation), FINITE BRANCH only.  No whole-ring-domain claim.

Facts verified here (all point readings at the certified root, mp.dps = 50):
  T_k = sqrt(R^2 - sin^2 a_k)  =>  rho_k = cos a_k - T_k   =>  d rho_k/dR = -R/T_k != 0
  U_k = C_k + C_{k+1} - e_k    =>  Re U_k, Im U_k depend on (a, R) through the T's
  y0 = 2 Re U_3 - rho_4   (uses the U_3 row + chain identity |C_4 - U_3| = R + C_4 on axis)
  y1 = Re U_8 + R         (uses the U_8 row + U_8 on axis, Im U_8 = 0 identically)
  h  = sqrt(R^2 - d^2), d = (y1-y0)/2
  remaining content rows: E1 = U_1 row, E2 = U_2 row, E3 = waist row
  => THE FAMILY IS {E1 = E2 = E3 = 0}:  THREE equations in FIVE unknowns (a0..a3, R).

Withdrawn (this file replaces it): "the U_1 row is linear in R, so R is an explicit function of
the angles".  Rearranging gives 2 R (ReU_8 - ReU_1) + (ReU_8-ReU_1)^2 + (ImU_1)^2 = 0, but
ReU_8, ReU_1, ImU_1 all still depend on R (via the T's).  Evaluating that RHS at the true R is
circular: it is the fixed-point map R -> phi(R), not a closed form.  Demonstrated below.
"""
import json
import sys
from pathlib import Path

from mpmath import mp, mpf

HERE = Path(__file__).parent
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
OUT = HERE / 'r20_tc_r_dependency.json'
LOG = []


def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s)
    LOG.append(s)
    sys.stdout.flush()


def build(a04, y0v, y1v, Rv):
    """ring data as functions of the input tuple; Rv is an explicit argument (the point)."""
    a4 = mp.pi - 2 * sum(a04)
    a = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
    T = [mp.sqrt(Rv ** 2 - mp.sin(a[k]) ** 2) for k in range(9)]
    rho = [mp.cos(a[k]) - T[k] for k in range(9)]
    th = [None] * 9
    th[4] = mpf(0)
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
    e = [(mp.cos(th[k] + a[k]), mp.sin(th[k] + a[k])) for k in range(9)]
    U = [(C[k][0] + C[(k + 1) % 9][0] - e[k][0], C[k][1] + C[(k + 1) % 9][1] - e[k][1])
         for k in range(9)]
    return dict(T=T, rho=rho, th=th, C=C, e=e, U=U)


def rows(a04, Rv):
    """the 3 remaining content rows with y0,y1 eliminated (branch A/B) and h derived."""
    rd = build(a04, mpf(0), mpf(0), Rv)
    U, C, rho = rd['U'], rd['C'], rd['rho']
    y0 = 2 * U[3][0] - rho[4]
    y1 = U[8][0] + Rv
    m_ = (y0 + y1) / 2
    d_ = (y1 - y0) / 2
    h_ = mp.sqrt(Rv ** 2 - d_ ** 2)
    E1 = (y1 - U[1][0]) ** 2 + U[1][1] ** 2 - Rv ** 2
    E2 = (y0 - U[2][0]) ** 2 + U[2][1] ** 2 - Rv ** 2
    E3 = (m_ - C[6][0]) ** 2 + (h_ - C[6][1]) ** 2 - Rv ** 2
    return [E1, E2, E3], dict(y0=y0, y1=y1, m=m_, d=d_, h=h_, U=U, C=C, rho=rho)


def main():
    mp.dps = 50
    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    ch = d['certificate']['center_hex']
    a04 = [mpf(float.fromhex(ch[k])) for k in range(4)]
    y0v, y1v, Rv = (mpf(float.fromhex(ch[4])), mpf(float.fromhex(ch[5])), mpf(float.fromhex(ch[6])))
    radius = float.fromhex(d['certificate']['radius_hex'])
    rd = build(a04, y0v, y1v, Rv)
    rec = {}

    P('=== 1. R-dependence of the ring data (LOAD-BEARING, no explicit R possible) ===')
    tab = []
    for k in range(5):
        dR = -Rv / rd['T'][k]
        P('  k=%d  T_k = %.12f   d rho_k/dR = -R/T_k = %.9f' % (k, float(rd['T'][k]), float(dR)))
        tab.append(dict(k=k, T=fstr_f(rd['T'][k]), drho_dR=fstr_f(dR)))
    rec['drho_dR'] = tab
    h_ = mpf('1e-25')
    fd = []
    for k in range(5):
        def rk(Rx, kk=k):
            a4 = mp.pi - 2 * sum(a04)
            av = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
            return mp.cos(av[kk]) - mp.sqrt(Rx ** 2 - mp.sin(av[kk]) ** 2)
        fd.append((rk(Rv + h_) - rk(Rv - h_)) / (2 * h_))
    P('  finite-difference agreement (max |fd - (-R/T_k)|): %s' % fstr_f(max(abs(fd[k] + Rv / rd['T'][k]) for k in range(5))))
    rec['drho_dR_fd_maxdiff'] = fstr_f(max(abs(fd[k] + Rv / rd['T'][k]) for k in range(5)))

    P('')
    P('=== 2. the three remaining content rows (y0,y1 eliminated; h derived) ===')
    E, aux = rows(a04, Rv)
    for nm, v in zip(('E1 (U_1 row)', 'E2 (U_2 row)', 'E3 (waist row)'), E):
        P('  %-14s = %s' % (nm, fstr_f(v, 6)))
    P('  y0 = 2ReU_3 - rho_4 : diff vs certified y0 = %s' % fstr_f(aux['y0'] - y0v, 5))
    P('  y1 = ReU_8 + R      : diff vs certified y1 = %s' % fstr_f(aux['y1'] - y1v, 5))
    P('  h  = sqrt(R^2-d^2)  : %s' % fstr_f(aux['h'], 16))
    P('  => family = {E1 = E2 = E3 = 0}: 3 equations in 5 unknowns (a0..a3, R).')
    rec['content_rows_at_root'] = {'E1': fstr_f(E[0], 6), 'E2': fstr_f(E[1], 6), 'E3': fstr_f(E[2], 6)}
    rec['y0_y1_elimination_diffs'] = {'y0': fstr_f(aux['y0'] - y0v, 5), 'y1': fstr_f(aux['y1'] - y1v, 5)}
    rec['content_count'] = {'equations': 3, 'unknowns': ['a0', 'a1', 'a2', 'a3', 'R'],
                            'eliminated': ['y0 (U_3 row)', 'y1 (U_8 row)', 'h (derived: sqrt(R^2-d^2))']}

    P('')
    P('=== 3. the withdrawn "explicit R" rearrangement is a FIXED-POINT map, not a solution ===')
    U = aux['U']

    def phi(Rx):
        """the rearrangement R = -[(ReU_8-ReU_1)^2 + (ImU_1)^2] / (2 (ReU_8-ReU_1)) with the
        angles fixed at the root and R treated as the argument -- still implicit in R."""
        u = build(a04, mpf(0), mpf(0), Rx)['U']
        dd = u[8][0] - u[1][0]
        return -((dd) ** 2 + u[1][1] ** 2) / (2 * dd)

    for dR in (mpf(0), mpf('1e-3'), mpf('-1e-3')):
        P('  R = %.16f : phi(R) - R = %s' % (float(Rv + dR), fstr_f(phi(Rv + dR) - (Rv + dR), 4)))
    P('  (phi(R*) = R* is the fixed-point identity; for R != R* phi(R) != R, so phi is NOT an')
    P('   explicit function of the angles.  The angles do not enter phi alone: R enters via T_k.)')
    rec['fixed_point_map'] = {('R%+0.0e' % float(dR)): fstr_f(phi(Rv + dR) - (Rv + dR), 4)
                              for dR in (mpf(0), mpf('1e-3'), mpf('-1e-3'))}

    # analytic dE1/dR  (nonzero => R is locally an implicit function of the angles from E1 alone)
    def E1_of_R(Rx):
        return rows(a04, Rx)[0][0]
    dE1 = (E1_of_R(Rv + h_) - E1_of_R(Rv - h_)) / (2 * h_)
    P('')
    P('  dE1/dR at the root = %s  (nonzero => R is LOCALLY an implicit function of the angles;' % fstr_f(dE1, 8))
    P('   but no closed form exists and the family needs all three rows.)')
    rec['dE1_dR'] = fstr_f(dE1, 8)

    P('')
    P('=== 4. dependency graph (data) ===')
    graph = {
        'a_k': ['sin a_k', 'cos a_k', 'theta_k', 'e_k', 'T_k (jointly with R)'],
        'R': ['T_k = sqrt(R^2 - sin^2 a_k)', 'd = (y1-y0)/2', 'h = sqrt(R^2-d^2)',
              'explicit -R^2 / +R terms in E1,E2,E3'],
        'T_k -> rho_k -> C_k -> U_k': ['Re U_k', 'Im U_k'],
        'U_k, R': ['y0 = 2ReU_3 - rho_4', 'y1 = ReU_8 + R', 'E1, E2, E3'],
    }
    for kk, vv in graph.items():
        P('  %s -> %s' % (kk, ', '.join(vv)))
    rec['dependency_graph'] = graph
    P('  => R is NOT eliminable from the closed representation: it occurs inside every T_k,')
    P('     inside y1, and explicitly.  Any claim "R = explicit function of the angles" is false.')

    P('')
    P('=== 5. branch facts (the two complementary roots) ===')
    y0_other = rd['rho'][4]
    y1_other = U[8][0] - Rv
    inner = 1 - Rv
    P('  y0 = rho_4 = C_4.x = %s  ; |H0| = %s  vs 1-R = %s  -> %s'
      % (fstr_f(y0_other, 10), fstr_f(abs(y0_other), 10), fstr_f(inner, 10),
         'INFEASIBLE if hubs must be inner-disk centres (|H| <= 1-R)' if abs(y0_other) > inner else 'admissible'))
    P('  y1 = ReU_8 - R = %s  ; |H1| = %s  vs 1-R = %s  -> %s'
      % (fstr_f(y1_other, 10), fstr_f(abs(y1_other), 10), fstr_f(inner, 10),
         'INFEASIBLE if hubs must be inner-disk centres (|H| <= 1-R)' if abs(y1_other) > inner else 'admissible'))
    rec['branch_facts'] = {
        'y0_other_rho4': fstr_f(y0_other, 12), 'y1_other': fstr_f(y1_other, 12),
        'one_minus_R': fstr_f(inner, 12),
        'note': 'both complementary roots make |H| > 1-R; exclusion is conditional on the '
                'inner-disk-centre requirement |H| <= 1-R, which is part of the model class, '
                'not proved here'}

    rec['scope'] = ('symmetric active family (mirror + 5 active rows + boundary saturation), '
                    'finite branch only; point readings at the certified root, mp.dps=50; '
                    'no whole-ring-domain claim')
    rec['withdrawn'] = ('"2 angle-only equations + explicit R": the U_1 rearrangement is a '
                        'fixed-point map, not an R-elimination; correct count is 3 equations in '
                        '5 unknowns (a0..a3,R)')
    rec['root'] = {'a04': [fstr_f(v, 20) for v in a04], 'y0': fstr_f(y0v, 20),
                   'y1': fstr_f(y1v, 20), 'R': fstr_f(Rv, 20), 'box_radius': radius}
    OUT.write_text(json.dumps(rec, indent=2))
    (HERE / 'r20_tc_r_dependency.log').write_text('\n'.join(LOG) + '\n')
    print('\nsaved %s / r20_tc_r_dependency.log' % OUT.name)


def fstr_f(v, n=8):
    try:
        return mp.nstr(mp.mpf(v), n)
    except Exception:
        return str(v)


if __name__ == '__main__':
    main()
