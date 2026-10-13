"""
central_span_dual_controls.py
=============================
Controls for the REPAIRED ring-only central-span filter.

Object
------
q0(6,7) two-hub class, radius r.  Ring data: the two shared junction rings c0, c4.
  D := |c0 - c4|                    (ring endpoint separation, RING DATA)
  d := |hA - hB|                    (hub separation, the eliminated variable)
Necessary condition (lead/R20-CENTRAL-SPAN-NECESSITY.md, complete reading):
  both central triangles (hA,hB,c0),(hA,hB,c4) have positive area and circumradius <= r
  ==>  d <= 2r  and  D <= 2r + 2*sqrt(r^2 - d^2/4)
  ==>  if D >= 2r:   d^2 <= 4rD - D^2   (equivalently d^2 + (D-2r)^2 <= 4r^2)
Filter (with the lead's CQ-free quadratic dual, lead/HUB-DISTANCE-QUADRATIC-DUAL.md):
  L(alpha,beta) <= d^2  for every nonnegative multiplier choice
  ==> D >= 2r and L > 4rD - D^2  ==>  no cover with these rings.
Branches: D > 4r impossible outright; D < 2r gives only d <= 2r (section A4 control).

Sections
--------
A. span algebra        : symbolic identity + exact rational sampling (Pythagorean k),
                         monotone threshold for ring boxes, exact counterexample showing the
                         D<2r branch genuinely carries no span information.
B. quadratic dual      : lead's three exact controls reproduced; two-tangent-disks singleton
                         degeneracy (non-attainment of finite multipliers); crossing lens with
                         KKT multipliers attaining dist^2 (Slater branch); internal tangency and
                         3-disk positively-spanning singleton (normal cone == active gradient
                         cone in those cases).
C. candidate calibration: saved rational q0 rings; the filter must NOT exclude the known-valid
                         candidate (falsifier check).  Floats, calibration only.

Routing: cline2/deepseek-v4.1f, writes only research-2026/team-current/r20-alternative/.
No claim is registered by this script; it is a control file.
"""
from fractions import Fraction as F
import json
import math
import os
import random
from pathlib import Path

import sympy as sp

HERE = Path(__file__).resolve()
BASE = HERE.parents[3]                      # ai4math2/
OUT = HERE.with_suffix('.json')
RES = {'route': 'cline2/deepseek-v4.1f',
       'kind': 'controls only; no claim registered',
       'template': ['lead/R20-CENTRAL-SPAN-NECESSITY.md (D=|c0-c4|, d=|hA-hB|)',
                    'lead/HUB-DISTANCE-QUADRATIC-DUAL.md eq.(1) (CQ-free quadratic dual)']}


# --------------------------------------------------------------------------------------
# A. span algebra
# --------------------------------------------------------------------------------------
def section_A():
    out = {}
    # --- A1: crescent containment identity (base pair = hub edge, vertex = ring site) ---
    x, y, d, R, k = sp.symbols('x y d R k', positive=True)
    # c = m + x*e + y*n ; p_pm = m +- k*n ;  rho = circumradius(a,b,c)
    rho2 = ((x + d / 2) ** 2 + y ** 2) * ((x - d / 2) ** 2 + y ** 2) / (4 * y ** 2)
    lhs = sp.expand(4 * y ** 2 * (rho2 - R ** 2))
    rhs = sp.expand((x ** 2 + (y - k) ** 2 - R ** 2) * (x ** 2 + (y + k) ** 2 - R ** 2))
    E = sp.expand((lhs - rhs).subs(R ** 2, k ** 2 + d ** 2 / 4))   # r^2 = k^2 + d^2/4
    out['A1_identity_4y2(rho2-r2)_minus_(|c-p+|2-r2)(|c-p-|2-r2)'] = str(E)
    # --- A2: algebraic equivalence of the two span forms ---
    D = sp.symbols('D', positive=True)
    E2 = sp.expand((4 * R * D - D ** 2 - d ** 2) - (4 * R ** 2 - d ** 2 - (D - 2 * R) ** 2))
    out['A2_(4rD-D2-d2)_minus_(4r2-d2-(D-2r)2)'] = str(E2)
    # monotonicity of f(D)=4rD-D^2 on [2r,oo): f(Dlo)-f(Dhi) = (Dhi-Dlo)(Dhi+Dlo-4r) >= 0
    Dlo, Dhi = sp.symbols('Dlo Dhi', positive=True)
    E3 = sp.expand(((4 * R * Dlo - Dlo ** 2) - (4 * R * Dhi - Dhi ** 2))
                   - (Dhi - Dlo) * (Dhi + Dlo - 4 * R))
    out['A3_monotonicity_identity'] = str(E3)

    # --- exact rational sampling on Pythagorean (r,d,k) ---
    def rho2_exact(hA, hB, c):
        """squared circumradius by side/area formula, all-Fraction."""
        ax, ay = hB[0] - hA[0], hB[1] - hA[1]
        bx, by = c[0] - hA[0], c[1] - hA[1]
        a2 = ax * ax + ay * ay
        b2 = bx * bx + by * by
        cx, cy = c[0] - hB[0], c[1] - hB[1]
        c2 = cx * cx + cy * cy
        ar2 = (ax * by - ay * bx) ** 2          # (2*area)^2
        if ar2 == 0:
            return None
        return a2 * b2 * c2 / (4 * ar2)

    triples = [(F(3, 5), F(4, 5), F(1)), (F(5, 13), F(12, 13), F(1)),
               (F(8, 17), F(15, 17), F(1)), (F(20, 29), F(21, 29), F(1))]
    stats = {'samples': 0, 'rho_le_r': 0, 'containment_violations': 0,
             'span_violations': 0, 'sampled_pairs': 0, 'branch_D_ge_2r': 0,
             'branch_violations': 0, 'ge4r_pairs': 0}
    rng = random.Random(20260925)
    for a, kk, r in triples:                    # d = 2a, k = sqrt(r^2-a^2)
        dd = 2 * a
        hA = (F(-a), F(0))
        hB = (F(a), F(0))
        pp = (F(0), kk)
        pm = (F(0), -kk)
        good = []
        for i in range(-24, 25):
            for j in range(-24, 25):
                c = (F(i, 5), F(j, 5))
                r2 = rho2_exact(hA, hB, c)
                if r2 is None:
                    continue
                stats['samples'] += 1
                if r2 <= r * r:                  # circumradius <= r
                    stats['rho_le_r'] += 1
                    insidep = (c[0] ** 2 + (c[1] - kk) ** 2) <= r * r
                    insidem = (c[0] ** 2 + (c[1] + kk) ** 2) <= r * r
                    if not (insidep or insidem):   # crescent containment
                        stats['containment_violations'] += 1
                    good.append(c)
        # span bound on pairs -- ALL comparisons exact rational (k is rational here)
        lim = 2 * r + 2 * kk
        for _ in range(400):
            c0 = rng.choice(good)
            c4 = rng.choice(good)
            D2 = (c0[0] - c4[0]) ** 2 + (c0[1] - c4[1]) ** 2
            stats['sampled_pairs'] += 1
            if D2 > lim * lim:                              # D <= 2r+2k
                stats['span_violations'] += 1
            if D2 >= 4 * r * r:                             # D >= 2r branch
                stats['branch_D_ge_2r'] += 1
                # d^2 <= 4rD-D^2  <==>  D <= 2r+2k   when D >= 2r (both sides >= 0)
                if D2 > lim * lim:
                    stats['branch_violations'] += 1
            if D2 > 16 * r * r:                             # D > 4r branch
                stats['ge4r_pairs'] += 1
    out['A4_exact_sampling'] = stats

    # --- A5: exact rational counterexample: D < 2r carries no span information ---
    # r=1, hubs (-3/5,0),(3/5,0)  => d=6/5, k=4/5 (Pythagorean), p_pm=(0,+-4/5)
    # c0=(1/2,1/10) above, c4=(1/2,-1/10) below (opposite sides, positive area)
    r1 = F(1)
    hA = (F(-3, 5), F(0))
    hB = (F(3, 5), F(0))
    c0 = (F(1, 2), F(1, 10))
    c4 = (F(1, 2), F(-1, 10))
    cv = {}
    cv['r'] = str(r1)
    cv['hA'] = [str(v) for v in hA]
    cv['hB'] = [str(v) for v in hB]
    cv['c0'] = [str(v) for v in c0]
    cv['c4'] = [str(v) for v in c4]
    cv['d'] = str(hB[0] - hA[0])
    cv['k'] = str(F(4, 5))
    cv['rho2_c0'] = str(rho2_exact(hA, hB, c0))
    cv['rho2_c4'] = str(rho2_exact(hA, hB, c4))
    cv['rho_le_r_both'] = bool(rho2_exact(hA, hB, c0) <= 1 and rho2_exact(hA, hB, c4) <= 1)
    cv['positive_area_both'] = True
    D2 = (c0[0] - c4[0]) ** 2 + (c0[1] - c4[1]) ** 2
    cv['D2'] = str(D2)
    cv['D_lt_2r'] = bool(D2 < 4)
    dd = F(6, 5)
    # violation of the unrestricted quarter-disk form: d^2 + (D-2r)^2 > 4r^2
    # (D irrational; compare via D^2:  (D-2)^2 = D^2 -4D +4  -> needs sqrt; instead exhibit
    #  the equivalent failed inequality d^2 <= 4rD - D^2 by the exact rational bound
    #  d^2 + 4 = 144/25+100/25 ; 4rD <= 2*sqrt(D2) < 1  since D^2=1/25 => D=1/5)
    cv['four_rD_minus_D2_upper'] = str(4 * r1 * F(1, 5) - D2)      # exact, D=1/5
    cv['d2'] = str(dd * dd)
    cv['unrestricted_form_fails'] = bool(dd * dd > 4 * r1 * F(1, 5) - D2)
    cv['note'] = ('D=1/5 < 2r=2, both circumradii <= r, positive area, opposite sides; '
                  'd^2=36/25 > 4rD-D^2=19/25, so the quarter-disk/4rD-D^2 form is FALSE on D<2r')
    out['A5_D_lt_2r_counterexample'] = cv
    return out


# --------------------------------------------------------------------------------------
# B. quadratic dual controls
# --------------------------------------------------------------------------------------
def lower(P, radii, alpha, Q, radii2, beta):
    """lead eq.(1), exact rational arithmetic.  P: list of 2-lists, radii/alpha same length."""
    A = sum(alpha)
    B = sum(beta)
    delta = A + B + A * B
    assert delta > 0, 'delta must be positive'
    Pv = [sum(w * a[t] for w, a in zip(alpha, P)) for t in range(2)]
    Qv = [sum(w * a[t] for w, a in zip(beta, Q)) for t in range(2)]
    T = sum(w * (a[0] ** 2 + a[1] ** 2 - v * v) for w, a, v in zip(alpha, P, radii))
    T += sum(w * (a[0] ** 2 + a[1] ** 2 - v * v) for w, a, v in zip(beta, Q, radii2))
    dP = Pv[0] ** 2 + Pv[1] ** 2
    dQ = Qv[0] ** 2 + Qv[1] ** 2
    PQ = Pv[0] * Qv[0] + Pv[1] * Qv[1]
    return T - ((1 + B) * dP + 2 * PQ + (1 + A) * dQ) / delta


def section_B():
    out = {}
    # --- B1/B2: lead's controls 1,2 ---
    b1 = lower([[0, 0]], [1], [1], [[3, 0]], [1], [1])
    b2 = lower([[0, 0]], [1], [1], [[0, 0]], [1], [1])
    out['B1_separated_unit_disks_L'] = str(b1)          # 1 = dist^2
    out['B2_coincident_disks_L'] = str(b2)              # -2 (legal but weak)
    # --- B3: two tangent disks singleton + disk; non-attainment ---
    b3 = {}
    vals = []
    for t in [F(1), F(2), F(10), F(100)]:
        z = lower([[-1, 0], [1, 0]], [1, 1], [t, t], [[0, 3]], [1], [2])
        vals.append([str(t), str(z), str(4 - 6 / (1 + 3 * t))])
    b3['L_of_t'] = vals
    b3['closed_form'] = 'L(t) = (12t-2)/(1+3t) = 4 - 6/(1+3t)'
    Lt = lambda t: (12 * t - 2) / (1 + 3 * t)
    b3['monotone_increment_L2_minus_L1'] = str(Lt(F(2)) - Lt(F(1)))
    b3['increment_formula'] = 'L(t+1)-L(t) = 18/((1+3t)(4+3t)) > 0'
    b3['sup'] = '4 = dist^2(K_A,K_B); finite multipliers never attain it'
    b3['K_A'] = 'B((-1,0),1) cap B((1,0),1) = {(0,0)}'
    b3['K_B'] = 'B((0,3),1)'
    b3['dist'] = '2'
    # cone data (exact integer vectors)
    b3['active_gradients_at_0'] = [[2, 0], [-2, 0]]
    b3['active_gradient_cone'] = 'x-axis (line)'
    b3['normal_cone_of_singleton'] = 'R^2 (tangent cone = {0})'
    b3['separating_direction_u'] = [0, -1]
    b3['u_in_active_cone'] = False
    b3['KKT_solvable'] = False
    out['B3_two_tangent_disks_singleton'] = b3
    # --- B4: crossing lens (Slater) with KKT multipliers attaining dist^2 exactly ---
    s3 = sp.sqrt(3)
    al = 2 / s3 - sp.Rational(1, 2)
    be = 2 - s3 / 2
    Lsym = lower([[0, 0], [1, 0]], [1, 1], [al, al], [[sp.Rational(1, 2), -3]], [1], [be])
    dist2 = (2 - s3 / 2) ** 2
    b4 = {'alpha_KKT': str(sp.nsimplify(al)), 'beta_KKT': str(sp.nsimplify(be)),
          'L_symbolic': str(sp.simplify(Lsym)),
          'dist_squared_symbolic': str(sp.simplify(dist2)),
          'exact_attainment': str(sp.simplify(sp.expand(Lsym - dist2)))}
    b4['K_A'] = 'B((0,0),1) cap B((1,0),1) (genuine lens, Slater holds)'
    b4['K_B'] = 'B((1/2,-3),1)'
    b4['primal_pair'] = 'a*=(1/2,-sqrt3/2) (lens corner), b*=(1/2,-2)'
    # verify stationarity of the dual minimiser at the primal pair (exact symbolic)
    A = 2 * al
    B = be
    Pa = al * sp.Matrix([0, 0]) + al * sp.Matrix([1, 0])
    Qb = be * sp.Matrix([sp.Rational(1, 2), -3])
    astar = sp.Matrix([sp.Rational(1, 2), -s3 / 2])
    bstar = sp.Matrix([sp.Rational(1, 2), -2])
    g_a = sp.simplify((1 + A) * astar - bstar - Pa)[:]
    g_b = sp.simplify((1 + B) * bstar - astar - Qb)[:]
    b4['stationarity_a'] = [str(v) for v in g_a]
    b4['stationarity_b'] = [str(v) for v in g_b]
    out['B4_crossing_lens_Slater_attainment'] = b4
    # --- B5: internal tangency / containment: cone == normal cone (ray) ---
    b5 = {'K_A': 'B((0,0),2) cap B((1,0),1) = B((1,0),1) (internal tangency at (2,0))',
          'active_gradients_at_(2,0)': [[4, 0], [2, 0]],
          'active_gradient_cone': 'positive x-axis (ray)',
          'normal_cone': 'positive x-axis (ray)',
          'equal': True}
    out['B5_internal_tangency'] = b5
    # --- B5b: strict containment: only the smaller disk is active ---
    b5b = {'K_A': 'B((0,0),3) cap B((1,0),1) = B((1,0),1) (strict containment)',
           'active_gradients_at_(2,0)': [[2, 0]],
           'active_gradient_cone': 'positive x-axis (ray)',
           'normal_cone': 'positive x-axis (ray)',
           'equal': True}
    out['B5b_containment'] = b5b
    # --- B6: 3-disk singleton with positively spanning normals ---
    e1 = sp.Matrix([1, 0]); e2 = sp.Matrix([sp.Rational(-1, 2), s3 / 2])
    e3 = sp.Matrix([sp.Rational(-1, 2), -s3 / 2])
    xs = sp.symbols('x0 x1', real=True)
    xv = sp.Matrix(xs)
    # sum of the three linearised constraints 2<x,e_i> >= |x|^2  (equality at 0)
    b6 = {'centers': [str(list(v)) for v in (e1, e2, e3)], 'radii': '1 each',
          'claim': 'intersection = {0} (all three circles pass through 0)',
          'sum_of_centers_zero': str(sp.simplify(e1 + e2 + e3)),
          'identity': 'sum_i [2<x,e_i>] = 2<x, sum e_i> = 0 >= 3|x|^2  on the intersection',
          'sum_identity_residual': str(sp.expand(3 * (xs[0] ** 2 + xs[1] ** 2)
                                                 - sum(xs[0] ** 2 + xs[1] ** 2
                                                       - 2 * (xs[0] * v[0] + xs[1] * v[1])
                                                       for v in (e1, e2, e3)))),
          'active_gradients': [str(list(-2 * v)) for v in (e1, e2, e3)],
          'zero_in_int_conv': str(sp.simplify(sp.Rational(1, 3) * (-2 * e1 - 2 * e2 - 2 * e3))),
          'active_gradient_cone': 'R^2 (0 in interior of convex hull of active gradients)',
          'normal_cone': 'R^2 (K is a singleton)',
          'equal': True}
    out['B6_three_disk_singleton_positively_spanning'] = b6
    # --- B7: statement table ---
    out['B7_scope'] = {
        'cone_active_gradients_subset_N': 'always (weak duality of the linearised cones)',
        'equality_if_int_K_nonempty': 'yes: Slater at a strictly feasible point gives '
                                      'T_K(x)=linearised cone for every x in K, hence '
                                      'N_K(x)=cone{grad g_i(x): i active}',
        'equality_at_singleton_K={x0}': 'N_K(x0)=R^2; equals cone{active gradients} iff '
                                        '0 in interior of their convex hull',
        'genuine_failure': 'two externally tangent disks (antipodal active gradients): '
                           'cone = line, N = R^2 (B3)',
    }
    return out


# --------------------------------------------------------------------------------------
# C. candidate calibration (numeric, saved rational rings)
# --------------------------------------------------------------------------------------
def section_C():
    out = {'label': 'NUMERIC calibration on the saved rational q0 rings; not a certificate'}
    try:
        os.chdir(BASE)
        qlead = BASE / 'research-2026/team-current/lead/q0_exact_closure_radius.py'
        src = qlead.read_text()
        ns = {'__file__': str(qlead)}
        exec(src.split('edges=sorted')[0], ns)
        import numpy as np
        c = ns['c']
    except Exception as exc:                                   # pragma: no cover
        out['status'] = 'skipped: ' + repr(exc)
        return out
    r = 0.3799838531198388
    out['r_saved_float'] = r
    norms = np.linalg.norm(c, axis=1)
    hubs = list(np.argsort(norms)[:2])
    hA, hB = c[hubs[0]], c[hubs[1]]
    d = float(np.linalg.norm(hA - hB))

    def circ(a, b, x):
        ax, bx = a - x, b - x
        cr = ax[0] * bx[1] - ax[1] * bx[0]
        if cr == 0:
            return float('inf')
        return float(np.linalg.norm(ax) * np.linalg.norm(bx) * np.linalg.norm(a - b) / (2 * abs(cr)))

    rho = [circ(hA, hB, c[i]) for i in range(9)]
    act = [i for i in range(9) if rho[i] <= r + 1e-12]
    out['hub_indices'] = hubs
    out['hub_points'] = [list(map(float, hA)), list(map(float, hB))]
    out['hub_distance_d'] = d
    out['ring_circumradii_minus_r'] = [round(rho[i] - r, 9) for i in range(9)]
    out['active_central_rings'] = act
    if len(act) != 2:
        out['status'] = 'unexpected number of active central rings; calibration aborted'
        return out
    c0, c4 = c[act[0]], c[act[1]]
    D2 = float((c0[0] - c4[0]) ** 2 + (c0[1] - c4[1]) ** 2)
    D = math.sqrt(D2)
    T = 4 * r * D - D * D
    out.update({'c0': list(map(float, c0)), 'c4': list(map(float, c4)),
                'D': D, '2r': 2 * r, '4r': 4 * r, 'D_ge_2r': bool(D >= 2 * r),
                'threshold_T_4rD_minus_D2': T, 'd_squared': d * d,
                'slack_T_minus_d2': T - d * d,
                'slack_quarter_disk_4r2_minus_d2_minus_(D-2r)2': 4 * r * r - d * d - (D - 2 * r) ** 2})
    # pins (inner radical-line roots), same convention as the lead's variance calibration
    pins = []
    for i in range(9):
        a_, b_ = c[i], c[(i + 1) % 9]
        m = (a_ + b_) / 2
        dd = float(np.linalg.norm(b_ - a_))
        n = np.array([-(b_ - a_)[1], (b_ - a_)[0]]) / dd
        kk = math.sqrt(r * r - dd * dd / 4)
        pins.append(min([m + kk * n, m - kk * n], key=np.linalg.norm))
    pins = np.array(pins)
    dist_hA = [float(np.linalg.norm(pins[i] - hA)) for i in range(9)]
    dist_hB = [float(np.linalg.norm(pins[i] - hB)) for i in range(9)]
    actA_t = [i for i in range(9) if abs(dist_hA[i] - r) <= 1e-9]     # tight (== r)
    actB_t = [i for i in range(9) if abs(dist_hB[i] - r) <= 1e-9]
    actA_l = [i for i in range(9) if dist_hA[i] <= r + 1e-9]          # loose (<= r)
    actB_l = [i for i in range(9) if dist_hB[i] <= r + 1e-9]
    out['tight_pins_hubA'] = actA_t
    out['tight_pins_hubB'] = actB_t
    out['loose_pins_hubA'] = actA_l
    out['loose_pins_hubB'] = actB_l

    def lower_np(P, radii, alpha, Q, radii2, beta):
        A = sum(alpha); B = sum(beta); delta = A + B + A * B
        Pv = sum(w * p for w, p in zip(alpha, P))
        Qv = sum(w * q for w, q in zip(beta, Q))
        T_ = sum(w * (p @ p - v * v) for w, p, v in zip(alpha, P, radii))
        T_ += sum(w * (q @ q - v * v) for w, q, v in zip(beta, Q, radii2))
        return float(T_ - ((1 + B) * (Pv @ Pv) + 2 * (Pv @ Qv) + (1 + A) * (Qv @ Qv)) / delta)

    def var_bound(idx, w):
        p = pins[idx]; w = np.array(w, dtype=float); w = w / w.sum()
        b = w @ p
        V = sum(w[i] * w[j] * float(np.sum((p[i] - p[j]) ** 2))
                for i in range(len(idx)) for j in range(i))
        return b, V, math.sqrt(max(0.0, r * r - V))

    if not actA_t or not actB_t:
        out['dual_note'] = 'no tight pin set; quadratic-dual calibration skipped'
        return out
    wA = [459977731 / 1e9, 80044539 / 1e9, 459977730 / 1e9]      # lead's rational weights
    if len(actA_t) == 3:
        Lquad = lower_np(pins[actA_t], [r] * 3, wA, pins[actB_t], [r] * len(actB_t),
                         [1 / len(actB_t)] * len(actB_t))
        bA, VA, eA = var_bound(actA_t, wA)
        out['L_quadratic_dual'] = Lquad
    else:
        out['dual_note'] = f'tight pin count hubA={len(actA_t)}; weights not transferred'
    bB, VB, eB = var_bound(actB_t, [1] * len(actB_t))
    out['variance_eps'] = [eA if 'eA' in dir() else None, eB]
    if 'L_quadratic_dual' in out:
        Lvar = max(0.0, float(np.linalg.norm(bA - bB)) - eA - eB)
        out['L_variance_localization'] = Lvar
        out['filter_excludes_candidate_quad'] = bool(out['L_quadratic_dual'] > T)
        out['filter_excludes_candidate_var'] = bool(Lvar * Lvar > T)
        out['consistency'] = 'no exclusion expected: the saved candidate is a valid cover'
        # validity calibration of both lower bounds against the known answer d
        out['L_quadratic_dual_le_d2'] = bool(out['L_quadratic_dual'] <= d * d)
        out['L_variance_localization_le_d'] = bool(Lvar <= d)
    # rigorous enclosure of D from the exact rational ring coordinates
    try:
        raw = json.loads((BASE / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
        C0 = [[F(int(v), 10 ** 17) for v in a] for a in raw['centers_scaled_1e17']]
        rings = sorted([i for i in range(11) if i not in [0, 2]],
                       key=lambda i: math.atan2(float(C0[i][1]), float(C0[i][0])))
        Cex0 = [C0[i] for i in rings] + [C0[0], C0[2]]
        sh, sw = int(ns['shift']), int(ns['swap'])       # mapping used by the lead's prefix
        order = [(i + sh) % 9 for i in range(9)] + ([10, 9] if sw else [9, 10])
        cex = [Cex0[i] for i in order]
        out['exact_mapping_shift_swap'] = [sh, sw]
        i0, i4 = act[0], act[1]
        Dex2 = (cex[i0][0] - cex[i4][0]) ** 2 + (cex[i0][1] - cex[i4][1]) ** 2
        den = Dex2.denominator
        s = math.isqrt(Dex2.numerator * den)      # floor(den*sqrt(Dex2))
        Dlo = F(s, den)
        Dhi = F(s + 1, den)
        rF = F(r)          # saved float radius as an exact rational
        out['D_exact_square'] = str(Dex2)
        out['D_enclosure'] = [float(Dlo), float(Dhi)]
        out['D_exact_center_float'] = math.sqrt(float(Dex2))
        if Dlo >= 2 * rF:
            out['T_upper_from_Dlo'] = float(4 * rF * Dlo - Dlo * Dlo)
        out['D_enclosure_check_ge_2r'] = bool(Dlo >= 2 * rF)
    except Exception as exc:                                   # pragma: no cover
        out['D_enclosure_error'] = repr(exc)
    return out


def main():
    RES['A_span'] = section_A()
    RES['B_dual'] = section_B()
    RES['C_candidate'] = section_C()
    OUT.write_text(json.dumps(RES, indent=2, default=str))
    print(json.dumps(RES, indent=2, default=str))


if __name__ == '__main__':
    main()
