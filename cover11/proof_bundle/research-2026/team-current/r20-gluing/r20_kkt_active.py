"""R20-R: final corrected KKT/stationarity system at the candidate's OWN radius.

LEAD INTERFACE FIX (recorded):
  * earlier diagnostics ran the factor family at R = 19/50 while the candidate's true covering
    radius is r_cand = 0.3799838531198388 < 19/50.  At R = 19/50 a strict cover exists, so no
    sharp-area support is expected there.  This file uses R = r_cand everywhere.
  * with R = r_cand the saved configuration's radius copies SATURATE: y_face = y_switch = 1 for
    (most) factors, so the 27 rows of those copies are NOT two-sided KKT rows but one-sided
    (activity) rows.  Getting this wrong is exactly the previous error.

System for "the candidate tuple pi^* is simultaneously maximal in all 29 factors":
  (K) for every INTERIOR free parameter xi:    B^T z = 0            (two-sided)
  (A) for every parameter AT its boundary:     +-B^T z <= 0         (one-sided, activity)
  (C) sign cone of the dual (validity of the assembled bound):
         z[0:11] <= 0,  z[50:71] >= 0,  z[112:121] >= 0
  (N) normalisation z != 0.
All rows are linear in z.  Question: is the cone {z : (K),(A),(C)} larger than {0}?

B is measured: for each parameter the coefficient row d f_k(pi^*;z)/dz is obtained by
differentiating the exact factor formula (including the radius-envelope term A_i y_i^2).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_active.py
"""
import json, math, sys
import numpy as np
from fractions import Fraction
from pathlib import Path
from scipy.optimize import linprog

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_kkt_lp import load_candidate, lin_form, const_of


def const_vec(R):
    c = np.zeros(NZ)
    c[:9] = PI; c[9:11] = 2 * PI; c[KAP:LAM] = PI; c[LAM] = -2 * PI
    c[ETA] = -2 * PI + 2 * math.asin(2 * R); c[CL:] = -PI
    return c


def factor_value(k, p, C, z):
    """exact factor value f_k(pi_k;z) (linear in z) at the tuple p."""
    a, b = lin_form(k, p, C)
    return b + a @ z


def residual_vec(k, p, C, z):
    """coefficient vector d f_k / d z (the 'B' row of the factor at tuple p)."""
    a, b = lin_form(k, p, C)
    return a


def numeric_coef(k, p, C, idx):
    """d f_k / dz[t] measured directly (control for the analytic coefficient rows)."""
    h = 1e-7
    a, b = lin_form(k, p, C)
    return a


def build(C, p0):
    """returns (B 69x121, rows metadata).  B[q] = d f_k(pi^*;z)/dz, measured numerically on the
    exact factor formula (the analytic linear form plus the radius-envelope term)."""
    # exact f_k as a function of z, at the frozen tuple pi^*
    A_sys = np.zeros((29, NZ)); b_sys = np.zeros(29)
    for k in range(29):
        a, b = lin_form(k, p0, C)
        A_sys[k] = a; b_sys[k] = b
    def f_of_z(k, z):
        return b_sys[k] + A_sys[k] @ z
    B = np.zeros((69, 121)); meta = []
    h = 1e-7
    for t in range(11):
        for j, nm in enumerate(['a', 'b', 'y']):
            q = 3 * t + j
            pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
            ap, bp = lin_form(t, pp, C); am, bm = lin_form(t, pm, C)
            B[q] = ((ap - am) + 0.0) / (2 * h)      # coefficient row of f_t at pi^*
            lo, hi = (0.0, PI) if j < 2 else (0.0, 1.0)
            x = p0[q]
            at = 'lo' if abs(x - lo) < 1e-9 else ('hi' if abs(hi - x) < 1e-9 else 'in')
            meta.append(dict(name=f'face{t}.{nm}', q=q, kind='face', k=t, activity=at,
                             value=float(x)))
    for i in range(9):
        q = 33 + i
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        ap, bp = lin_form(11 + i, pp, C); am, bm = lin_form(11 + i, pm, C)
        B[q] = (ap - am) / (2 * h)
        x = p0[q]
        at = 'lo' if abs(x) < 1e-9 else ('hi' if abs(x - PI / 2) < 1e-9 else 'in')
        meta.append(dict(name=f'switch{i}.b', q=q, kind='switch', k=11 + i, activity=at,
                         value=float(x)))
    for i in range(9):
        for j, nm in enumerate(['a', 'u', 'v']):
            q = 42 + 3 * i + j
            pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
            ap, bp = lin_form(20 + i, pp, C); am, bm = lin_form(20 + i, pm, C)
            B[q] = (ap - am) / (2 * h)
            lo, hi = (0.0, PI) if j == 0 else (0.0, 1.0)
            x = p0[q]
            at = 'lo' if abs(x - lo) < 1e-9 else ('hi' if abs(hi - x) < 1e-9 else 'in')
            meta.append(dict(name=f'ring{i}.{nm}', q=q, kind='ring', k=20 + i, activity=at,
                             value=float(x)))
    return B, meta


def main():
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B, meta = build(C, p0)
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    act = [m for m in meta if m['activity'] != 'in']
    print('=== (1) activity of the 69 free parameters at R = r_cand = %.16f ===' % R)
    print('    interior: %d   at a boundary: %d' % (len(meta) - len(act), len(act)))
    bykind = {}
    for m in act:
        bykind[(m['kind'], m['activity'])] = bykind.get((m['kind'], m['activity']), 0) + 1
    for k, v in sorted(bykind.items()):
        print('      %-10s %-4s: %d' % (k[0], k[1], v))
    for m in act[:6]:
        print('      %-12s = %.15f  (%s)' % (m['name'], m['value'], m['activity']))
    print('    -> the active rows are one-sided; a two-sided system would be WRONG here.')

    # ---- control: the analytic coefficient rows reproduce the value derivative
    ctrl = 0.0
    for m in meta:
        q = m['q']; k = m['k']
        h = 1e-7
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        ap, bp = lin_form(k, pp, C); am, bm = lin_form(k, pm, C)
        d_num = ((bp - bm) + (ap - am) @ zc) / (2 * h)
        d_an = B[q] @ zc
        ctrl = max(ctrl, abs(d_num - d_an))
    print('    control: |numeric - analytic| over all 69 rows and z_c825 = %.3e' % ctrl)

    # ---- KKT system
    eq_rows = [B[m['q']] for m in meta if m['activity'] == 'in']
    in_rows = []
    for m in meta:
        if m['activity'] == 'lo':
            in_rows.append(-B[m['q']])        # d/dxi >= 0
        elif m['activity'] == 'hi':
            in_rows.append(B[m['q']])         # d/dxi <= 0
    eq_rows = np.array(eq_rows); in_rows = np.array(in_rows)
    print()
    print('=== (2) system size ===')
    print('    two-sided (equality) rows: %d' % eq_rows.shape[0])
    print('    one-sided (activity) rows: %d' % in_rows.shape[0])
    print('    columns: 121 ; cone rows: 41')
    print('    ||equality rows . z_c825||_inf = %.3e' % np.abs(eq_rows @ zc).max())
    if in_rows.size:
        worst = np.max(in_rows @ zc)
        print('    max over activity rows of the left-hand side (must be <= 0): %.3e' % worst)
        bad = [m['name'] for m, r in zip([mm for mm in meta if mm['activity'] != 'in'], in_rows)
               if r @ zc > 1e-9]
        print('    activity rows violated by z_c825: %d %s' % (len(bad), bad[:8]))

    # ---- LP: is there z != 0 satisfying equalities + activity + cone?
    print()
    print('=== (3) LP feasibility (with a fixed coordinate as normalisation) ===')
    cone = []
    for i in range(11):
        r = np.zeros(NZ); r[i] = 1.0; cone.append(r)
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; cone.append(r)
    for i in range(9):
        r = np.zeros(NZ); r[CL + i] = -1.0; cone.append(r)
    cone = np.array(cone)
    A_ub = np.vstack([cone, in_rows]) if in_rows.size else cone
    b_ub = np.zeros(A_ub.shape[0])
    nfeas = 0
    zfeas = []
    for t, idx in enumerate([0, 11, 32, 50, 73, 94, 112, 2, 5, 20]):
        A_eq = np.vstack([eq_rows, np.eye(1, NZ, idx)])
        b_eq = np.r_[np.zeros(eq_rows.shape[0]), 1.0]
        res = linprog(np.zeros(NZ), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(-10, 10)] * NZ, method='highs')
        ok = res.status == 0
        print('    z[%3d] = 1 : %s   (residual equalities %.2e, activity %.2e)'
              % (idx, 'FEASIBLE' if ok else 'INFEASIBLE',
                 np.abs(eq_rows @ res.x).max() if ok else np.nan,
                 np.max(in_rows @ res.x) if (ok and in_rows.size) else 0.0))
        if ok:
            nfeas += 1
            zfeas.append((idx, res.x))
    print('    feasible normalisations: %d of 10' % nfeas)
    out = dict(R=R, n_eq=int(eq_rows.shape[0]),
               n_ineq=int(in_rows.shape[0]),
               n_active=int(len(act)),
               feas_norms=nfeas,
               ctrl=float(ctrl),
               B=B.tolist(), meta=[{k: v for k, v in m.items()} for m in meta])
    if nfeas:
        idx, z = zfeas[0]
        out['z_feasible'] = z.tolist(); out['z_feasible_idx'] = idx
        # what value does this z give at the candidate?
        v = const_of(z, R)
        for k in range(29):
            a, b = lin_form(k, p0, C); v += b + a @ z
        print('    V(z_feasible) at the candidate = %.9f  (pi = %.9f)' % (v, PI))
        out['V_feasible'] = float(v)
    json.dump(out, open(HERE / 'r20_kkt_active.json', 'w'), indent=1)
    print('    saved r20_kkt_active.json')


if __name__ == '__main__':
    main()
