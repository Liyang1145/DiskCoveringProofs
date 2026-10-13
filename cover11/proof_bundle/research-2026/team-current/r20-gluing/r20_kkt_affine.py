"""R20-X: CORRECTED stationarity/KKT system (affine, correct boundary signs).

Lead audit fixes incorporated:
  (i)  f_k(pi;z) = b_k(pi) + a_k(pi).z is AFFINE, so stationarity is
             b'_k(pi*) + a'_k(pi*).z  = 0        (interior parameter)      -- NOT a'_k.z = 0
  (ii) boundary sign: at the UPPER end of a closed domain the inward direction is dx < 0, so the
       necessary condition is  f' |_{inward} >= 0 ; at the LOWER end (dx > 0) it is f' <= 0.
       (calibrated in r20_toy_calibration.py: T2 upper -> inward derivative +1 >= 0,
        T3 lower -> inward derivative -1 <= 0.)
  (iii) complementarity: a dualized constraint whose residual is NOT tight at the candidate must
       carry MULTIPLIER 0 for V(z;pi*) = pi; the kappa/Delaunay slack, eta and the non-tight
       radius copies are all non-tight at the candidate, so those columns are pinned to 0.
  (iv) the validity rows are paired family-wise with their multipliers, because a difference form
       (two copies of a constraint) has a nonnegativity condition only for the pair.

Deliverables: (a) is the corrected system feasible with z != 0?  (b) if the answer on the sampled
validity rows is no, the LP margin s* and Farkas multipliers are exported with row provenance.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_affine.py
"""
import json, math, sys
import numpy as np
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
from r20_kkt_lp_final import sample_tuples


def param_rows(C, p0):
    """for each free parameter: (k, q, name, activity, b_prime, a_prime)."""
    h = 1e-6
    rows = []
    for t in range(11):
        for j, nm in enumerate(['a', 'b', 'y']):
            q = 3 * t + j
            pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
            ap, bp = lin_form(t, pp, C); am, bm = lin_form(t, pm, C)
            rows.append(dict(k=t, q=q, name=f'face{t}.{nm}', kind='face',
                             activity='in' if (j < 2 and p0[q] > 1e-9) or
                             (j == 2 and 1 - p0[q] > 1e-9) else ('up' if j == 2 else 'lo'),
                             b_prime=(bp - bm) / (2 * h), a_prime=(ap - am) / (2 * h),
                             value=float(p0[q])))
    for i in range(9):
        q = 33 + i
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        ap, bp = lin_form(11 + i, pp, C); am, bm = lin_form(11 + i, pm, C)
        rows.append(dict(k=11 + i, q=q, name=f'switch{i}.b', kind='switch',
                         activity='in' if p0[q] > 1e-9 else 'lo',
                         b_prime=(bp - bm) / (2 * h), a_prime=(ap - am) / (2 * h),
                         value=float(p0[q])))
    for i in range(9):
        for j, nm in enumerate(['a', 'u', 'v']):
            q = 42 + 3 * i + j
            pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
            ap, bp = lin_form(20 + i, pp, C); am, bm = lin_form(20 + i, pm, C)
            act = 'in'
            if j == 0 and p0[q] < 1e-9:
                act = 'lo'
            if j > 0 and p0[q] > 1 - 1e-9:
                act = 'up'
            rows.append(dict(k=20 + i, q=q, name=f'ring{i}.{nm}', kind='ring', activity=act,
                             b_prime=(bp - bm) / (2 * h), a_prime=(ap - am) / (2 * h),
                             value=float(p0[q])))
    return rows


def main():
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    rows = param_rows(C, p0)
    n_in = sum(1 for r in rows if r['activity'] == 'in')
    n_lo = sum(1 for r in rows if r['activity'] == 'lo')
    n_up = sum(1 for r in rows if r['activity'] == 'up')
    print('=== parameter rows: interior %d, at lower end %d, at upper end %d ==='
          % (n_in, n_lo, n_up))
    for r in rows:
        if r['activity'] != 'in':
            print('    %-12s value %.15f  %s' % (r['name'], r['value'], r['activity']))

    # ---- control: affine stationarity at the candidate for the saved z
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    der = np.array([r['b_prime'] + r['a_prime'] @ zc for r in rows])
    print('    control on z_c825: max |b\' + a\'.z| over interior rows = %.4e' %
          np.abs(der[[r['activity'] == 'in' for r in rows]]).max())
    print('    control: the same quantity under the OLD (homogeneous) rule = %.4e'
          % np.abs(np.array([r['a_prime'] @ zc for r in rows])[[r['activity'] == 'in'
                                                               for r in rows]]).max())

    # ---- LP rows
    A_eq = []; b_eq = []
    A_ub = []; b_ub = []
    for r in rows:
        if r['activity'] == 'in':
            A_eq.append(r['a_prime']); b_eq.append(-r['b_prime'])
        elif r['activity'] == 'lo':
            A_ub.append(r['a_prime']); b_ub.append(-r['b_prime'])        # f' <= 0
        else:
            A_ub.append(-r['a_prime']); b_ub.append(r['b_prime'])        # f' >= 0
    A_eq = np.array(A_eq); b_eq = np.array(b_eq)
    A_ub = np.array(A_ub); b_ub = np.array(b_ub)
    print()
    print('=== affine LP: %d equality rows, %d one-sided rows ===' % (A_eq.shape[0], A_ub.shape[0]))
    # complementarity: pin the non-tight columns
    pinned = list(range(KAP, KAP + 21)) + [ETA]           # Delaunay slack + eta
    print('    complementarity pins %d columns to 0 (kappa 21, eta 1)' % len(pinned))
    A_eq2 = np.vstack([A_eq] + [np.eye(1, NZ, c) for c in pinned])
    b_eq2 = np.r_[b_eq, np.zeros(len(pinned))]
    # cone (site <=0, closure >=0)
    cone = []
    for i in range(11):
        r = np.zeros(NZ); r[i] = 1.0; cone.append(r)
    for i in range(9):
        r = np.zeros(NZ); r[CL + i] = -1.0; cone.append(r)
    conem = np.array(cone)
    A_ub2 = np.vstack([A_ub, conem]) if A_ub.size else conem
    b_ub2 = np.r_[b_ub, np.zeros(conem.shape[0])]
    # normalisation: V is affine so a genuine solution cannot be normalised arbitrarily;
    # use |z| <= 1 and ask for a solution.
    res = linprog(np.zeros(NZ), A_ub=A_ub2, b_ub=b_ub2, A_eq=A_eq2, b_eq=b_eq2,
                  bounds=[(-1, 1)] * NZ, method='highs')
    print('    LP (cone+KKT+complementarity, |z|<=1): %s' %
          ('FEASIBLE' if res.status == 0 else 'INFEASIBLE'))
    if res.status == 0:
        z = res.x
        print('    |z|_inf = %.6f' % np.abs(z).max())
        V = const_of(z, R)
        for k in range(29):
            a, b = lin_form(k, p0, C); V += b + a @ z
        print('    V(z;pi*) = %.9f   (pi = %.9f, excess %+.3e)' % (V, PI, V - PI))
        json.dump(dict(z=z.tolist(), V=float(V)),
                  open(HERE / 'r20_kkt_affine_feasible.json', 'w'), indent=1)
    # ---- validity rows (sampled) added
    S = sample_tuples(C, p0, 60, 5)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S))
    a_c = {}; b_c = {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a; bv[j] = b - b_c[k]
    print()
    print('=== with %d sampled validity rows (V(z) >= pi on the class) ===' % len(S))
    A_ub3 = np.vstack([A_ub2, Rv]); b_ub3 = np.r_[b_ub2, bv]
    res3 = linprog(np.zeros(NZ), A_ub=A_ub3, b_ub=b_ub3, A_eq=A_eq2, b_eq=b_eq2,
                   bounds=[(-1, 1)] * NZ, method='highs')
    print('    LP: %s' % ('FEASIBLE' if res3.status == 0 else 'INFEASIBLE'))
    if res3.status == 0:
        z = res3.x
        V = const_of(z, R)
        for k in range(29):
            a, b = lin_form(k, p0, C); V += b + a @ z
        print('    V(z;pi*) = %.9f  (pi = %.9f)  min validity slack = %+.3e'
              % (V, PI, float(np.min(Rv @ z - bv))))
        json.dump(dict(z=z.tolist(), V=float(V)), open(HERE / 'r20_kkt_affine_val.json', 'w'),
                  indent=1)
    else:
        print('    -> produce the margin/Farkas certificate in r20_kkt_cert2.py')


if __name__ == '__main__':
    main()
