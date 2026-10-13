"""R20-WIT: extract and TEST the witness z (is it a genuine upper-bound certificate?).

The combined system (46 rational competitors + candidate affine KKT + producer cone + tightness)
is FEASIBLE, giving z with f_k(pi*;z) >= f_k(X;z) on the sampled competitors and V(z;pi*) = pi.

That is only a SAMPLED statement.  A genuine sharp witness needs
        V(z; X) <= pi        for EVERY tuple X of every factor (continuum),
equivalently  z_c g_c >= 0 on the class.  This script attacks the witness directly:

  T1  reproduce the constraints at the witness (competitors, KKT rows, cone, tightness);
  T2  direct search for a violating tuple: minimise V(z;X) over the 78-parameter domain with
      multi-start local optimisation; any X with V(z;X) > pi refutes the witness;
  T3  if no violation is found, report the search scope honestly (sampling is necessary-only).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_witness_test.py
"""
import json, math, sys
import numpy as np
from pathlib import Path
from scipy.optimize import linprog, minimize

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
KAP, ETA, LAM = 50, 72, 71
R_CAND = 0.3799838531198388
IF, IB, IR = 0, 33, 51
sys.path.insert(0, str(HERE))
from r20_decisive import build, cone
from r20_producer_family import value_and_row, param_table


def get_witness(ZMAX=100.0):
    d = build()
    Vc = np.zeros(NZ)
    for k in range(29):
        Vc += d['M0'][k]
    Vconst = float(d['v0'].sum())
    cA, cb = cone()
    AU = np.vstack([-d['G'], d['Aup'], cA, Vc[None, :], -Vc[None, :]])
    bU = np.concatenate([-d['h'], d['bup'], cb, [PI - Vconst], [-1e-12]])
    res = linprog(np.zeros(NZ), A_ub=AU, b_ub=bU, A_eq=d['Aeq'], b_eq=d['beq'],
                  bounds=[(-ZMAX, ZMAX)] * NZ, method='highs')
    assert res.status == 0
    return d, res.x, Vconst, Vc


def main():
    d, z, Vconst, Vc = get_witness()
    C = d['C']; p0 = d['p0']
    print('=== R20-WIT: witness test ===')
    print('   |z|inf = %.6g   V(z;pi*) = %.12f  (pi = %.12f)'
          % (np.abs(z).max(), Vconst + Vc @ z, PI))
    print('   T1 competitor slack min = %+.3e (over %d rows)' % (float(np.min(d['G'] @ z - d['h'])),
                                                                  len(d['h'])))
    print('   T1 KKT equality residual = %.3e ; one-sided max = %+.3e ; cone min = %+.3e'
          % (float(np.abs(d['Aeq'] @ z - d['beq']).max()),
             float(np.max(d['Aup'] @ z - d['bup'])),
             float(np.min(z[KAP:KAP + 21]))))
    # T2: direct search for a violating tuple
    rng = np.random.default_rng(9)
    R = C['R']
    def Vof(X):
        s = 0.0
        for k in range(29):
            v, M = value_and_row(k, X, C)
            s += v + M @ z
        return s
    def project(X):
        X = X.copy()
        for t in range(11):
            a = min(max(X[3 * t], 1e-9), PI - 1e-9); b = min(max(X[3 * t + 1], 1e-9), PI - 1e-9)
            if a + b > PI - 1e-9:
                b = PI - 1e-9 - a
            X[3 * t] = a; X[3 * t + 1] = b; X[3 * t + 2] = min(max(X[3 * t + 2], 0.0), 1.0)
        for i in range(9):
            X[IB + i] = min(max(X[IB + i], 1e-9), PI / 2 - 1e-9)
            X[IB + 9 + i] = min(max(X[IB + 9 + i], 0.0), 1.0)
        for i in range(9):
            X[IR + 3 * i] = min(max(X[IR + 3 * i], 1e-9), PI - 1e-9)
            X[IR + 3 * i + 1] = min(max(X[IR + 3 * i + 1], 0.0), 1.0)
            X[IR + 3 * i + 2] = min(max(X[IR + 3 * i + 2], 0.0), 1.0)
        return X
    best = Vof(p0); bestX = p0.copy()
    starts = [p0.copy()] + [project(p0 + rng.normal(0, 0.5, 78)) for _ in range(40)]
    for X0 in starts:
        out = minimize(lambda X: -Vof(project(X)), X0, method='Nelder-Mead',
                       options=dict(maxiter=3000, xatol=1e-10, fatol=1e-12))
        v = Vof(project(out.x))
        if v > best:
            best = v; bestX = project(out.x)
    print('   T2 best (largest) V(z;X) found = %.12f   excess over pi = %+.3e'
          % (best, best - PI))
    if best > PI + 1e-9:
        print('      => VIOLATION: the witness is NOT a valid upper bound.')
        print('      worst tuple (first 12 params): %s' % np.round(bestX[:12], 6))
    else:
        print('      => no violation found in %d starts (necessary-only evidence).' % len(starts))
    json.dump(dict(z=z.tolist(), V_cand=float(Vconst + Vc @ z), max_found=float(best),
                   excess=float(best - PI), worst=list(map(float, bestX))),
              open(HERE / 'r20_witness_test.json', 'w'), indent=1)
    print('   saved r20_witness_test.json')


if __name__ == '__main__':
    main()
