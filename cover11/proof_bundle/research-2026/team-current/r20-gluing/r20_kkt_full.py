"""R20-J: the full necessary LP — simultaneous maximality of the saved candidate in all 29 factors.

Obligation (exact form; diagnostic, no claim registered):
    exists z (121 columns) with
      (i)   stationarity/KKT rows      B^T z = 0            (69 rows)
      (ii)  global maximality          f_k(pi^*;z) >= f_k(x;z)  for all x in factor k's domain
      (iii) sign cone making the assembled bound a valid upper bound
      (iv)  z != 0
All rows are LINEAR in z, so the system is a small LP.

Q1 (feasibility):   is there z != 0 satisfying (i)+(ii)+(iii)?
Q2 (margin):        maximise  s  s.t.  f_k(pi^*;z) - f_k(x;z) >= s  for every sampled x,
                    which measures how far the candidate is from being a simultaneous maximum.
Q3 (Farkas):        if Q1 is infeasible, the LP dual gives an explicit infeasibility witness.

Caliber:  R = r_cand = 0.3799838531198388 (lead interface fix); at R = 19/50 a strict cover
exists so no sharp-area support is expected there.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_full.py
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
OFF_FACE, OFF_BSW, OFF_RNG = 0, 33, 42
NP = 69
sys.path.insert(0, str(HERE))
from r20_kkt_lp import load_candidate, lin_form, const_of, kkt_B


def full_with(X, k, sub):
    Y = X.copy()
    if k < 11:
        Y[OFF_FACE + 3 * k:OFF_FACE + 3 * k + 3] = sub
    elif k < 20:
        Y[OFF_BSW + k - 11] = sub[0]
    else:
        i = k - 20
        Y[OFF_RNG + 3 * i:OFF_RNG + 3 * i + 3] = sub
    return Y


def build_rows(C, p0, npts=160, seed=7):
    R = C['R']; rng = np.random.default_rng(seed)
    a_cand = []; b_cand = []
    for k in range(29):
        a, b = lin_form(k, p0, C)
        a_cand.append(a); b_cand.append(b)
    grids = {}
    for k in range(11):
        a = rng.uniform(0, PI, 4 * npts); b = rng.uniform(0, PI, 4 * npts)
        ok = a + b <= PI
        a = a[ok][:npts]; b = b[ok][:npts]
        y = rng.uniform(0, 1, len(a))
        grids[k] = np.c_[a, b, y]
    for k in range(11, 20):
        grids[k] = np.c_[rng.uniform(1e-9, PI / 2, npts), rng.uniform(0, 1, npts)]
    for k in range(20, 29):
        a = rng.uniform(1e-6, PI - 1e-6, 2 * npts); u = rng.uniform(0, 1, 2 * npts)
        v = rng.uniform(0, 1, 2 * npts)
        q = (u - v) ** 2 + 4 * u * v * np.sin(a / 2) ** 2
        qmin = 4 * math.sin(PI - 8 * math.asin(R)) ** 2 / R ** 2
        ok = q >= qmin
        grids[k] = np.c_[a[ok], u[ok], v[ok]][:npts]
    rows = []; rhs = []; meta = []
    for k in range(29):
        for sub in grids[k]:
            X = full_with(p0, k, sub)
            a, b = lin_form(k, X, C)
            # f_k(pi*) - f_k(x) = (b_cand + a_cand.z) - (b + a.z) >= s
            rows.append(a_cand[k] - a); rhs.append(b - b_cand[k]); meta.append(k)
    return np.array(rows), np.array(rhs), np.array(meta)


def cone_rows():
    A = []; b = []
    for i in range(11):                     # site/hub: z <= 0
        r = np.zeros(NZ); r[i] = 1.0; A.append(r); b.append(0.0)
    for i in range(21):                     # kappa (Delaunay slack): z >= 0
        r = np.zeros(NZ); r[KAP + i] = -1.0; A.append(r); b.append(0.0)
    for i in range(9):                      # closure: z >= 0
        r = np.zeros(NZ); r[CL + i] = -1.0; A.append(r); b.append(0.0)
    return np.array(A), np.array(b)


def main():
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B = kkt_B(C, p0)
    print('[A] B: %s rank %d' % (B.shape, np.linalg.matrix_rank(B, tol=1e-9)))
    rows, rhs, meta = build_rows(C, p0)
    print('[B] global-maximality rows: %d (grid sample)' % len(rows))
    coneA, coneb = cone_rows()

    # ---- Q2: maximise margin s over the cone, with the KKT rows as equalities
    print('[C] LP: maximise s subject to KKT rows B^T z = 0, cone, f_k(pi*)-f_k(x) >= s')
    nv = NZ + 1
    Aub = []; bub = []
    pad = np.zeros((len(coneA), 1))
    Aub += list(np.hstack([coneA, pad])); bub += list(coneb)
    Aub += list(np.hstack([rows, np.zeros((len(rows), 1))])); bub += list(rhs)
    Aub = np.array(Aub); bub = np.array(bub)
    Aeq = np.hstack([B, np.zeros((NP, 1))])
    beq = np.zeros(NP)
    c = np.zeros(nv); c[NZ] = -1.0
    bounds = [(-5, 5)] * NZ + [(None, None)]
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
    print('    status', res.status, res.message)
    if res.status == 0:
        z = res.x[:NZ]; s = res.x[NZ]
        print('    optimal margin s* = %+.6e   ||z||_inf = %.6f' % (s, np.abs(z).max()))
        viol = np.min(rows @ z + rhs)
        print('    worst sampled global-max row = %+.6e' % viol)
        # verify the KKT rows really hold
        print('    ||B^T z||_inf = %.3e' % np.abs(B @ z).max())
        # check V(z) at the candidate
        btot = const_of(z, R); 
        for k in range(29):
            a, b = lin_form(k, p0, C); btot += b + a @ z
        print('    V(z) at candidate = %.9f  (pi = %.9f)' % (btot, PI))
        json.dump(dict(z=z.tolist(), s=float(s), worst=float(viol), n_rows=int(len(rows)),
                       R=R_CAND, V_cand=float(btot), z_c825=None),
                  open(HERE / 'r20_kkt_full.json', 'w'), indent=1)
        print('    saved r20_kkt_full.json')

    # ---- Q1 variant: no margin variable, pure feasibility with a normalisation
    print('[D] pure feasibility: z in cone, KKT rows, f_k(pi*) >= f_k(x), and a fixed coordinate')
    j0 = int(np.argmax(np.abs(B @ np.ones(NZ))))
    for norm in range(NZ):
        pass
    # simplest normalisation: z_c >= 1 for one column that is free in the cone
    best = None
    for t in (11, 32, 73, 94, 112):
        Aeq2 = np.vstack([B, np.eye(1, NZ, t)])
        beq2 = np.r_[np.zeros(NP), 1.0]
        res2 = linprog(np.zeros(NZ), A_ub=np.vstack([coneA, rows]), b_ub=np.r_[coneb, rhs],
                       A_eq=Aeq2, b_eq=beq2, bounds=[(-5, 5)] * NZ, method='highs')
        if res2.status == 0:
            z2 = res2.x
            print('    z[%d]=1 feasible: ||B^T z||_inf=%.2e  worst row %+.2e'
                  % (t, np.abs(B @ z2).max(), np.min(rows @ z2 + rhs)))
            best = (t, z2)
            break
        else:
            print('    z[%d]=1 infeasible (%s)' % (t, res2.message))
    if best is not None:
        t, z2 = best
        json.dump(dict(z=z2.tolist(), fixed_index=t), open(HERE / 'r20_kkt_feasible.json', 'w'), indent=1)
        print('    saved r20_kkt_feasible.json')


if __name__ == '__main__':
    main()
