"""R20-T: definitive LP at the correct caliber — can the pure 29-factor family justify the
candidate as a simultaneous maximum at R = r_cand?

WHY THIS FILE.  With R = r_cand = 0.3799838531198388 the saved configuration's radius copies
saturate (y = 1 for many factors), which is the caliber point the lead raised.  The earlier
r20_kkt_system.json used R = 19/50 and the earlier Farkas runs treated the copies with the wrong
cone, so neither answers the question.

CONSTRUCTION (each entry measured directly from the factor formulas, no hand-derived signs):
  * The z-coefficient row of factor k at tuple X is  a_k(X)  with  f_k(X;z) = b_k(X) + a_k(X).z.
  * Constraint / sign-safety rows: for every sampled tuple X in every factor's own domain,
        row(X) = a_k(pi^*) - a_k(X),   rhs(X) = b_k(X) - b_k(pi^*),
    so "V(z) >= pi" means row(X).z >= rhs(X) for all X.  These rows are the exact validity
    condition of the assembled bound (they encode z_c*g_c >= 0 on the class, whatever the
    per-family sign convention is).
  * KKT rows: d/dxi f_k(pi^*;z) = 0 for interior parameters, one-sided for the 27 active copies.
  * Cone rows: z <= 0 for the site/hub family, z >= 0 for the Delaunay and closure families.

QUESTIONS
  Q1: is {z : validity rows, KKT rows, cone} larger than {0}?
  Q2: for such z, does V(z) = pi hold at the candidate?
  Q3: if infeasible, produce the Farkas certificate from the sampled rows.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_lp_final.py
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
from r20_kkt_active import build, const_vec


def sample_tuples(C, p0, npts, seed):
    """sample tuples inside each factor's own domain; return (list of (k, X), arrays)."""
    rng = np.random.default_rng(seed)
    R = C['R']; out = []
    for k in range(11):
        cnt = 0
        while cnt < npts:
            a = rng.uniform(1e-9, PI); b = rng.uniform(1e-9, PI)
            if a + b >= PI - 1e-9:
                continue
            y = rng.uniform(0, 1)
            X = p0.copy(); X[3 * k:3 * k + 3] = (a, b, y)
            out.append((k, X)); cnt += 1
    for k in range(11, 20):
        for _ in range(npts):
            b = rng.uniform(1e-9, PI / 2)
            X = p0.copy(); X[33 + k - 11] = b
            out.append((k, X))
    qmin = 4 * math.sin(PI - 8 * math.asin(R)) ** 2 / R ** 2
    for k in range(20, 29):
        cnt = 0
        while cnt < npts:
            a = rng.uniform(1e-6, PI - 1e-6); u = rng.uniform(0, 1); v = rng.uniform(0, 1)
            q = (u - v) ** 2 + 4 * u * v * math.sin(a / 2) ** 2
            if q < qmin:
                continue
            X = p0.copy(); i = k - 20
            X[42 + 3 * i:42 + 3 * i + 3] = (a, u, v)
            out.append((k, X)); cnt += 1
    return out


def main():
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B, meta = build(C, p0)
    a_c, b_c = {}, {}
    for k in range(29):
        a, b = lin_form(k, p0, C); a_c[k] = a; b_c[k] = b
    # ---- validity rows
    print('=== building validity rows from the factor formulas (exact) ===')
    npts = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    S = sample_tuples(C, p0, npts, seed)
    Rv = np.zeros((len(S), NZ)); bv = np.zeros(len(S)); worst_a = 0.0
    for j, (k, X) in enumerate(S):
        a, b = lin_form(k, X, C)
        Rv[j] = a_c[k] - a
        bv[j] = b - b_c[k]
    print('    sampled tuples: %d (%d per factor)' % (len(S), npts))
    # control on the definition: V(z) - pi = sum_k (f_k(pi*) - f_k(X)) at z where X is the argmax
    print('    row definition check on the saved z_c825:')
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    lhs = Rv @ zc - bv   # = sum over samples of (f_k(pi*) - f_k(X)); negative if the sample is better
    print('       min over samples of [f_k(pi*) - f_k(X)] = %+.6f  (the candidate is beaten there)'
          % lhs.min())

    # ---- KKT + cone rows
    eq = []; ineq = []
    for m in meta:
        if m['activity'] == 'in':
            eq.append(B[m['q']])
        elif m['activity'] == 'lo':
            ineq.append(-B[m['q']])
        else:
            ineq.append(B[m['q']])
    eq = np.array(eq); ineq = np.array(ineq)
    cone = []
    for i in range(11):
        r = np.zeros(NZ); r[i] = 1.0; cone.append(r)
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; cone.append(r)
    for i in range(9):
        r = np.zeros(NZ); r[CL + i] = -1.0; cone.append(r)
    cone = np.array(cone)
    # V(z) >= pi at the candidate is automatic (V(pi*;z) = pi + sum_c z_c A_c, A_c=0 by construction)
    # ---- LP feasibility for several normalisations
    print()
    print('=== LP: z in cone, KKT rows, one-sided rows, validity rows (V >= pi on the class) ===')
    A_ub = np.vstack([cone, ineq, Rv])
    b_ub = np.r_[np.zeros(cone.shape[0] + ineq.shape[0]), bv]
    print('    rows: cone %d + one-sided %d + validity %d = %d ; columns 121'
          % (cone.shape[0], ineq.shape[0], Rv.shape[0], A_ub.shape[0]))
    found = []
    for idx in [11, 32, 50, 73, 94, 112, 20, 115, 41]:
        A_eq = np.vstack([eq, np.eye(1, NZ, idx)])
        b_eq = np.r_[np.zeros(eq.shape[0]), 1.0]
        res = linprog(np.zeros(NZ), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(-20, 20)] * NZ, method='highs')
        ok = res.status == 0
        if ok:
            z = res.x
            V = const_of(z, R)
            for k in range(29):
                V += b_c[k] + a_c[k] @ z
            found.append((idx, z, V))
            print('    z[%3d]=1: FEASIBLE   V(z) = %+.6f   min validity slack = %+.3e'
                  % (idx, V, float(np.min(Rv @ z - bv))))
        else:
            print('    z[%3d]=1: INFEASIBLE (%s)' % (idx, res.message))
    print('    feasible: %d of 9' % len(found))
    out = dict(R=R, npts=npts, seed=seed, n_samples=int(len(S)),
               feasible=[dict(idx=int(i), V=float(v), z=z.tolist()) for i, z, v in found])
    json.dump(out, open(HERE / 'r20_kkt_lp_final.json', 'w'), indent=1)
    print('    saved r20_kkt_lp_final.json')


if __name__ == '__main__':
    main()
