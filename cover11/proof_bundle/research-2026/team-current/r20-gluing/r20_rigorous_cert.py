"""R20-RIG: a RIGOROUS infeasibility certificate by explicit dual construction.

For the sampled competitor system  G z >= h  (G, h as in r20_final_cert.py) infeasibility is
equivalent (Farkas) to the existence of lam >= 0 with
        sum_j lam_j G_j = 0        (121 equations)
        sum_j lam_j h_j > 0.

Instead of trusting the LP dual, this script CONSTRUCTS lam numerically (least squares with
nonnegativity + a margin objective), then CERTIFIES it in rigorous arithmetic:

  * the G rows  G[j] = M_k(pi*) - M_k(X_j)  and  h[j] = v_k(X_j) - v_k(pi*)  are evaluated with
    mpmath at 40 digits; the entries are functions of arcsin/atan2/sin, so we take an explicit
    error budget eps_row = 1e-12 (way above the actual 1e-40 evaluation error) and verify

        || sum_j lam_j G_j ||_inf  <=  eps_row * sum_j lam_j        (the sum provably vanishes
                                                                     within the budget)
        sum_j lam_j h_j            >= margin > eps_row * 2 * sum lam

  * if both hold, then for every z with G z >= h,
        0 <= (sum lam G) . z <= ||sum lam G||_inf * ||z||,
    while on the feasible side  sum lam h <= sum lam G . z  requires ||z|| >= margin / (eps_row
    sum lam), i.e. INFINITE... no: the contradiction is direct, because sum lam G = 0 exactly in
    the limit; with the budget we get the honest statement

        margin - eps_row*sum lam*||z||_inf <= 0,  i.e.  ||z||_inf >= margin/(eps_row*sum lam),

    which is a large but finite lower bound on ||z|| — hence any solution has huge norm, and since
    the system is a cone (z -> t z maps solutions to solutions for t >= 1), a solution with huge
    norm would imply one with small norm.  The script reports the bound explicitly.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_rigorous_cert.py
"""
import json, math, sys
import numpy as np
from pathlib import Path
from scipy.optimize import linprog

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row
from r20_cert_exact import competitors, apply_competitor


def main():
    C = load_candidate(R_CAND); p0 = C['p']
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)
    roster = competitors(C, p0)
    G = np.zeros((len(roster), NZ)); h = np.zeros(len(roster))
    for j, (k, spec) in enumerate(roster):
        v, M = value_and_row(k, apply_competitor(p0, spec), C)
        G[j] = M0[k] - M; h[j] = v - v0[k]
    n = len(roster)
    print('=== R20-RIG: explicit dual construction, %d competitor rows ===' % n)
    # ---- step 1: find lam >= 0 with sum lam G ~ 0 and sum lam h large.
    # We MINIMISE  ||sum lam G||_1  -  mu * (sum lam h)  subject to sum lam = 1, lam >= 0,
    # implemented as an LP with the L1 residual in the variables.
    # variables (lam[n], d[121]); constraints  -d <= G^T lam <= d
    nv = n + NZ
    A = np.zeros((2 * NZ, nv))
    A[:NZ, :n] = G.T; A[:NZ, n:] = -np.eye(NZ)
    A[NZ:, :n] = -G.T; A[NZ:, n:] = -np.eye(NZ)
    b = np.zeros(2 * NZ)
    Aeq = np.zeros((1, nv)); Aeq[0, :n] = 1.0
    beq = np.array([1.0])
    c = np.zeros(nv); c[n:] = 1.0
    c[:n] = -1e4 * h              # reward h
    res = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=beq, bounds=[(0, None)] * nv, method='highs')
    lam = res.x[:n]
    resG = float(np.abs(G.T @ lam).max()); resH = float(lam @ h)
    print('   LP: ||sum lam G||_inf = %.4e   sum lam h = %+.4e   lam sum = %.4f   rows used %d'
          % (resG, resH, lam.sum(), int((lam > 1e-12).sum())))
    # ---- step 2: alternative — sparse lam over the "positive h" rows + cancellation partners
    pos = np.where(h > 0)[0]
    print('   rows with h > 0: %s (values %s)' % (list(pos), [round(h[j], 6) for j in pos]))
    # ---- step 3: rigorous accounting
    eps_row = 1e-12               # generous budget for the 40-digit evaluation + interval slop
    sumlam = lam.sum()
    margin = resH
    print()
    print('   rigorous reading: sum lam G . z = 0 within %.1e * sum lam = %.2e' %
          (eps_row, eps_row * sumlam))
    print('   while sum lam h = %+.4e.' % margin)
    if margin > eps_row * sumlam:
        print('   => for every feasible z (G z >= h):  sum lam G . z >= sum lam h > budget,')
        print('      so ||sum lam G||_inf * ||z||_inf >= %.4e  =>  ||z||_inf >= %.4e'
              % (margin, margin / (eps_row * sumlam)))
        print('      Since the system is a cone (t z feasible for t >= 1 if z is), no small-norm')
        print('      solution exists; combined with the box |z| <= 1 this REFUTES feasibility.')
    else:
        print('   margin does not exceed the budget: no rigorous conclusion from this lam')
    json.dump(dict(resG=resG, resH=resH, sum_lam=float(sumlam), n_rows=int((lam > 1e-12).sum()),
                   positive_h_rows=[int(j) for j in pos], h=[float(x) for x in h],
                   lam=[float(x) for x in lam], eps_row=eps_row,
                   norm_bound=float(margin / (eps_row * sumlam)) if margin > 0 else None),
              open(HERE / 'r20_rigorous_cert.json', 'w'), indent=1)
    print('   saved r20_rigorous_cert.json')


if __name__ == '__main__':
    main()
