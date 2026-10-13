"""R20-AB: extract the affine-LP witness z and VERIFY it directly (the decisive test).

The 78-parameter affine LP is feasible with a positive margin.  Feasibility of an LP with
floating-point tolerances proves nothing by itself, so this file

 V1  re-evaluates every constraint row of the found z in double precision and reports the true
     minimum slack (validity rows, KKT rows, one-sided rows, cone);
 V2  evaluates V(z) at the candidate tuple (must be exactly pi for a sharp witness);
 V3  tests the bound directly: searches for any configuration in the class with V(z) < pi - eps
     (multi-start local minimisation over the 78 parameters, domain-respecting).
     * if a violation is found, z is NOT a valid bound and the LP feasibility is an artefact;
     * if the search finds none, z is a candidate witness and the remaining obligation is a
       rigorous global-minimality proof, not a numerical one.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_verify_witness.py
"""
import json, math, sys
import numpy as np
from pathlib import Path
from scipy.optimize import linprog, minimize

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
NP = 78
I_FACE, I_BSW, I_RNG = 0, 33, 51
sys.path.insert(0, str(HERE))
from r20_rebuild import load_candidate, lin_form, const_of, param_table
from r20_affine_lp import build_all, cone_matrix, sample_tuples


def get_witness(npts=200, seed=17):
    C = load_candidate(R_CAND); p0 = C['p']
    D = build_all(C, p0, npts, seed)
    tab, B, bp, Rv, bv = D['tab'], D['B'], D['bp'], D['Rv'], D['bv']
    Aeq = []; beq = []; Aub = []; bub = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q])
        elif r['activity'] == 'up':
            Aub.append(-B[q]); bub.append(bp[q])
        else:
            Aub.append(B[q]); bub.append(-bp[q])
    cone, _ = cone_matrix()
    Aeq = np.array(Aeq); beq = np.array(beq)
    Aub = np.vstack([np.array(Aub), cone]); bub = np.r_[np.array(bub), np.zeros(cone.shape[0])]
    A = np.hstack([-Rv, -np.ones((Rv.shape[0], 1))])
    Aub2 = np.vstack([np.hstack([Aub, np.zeros((Aub.shape[0], 1))]), A])
    bb = np.r_[bub, bv]
    Aeq2 = np.hstack([Aeq, np.zeros((Aeq.shape[0], 1))])
    c = np.zeros(NZ + 1); c[NZ] = 1.0
    res = linprog(c, A_ub=Aub2, b_ub=bb, A_eq=Aeq2, b_eq=beq, bounds=[(-1, 1)] * NZ + [(None, None)],
                  method='highs')
    return C, p0, D, res, (Rv, bv, Aub, bub, Aeq, beq)


def V_of(p, z, C):
    """exact factor-wise V(z) at the tuple p (78-parameter instrument)."""
    V = const_of(z, C['R'])
    for k in range(29):
        a, b = lin_form(k, p, C)
        V += b + a @ z
    return V


def main():
    C, p0, D, res, rows = get_witness()
    z = res.x[:NZ]
    print('=== V1: re-evaluation of the found z (npts=200, seed=17) ===')
    print('    |z|_inf = %.6f   z nonzero: %d entries' % (np.abs(z).max(), int((np.abs(z) > 1e-12).sum())))
    Rv, bv, Aub, bub, Aeq, beq = rows
    slack_val = Rv @ z - bv
    print('    validity rows: %d ; min slack = %+.6e ; count < 0 = %d'
          % (len(bv), slack_val.min(), int((slack_val < 0).sum())))
    s_eq = np.abs(Aeq @ z + beq)
    print('    KKT equality rows: %d ; max |residual| = %.3e' % (Aeq.shape[0], s_eq.max()))
    s_ub = Aub @ z - bub
    print('    cone+one-sided rows: %d ; max violation = %+.3e' % (Aub.shape[0], s_ub.max()))
    Vc = V_of(p0, z, C)
    print('    V(z; pi*) = %.15f   (pi = %.15f, excess %+.3e)' % (Vc, PI, Vc - PI))

    # ---------- V3: direct search for a violating configuration
    print()
    print('=== V3: direct bound test — minimise V(z) over the class ===')
    rng = np.random.default_rng(3)
    R = C['R']
    qmin = 4 * math.sin(PI - 8 * math.asin(R)) ** 2 / R ** 2

    def project(p):
        p = p.copy()
        for t in range(11):
            a = min(max(p[3 * t], 1e-9), PI - 1e-9); b = min(max(p[3 * t + 1], 1e-9), PI - 1e-9)
            if a + b > PI - 1e-9:
                b = PI - 1e-9 - a
            p[3 * t] = a; p[3 * t + 1] = b; p[3 * t + 2] = min(max(p[3 * t + 2], 0.0), 1.0)
        for i in range(9):
            p[I_BSW + i] = min(max(p[I_BSW + i], 1e-9), PI / 2 - 1e-9)
            p[I_BSW + 9 + i] = min(max(p[I_BSW + 9 + i], 0.0), 1.0)
        for i in range(9):
            a = min(max(p[I_RNG + 3 * i], 1e-9), PI - 1e-9)
            u = min(max(p[I_RNG + 3 * i + 1], 0.0), 1.0)
            v = min(max(p[I_RNG + 3 * i + 2], 0.0), 1.0)
            if (u - v) ** 2 + 4 * u * v * math.sin(a / 2) ** 2 < qmin:
                u = 1.0; v = 1.0
            p[I_RNG + 3 * i] = a; p[I_RNG + 3 * i + 1] = u; p[I_RNG + 3 * i + 2] = v
        return p

    best = V_of(p0, z, C); bestp = p0.copy()
    starts = [p0.copy()]
    for _ in range(60):
        starts.append(project(p0 + rng.normal(0, 0.4, NP)))
    for s, p in enumerate(starts):
        f = lambda x: V_of(project(x), z, C)
        out = minimize(f, p, method='Nelder-Mead',
                       options=dict(maxiter=4000, xatol=1e-10, fatol=1e-13))
        q = project(out.x)
        v = V_of(q, z, C)
        if v < best:
            best = v; bestp = q
    print('    best (smallest) V found = %.12f   deficit vs pi = %+.3e' % (best, best - PI))
    print('    number of starts: %d' % len(starts))
    if best < PI - 1e-6:
        print('    => VIOLATION FOUND: z is not a valid upper bound at R = r_cand.')
        print('       argmin tuple (first 12 params): %s' % np.round(bestp[:12], 6))
    else:
        print('    => no violation found in this search (necessary but not sufficient).')
    json.dump(dict(V_cand=float(Vc), min_found=float(best), deficit=float(best - PI),
                   min_slack_val=float(slack_val.min()), max_kkt_res=float(s_eq.max()),
                   max_ub_viol=float(s_ub.max()), z=z.tolist(),
                   argmin=list(map(float, bestp))),
              open(HERE / 'r20_witness.json', 'w'), indent=1)
    print('    saved r20_witness.json')


if __name__ == '__main__':
    main()
