"""R20-EXCH2: competition exchange WITH the candidate's affine KKT rows (bounded, 10 exchanges).

Scope statement (lead-specified): this tests the PRODUCER FAMILY's ability to support the saved
candidate as a simultaneous maximum, with the affine stationarity rows of the candidate included
(exactly the rows a sharp support must satisfy). It is a statement about this family at
R = r_cand, not about the covering theorem.

    find z :   (cuts)  f_k(pi*;z) >= f_k(X_j;z)   for the accumulated competitor cuts
               (KKT)   v'_r + M'_r . z = 0 (interior) / >= 0 (upper end) / <= 0 (lower end)
               (probe cone)  z[eta] = 0, z[kappa:] >= 0, z[lambda] >= 0
               (box)   |z|_inf <= ZMAX     -- the probe's own search used |z_i| <= 3, |z|_inf <= 3;
                                              ZMAX = 3 is therefore the *documented* scope, and
                                              ZMAX = 1e3 / 1e6 are reported as wider scopes.

Each exchange: solve the LP (feasibility; no objective), take the returned z, compute each
factor's true maximiser X_k* on its own box, add those 29 cuts, repeat. Report the verdict with
its scope; "no witness found within N exchanges" is NOT upgraded to a disproof.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_exch2.py
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
IF, IB, IR = 0, 33, 51
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row, param_table
from r20_exchange import factor_max


def setup():
    C = load_candidate(R_CAND); p0 = C['p']
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)
    B = np.load(HERE / 'r20_prod_B.npy'); bp = np.load(HERE / 'r20_prod_bp.npy')
    tab = param_table(p0)
    Aeq = []; beq = []; Aup = []; bup = []
    for r in tab:
        q = r['q']
        if r['activity'] == 'in':
            Aeq.append(B[q]); beq.append(-bp[q])
        elif r['activity'] == 'up':
            Aup.append(-B[q]); bup.append(bp[q])
        else:
            Aup.append(B[q]); bup.append(-bp[q])
    cone = []
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; cone.append(r)
    r = np.zeros(NZ); r[LAM] = -1.0; cone.append(r)
    r = np.zeros(NZ); r[ETA] = 1.0; cone.append(r)
    r = np.zeros(NZ); r[ETA] = -1.0; cone.append(r)
    return C, p0, v0, M0, np.array(Aeq), np.array(beq), np.array(Aup), np.array(bup), np.array(cone)


def seed_cuts(C, p0, v0, M0, rng, per_factor=3):
    G = []; h = []
    for k in range(29):
        for _ in range(per_factor):
            X = p0.copy()
            if k < 11:
                a = rng.uniform(1e-9, PI); b = rng.uniform(1e-9, PI - a)
                X[3 * k] = a; X[3 * k + 1] = b
            elif k < 20:
                X[IB + k - 11] = rng.uniform(1e-9, PI / 2)
            else:
                i = k - 20
                X[IR + 3 * i:IR + 3 * i + 3] = (rng.uniform(1e-6, PI - 1e-6),
                                                rng.uniform(0, 1), rng.uniform(0, 1))
            v, M = value_and_row(k, X, C)
            G.append(M0[k] - M); h.append(v - v0[k])
    return G, h


def run(ZMAX, verbose=True, seed=2):
    C, p0, v0, M0, Aeq, beq, Aup, bup, cone = setup()
    rng = np.random.default_rng(seed)
    G, h = seed_cuts(C, p0, v0, M0, rng)
    verdict = None
    hist = []
    for it in range(10):
        GA = np.array(G); hA = np.array(h)
        AU = np.vstack([-GA, Aup, cone]); bU = np.r_[-hA, bup, np.zeros(cone.shape[0])]
        res = linprog(np.zeros(NZ), A_ub=AU, b_ub=bU, A_eq=Aeq, b_eq=beq,
                      bounds=[(-ZMAX, ZMAX)] * NZ, method='highs')
        if res.status != 0:
            verdict = 'INFEASIBLE(boxed)'
            hist.append((it, len(h), None, None))
            break
        z = res.x
        V = v0.sum() + sum(M0[k] @ z for k in range(29))
        new = 0; worst = -1e30
        for k in range(29):
            val, X = factor_max(k, z, v0, M0, C, p0)
            ref = v0[k] + M0[k] @ z
            worst = max(worst, val - ref)
            if val - ref > 1e-10:
                v, M = value_and_row(k, X, C)
                G.append(M0[k] - M); h.append(v - v0[k]); new += 1
        hist.append((it, len(h) - new, float(V), float(worst), float(np.abs(z).max()), new))
        if verbose:
            print('   exchange %2d: cuts %4d (+%2d) | V(z;pi*) = %+.6f | worst excess %+.3e'
                  ' | |z|inf %.4g' % (it, len(h) - new, new, V, worst, np.abs(z).max()))
        if new == 0:
            verdict = 'WITNESS'
            json.dump(dict(z=z.tolist(), V=float(V), ZMAX=ZMAX, cuts=len(h)),
                      open(HERE / ('r20_exch2_witness_%g.json' % ZMAX), 'w'), indent=1)
            break
    if verdict is None:
        verdict = 'NO-WITNESS-IN-10'
    return dict(ZMAX=ZMAX, verdict=verdict, history=hist, cuts=len(h))


def main():
    print('=== R20-EXCH2: exchange with KKT rows, scope stated ===')
    print('   (the producer\'s own search used bounds |z_i| <= 3, so ZMAX = 3 is the documented')
    print('    scope of the saved dual family; wider scopes are reported for information)')
    out = []
    for ZMAX in (3.0, 1e3, 1e6):
        r = run(ZMAX)
        print('   ZMAX=%g -> %s (%d cuts)' % (ZMAX, r['verdict'], r['cuts']))
        out.append(r)
        print()
    json.dump(out, open(HERE / 'r20_exch2.json', 'w'), indent=1, default=str)
    print('   saved r20_exch2.json')


if __name__ == '__main__':
    main()
