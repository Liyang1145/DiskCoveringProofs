"""R20-DEC2: bounded decisive test.

Feasibility question (bounded, so linprog can settle it):
    exists z with   (COMP) G z >= h          [46 rational competitors]
                    (KKT)  affine stationarity at the candidate
                    (CONE) z[KAP:] >= 0, z[ETA] = 0, z[LAM] >= 0
                    (TIGHT) V(z; pi*) <= pi   [V is exactly pi at a valid sharp witness]
                    (BOX)  |z|_inf <= ZMAX

The box is only a normalisation: if the unboxed system has a solution, scaling it down (the KKT
rows are affine with a constant term; the competitor rows are conic) gives a solution with small
norm, so a reasonable ZMAX does not lose the answer.  Both ZMAX = 1e3 and 1e6 are tried.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_dec2.py
"""
import json, math, sys
import numpy as np
from pathlib import Path
from scipy.optimize import linprog

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
KAP, ETA, LAM = 50, 72, 71
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_decisive import build, cone


def main():
    d = build()
    Vc = np.zeros(NZ)
    for k in range(29):
        Vc += d['M0'][k]
    Vconst = float(d['v0'].sum())
    print('=== R20-DEC2: bounded feasibility ===')
    print('   V(z;pi*) = %.9f + Vc.z ; the tight requirement is V - pi <= 0, i.e. Vc.z <= %+.6e'
          % (Vconst, PI - Vconst))
    cA, cb = cone()
    for ZMAX in (1e3, 1e6):
        AU = [-d['G']]; bU = [-d['h']]
        AE = [d['Aeq']]; bE = [d['beq']]
        AU += [d['Aup'], cA, Vc[None, :]]
        bU += [d['bup'], cb, np.array([PI - Vconst])]
        AU = np.vstack(AU); bU = np.concatenate([np.asarray(x, float).ravel() for x in bU])
        AE = np.vstack(AE); bE = np.concatenate([np.asarray(x, float).ravel() for x in bE])
        res = linprog(np.zeros(NZ), A_ub=AU, b_ub=bU, A_eq=AE, b_eq=bE,
                      bounds=[(-ZMAX, ZMAX)] * NZ, method='highs')
        print('   ZMAX=%g : %s' % (ZMAX, 'FEASIBLE' if res.status == 0 else 'INFEASIBLE'))
        if res.status == 0:
            z = res.x
            V = Vconst + Vc @ z
            print('        witness |z|inf = %.6g   V = %.9f   competitor slack min = %+.3e'
                  % (np.abs(z).max(), V, float(np.min(d['G'] @ z - d['h']))))
            json.dump(dict(z=z.tolist(), V=float(V), ZMAX=ZMAX),
                      open(HERE / 'r20_dec2_witness.json', 'w'), indent=1)
            break
        # which subset fails?  dig by dropping TIGHT
        AU2 = np.vstack([-d['G'], d['Aup'], cA]); bU2 = np.concatenate(
            [np.asarray(-d['h'], float).ravel(), np.asarray(d['bup'], float).ravel(), cb])
        r2 = linprog(np.zeros(NZ), A_ub=AU2, b_ub=bU2, A_eq=AE, b_eq=bE,
                     bounds=[(-ZMAX, ZMAX)] * NZ, method='highs')
        print('        without TIGHT: %s' % ('FEASIBLE' if r2.status == 0 else 'INFEASIBLE'))
        if r2.status == 0:
            zg = r2.x
            print('        that witness has V = %.9f (must be <= pi = %.9f for tightness)'
                  % (Vconst + Vc @ zg, PI))
    json.dump(dict(Vconst=Vconst), open(HERE / 'r20_dec2.json', 'w'), indent=1)


if __name__ == '__main__':
    main()
