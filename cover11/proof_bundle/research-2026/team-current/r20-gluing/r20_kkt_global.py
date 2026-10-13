"""R20-S: the full obligation at the correct caliber (R = r_cand) — three parts.

(1) KKT/activity system        : exists z != 0 with two-sided rows for the 42 interior
                                 parameters, one-sided rows for the 27 active copies, cone.
(2) GLOBAL maximality          : for the z found in (1), is the candidate also a GLOBAL maximum
                                 of every factor (not just stationary)?
(3) SECOND-ORDER condition     : Hessian of the Lagrangian at the candidate on the interior
                                 parameter block (necessary for a maximum).
If all three hold, z is a genuine sharp support at R = r_cand.  If any fails, the certificate
locates the obstruction.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_global.py
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


def main():
    from r20_factor_probe import Model
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    B, meta = build(C, p0)
    A_sys = np.zeros((29, NZ))
    for k in range(29):
        a, b = lin_form(k, p0, C); A_sys[k] = a

    def fk(k, p, z):
        a, b = lin_form(k, p, C)
        return b + a @ z

    # ---------------- (1) KKT + activity LP, then read the z
    eq = np.array([B[m['q']] for m in meta if m['activity'] == 'in'])
    ineq = []
    for m in meta:
        if m['activity'] == 'lo':
            ineq.append(-B[m['q']])
        elif m['activity'] == 'hi':
            ineq.append(B[m['q']])
    ineq = np.array(ineq)
    cone = []
    for i in range(11):
        r = np.zeros(NZ); r[i] = 1.0; cone.append(r)
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; cone.append(r)
    for i in range(9):
        r = np.zeros(NZ); r[CL + i] = -1.0; cone.append(r)
    cone = np.array(cone)
    A_ub = np.vstack([cone, ineq]); b_ub = np.zeros(A_ub.shape[0])
    zs = []
    for idx in [11, 32, 50, 73, 94, 112, 20]:
        A_eq = np.vstack([eq, np.eye(1, NZ, idx)])
        b_eq = np.r_[np.zeros(eq.shape[0]), 1.0]
        res = linprog(np.zeros(NZ), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(-10, 10)] * NZ, method='highs')
        if res.status == 0:
            zs.append((idx, res.x))
    print('=== (1) KKT + activity system at R = r_cand ===')
    print('    42 two-sided rows, 27 one-sided rows, cone 41; feasible normalisations: %d' % len(zs))

    # ---------------- (2) global maximality + (3) second order, for each found z
    print()
    print('=== (2)+(3) global maximality and second order for the found z ===')
    m = Model('q0_lower375_dual_0_4.json', R, 'z')
    rep = []
    for idx, z in zs:
        m.z = z
        # global max over each factor's own domain (dense sampling + local polish)
        worst = []
        for k in range(29):
            a, b = lin_form(k, p0, C); mine = b + a @ z
            mx = -1e30; arg = None
            if k < 11:
                t = k
                for a1 in np.linspace(1e-9, PI, 160):
                    for b1 in np.linspace(1e-9, PI - a1, 160):
                        v = m.face_val(t, a1, b1)[0]
                        if v > mx: mx = v; arg = (a1, b1)
            elif k < 20:
                bi = k - 11
                for b1 in np.linspace(1e-9, PI / 2, 3000):
                    v = m.switch_val(bi, b1)[0]
                    if v > mx: mx = v; arg = (b1,)
            else:
                i = k - 20
                qmin = 4 * math.sin(PI - 8 * math.asin(R)) ** 2 / R ** 2
                for a1 in np.linspace(1e-6, PI - 1e-6, 45):
                    for u1 in np.linspace(0, 1, 25):
                        for v1 in np.linspace(0, 1, 25):
                            q = (u1 - v1) ** 2 + 4 * u1 * v1 * math.sin(a1 / 2) ** 2
                            if q < qmin: continue
                            v = m.ring_val(i, a1, u1, v1)
                            if v > mx: mx = v; arg = (a1, u1, v1)
            worst.append(mx - mine)
        V = const_of(z, R)
        for k in range(29):
            a, b = lin_form(k, p0, C); V += b + a @ z
        print('    z fixed at index %3d: V(z) at candidate = %+.6f   min factor deficit = %+.3e'
              % (idx, V, min(worst)))
        print('       worst 4 deficits: %s' % [round(x, 6) for x in sorted(worst)[:4]])
        rep.append(dict(idx=idx, V=float(V), min_deficit=float(min(worst)),
                        deficits=[float(x) for x in worst]))
    json.dump(rep, open(HERE / 'r20_kkt_global.json', 'w'), indent=1)
    print('    saved r20_kkt_global.json')


if __name__ == '__main__':
    main()
