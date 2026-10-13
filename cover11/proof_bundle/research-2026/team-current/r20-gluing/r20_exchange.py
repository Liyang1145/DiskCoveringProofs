"""R20-EXCH: finite competition-exchange LP for the sharp support (lead-specified procedure).

Object: the authoritative producer family `lead/q0_lower375_dual.py`:
  * factor k value at tuple pi_k and multiplier z:   f_k(pi_k; z) = v_k(pi_k) + M_k(pi_k) . z
  * ETA identically 0 (producer line 15/44): no factor carries an eta coefficient
  * producer cone: z[eta] = 0, z[kappa:] >= 0, z[lambda] >= 0, all other columns free.

Obligation tested: does there exist z such that the candidate tuple pi* is a SIMULTANEOUS MAXIMUM,
      f_k(pi*; z) >= f_k(X; z)  for all X in factor k's box, for every k,
equivalently V(z) = sum_k sup_X f_k(X;z) is attained at pi*?

Procedure (competition exchange, exactly as instructed):
  1. start with the cuts found by sampling;
  2. solve the LP:  max over z of the minimum slack  (or feasibility), with the cuts;
  3. for the returned z, compute each factor's TRUE maximiser X_k* = argmax_X f_k(X;z) on its own
     box by dense grid + local refinement (29 INDEPENDENT 1D/2D/3D problems — no joint search);
  4. add the new cuts, repeat, at most 10 exchanges;
  5. report: reliable feasible (with witness) or numerical infeasible. No artificial |z| box: the
     LP is used in feasibility form; the scaling is reported.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_exchange.py
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
IF, IB, IR = 0, 33, 51
sys.path.insert(0, str(HERE))
from r20_producer_family import load_candidate, value_and_row


# ------------------------------------------------------------------ factor boxes
def box(k):
    """the factor's own parameter box (the producer's construction domain)."""
    if k < 11:
        return [(0, PI), (0, PI)], 'face'
    if k < 20:
        return [(0, PI / 2)], 'switch'
    return [(0, PI), (0, 1), (0, 1)], 'ring'


def to_full(k, X_local, base):
    X = base.copy()
    if k < 11:
        X[3 * k] = X_local[0]; X[3 * k + 1] = X_local[1]
        # the third angle is pi - a - b: keep the box legal
        if X_local[0] + X_local[1] > PI:
            pass
    elif k < 20:
        X[IB + k - 11] = X_local[0]
    else:
        i = k - 20
        X[IR + 3 * i:IR + 3 * i + 3] = X_local
    return X


def face_obj(k, t, z, C, p0):
    """negated objective for face k with the legal box a, b >= 0, a + b <= pi."""
    a = min(max(t[0], 1e-9), PI - 2e-9)
    b = min(max(t[1], 1e-9), PI - a - 1e-9)
    X = p0.copy(); X[3 * k] = a; X[3 * k + 1] = b
    v, M = value_and_row(k, X, C)
    return -(v + M @ z)


def factor_max(k, z, v0, M0, C, p0, ngrid=None):
    """argmax of f_k(X;z) = v_k(X) + M_k(X).z over the factor's own box. Returns (value, X)."""
    if ngrid is None:
        ngrid = 121 if k < 11 else (400 if k < 20 else 24)
    if k < 11:
        best = (-1e30, None)
        aa = np.linspace(1e-9, PI - 2e-9, ngrid)
        for a in aa:
            bs = np.linspace(1e-9, max(1e-9, PI - a - 1e-9), max(4, ngrid // 2))
            for b in bs:
                X = p0.copy(); X[3 * k] = a; X[3 * k + 1] = b
                v, M = value_and_row(k, X, C)
                val = v + M @ z
                if val > best[0]:
                    best = (val, np.array([a, b]))
        out = minimize(lambda t: face_obj(k, t, z, C, p0), best[1],
                       method='Nelder-Mead', options=dict(maxiter=2000, xatol=1e-12))
        t = np.array([min(max(out.x[0], 1e-9), PI - 2e-9), min(max(out.x[1], 1e-9), PI - 1e-9)])
        if t[0] + t[1] > PI - 1e-9:
            t[1] = PI - 1e-9 - t[0]
        X = p0.copy(); X[3 * k] = t[0]; X[3 * k + 1] = t[1]
        v, M = value_and_row(k, X, C)
        return float(v + M @ z), X
    if k < 20:
        bs = np.linspace(1e-9, PI / 2 - 1e-9, ngrid)
        vals = []
        for b in bs:
            X = p0.copy(); X[IB + k - 11] = b
            v, M = value_and_row(k, X, C)
            vals.append(v + M @ z)
        i = int(np.argmax(vals))

        def sw_obj(t):
            bb = min(max(t[0], 1e-9), PI / 2 - 1e-9)
            X = p0.copy(); X[IB + k - 11] = bb
            v, M = value_and_row(k, X, C)
            return -(v + M @ z)
        out = minimize(sw_obj, [bs[i]], method='Nelder-Mead',
                       options=dict(maxiter=1000, xatol=1e-12))
        t = min(max(out.x[0], 1e-9), PI / 2 - 1e-9)
        X = p0.copy(); X[IB + k - 11] = t
        v, M = value_and_row(k, X, C)
        return float(v + M @ z), X
    # ring: 3D
    best = (-1e30, None)
    for a in np.linspace(1e-6, PI - 1e-6, ngrid):
        for u in np.linspace(0, 1, ngrid):
            for v in np.linspace(0, 1, ngrid):
                X = p0.copy(); i = k - 20
                X[IR + 3 * i:IR + 3 * i + 3] = (a, u, v)
                vv, M = value_and_row(k, X, C)
                val = vv + M @ z
                if val > best[0]:
                    best = (val, np.array([a, u, v]))

    def rg_obj(t):
        aa = min(max(t[0], 1e-9), PI - 1e-9)
        uu = min(max(t[1], 0.0), 1.0); vv2 = min(max(t[2], 0.0), 1.0)
        X = p0.copy(); i = k - 20
        X[IR + 3 * i:IR + 3 * i + 3] = (aa, uu, vv2)
        vv, M = value_and_row(k, X, C)
        return -(vv + M @ z)
    out = minimize(rg_obj, best[1], method='Nelder-Mead',
                   options=dict(maxiter=1500, xatol=1e-12))
    t = np.clip(out.x, [1e-9, 0.0, 0.0], [PI - 1e-9, 1.0, 1.0])
    X = p0.copy(); i = k - 20
    X[IR + 3 * i:IR + 3 * i + 3] = t
    v, M = value_and_row(k, X, C)
    return float(v + M @ z), X


def main():
    C = load_candidate(R_CAND); p0 = C['p']
    v0 = np.zeros(29); M0 = np.zeros((29, NZ))
    for k in range(29):
        v0[k], M0[k] = value_and_row(k, p0, C)
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    print('=== R20-EXCH: competition exchange on the producer family ===')
    print('   candidate value  V_const = sum_k v_k(pi*) = %.12f' % v0.sum())
    print('   f_k(pi*;z) = v_k(pi*) + M_k(pi*).z ; candidate slacks are linear in z')
    # initial cuts: the candidate itself is the reference; cuts come from competitors
    cuts_G = []; cuts_h = []
    rng = np.random.default_rng(2)
    for k in range(29):
        for _ in range(3):
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
            cuts_G.append(M0[k] - M); cuts_h.append(v - v0[k])
    cone = []
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; cone.append(r)
    r = np.zeros(NZ); r[LAM] = -1.0; cone.append(r)
    r = np.zeros(NZ); r[ETA] = 1.0; cone.append(r)
    r = np.zeros(NZ); r[ETA] = -1.0; cone.append(r)
    cone = np.array(cone)
    for it in range(10):
        G = np.array(cuts_G); h = np.array(cuts_h)
        AU = np.vstack([-G, cone]); bU = np.r_[-h, np.zeros(cone.shape[0])]
        res = linprog(np.zeros(NZ), A_ub=AU, b_ub=bU, bounds=[(None, None)] * NZ, method='highs')
        if res.status != 0:
            print('   exchange %2d: LP INFEASIBLE with %d cuts -> numerical infeasibility'
                  % (it, len(h)))
            break
        z = res.x
        V = v0.sum() + sum(M0[k] @ z for k in range(29))
        # true factor-wise maximisers
        worst = []; newcuts = 0
        for k in range(29):
            val, X = factor_max(k, z, v0, M0, C, p0)
            ref = v0[k] + M0[k] @ z
            worst.append(val - ref)
            if val - ref > 1e-10:
                v, M = value_and_row(k, X, C)
                cuts_G.append(M0[k] - M); cuts_h.append(v - v0[k]); newcuts += 1
        print('   exchange %2d: cuts %4d -> %4d (+%d) | V(z;pi*) = %+.6f | worst factor excess'
              ' = %+.3e | |z|inf = %.4g'
              % (it, len(h), len(cuts_h), newcuts, V, max(worst), np.abs(z).max()))
        if newcuts == 0:
            print('   no new cut: pi* is a simultaneous maximum for this z (within tolerance)')
            json.dump(dict(z=z.tolist(), V=float(V), cuts=int(len(cuts_h))),
                      open(HERE / 'r20_exchange_witness.json', 'w'), indent=1)
            break
    print('   (LP is in feasibility form: no artificial |z| box was imposed; the reported |z|inf')
    print('    is the norm the solver happened to return, not a constraint.)')


if __name__ == '__main__':
    main()
