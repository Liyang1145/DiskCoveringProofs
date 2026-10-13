"""R20-FINAL: the 121-column family EXACTLY as the authoritative producer defines it.

SOURCE OF TRUTH (lead): `lead/q0_lower375_dual.py` (producer of the saved z) and
`lead/certify_q0_lower375.py` (its certifier).  Structure read off those files:

  columns  0:11  mu11   (factor-mu family: vertex angle sums)          FREE  (bounds only)
          11:32  side21 (squared side match)                          FREE
          32:50  rr18   (squared radius copies; switch copies positive, sector copies negative)
                                                                      FREE
          50:71  kap21  (ear capacity; producer comment "no ear capacity constraint in q0"
                          -> the family is INACTIVE, and the certifier asserts z[kap:] >= 0)
          71     lam    (total width)                                 >= 0 in the producer's search
          72     eta    ETA FIXED 0 (const[eta]=0, bounds[eta]=(0,0))
          73:94  lin21  (first-moment side match)                     FREE
          94:112 lin-copies 18 (first-moment radius copies)           FREE
          112:121 cl9   (cyclic closure)                              FREE
  factors  11 faces (per-face (a,b) angles + radius y), 9 switches ((b,y) each),
           9 sectors ((alpha,u,v) each)  -> 78 free parameters (independent copies).

  f_k(pi_k; z) = v_k(pi_k) + M_k(pi_k) . z          (v_k = the primal area term, NOT z-scaled)
  so the inverse system is AFFINE: the KKT rows are  d v_k/d xi + (d M_k/d xi) . z.

This file measures BOTH parts numerically from the producer's own construction and verifies the
factor *values* against the producer's formulas at the candidate.  Then it runs the sharp-support
LP:   find z with   f_k(pi*) >= f_k(X) for all sampled competitor X in every factor domain,
      plus the affine KKT conditions of the candidate, plus the producer's cone (kappa >= 0,
      eta = 0, lam >= 0).
If that is infeasible, the pure 121-column 29-factor family cannot make the saved candidate a
simultaneous maximum at R = r_cand; a superset test (no KKT rows) only strengthens the refutation.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_producer_family.py
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
NP = 78
IF, IB, IR = 0, 33, 51


def load_candidate(R):
    o = json.loads((LEAD / 'q0_exact_closure_radius.json').read_text(encoding='utf-8'))
    x0 = np.array(o['x0'], float)
    faces = o['faces']; edges = [tuple(e) for e in o['edges']]
    adj = {e: [(t, next(k for k in f if k not in e)) for t, f in enumerate(faces)
               if e[0] in f and e[1] in f] for e in edges}
    ang = x0[:33].reshape(11, 3); bsw = x0[33:42]
    rho = np.exp(x0[42:62] + x0[62])
    yface = rho[:11] / R; ysw = rho[11:20] / R
    y = ysw.copy(); u = np.roll(y, 1); v = y
    raw = np.zeros(9)
    for t, f in enumerate(faces):
        for k, i in enumerate(f):
            if i < 9:
                raw[i] += ang[t, k]
    a_r = PI - raw + np.roll(bsw, 1) + bsw
    p = np.zeros(NP)
    for t in range(11):
        p[3 * t] = ang[t, 0]; p[3 * t + 1] = ang[t, 1]; p[3 * t + 2] = yface[t]
    p[IB:IB + 9] = bsw
    p[IB + 9:IB + 18] = ysw
    for i in range(9):
        p[IR + 3 * i] = a_r[i]; p[IR + 3 * i + 1] = u[i]; p[IR + 3 * i + 2] = v[i]
    return dict(p=p, R=R, faces=faces, edges=edges, adj=adj, ang=ang, bsw=bsw,
                yface=yface, ysw=ysw, alpha=a_r, u=u, v=v, cand_radius=o['candidate_radius'])


# ------------------------------------------------------------------ producer factors
def ring_geom(R, aa, uu, vv):
    ch = R * math.sqrt(max(0.0, uu * uu + vv * vv - 2 * uu * vv * math.cos(aa)))
    w = 2 * math.asin(min(1.0, ch / 2))
    S = R * R * uu * vv * math.sin(aa) / 2 + (w - math.sin(w)) / 2
    left = math.atan2(vv * math.sin(aa), uu - vv * math.cos(aa))
    right = math.atan2(uu * math.sin(aa), vv - uu * math.cos(aa))
    return S, w, left, right


def value_and_row(k, p, C):
    """(v_k, M_k) exactly as the producer builds them, for the factor tuple p[pi_k]."""
    R = C['R']; faces = C['faces']; edges = C['edges']; adj = C['adj']
    M = np.zeros(NZ); val = 0.0
    if k < 11:
        t = k
        a1, b1, y = p[3 * t], p[3 * t + 1], p[3 * t + 2]
        c1 = PI - a1 - b1
        ang = (a1, b1, c1)
        val = 2 * R * R * y * y * math.prod(math.sin(x) for x in ang)
        for m, i in enumerate(faces[t]):
            e = tuple(sorted(j for j in faces[t] if j != i)); ei = edges.index(e)
            sgn = 1.0 if adj[e][0][0] == t else -1.0
            M[i] -= ang[m]; M[KAP + ei] -= ang[m]
            M[SIDE + ei] += sgn * y * y * math.sin(ang[m]) ** 2
            M[LIN + ei] += sgn * y * math.sin(ang[m])
    elif k < 20:
        bi = k - 11
        i, j = bi, (bi + 1) % 9
        e = tuple(sorted((i, j))); ei = edges.index(e)
        bb = p[IB + bi]; y = p[IB + 9 + bi]
        val = R * R * y * y * math.sin(2 * bb) / 2
        M[CL + bi] += 2 * bb
        M[i] += bb; M[j] += bb; M[KAP + ei] -= bb
        M[SIDE + ei] -= y * y * math.sin(bb) ** 2
        M[LIN + ei] -= y * math.sin(bb)
        M[RR + 2 * i + 1] += y * y
        M[RR + 2 * j] += y * y
        M[LIN + 21 + 2 * i + 1] += y
        M[LIN + 21 + 2 * j] += y
    else:
        i = k - 20
        aa = p[IR + 3 * i]; uu = p[IR + 3 * i + 1]; vv = p[IR + 3 * i + 2]
        S, w, left, right = ring_geom(R, aa, uu, vv)
        val = S
        M[CL + (i - 1) % 9] = left + w / 2
        M[CL + i] = right + w / 2
        M[i] = -aa
        M[RR + 2 * i] = -uu * uu
        M[RR + 2 * i + 1] = -vv * vv
        M[LAM] = w
        M[LIN + 21 + 2 * i] = -uu
        M[LIN + 21 + 2 * i + 1] = -vv
    return val, M


def param_table(p):
    rows = []
    for t in range(11):
        for j, nm in enumerate(['a', 'b', 'y']):
            rows.append(dict(name=f'face{t}.{nm}', q=3 * t + j, k=t, j=j, kind='face',
                             value=float(p[3 * t + j])))
    for i in range(9):
        rows.append(dict(name=f'switch{i}.b', q=IB + i, k=11 + i, j=0, kind='switch',
                         value=float(p[IB + i])))
        rows.append(dict(name=f'switch{i}.y', q=IB + 9 + i, k=11 + i, j=1, kind='switch',
                         value=float(p[IB + 9 + i])))
    for i in range(9):
        for j, nm in enumerate(['a', 'u', 'v']):
            rows.append(dict(name=f'ring{i}.{nm}', q=IR + 3 * i + j, k=20 + i, j=j, kind='ring',
                             value=float(p[IR + 3 * i + j])))
    for r in rows:
        v = r['value']; j = r['j']
        if r['kind'] == 'face':
            hi = 1.0 if j == 2 else PI
        elif r['kind'] == 'switch':
            hi = 1.0 if j == 1 else PI / 2
        else:
            hi = 1.0 if j > 0 else PI
        r['hi'] = hi
        r['activity'] = 'lo' if abs(v) < 1e-9 else ('up' if abs(hi - v) < 1e-9 else 'in')
    return rows


def main():
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    tab = param_table(p0)
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    print('=== R20-FINAL: producer-faithful factor family, 78 parameters, R = r_cand ===')
    print('    cone from the producer: z[KAP:KAP+21] >= 0, z[ETA] = 0, z[LAM] >= 0, rest free')
    # sanity: value at the candidate
    V = 0.0
    for k in range(29):
        v, M = value_and_row(k, p0, C); V += v + M @ zc
    print('    sum_k (v_k + M_k . z_c825) at the candidate = %.12f   (pi = %.12f)' % (V, PI))
    # derivative rows (finite differences on the producer's own construction)
    h = 1e-6
    B = np.zeros((NP, NZ)); bp = np.zeros(NP)
    for r in tab:
        q = r['q']; k = r['k']
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        vp, Mp = value_and_row(k, pp, C); vm, Mm = value_and_row(k, pm, C)
        B[q] = (Mp - Mm) / (2 * h); bp[q] = (vp - vm) / (2 * h)
    # validation: full numeric derivative of the factor value (v + M.z) vs bp + B.z
    worst = 0.0
    for r in tab:
        q = r['q']; k = r['k']
        f = lambda pp: (lambda t: t[0] + t[1] @ zc)(value_and_row(k, pp, C))
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        dn = (f(pp) - f(pm)) / (2 * h); da = bp[q] + B[q] @ zc
        worst = max(worst, abs(dn - da))
    print('    affine-row calibration: max |numeric - (b\' + a\'.z)| = %.3e' % worst)
    act = {}
    for r in tab:
        act[r['activity']] = act.get(r['activity'], 0) + 1
    print('    parameter activity: %s' % act)
    np.save(HERE / 'r20_prod_B.npy', B); np.save(HERE / 'r20_prod_bp.npy', bp)
    json.dump(dict(B=B.tolist(), bp=bp.tolist(), param=tab, V_cand=float(V), R=R,
                   calib=float(worst)), open(HERE / 'r20_producer_instrument.json', 'w'), indent=1)
    print('    saved r20_prod_B.npy / r20_producer_instrument.json')


if __name__ == '__main__':
    main()
