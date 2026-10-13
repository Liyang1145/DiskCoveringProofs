"""R20-H: the 121-column x 69-parameter stationarity (KKT) system of the 29-factor family,
plus the hole-capacity LP (minimise the linearised dual value over the tangent cone).

Diagnostic only (no claim registered; lead kernels read-only; writes only in this directory).

CONSTRUCTION
  29 factors of the q0(6,7) span-4 family.  Factor k's value is f_k(pi_k ; z), LINEAR in z at
  fixed tuple pi_k.  The saved genuine candidate (`lead/q0_exact_closure_radius.json`,
  r = 0.3799838531198388) supplies the test tuple pi^* (69 free parameters).

  Rows   : B[q, :] = d f_k(pi^*; z) / d z   for the parameter q of factor k, MEASURED by
           finite differences of the factor's own formula (the envelope form of the max).
           For a row whose parameter sits on the closed domain boundary the correct condition is
           one-sided: the objective must not increase when the parameter moves inward, i.e.
           (d/dxi)(sum_c z_c coeff_c) = -B[q,:].z <= 0 for a lower end and >= 0 for an upper end.
  Columns: the 121 z of `lead/q0_lower375_dual_0_4.json`.

  The stationarity of the Lagrangian sum at pi^* is exactly
        B^T z = 0        (all 69 parameters interior at the candidate)
  and the tightness of the resulting bound at R = r* is
        const(z) + sum_k f_k(pi^*; z) = pi   i.e.   sum_c z_c A_c = pi,
  where A_c = (coefficient of z_c at pi^*) - (coefficient at the candidate tuple) = -B-constant.
  Since the linear forms are exact, that quantity is what the LP below minimises.

HOLE-CAPACITY LP:  minimise  -(const(z) + sum_k f_k(pi^*,z))  subject to the sign cone
  (validity of the assembled bound: z_c * residual_c >= 0 on the feasible set), the walk
  normalisation sum_c |z_c| <= 1 or z = 0, and the linearised tangent-cone constraints.
  A strictly positive minimum is an explicit Farkas-type witness that pi^* cannot be a
  simultaneous maximum with any z in the cone.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_assembly.py
"""
import json, math
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
NZ = 121
R_DUAL = 19 / 50
OFF_FACE, OFF_BSW, OFF_RNG = 0, 33, 42
NP = 69


# ------------------------------------------------------------------ primal data
def load_candidate():
    o = json.loads((LEAD / 'q0_exact_closure_radius.json').read_text(encoding='utf-8'))
    x0 = np.array(o['x0'], float)
    faces = o['faces']; edges = [tuple(e) for e in o['edges']]
    adj = {e: [(t, next(k for k in f if k not in e)) for t, f in enumerate(faces)
               if e[0] in f and e[1] in f] for e in edges}
    ang = x0[:33].reshape(11, 3); bsw = x0[33:42]
    rho = np.exp(x0[42:62] + x0[62])
    yface = rho[:11] / R_DUAL; ysw = rho[11:20] / R_DUAL
    y = ysw.copy(); u = np.roll(y, 1); v = y
    raw = np.zeros(9)
    for t, f in enumerate(faces):
        for k, i in enumerate(f):
            if i < 9:
                raw[i] += ang[t, k]
    a_r = PI - raw + np.roll(bsw, 1) + bsw
    p = np.zeros(NP)
    for t in range(11):
        p[OFF_FACE + 3 * t] = ang[t, 0]; p[OFF_FACE + 3 * t + 1] = ang[t, 1]
        p[OFF_FACE + 3 * t + 2] = yface[t]
    p[OFF_BSW:OFF_BSW + 9] = bsw
    for i in range(9):
        p[OFF_RNG + 3 * i] = a_r[i]; p[OFF_RNG + 3 * i + 1] = u[i]; p[OFF_RNG + 3 * i + 2] = v[i]
    return dict(p=p, R=R_DUAL, faces=faces, edges=edges, adj=adj, ang=ang, bsw=bsw,
                yface=yface, ysw=ysw, alpha=a_r, u=u, v=v, cand_radius=o['candidate_radius'])


def param_table(p):
    rows = []
    for t in range(11):
        rows += [(f'face{t}.a', 'face', t, 3 * t, p[OFF_FACE + 3 * t], 'lo'),
                 (f'face{t}.b', 'face', t, 3 * t + 1, p[OFF_FACE + 3 * t + 1], 'lo'),
                 (f'face{t}.y', 'face', t, 3 * t + 2, p[OFF_FACE + 3 * t + 2], 'hi')]
    for i in range(9):
        rows += [(f'switch{i}.b', 'switch', i, i, p[OFF_BSW + i], 'lo')]
    for i in range(9):
        rows += [(f'ring{i}.a', 'ring', i, 3 * i, p[OFF_RNG + 3 * i], 'lo'),
                 (f'ring{i}.u', 'ring', i, 3 * i + 1, p[OFF_RNG + 3 * i + 1], 'hi'),
                 (f'ring{i}.v', 'ring', i, 3 * i + 2, p[OFF_RNG + 3 * i + 2], 'hi')]
    out = []
    for name, kind, k, idx, val, end in rows:
        if end == 'lo':
            act = 'lo0' if val < 1e-9 else 'interior'
        else:
            act = 'hi1' if 1.0 - val < 1e-9 else 'interior'
        out.append(dict(name=name, kind=kind, k=k, idx=idx,
                        qi={'face': OFF_FACE, 'switch': OFF_BSW, 'ring': OFF_RNG}[kind] + idx,
                        val=val, activity=act, end=end))
    return out


# ------------------------------------------------------------------ factor formulas (primal side)
class Factors:
    def __init__(self, C):
        self.C = C; self.R = C['R']
        self.faces = C['faces']; self.edges = C['edges']; self.adj = C['adj']

    def tuple_of(self, p):
        ang = np.zeros((11, 3))
        for t in range(11):
            a = p[OFF_FACE + 3 * t]; b = p[OFF_FACE + 3 * t + 1]
            ang[t] = (a, b, PI - a - b)
        bsw = np.asarray(p[OFF_BSW:OFF_BSW + 9], float)
        rng = np.asarray(p[OFF_RNG:OFF_RNG + 27], float).reshape(9, 3)
        return ang, bsw, rng

    def linear_form(self, k, p):
        """(a_k, b_k): f_k(pi_k ; z) = b_k + a_k . z at tuple p."""
        faces, edges, adj, R = self.faces, self.edges, self.adj, self.R
        ang, bsw, rng = self.tuple_of(p)
        a = np.zeros(NZ); b = 0.0
        if k < 11:
            t = k; f = faces[t]; y = p[OFF_FACE + 3 * t + 2]
            for m, i in enumerate(f):
                e = tuple(sorted(j for j in f if j != i)); ei = edges.index(e)
                sgn = 1.0 if adj[e][0][0] == t else -1.0
                s = math.sin(ang[t, m])
                a[i] += -ang[t, m]; a[KAP + ei] += -ang[t, m]
                a[SIDE + ei] += sgn * y ** 2 * s ** 2
                a[LIN + ei] += sgn * y * s
            b += 2 * R * R * y ** 2 * math.prod(np.sin(ang[t]))
        elif k < 20:
            bi = k - 11; i, j = bi, (bi + 1) % 9
            e = tuple(sorted((i, j))); ei = edges.index(e)
            bb = bsw[bi]; y = rng[i, 2]
            a[CL + bi] += 2 * bb
            a[i] += bb; a[j] += bb; a[KAP + ei] += -bb
            a[SIDE + ei] += -y ** 2 * math.sin(bb) ** 2
            a[LIN + ei] += -y * math.sin(bb)
            a[RR + 2 * i + 1] += y ** 2
            a[RR + 2 * j] += rng[j, 1] ** 2
            a[LIN + 21 + 2 * i + 1] += y
            a[LIN + 21 + 2 * j] += rng[j, 1]
            b += R * R * y ** 2 * math.sin(2 * bb) / 2
        else:
            i = k - 20
            aa, uu, vv = rng[i]
            q = (uu - vv) ** 2 + 4 * uu * vv * math.sin(aa / 2) ** 2
            w = 2 * math.asin(min(1.0, R * math.sqrt(max(q, 0)) / 2))
            L = math.atan2(vv * math.sin(aa), uu - vv * math.cos(aa)); T = PI - aa - L
            a[CL + (i - 1) % 9] += L + w / 2
            a[CL + i] += T + w / 2
            a[i] += -aa
            a[RR + 2 * i] += -uu ** 2
            a[RR + 2 * i + 1] += -vv ** 2
            a[LAM] += w
            a[LIN + 21 + 2 * i] += -uu
            a[LIN + 21 + 2 * i + 1] += -vv
            b += R * R * uu * vv * math.sin(aa) / 2 + (w - math.sin(w)) / 2
        return a, b


def const_of(z, R):
    return (PI * (z[:9].sum() + 2 * z[9:11].sum() + z[KAP:LAM].sum() - 2 * z[LAM] - 2 * z[ETA])
            + 2 * z[ETA] * math.asin(2 * R) - PI * z[CL:].sum())


def main():
    C = load_candidate(); F = Factors(C)
    p0, R = C['p'], C['R']
    tab = param_table(p0)
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])

    # ---------- 0) LINEAR FORM IS EXACT: reproduce the lead kernel's per-factor upper at pi^*
    from r20_factor_probe import Model
    m = Model('q0_lower375_dual_0_4.json', R, 'z'); m.z = zc
    dev = []
    for k in range(29):
        a, b = F.linear_form(k, p0); mine = b + a @ zc
        if k < 11:
            t = k; code = m.face_val(t, p0[OFF_FACE + 3 * t], p0[OFF_FACE + 3 * t + 1])[0]
        elif k < 20:
            bi = k - 11; code = m.switch_val(bi, p0[OFF_BSW + bi])[0]
        else:
            i = k - 20
            code = m.ring_val(i, p0[OFF_RNG + 3 * i], p0[OFF_RNG + 3 * i + 1], p0[OFF_RNG + 3 * i + 2])
        dev.append(abs(code - mine))
    print('[0] factor-formula calibration vs lead kernel F_k(pi^*;z) at the candidate tuple:'
          ' max dev = %.2e (mean %.2e)' % (max(dev), float(np.mean(dev))))
    V_cand = const_of(zc, R) + sum(F.linear_form(k, p0)[0] @ zc + F.linear_form(k, p0)[1]
                                   for k in range(29))
    print('[0] V(z_c825) at the CANDIDATE tuple = %.15f   (pi = %.15f, V-pi = %+.3e)'
          % (V_cand, PI, V_cand - PI))

    # ---------- 1) B: d f_k / d z for every parameter row (measured on the factor's own formula)
    B = np.zeros((NP, NZ))
    h = 1e-7
    for r in tab:
        k = r['k']; q = r['qi']
        a0, b0 = F.linear_form(k, p0)
        ap = np.zeros(NZ); am = np.zeros(NZ)
        pp = p0.copy(); pm = p0.copy()
        if r['end'] == 'lo' and p0[q] < 1e-9:      # one-sided (boundary)
            step = h
            pp[q] = p0[q] + step
            ap, _ = F.linear_form(k, pp)
            B[q] = (ap - a0) / step
        elif r['end'] == 'hi' and 1.0 - p0[q] < 1e-9:
            step = -h
            pp[q] = p0[q] + step
            ap, _ = F.linear_form(k, pp)
            B[q] = (ap - a0) / step
        else:
            pp[q] = p0[q] + h; pm[q] = p0[q] - h
            ap, _ = F.linear_form(k, pp); am, _ = F.linear_form(k, pm)
            B[q] = (ap - am) / (2 * h)
        r['Bnorm'] = float(np.linalg.norm(B[q]))

    # ---------- 2) stationarity value of the saved z and of the null-space question
    Bz = B @ zc
    print('[2] |B^T z_c825|_inf = %.6e  at row %s' % (np.abs(Bz).max(),
                                                       tab[int(np.argmax(np.abs(Bz)))]['name']))
    # what the LP would see: minimise -(const + sum f_k(pi^*,z)) = pi - V(z) over z in the cone
    # V(z) is linear in z: V = const(z) + sum_k (b_k + a_k . z) at pi^*
    A_lin = np.zeros(NZ); b_lin = 0.0
    for k in range(29):
        a, b = F.linear_form(k, p0)
        A_lin += a; b_lin += b
    # const(z) is linear too:
    cvec = np.zeros(NZ)
    cvec[:9] = PI; cvec[9:11] = 2 * PI; cvec[KAP:LAM] = PI; cvec[LAM] = -2 * PI
    cvec[ETA] = -2 * PI + 2 * math.asin(2 * R); cvec[CL:] = -PI
    coeffV = cvec + A_lin
    print('[2] V(z) = %.12f + z . coeffV ;  coeffV . z_c825 = %.12f' % (b_lin, coeffV @ zc))
    np.save(HERE / 'r20_kkt_B.npy', B)
    json.dump(dict(param_names=[r['name'] for r in tab], activity=[r['activity'] for r in tab],
                   val=[r['val'] for r in tab], Bz=Bz.tolist(),
                   coeffV=coeffV.tolist(), b_lin=b_lin, R=R_DUAL,
                   z_c825=zc.tolist(), V_cand=V_cand),
              open(HERE / 'r20_kkt_assembly.json', 'w'), indent=1)
    print('[2] saved r20_kkt_B.npy, r20_kkt_assembly.json')


if __name__ == '__main__':
    main()
