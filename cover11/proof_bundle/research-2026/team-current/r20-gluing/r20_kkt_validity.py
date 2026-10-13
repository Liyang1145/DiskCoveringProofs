"""R20-H: validity audit of the C825 z at the candidate's own radius, and the LP system.

Context correction (lead interface fix, recorded):  the earlier diagnostic ran the factor family
at R = 19/50 with the candidate's tuple, but the candidate's own covering radius is
r_cand = 0.3799838531198388 < 19/50, at which the R-disk cover is NOT tight (a strict cover
exists).  The sharp-area support can only be asked at R = r_cand.  The 121-column z of
`lead/q0_lower375_dual_0_4.json` is a dual at R = 3/8; the factor family at R = r_cand has
different radii copies and hence different active-set/KKT rows.
"""
import json, math
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
NZ = 121
R_CAND = 0.3799838531198388
OFF_FACE, OFF_BSW, OFF_RNG = 0, 33, 42
NP = 69


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
        p[OFF_FACE + 3 * t] = ang[t, 0]; p[OFF_FACE + 3 * t + 1] = ang[t, 1]
        p[OFF_FACE + 3 * t + 2] = yface[t]
    p[OFF_BSW:OFF_BSW + 9] = bsw
    for i in range(9):
        p[OFF_RNG + 3 * i] = a_r[i]; p[OFF_RNG + 3 * i + 1] = u[i]; p[OFF_RNG + 3 * i + 2] = v[i]
    return dict(p=p, R=R, faces=faces, edges=edges, adj=adj, ang=ang, bsw=bsw, yface=yface,
                ysw=ysw, alpha=a_r, u=u, v=v, rho=rho, cand_radius=o['candidate_radius'])


def const_of(z, R):
    return (PI * (z[:9].sum() + 2 * z[9:11].sum() + z[KAP:LAM].sum() - 2 * z[LAM] - 2 * z[ETA])
            + 2 * z[ETA] * math.asin(2 * R) - PI * z[CL:].sum())


class Factor:
    """signed ring/face/switch formula exactly as claim/clarify_q0_closure.py uses it, but
    cleaned up to the primal-side convention S_c and linear in z at a frozen tuple."""

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

    def lin(self, k, p):
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


def audit(R):
    C = load_candidate(R); F = Factor(C); p0 = C['p']
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    a = np.zeros(NZ); bl = 0.0
    for k in range(29):
        ak, bk = F.lin(k, p0); a += ak; bl += bk
    V = const_of(zc, R) + bl + a @ zc
    return C, F, p0, zc, V, a, bl


if __name__ == '__main__':
    for R in (3 / 8, 0.38, R_CAND):
        C, F, p0, zc, V, a, bl = audit(R)
        print('R = %.16f   V(z_c825 at candidate tuple) = %.15f   V-pi = %+.3e'
              % (R, V, V - PI))
    # local validity probe: move each parameter one at a time and look for V < pi
    R = R_CAND
    C, F, p0, zc, V0, a, bl = audit(R)
    def Vof(p):
        t = const_of(zc, R)
        for k in range(29):
            ak, bk = F.lin(k, p); t += bk + ak @ zc
        return t
    print('V0 =', V0)
    for q in range(NP):
        best = V0
        for s in (-1, 1):
            for h in (1e-6, 1e-5, 1e-4, 1e-3, 1e-2, 1e-1):
                p = p0.copy(); p[q] += s * h
                if p[q] < 0:
                    continue
                try:
                    v = Vof(p)
                except Exception:
                    continue
                if v < best:
                    best = v
        if best < V0 - 1e-12:
            print('   param %2d  dV = %+.6e' % (q, best - V0))
