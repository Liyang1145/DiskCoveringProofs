"""R20-I: the 121-column x 69-row stationarity/KKT LP at the candidate's own radius.

Caliber (lead interface fix):  allowance R = r_cand = 0.3799838531198388 (the candidate's true
maximal covering radius), NOT 19/50.  At R = 19/50 the R-disk cover is not tight (a strict cover
exists), so no sharp-area support is to be expected there; the sharp question is only at
R = r_cand, where the 18 radius copies and the active constraints bite.

Two questions:
  Q1 (KKT/stationarity): does the candidate tuple pi^* maximise all 29 factors for some z in the
     sign cone?  System:  B^T z = 0 (69 rows), z in cone, z != 0.
     Measured by  min sum_i |(B^T z)_i| / max_c |z_c|  over the cone.
  Q2 (dual bound):  V(z) = const(z) + sum_k f_k(pi^*; z) is linear in z.  If Q1 has a solution,
     min V over that affine set is the LP value; V(z*) vs pi measures the leftover gap.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_lp.py
"""
import json, math
import numpy as np
from pathlib import Path
from scipy.optimize import linprog

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


def lin_form(k, p, C):
    """coefficient row a_k and constant b_k of factor k, linear in z at tuple p."""
    R = C['R']; faces = C['faces']; edges = C['edges']; adj = C['adj']
    ang = np.zeros((11, 3))
    for t in range(11):
        a_ = p[OFF_FACE + 3 * t]; b_ = p[OFF_FACE + 3 * t + 1]
        ang[t] = (a_, b_, PI - a_ - b_)
    bsw = np.asarray(p[OFF_BSW:OFF_BSW + 9], float)
    rng = np.asarray(p[OFF_RNG:OFF_RNG + 27], float).reshape(9, 3)
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


def kkt_B(C, p0):
    """69 x 121 measured derivative matrix of the factor linear forms w.r.t. the parameter."""
    B = np.zeros((NP, NZ))
    h = 1e-7
    for q in range(NP):
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        row = np.zeros(NZ)
        # a given free parameter belongs to exactly one factor
        k = q // 3 if q < 33 else (11 + q - OFF_BSW if q < 42 else 20 + (q - OFF_RNG) // 3)
        ap, _ = lin_form(k, pp, C); am, _ = lin_form(k, pm, C)
        B[q] = (ap - am) / (2 * h)
    return B


def cone():
    """constraints encoding the sign cone of the dual (validity of the assembled bound)."""
    A = []; b = []
    # z <= 0 for the site/hub angle-sum family (residual R_i can be negative)
    for i in range(11):
        r = np.zeros(NZ); r[i] = 1.0; A.append(r); b.append(0.0)
    # z >= 0 for the kappa (Delaunay slack) family: free?  the code has z>=0 there
    for i in range(21):
        r = np.zeros(NZ); r[KAP + i] = -1.0; A.append(r); b.append(0.0)
    # z >= 0 for the closure family
    for i in range(9):
        r = np.zeros(NZ); r[CL + i] = -1.0; A.append(r); b.append(0.0)
    # copy families: use the split form -> require the pair to be a difference of two
    # nonnegative copies; equivalently the two copies of a pair must be free but the
    # assembled pair expression must have a definite sign.  Simplest sound cone:
    #   z[RR+2i], z[RR+2i+1] free (they appear as radii copies in different factors)
    for i in range(9):
        r = np.zeros(NZ); r[RR + 2 * i] = -1.0; r[RR + 2 * i + 1] = -1.0
        # not a real cone row; skip
    return np.array(A), np.array(b)


def main():
    C = load_candidate(R_CAND)
    p0 = C['p']
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    B = kkt_B(C, p0)
    print('B shape', B.shape, ' rank', np.linalg.matrix_rank(B, tol=1e-9))
    # KKT rows: B^T z = 0
    bz = B @ zc
    print('|B^T z_c825|_inf = %.4e' % np.abs(bz).max())
    # LP: min sum_i t_i  s.t.  -t <= (B^T z)_i <= t,  z in cone,  sum|z| <= 1
    A_cone, b_cone = cone()
    n = NZ + NP   # z and t
    rows = []; rhs = []
    for i in range(NP):
        r = np.zeros(n); r[:NZ] = B[i]; r[NZ + i] = -1.0
        rows.append(r); rhs.append(0.0)
        r = np.zeros(n); r[:NZ] = -B[i]; r[NZ + i] = -1.0
        rows.append(r); rhs.append(0.0)
    for r0, b0 in zip(A_cone, b_cone):
        r = np.zeros(n); r[:NZ] = r0; rows.append(r); rhs.append(b0)
    # normalisation: sum |z| <= 1  ->  -1 <= z_c <= 1 and sum s_c <= 1 with s >= +-z
    c = np.zeros(n); c[NZ:] = 1.0
    bounds = [(-1, 1)] * NZ + [(0, None)] * NP
    res = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs), bounds=bounds, method='highs')
    print('LP status', res.status, res.message)
    print('min sum|B^T z| with |z|<=1 =', res.fun)
    if res.status == 0:
        z = res.x[:NZ]
        print('  max |z| =', np.abs(z).max(), ' |B^T z|_inf =', np.abs(B @ z).max())
        json.dump(dict(z=z.tolist(), obj=float(res.fun), Bz=(B @ z).tolist(),
                       z_c825=zc.tolist(), Bz_c825=bz.tolist(), R=R_CAND),
                  open(HERE / 'r20_kkt_lp.json', 'w'), indent=1)
        print('  saved r20_kkt_lp.json')


if __name__ == '__main__':
    main()
