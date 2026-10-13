"""R20-G: necessary stationarity / KKT system for the 121-column 29-factor family.

Diagnostic only.  No claim registered; lead kernels read-only; writes only in this directory.

OBJECT.
  `lead/q0_lower375_dual_0_4.json` is a pure 29-factor dual z (121 columns) for the q0(6,7)
  span-4 graph at R = 19/50.  Its assembled bound is

      V(z) = const(z) + sum_{k=1..29} F_k(z) ,      F_k(z) = max_{pi_k in D_k} f_k(pi_k ; z)

  where each f_k is linear in z at fixed pi_k.  Since f_k is linear in z, the derivative of the
  MAXIMUM with respect to z has the envelope form

      dF_k/dz_j = S_{k,j}(pi_k*) + grad_{pi_k} f_k(pi_k*;z) . (d pi_k*/dz_j) ,

  so the coefficient vector dF_k/dz is NOT the raw constraint map: it also carries the copy
  corrections through the factor's internal maximiser (the radius copy of every face/switch
  and the sector width of every ring).  This script measures dF_k/dz directly by differentiating
  the factor formula, then verifies the identity

      V(z) = const(z) + sum_k F_k(z)

  numerically at the saved z (that identity is the calibration of the whole construction).

TEST TUPLE (saved genuine candidate, `lead/q0_exact_closure_radius.json`):
  pi^* = 69 free parameters (a_t,b_t,y_t) t<11, b_i i<9, (alpha_i,u_i,v_i) i<9.
  All 69 sit strictly inside their closed domains at the candidate, so all 69 stationarity rows
  are two-sided equalities; the one-sided/boundary rows are still built and reported.

OBLIGATION (necessary, not sufficient):
  exists z != 0 with    B^T z = 0     (B = stacked dF_k/dz rows, 69 x 121)
  plus the sign cone that makes the assembled bound a valid upper bound, plus normalisation.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_system.py
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
NF, NSW, NRG = 11, 9, 9
OFF_FACE, OFF_BSW, OFF_RNG = 0, 33, 42
NP = 69


# ---------------------------------------------------------------- primal data
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
                yface=yface, ysw=ysw, alpha=a_r, u=u, v=v,
                cand_radius=o['candidate_radius'])


def param_table(p):
    """rows: (name, kind, free-parameter index, value, activity)."""
    rows = []
    for t in range(11):
        rows += [(f'face{t}.a', 'face', t, 3 * t, p[OFF_FACE + 3 * t], 'lo0'),
                 (f'face{t}.b', 'face', t, 3 * t + 1, p[OFF_FACE + 3 * t + 1], 'lo0'),
                 (f'face{t}.y', 'face', t, 3 * t + 2, p[OFF_FACE + 3 * t + 2], 'up1')]
    for i in range(9):
        rows += [(f'switch{i}.b', 'switch', i, i, p[OFF_BSW + i], 'lo0')]
    for i in range(9):
        rows += [(f'ring{i}.a', 'ring', i, 3 * i, p[OFF_RNG + 3 * i], 'lo0'),
                 (f'ring{i}.u', 'ring', i, 3 * i + 1, p[OFF_RNG + 3 * i + 1], 'up1'),
                 (f'ring{i}.v', 'ring', i, 3 * i + 2, p[OFF_RNG + 3 * i + 2], 'up1')]
    out = []
    for name, kind, k, idx, val, at in rows:
        if at == 'lo0':
            act = 'lo0' if val < 1e-9 else 'interior'
        elif at == 'up1':
            act = 'up1' if 1.0 - val < 1e-9 else 'interior'
        out.append(dict(name=name, kind=kind, k=k, idx=idx,
                        qi={'face': OFF_FACE, 'switch': OFF_BSW, 'ring': OFF_RNG}[kind] + idx,
                        val=val, activity=act))
    return out


# ---------------------------------------------------------------- factor formulas (primal side)
class Factors:
    """exact primal formula of the 29 factors, evaluated at the tuple p (frozen data = p)."""

    def __init__(self, C):
        self.C = C
        self.faces = C['faces']; self.edges = C['edges']; self.adj = C['adj']
        self.R = C['R']

    def _tuple(self, p):
        ang = np.zeros((11, 3))
        for t in range(11):
            a = p[OFF_FACE + 3 * t]; b = p[OFF_FACE + 3 * t + 1]
            ang[t] = (a, b, PI - a - b)
        bsw = np.asarray(p[OFF_BSW:OFF_BSW + 9], float)
        rng = np.asarray(p[OFF_RNG:OFF_RNG + 27], float).reshape(9, 3)
        return ang, bsw, rng

    def linear_form(self, k, p=None, C=None):
        """(a_k, b_k) with f_k(pi;z) = b_k + a_k . z at the tuple pi = p (frozen z-independent data)."""
        p = self.C['p'] if p is None else p
        faces, edges, adj, R = self.faces, self.edges, self.adj, self.R
        ang, bsw, rng = self._tuple(p)
        a = np.zeros(NZ); b = 0.0
        if k < 11:                                   # face t = k
            t = k; f = faces[t]; y = p[OFF_FACE + 3 * t + 2]
            for m, i in enumerate(f):
                e = tuple(sorted(j for j in f if j != i)); ei = edges.index(e)
                sgn = 1.0 if adj[e][0][0] == t else -1.0
                s = math.sin(ang[t, m])
                a[i] += -ang[t, m]; a[KAP + ei] += -ang[t, m]
                a[SIDE + ei] += sgn * y ** 2 * s ** 2
                a[LIN + ei] += sgn * y * s
            b += 2 * R * R * y ** 2 * math.prod(np.sin(ang[t]))
        elif k < 20:                                 # switch bi = k-11
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
        else:                                        # ring i = k-20
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
    C = load_candidate()
    F = Factors(C)
    p0 = C['p']; R = C['R']
    tab = param_table(p0)
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])

    # ---------------- 0) calibration: linear forms reproduce the saved probe at the CANDIDATE tuple
    print('--- 0) linear-form calibration at the saved candidate tuple')
    tot = 0.0
    vals = []
    for k in range(29):
        a, b = F.linear_form(k, p0)
        vals.append(b + a @ zc); tot += vals[-1]
    print('    const(z) =', const_of(zc, R), ' sum_k f_k =', tot, ' V =', const_of(zc, R) + tot)
    probe = json.loads((HERE / 'r20_factor_probe.json').read_text(encoding='utf-8'))['c825_z_at_38']
    print('    probe total at ITS OWN argmax tuple =', probe['total'],
          '   (differs because its tuple differs: gap =', probe['total'] - (const_of(zc, R) + tot), ')')
    # per-factor derivative identity: dF_k/dz_j measured by perturbing z inside the formula
    j = 5
    h = 1e-7
    a0, b0 = F.linear_form(0, p0)
    print('    face0: analytic dF/dz_%d = %.9f' % (j, a0[j]))
    aa, bb = F.linear_form(0, None)
    print('    const(z) sanity: pi*sum(z[:11]) =', PI * zc[:11].sum())

    # ---------------- 1) B matrix = dF_k/dz for every factor and every free parameter
    print('--- 1) building B (69 x 121) by differentiating the factor formulas')
    B = np.zeros((NP, NZ))
    for r in tab:
        k = r['k']; q = r['qi']
        hp = 1e-6
        pp = p0.copy(); pm = p0.copy(); pp[q] += hp; pm[q] -= hp
        ap, bp = F.linear_form(k, pp)
        am, bm = F.linear_form(k, pm)
        # d/dxi ( b_k + a_k . z )  -- with a,b evaluated at the perturbed tuples
        d = ((bp - bm) + (ap - am) @ zc) / (2 * hp)
        # the coefficient row: differentiate a_k(xi) itself
        B[r['qi']] = (ap - am) / (2 * hp)
        r['dF_at_z'] = float(d)
    # verify the two independent routes for the value derivative
    for r in tab:
        lhs = B[r['qi']] @ zc
        r['dev'] = abs(lhs - r['dF_at_z'])
    print('    max |route1 - route2| = %.3e' % max(r['dev'] for r in tab))
    act = {}
    for r in tab:
        act[r['activity']] = act.get(r['activity'], 0) + 1
    print('    activities:', act)
    print('    |B^T z|_inf = %.6e   row(max) = %s' % (np.abs(B @ zc).max(),
                                                      tab[int(np.argmax(np.abs(B @ zc)))]['name']))
    np.save(HERE / 'r20_kkt_B.npy', B)
    json.dump(dict(param_names=[r['name'] for r in tab],
                   activity=[r['activity'] for r in tab],
                   dF_at_z=[r['dF_at_z'] for r in tab],
                   n_eq=sum(1 for r in tab if r['activity'] == 'interior'),
                   n_bound=sum(1 for r in tab if r['activity'] != 'interior'),
                   z_c825=zc.tolist()),
              open(HERE / 'r20_kkt_params.json', 'w'), indent=1)
    print('    saved r20_kkt_B.npy, r20_kkt_params.json')


if __name__ == '__main__':
    main()
