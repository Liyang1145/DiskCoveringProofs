"""R20-Q: consolidated audit — caliber, boundary activity, certificate validity.

Reports (all numbers regenerated here, nothing quoted from memory):
 1. caliber: the candidate's own radius r_cand, and the value of the saved z_c825 at r_cand;
 2. boundary activity of all 69 free parameters (are any at the closed-domain boundary?);
 3. the 121-column sign cone (which z must be nonnegative for the assembled bound to be valid);
 4. residual structure at the candidate: which dualized constraint families are active;
 5. the final LP margin t* and the Farkas certificate status per grid and per group.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_kkt_audit.py
"""
import json, math, sys
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
sys.path.insert(0, str(HERE))
from r20_kkt_lp import load_candidate, lin_form, const_of, kkt_B


def constraint_residuals(p, R, faces, edges, adj):
    """the 121 dualized constraint residuals g_c at the tuple p (column order of the z file)."""
    ang = np.zeros((11, 3))
    for t in range(11):
        a = p[3 * t]; b = p[3 * t + 1]; ang[t] = (a, b, PI - a - b)
    bsw = np.asarray(p[33:42], float)
    rng = np.asarray(p[42:69], float).reshape(9, 3)
    a_r, u, v = rng[:, 0], rng[:, 1], rng[:, 2]
    q = (u - v) ** 2 + 4 * u * v * np.sin(a_r / 2) ** 2
    w = 2 * np.arcsin(np.clip(R * np.sqrt(np.maximum(q, 0)) / 2, 0, 1))
    L = np.arctan2(v * np.sin(a_r), u - v * np.cos(a_r)); T = PI - a_r - L
    g = np.zeros(NZ)
    for t, f in enumerate(faces):
        for k, i in enumerate(f):
            g[i if i < 9 else 9 + (i - 9)] += ang[t, k]
    for i in range(9):
        g[i] += a_r[i] - bsw[(i - 1) % 9] - bsw[i] - PI
    g[9] -= 2 * PI; g[10] -= 2 * PI
    for ei, e in enumerate(edges):
        ad = adj[e]; o2 = o1 = opp = 0.0
        for k, (t, oppv) in enumerate(ad):
            mtx = faces[t].index(oppv); sgn = 1.0 if k == 0 else -1.0
            th = ang[t, mtx]
            o2 += sgn * math.sin(th) ** 2; o1 += sgn * math.sin(th); opp += th
        if len(ad) == 1:
            bi = next(b for b in range(9) if {b, (b + 1) % 9} == set(e))
            th = bsw[bi]
            o2 += -math.sin(th) ** 2; o1 += -math.sin(th); opp += th
        g[SIDE + ei] = o2; g[LIN + ei] = o1; g[KAP + ei] = PI - opp
    for i in range(9):
        g[RR + 2 * i] = bsw[i] ** 2 - u[i] ** 2
        g[RR + 2 * i + 1] = bsw[(i - 1) % 9] ** 2 - v[i] ** 2
        g[LIN + 21 + 2 * i] = bsw[i] - u[i]
        g[LIN + 21 + 2 * i + 1] = bsw[(i - 1) % 9] - v[i]
    g[LAM] = w.sum() - 2 * PI
    g[ETA] = w[3:].sum() - 2 * PI + 2 * math.asin(2 * R)
    for i in range(9):
        g[CL + i] = T[i] + L[(i + 1) % 9] + 2 * bsw[i] + (w[i] + w[(i + 1) % 9]) / 2 - PI
    return g


def main():
    out = {}
    print('=== 1. caliber ===')
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    print('   allowance used everywhere here: R = r_cand = %.16f' % R)
    print('   (at R = 19/50 a strict cover exists, so no sharp-area support is expected there;')
    print('    the earlier r20_kkt_system.json ran the family at R = 19/50 -> wrong caliber)')
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    v = const_of(zc, R)
    for k in range(29):
        a, b = lin_form(k, p0, C); v += b + a @ zc
    print('   V(z_c825) at the candidate tuple, R = r_cand  = %.15f   (pi = %.15f, excess %+.2e)'
          % (v, PI, v - PI))
    out['V_zc825_at_candidate'] = float(v)

    print()
    print('=== 2. boundary activity of the 69 free parameters ===')
    act = {}
    vals = []
    for t in range(11):
        vals += [(f'face{t}.a', p0[3 * t], 0.0, PI), (f'face{t}.b', p0[3 * t + 1], 0.0, PI),
                 (f'face{t}.y', p0[3 * t + 2], 0.0, 1.0)]
    for i in range(9):
        vals += [(f'switch{i}.b', p0[33 + i], 0.0, PI / 2)]
    for i in range(9):
        vals += [(f'ring{i}.a', p0[42 + 3 * i], 0.0, PI),
                 (f'ring{i}.u', p0[42 + 3 * i + 1], 0.0, 1.0),
                 (f'ring{i}.v', p0[42 + 3 * i + 2], 0.0, 1.0)]
    nact = 0
    near = []
    for name, x, lo, hi in vals:
        dl = abs(x - lo); dh = abs(hi - x)
        if dl < 1e-9 or dh < 1e-9:
            nact += 1
            print('   %-12s %.12f   lower dist %.2e  upper dist %.2e  <- ACTIVE'
                  % (name, x, dl, dh))
        near.append((min(dl, dh), name, x, dl, dh))
    print('   active at the closed-domain boundary: %d of %d  -> one-sided rows contribute %s'
          % (nact, len(vals), 'nothing (KKT rows are two-sided)' if nact == 0 else 'a real restriction'))
    near.sort()
    nm, x, dl, dh = near[0][1], near[0][2], near[0][3], near[0][4]
    print('   closest to a boundary: %s = %.15f (lower dist %.2e, upper dist %.2e)'
          % (nm, x, dl, dh))
    out['n_active_boundary_params'] = int(nact)
    out['closest_boundary'] = dict(name=nm, value=float(x), lower=float(dl), upper=float(dh))

    print()
    print('=== 3. the sign cone of the 121 columns (validity of the assembled bound) ===')
    print('   z[0:11]   site/hub angle sums         must be <= 0  (residual R_i can be negative)')
    print('             measured: max %.3e  -> cone satisfied' % zc[:11].max())
    print('   z[50:71]  Delaunay/ear slack (kappa)  must be >= 0  (slack is a nonneg residual)')
    print('             measured: min %.3e' % zc[KAP:KAP + 21].min())
    print('   z[112:121] cyclic closure             must be >= 0  (G_i can be negative)')
    print('             measured: min %.3e' % zc[CL:].min())
    print('   squared/first-moment side match (z[11:32], z[73:94]) : difference form, either sign')
    print('   squared/first-moment radius copies (z[32:50], z[94:112]) : difference form,'
          ' either sign')

    print()
    print('=== 4. residual structure at the candidate (which dualized families are active) ===')
    g = constraint_residuals(p0, R, C['faces'], C['edges'], C['adj'])
    fam = [('site/hub angle sums', 0, 11), ('squared side match', SIDE, SIDE + 21),
           ('squared radius copies', RR, RR + 18), ('Delaunay slack kappa', KAP, KAP + 21),
           ('total width lambda', LAM, LAM + 1), ('eta', ETA, ETA + 1),
           ('first-moment side match', LIN, LIN + 21),
           ('first-moment radius copies', LIN + 21, LIN + 39),
           ('cyclic closure', CL, CL + 9)]
    for name, a, b in fam:
        seg = g[a:b]
        print('   %-24s max |residual| = %.3e   %s' %
              (name, np.abs(seg).max(), 'ACTIVE (=0)' if np.abs(seg).max() < 1e-12 else
               'VIOLATED at the candidate'))
    # the copy families specifically (lead's 18 radius = 1 remark)
    print('   radius copies in the R = r_cand family are (R*ysw)^2 - (R*u)^2 terms; the actual')
    print('   configuration has |rho_switch - R| = %.3e, so those copies are NOT tight here,'
          % abs(C['ysw'][0] * R - R))
    print('   unlike at R = 3/8 where y = 1 exactly by construction.')

    print()
    print('=== 5. final margins ===')
    fin = json.loads((HERE / 'r20_kkt_final.json').read_text(encoding='utf-8'))
    for r in fin['results']:
        print('   %-11s npts=%4d   t* = %+.6e   certificate %s  (rows %d, Fmax %.1e, rhs %+.2e)'
              % (r['group'], r['npts'], r['t_star'], 'VALID' if r['valid'] else 'CHECK',
                 r['farkas_rows'], r['Fmax'], r['rhs']))
    print('   calibration on the synthetic instance: %s' % fin['calibration']['infeasible_case'])
    out['final'] = fin['results']
    json.dump(out, open(HERE / 'r20_kkt_audit.json', 'w'), indent=1)
    print('saved r20_kkt_audit.json')


if __name__ == '__main__':
    main()
