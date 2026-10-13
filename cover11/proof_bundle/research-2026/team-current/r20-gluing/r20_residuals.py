"""R20-B: residual restoration at a saved 29-factor relaxation solution.

Given the saved dual z (C825 span-4 q0(6,7) coefficients) and the per-factor argmax
points from r20_factor_probe.py, assemble:

  D(z;x*) = const + sum_k F_k(z;x*_k)                                   (factor side)
          = area_atoms(x*) + sum_c z_c * g_c(x*)                        (constraint side)

where g_c are the residuals of the constraints dualized by z:
  site angle sums      R_i      = sum_{faces at i} theta + alpha_i - b_{i-1} - b_i - pi
  hub angle sums       R_9,R_10 = sum_{faces at hub} theta - 2 pi
  Delaunay slack       slack_e  = pi - (opposite site angles [+ switch b])
  squared side match   match2_e = sum_adj sgn * y_t^2 sin^2(theta)
  first-moment match   match1_e = sum_adj sgn * y_t sin(theta)
  squared radius copy  copy2    = y_sw^2 - u^2 (or v^2)  [left/right]
  first radius copy    copy1    = y_sw   - u   (or v)
  cyclic closure       G_i      = T_i + L_{i+1} + 2 b_i + (w_i + w_{i+1})/2 - pi
  total width          W        = sum_i w_i - 2 pi
  eta atom             Eta      = sum_{i>=3} w_i - 2 pi + 2 asin(2R)

Diagnostic only; no claim; writes only in this directory.
"""
import json, math
import numpy as np
from pathlib import Path
from r20_factor_probe import Model, PI, SIDE, RR, KAP, LAM, ETA, LIN, CL, maximize_all

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'


def assemble(m, fac):
    """Recompute per-factor values/argmax y and collect primal copies."""
    F = np.zeros(29)
    yface = np.zeros(11); ysw = np.zeros(9)
    ang = np.zeros((11, 3)); bsw = np.zeros(9); rng = np.zeros((9, 3))  # alpha,u,v
    for r in fac:
        k = r['idx']
        if r['kind'] == 'face':
            v, y = m.face_val(r['idx'], r['a'], r['b'])
            a, b = r['a'], r['b']; ang[r['idx']] = (a, b, PI - a - b); yface[r['idx']] = y
        elif r['kind'] == 'switch':
            v, y = m.switch_val(r['idx'] - 11, r['b'])
            bsw[r['idx'] - 11] = r['b']; ysw[r['idx'] - 11] = y
        else:
            v = r['val']; rng[r['idx'] - 20] = (r['a'], r['u'], r['v'])
        F[k] = v
    return F, ang, yface, bsw, ysw, rng


def residuals(m, ang, yface, bsw, ysw, rng):
    z = m.z
    G = dict()
    # sector geometry
    alpha, u, v = rng[:, 0], rng[:, 1], rng[:, 2]
    q = (u - v) ** 2 + 4 * u * v * np.sin(alpha / 2) ** 2
    w = 2 * np.arcsin(np.clip(m.R * np.sqrt(q) / 2, 0, 1))
    L = np.arctan2(v * np.sin(alpha), u - v * np.cos(alpha))
    T = PI - alpha - L
    # 1) angle sums
    Rsite = np.zeros(9); Rhub = np.zeros(2)
    for i in range(9):
        Rsite[i] = -PI
    for t, f in enumerate(m.faces):
        for k, i in enumerate(f):
            if i < 9: Rsite[i] += ang[t, k]
            else: Rhub[i - 9] += ang[t, k]
    Rsite += alpha - np.roll(bsw, 1) - bsw
    Rhub -= 2 * PI
    # 2) edge residuals
    slack = np.zeros(21); m2 = np.zeros(21); m1 = np.zeros(21); ekind = []
    for ei, e in enumerate(m.edges):
        ad = m.adj[e]
        terms2 = []; terms1 = []; opp = []
        for k, (t, oppv) in enumerate(ad):
            mtx = m.faces[t].index(oppv); sgn = 1.0 if k == 0 else -1.0
            yy = yface[t]
            terms2.append(sgn * yy ** 2 * math.sin(ang[t, mtx]) ** 2)
            terms1.append(sgn * yy * math.sin(ang[t, mtx]))
            opp.append(ang[t, mtx])
        if len(ad) == 1:
            bi = next(b for b in range(9) if {b, (b + 1) % 9} == set(e))
            terms2.append(-ysw[bi] ** 2 * math.sin(bsw[bi]) ** 2)
            terms1.append(-ysw[bi] * math.sin(bsw[bi]))
            opp.append(bsw[bi]); ekind.append('switch')
        else:
            ekind.append('face')
        slack[ei] = PI - sum(opp); m2[ei] = sum(terms2); m1[ei] = sum(terms1)
    # 3) radius copies
    c2L = ysw[np.arange(9) - 1] ** 2 - u ** 2
    c2R = ysw ** 2 - v ** 2
    c1L = ysw[np.arange(9) - 1] - u
    c1R = ysw - v
    # 4) closure, width
    Gc = T + np.roll(L, -1) + 2 * bsw + (w + np.roll(w, -1)) / 2 - PI
    W = w.sum() - 2 * PI
    Eta = w[3:].sum() - 2 * PI + 2 * math.asin(2 * m.R)
    G.update(site=Rsite, hub=Rhub, slack=slack, m2=m2, m1=m1, c2L=c2L, c2R=c2R,
             c1L=c1L, c1R=c1R, closure=Gc, W=W, Eta=Eta, alpha=alpha, u=u, v=v,
             w=w, L=L, T=T, b=bsw, ysw=ysw, yface=yface, ekind=ekind)
    return G


def weighted(m, G):
    z = m.z
    out = {}
    out['site'] = z[:9] @ G['site'] + z[9:11] @ G['hub']
    out['slack'] = z[KAP:KAP + 21] @ G['slack']
    out['m2'] = z[SIDE:SIDE + 21] @ G['m2']
    out['m1'] = z[LIN:LIN + 21] @ G['m1']
    out['copy2'] = z[RR:RR + 18:2] @ G['c2L'] + z[RR + 1:RR + 18:2] @ G['c2R']
    out['copy1'] = z[94:112:2] @ G['c1L'] + z[95:112:2] @ G['c1R']
    out['closure'] = z[CL:CL + 9] @ G['closure']
    out['width'] = z[LAM] * G['W'] + z[ETA] * G['Eta']
    return out


def area_atoms(m, ang, yface, bsw, ysw, rng):
    tot = 0.0
    for t in range(11):
        p = np.prod(np.sin(ang[t])); tot += 2 * m.R2 * yface[t] ** 2 * p
    for i in range(9):
        tot += m.R2 * ysw[i] ** 2 * math.sin(2 * bsw[i]) / 2
    alpha, u, v = rng[:, 0], rng[:, 1], rng[:, 2]
    q = (u - v) ** 2 + 4 * u * v * np.sin(alpha / 2) ** 2
    w = 2 * np.arcsin(np.clip(m.R * np.sqrt(q) / 2, 0, 1))
    tot += float(np.sum(m.R2 * u * v * np.sin(alpha) / 2 + (w - np.sin(w)) / 2))
    return tot


def run(tag, zfile, R, key='z'):
    m = Model(zfile, R, key)
    fac = maximize_all(m, tag)
    F, ang, yface, bsw, ysw, rng = assemble(m, fac)
    D_fac = m.const + F.sum()
    G = residuals(m, ang, yface, bsw, ysw, rng)
    Wc = weighted(m, G)
    A = area_atoms(m, ang, yface, bsw, ysw, rng)
    D_con = A + sum(Wc.values())
    print(f'[{tag}] D_factors={D_fac:.12f}  D_constraints={D_con:.12f}  id_err={D_con - D_fac:+.3e}')
    print(f'[{tag}] area_atoms={A:.9f}  (pi={PI:.9f}, area-pi={A - PI:+.6f})')
    for k, val in sorted(Wc.items(), key=lambda kv: -abs(kv[1])):
        res = {'site': np.abs(np.r_[G['site'], G['hub']]),
               'slack': np.abs(G['slack']), 'm2': np.abs(G['m2']), 'm1': np.abs(G['m1']),
               'copy2': np.abs(np.r_[G['c2L'], G['c2R']]), 'copy1': np.abs(np.r_[G['c1L'], G['c1R']]),
               'closure': np.abs(G['closure']), 'width': np.array([abs(G['W'])])}[k]
        print(f'   {k:8s} weighted={val:+.8f}  max|res|={res.max():.6f}  mean|res|={res.mean():.6f}')
    print(f'[{tag}] sum|z*g| (signed) = {sum(Wc.values()):+.8f};  V-pi = {D_fac - PI:+.8f}')
    # position readout
    print(f'[{tag}] y(switch)      = {np.round(ysw,6)}')
    print(f'[{tag}] u(ring)        = {np.round(rng[:,1],6)}')
    print(f'[{tag}] v(ring)        = {np.round(rng[:,2],6)}')
    print(f'[{tag}] yface          = {np.round(yface,6)}')
    print(f'[{tag}] closure G      = {np.round(G["closure"],6)}')
    print(f'[{tag}] Sum w - 2pi    = {G["W"]:+.6f}')
    print(f'[{tag}] alpha          = {np.round(rng[:,0],6)}')
    print(f'[{tag}] b(switch)      = {np.round(bsw,6)}')
    return dict(tag=tag, zfile=zfile, R=R, D_fac=D_fac, D_con=D_con, id_err=D_con - D_fac,
                area=A, Wc=Wc, G={k: (v.tolist() if isinstance(v, np.ndarray) else v)
                                  for k, v in G.items() if k not in ('alpha', 'u', 'v', 'w', 'L', 'T', 'b', 'ysw', 'yface')},
                fac=fac)


def main():
    out = []
    for tag, zf, R in [('c825_R375', 'q0_lower375_dual_0_4.json', 3 / 8),
                       ('c825_R38', 'q0_lower375_dual_0_4.json', 19 / 50)]:
        out.append(run(tag, zf, R))
    (HERE / 'r20_residuals.json').write_text(json.dumps(out, indent=1, default=float))
    print('written', HERE / 'r20_residuals.json')


if __name__ == '__main__':
    main()
