"""R20-D: (i) gap identity with corrected sign, (ii) piece-area / variable comparison
candidate vs high-value combination, (iii) ONE mechanism test:
cyclic sharing of the switch-point radii y_0..y_8 across the sector chain and switches
(the fan-chain global position closure), at fixed saved dual z.

Mechanism: the independent relaxation lets ring i choose (u_i,v_i) and switch i choose its own
y_i independently.  Genuine geometry requires  y_i(switch) = v_i(ring i) = u_{i+1}(ring i+1).
Impose exactly that and nothing else: boundary maximization becomes a max-plus cycle DP
  max_{y in [0,1]^9} sum_i [ R_i(y_{i-1},y_i) + S_i(y_i) ],  R_i = max_alpha ring_i, S_i = max_b switch_i.
For fixed z the sharing value <= the independent value (restriction of the product domain), and
both remain valid upper bounds on pi for genuine covers.  Finite y-grid => reported cycle value
is a LOWER bound on the true continuous cycle value, so the reported gain is an UPPER bound on
the true gain.  Diagnostic only; no claim; writes only in this directory.
"""
import json, math
import numpy as np
from pathlib import Path
from r20_factor_probe import Model, PI, SIDE, RR, KAP, LAM, ETA, LIN, CL, maximize_all
from r20_residuals import assemble, residuals, area_atoms

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'


def piece_areas(m, ang, yface, bsw, ysw, rng):
    site = [float(2 * m.R2 * yface[t] ** 2 * np.prod(np.sin(ang[t]))) for t in range(11)]
    sw = [float(m.R2 * ysw[i] ** 2 * math.sin(2 * bsw[i]) / 2) for i in range(9)]
    alpha, u, v = rng[:, 0], rng[:, 1], rng[:, 2]
    q = (u - v) ** 2 + 4 * u * v * np.sin(alpha / 2) ** 2
    w = 2 * np.arcsin(np.clip(m.R * np.sqrt(np.maximum(q, 1e-18)) / 2, 0, 1))
    sec = [float(m.R2 * u[i] * v[i] * math.sin(alpha[i]) / 2) for i in range(9)]
    seg = [float((w[i] - math.sin(w[i])) / 2 + (m.z[LAM] + (m.z[ETA] if i >= 3 else 0.0)) * w[i])
           for i in range(9)]
    seg0 = [float((w[i] - math.sin(w[i])) / 2) for i in range(9)]
    return dict(site=site, sw=sw, sec=sec, seg=seg, seg_raw=seg0, w=w.tolist(),
                alpha=alpha.tolist(), q=q.tolist())


def candidate_point(R):
    o = json.loads((LEAD / 'q0_exact_closure_radius.json').read_text(encoding='utf-8'))
    x0 = np.array(o['x0']); faces = o['faces']
    ang = x0[:33].reshape(11, 3); bsw = x0[33:42]
    rho = np.exp(x0[42:62] + x0[62])
    yface = rho[:11] / R; ysw = rho[11:20] / R
    u = np.roll(ysw, 1); v = ysw.copy()
    raw = np.zeros(9)
    for t, f in enumerate(faces):
        for k, i in enumerate(f):
            if i < 9: raw[i] += ang[t, k]
    alpha = PI - raw + np.roll(bsw, 1) + bsw
    return ang, yface, bsw, ysw, np.column_stack([alpha, u, v]), float(o['candidate_radius']), rho


def ring_grid(m, i, yg, al):
    cf = m.ring_coefs(i)
    U = yg[:, None, None]; V = yg[None, :, None]; A = al[None, None, :]
    q = (U - V) ** 2 + 4 * U * V * np.sin(A / 2) ** 2
    W = 2 * np.arcsin(np.clip(m.R * np.sqrt(np.maximum(q, 1e-18)) / 2, 0, 1))
    beta = np.arctan2(V * np.sin(A), U - V * np.cos(A))
    val = m.R2 * U * V * np.sin(A) / 2 + ((cf['C'] + 0.5) * W - np.sin(W) / 2)
    val = val - cf['mu'] * A - cf['d'] * U ** 2 - cf['e'] * V ** 2 - cf['dl'] * U - cf['el'] * V
    val = val + (cf['hl'] - cf['hr']) * beta - cf['hr'] * A + cf['hr'] * PI + (cf['hl'] + cf['hr']) * W / 2
    val = np.where(q >= m.qmin, val, -np.inf)
    return val.max(axis=2)


def switch_grid(m, i, yg, bg):
    """switch factor at FIXED shared radius y (no inner y-max): max over b."""
    cc, d, ee, g, h, _ = m.switch_coefs(i)
    bb = bg[None, :]
    A2 = m.R2 * np.sin(2 * bb) / 2 - d * np.sin(bb) ** 2 + ee
    B1 = g * np.sin(bb) + h
    val = cc * bb + A2 * yg[:, None] ** 2 + B1 * yg[:, None]
    return val.max(axis=1)


def cycle_dp(m, M=41, na=220, nb=400):
    yg = np.linspace(0, 1, M); al = np.linspace(1e-9, PI - 1e-9, na); bg = np.linspace(0, PI / 2, nb)
    Ring = np.stack([ring_grid(m, i, yg, al) for i in range(9)])
    Sw = np.stack([switch_grid(m, i, yg, bg) for i in range(9)])
    indep = float(sum(Ring[i].max() + Sw[i].max() for i in range(9)))
    best = -np.inf; beststate = None
    for c0 in range(M):
        dp = np.full(M, -np.inf); dp[c0] = Sw[0][c0]
        back = []
        for i in range(1, 9):
            v = dp[:, None] + Ring[i]
            bk = np.argmax(v, axis=0)
            dp = v.max(axis=0) + Sw[i]
            back.append(bk)
        tot = dp + Ring[0][:, c0]
        k = int(np.argmax(tot))
        if tot[k] > best:
            best = float(tot[k])
            cur = k; path = [cur]
            for bk in reversed(back):
                cur = int(bk[cur]); path.append(cur)
            beststate = (c0, k, list(reversed(path)))
    return yg, indep, best, beststate, Ring, Sw


def main():
    rep = {}
    for tag, zf, R in [('c825_R375', 'q0_lower375_dual_0_4.json', 3 / 8),
                       ('c825_R38', 'q0_lower375_dual_0_4.json', 19 / 50)]:
        m = Model(zf, R)
        fac = maximize_all(m, tag)
        F, ang, yface, bsw, ysw, rng = assemble(m, fac)
        G = residuals(m, ang, yface, bsw, ysw, rng); z = m.z
        A = area_atoms(m, ang, yface, bsw, ysw, rng)
        terms = dict(site=-(z[:9] @ G['site'] + z[9:11] @ G['hub']),
                     slack=z[KAP:KAP + 21] @ G['slack'],
                     m2=z[SIDE:SIDE + 21] @ G['m2'], m1=z[LIN:LIN + 21] @ G['m1'],
                     copy2=z[RR:RR + 18:2] @ G['c2L'] + z[RR + 1:RR + 18:2] @ G['c2R'],
                     copy1=z[94:112:2] @ G['c1L'] + z[95:112:2] @ G['c1R'],
                     closure=z[CL:CL + 9] @ G['closure'],
                     width=z[LAM] * G['W'] + z[ETA] * G['Eta'])
        V = float(m.const + F.sum())
        idn = A + sum(terms.values())
        print(f'[{tag}] IDENTITY A+sum={idn:.12f} vs V={V:.12f} err={idn - V:+.3e}')
        print(f'[{tag}] A-pi={A - PI:+.6f}; terms=' +
              ', '.join(f'{k}={v:+.6f}' for k, v in sorted(terms.items(), key=lambda kv: -abs(kv[1]))))
        pa = piece_areas(m, ang, yface, bsw, ysw, rng)
        print(f'[{tag}] piece sums: site={sum(pa["site"]):.6f} switch={sum(pa["sw"]):.6f} '
              f'sector={sum(pa["sec"]):.6f} seg={sum(pa["seg_raw"]):.6f} '
              f'| S w={sum(pa["w"]):.6f} (2pi={2 * PI:.6f})')
        rep[tag] = dict(identity_err=float(idn - V), area=float(A), A_minus_pi=float(A - PI),
                        terms={k: float(v) for k, v in terms.items()}, V=V,
                        ysw=ysw.tolist(), yface=yface.tolist(), u=rng[:, 1].tolist(),
                        v=rng[:, 2].tolist(), alpha=rng[:, 0].tolist(), b=bsw.tolist(),
                        closure=G['closure'].tolist(), W=float(G['W']), site=G['site'].tolist(),
                        hub=G['hub'].tolist(), m2=G['m2'].tolist(), m1=G['m1'].tolist(),
                        c1L=G['c1L'].tolist(), c1R=G['c1R'].tolist(),
                        c2L=G['c2L'].tolist(), c2R=G['c2R'].tolist(), piece=pa)
    # candidate comparison
    ang, yface, bsw, ysw, rng, rc, rho = candidate_point(19 / 50)
    m = Model('q0_lower375_dual_0_4.json', 19 / 50)
    A = area_atoms(m, ang, yface, bsw, ysw, rng)
    G = residuals(m, ang, yface, bsw, ysw, rng)
    pa = piece_areas(m, ang, yface, bsw, ysw, rng)
    print(f'[candidate] r={rc:.10f} A={A:.9f} A-pi={A - PI:+.3e} Sw-2pi={G["W"]:+.3e}')
    print(f'[candidate] piece sums: site={sum(pa["site"]):.6f} switch={sum(pa["sw"]):.6f} '
          f'sector={sum(pa["sec"]):.6f} seg={sum(pa["seg_raw"]):.6f}')
    print(f'[candidate] yface={np.round(yface,6)}\n[candidate] ysw={np.round(ysw,8)}')
    print(f'[candidate] alpha={np.round(rng[:,0],5)}')
    print(f'[candidate] b={np.round(bsw,5)}')
    print(f'[candidate] w={np.round(pa["w"],5)}')
    rep['candidate'] = dict(radius=rc, area=float(A), A_minus_pi=float(A - PI), W=float(G['W']),
                            ysw=ysw.tolist(), yface=yface.tolist(), alpha=rng[:, 0].tolist(),
                            u=rng[:, 1].tolist(), v=rng[:, 2].tolist(), b=bsw.tolist(),
                            piece=pa)
    # mechanism test
    for tag, zf, R in [('c825_R375', 'q0_lower375_dual_0_4.json', 3 / 8),
                       ('c825_R38', 'q0_lower375_dual_0_4.json', 19 / 50)]:
        m = Model(zf, R)
        fac = maximize_all(m, tag)
        fsum = sum(r['val'] for r in fac if r['kind'] == 'face')
        yg, indep, cyc, state, Ring, Sw = cycle_dp(m, M=41)
        V_ind = float(m.const + fsum + indep); V_cyc = float(m.const + fsum + cyc)
        radii = sorted(set(int(v) for v in state[2])) if state else []
        print(f'[{tag}] MECHANISM y-sharing: V_indep={V_ind:.9f} V_cycleDP={V_cyc:.9f} '
              f'gain={V_ind - V_cyc:+.6f} (pi={PI:.6f})')
        print(f'[{tag}]   cycle y-states={np.round(sorted(set(yg[list(radii)])),4)}')
        print(f'[{tag}]   independent per-ring sup={np.round([Ring[i].max() for i in range(9)],4)} '
              f'switch sup={np.round([Sw[i].max() for i in range(9)],4)}')
        rep.setdefault(tag, {}).update(V_indep=V_ind, V_cycle=V_cyc, gain=float(V_ind - V_cyc),
                                       cycle_y=[float(x) for x in sorted(set(yg[radii]))])
    (HERE / 'r20_mechanism.json').write_text(json.dumps(rep, indent=1, default=float))
    print('written', HERE / 'r20_mechanism.json')


if __name__ == '__main__':
    main()
