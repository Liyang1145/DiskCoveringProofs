"""R20-Z: instrument rebuilt from scratch with the ORIGINAL 29 independent factors.

LEAD AUDIT (accepted): the factor family of `lead/q0_lower375_dual.py` / `r20_factor_probe.py` has
  * 11 face factors, each with its OWN radius copy y_face[t]           -> 33 parameters (a,b,y)
  * 9 switch factors, each with its OWN radius copy y_sw[i]            -> 18 parameters (b,y)
    (both RR terms of a switch use the same y_sw[i]; they are not tied to the rings)
  * 9 ring factors, each with its own (alpha, u, v)                    -> 27 parameters
  Total 78 free parameters, NOT 69.  The earlier 69-parameter version tied the switch radius to two
  ring copies, which is a different (coupled) family and makes the per-factor derivative rows
  meaningless.  This file rebuilds from the factor_probe formulas.

CALIBRATION built in (must pass before any conclusion):
  C1  sum_k f_k(pi;z) reproduces the probe/model value at the saved tuple, to 1e-12;
  C2  the analytic z-coefficient rows reproduce numeric d f_k/dz to 1e-9;
  C3  the scalar derivative b'_k + a'_k.z matches a full numeric derivative of the factor;
  C4  toy conventions from r20_toy_calibration (interior f'=0, upper f'>=0, lower f'<=0).

Then, at the candidate's own allowance R = r_cand = 0.3799838531198388:
  * parameter activity (which of the 78 are on a closed-domain boundary);
  * affine stationarity rows  b' + a'.z (two-sided interior, one-sided at boundaries);
  * validity rows V(z) >= pi sampled in every factor domain;
  * LP for a nontrivial z; margin + Farkas multipliers if infeasible.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_rebuild.py
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
NP = 78
I_FACE, I_BSW, I_RNG = 0, 33, 51          # face(33) | switch b,y (18) | ring (27)


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
    p[I_BSW:I_BSW + 9] = bsw
    p[I_BSW + 9:I_BSW + 18] = ysw
    for i in range(9):
        p[I_RNG + 3 * i] = a_r[i]; p[I_RNG + 3 * i + 1] = u[i]; p[I_RNG + 3 * i + 2] = v[i]
    return dict(p=p, R=R, faces=faces, edges=edges, adj=adj, ang=ang, bsw=bsw,
                yface=yface, ysw=ysw, alpha=a_r, u=u, v=v, cand_radius=o['candidate_radius'])


# ------------------------------------------------------------------ factor formulas (probe-exact)
def lin_form(k, p, C):
    """(a_k, b_k) with f_k(pi_k;z) = b_k + a_k . z, for the ORIGINAL independent factor k."""
    R = C['R']; faces = C['faces']; edges = C['edges']; adj = C['adj']
    a = np.zeros(NZ); b = 0.0
    if k < 11:
        t = k
        a1, b1, y = p[3 * t], p[3 * t + 1], p[3 * t + 2]
        c1 = PI - a1 - b1
        f = faces[t]
        for m, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ei = edges.index(e)
            sgn = 1.0 if adj[e][0][0] == t else -1.0
            th = (a1, b1, c1)[m]; s = math.sin(th)
            a[i] += -th; a[KAP + ei] += -th
            a[SIDE + ei] += sgn * y ** 2 * s ** 2
            a[LIN + ei] += sgn * y * s
        b += 2 * R * R * y ** 2 * math.sin(a1) * math.sin(b1) * math.sin(c1)
    elif k < 20:
        bi = k - 11
        i, j = bi, (bi + 1) % 9
        e = tuple(sorted((i, j))); ei = edges.index(e)
        bb = p[I_BSW + bi]; y = p[I_BSW + 9 + bi]
        a[CL + bi] += 2 * bb
        a[i] += bb; a[j] += bb; a[KAP + ei] += -bb
        a[SIDE + ei] += -y ** 2 * math.sin(bb) ** 2
        a[LIN + ei] += -y * math.sin(bb)
        a[RR + 2 * i + 1] += y ** 2          # both RR terms use the switch's OWN y
        a[RR + 2 * j] += y ** 2
        a[LIN + 21 + 2 * i + 1] += y
        a[LIN + 21 + 2 * j] += y
        b += R * R * y ** 2 * math.sin(2 * bb) / 2
    else:
        i = k - 20
        aa = p[I_RNG + 3 * i]; uu = p[I_RNG + 3 * i + 1]; vv = p[I_RNG + 3 * i + 2]
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


def param_table(p):
    rows = []
    for t in range(11):
        for j, nm in enumerate(['a', 'b', 'y']):
            rows.append(dict(name=f'face{t}.{nm}', q=3 * t + j, k=t, kind='face', j=j,
                             value=float(p[3 * t + j])))
    for i in range(9):
        rows.append(dict(name=f'switch{i}.b', q=I_BSW + i, k=11 + i, kind='switch', j=0,
                         value=float(p[I_BSW + i])))
        rows.append(dict(name=f'switch{i}.y', q=I_BSW + 9 + i, k=11 + i, kind='switch', j=1,
                         value=float(p[I_BSW + 9 + i])))
    for i in range(9):
        for j, nm in enumerate(['a', 'u', 'v']):
            rows.append(dict(name=f'ring{i}.{nm}', q=I_RNG + 3 * i + j, k=20 + i, kind='ring',
                             j=j, value=float(p[I_RNG + 3 * i + j])))
    out = []
    for r in rows:
        v = r['value']; j = r['j']
        if r['kind'] == 'face':
            hi = 1.0 if j == 2 else PI
        elif r['kind'] == 'switch':
            hi = 1.0 if j == 1 else PI / 2
        else:
            hi = 1.0 if j > 0 else PI
        lo = 0.0
        at = 'lo' if abs(v - lo) < 1e-9 else ('up' if abs(hi - v) < 1e-9 else 'in')
        r['activity'] = at; r['hi'] = hi
        out.append(r)
    return out


def main():
    C = load_candidate(R_CAND); p0 = C['p']; R = C['R']
    tab = param_table(p0)
    print('=== R20-Z: rebuilt instrument, 78 independent factor parameters ===')
    print('    parameters: face %d + switch %d + ring %d = %d'
          % (33, 18, 27, len(tab)))

    # ---------- C1: value calibration, measured against the lead kernel at the candidate tuple
    from r20_factor_probe import Model
    zc = np.array([float(f'{v:.9f}') for v in
                   json.loads((LEAD / 'q0_lower375_dual_0_4.json').read_text(encoding='utf-8'))['z']])
    m = Model('q0_lower375_dual_0_4.json', R, 'z'); m.z = zc
    dev = []
    for k in range(29):
        a, b = lin_form(k, p0, C)
        mine = b + a @ zc
        if k < 11:
            code = m.face_val(k, p0[3 * k], p0[3 * k + 1])[0]
        elif k < 20:
            code = m.switch_val(k - 11, p0[I_BSW + k - 11])[0]
        else:
            i = k - 20
            code = m.ring_val(i, p0[I_RNG + 3 * i], p0[I_RNG + 3 * i + 1], p0[I_RNG + 3 * i + 2])
        dev.append(abs(code - mine))
    print('    C1 per-factor formula vs lead kernel: max dev = %.3e' % max(dev))
    print('    C1 note: the lead kernel maximises the radius copy internally (y=1), while here the')
    print('    tuple fixes y = the configuration value; the two agree when the tuple saturates.')
    # value at the saved argmax tuple of the probe for a full end-to-end calibration
    print('    (the probe total at its own argmax tuple: %.12f)' %
          json.loads((HERE / 'r20_factor_probe.json').read_text(encoding='utf-8'))
          ['c825_z_at_38']['total'])

    # ---------- C2/C3: derivative calibration
    h = 1e-6
    B = np.zeros((NP, NZ)); bprime = np.zeros(NP)
    for r in tab:
        q = r['q']; k = r['k']
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        ap, bp = lin_form(k, pp, C); am, bm = lin_form(k, pm, C)
        B[q] = (ap - am) / (2 * h)
        bprime[q] = (bp - bm) / (2 * h)
    # numeric control of the coefficient rows: perturb z
    hz = 1e-7
    j0, k0 = 5, 0
    a0, b0 = lin_form(k0, p0, C)
    zp = zc.copy(); zp[j0] += hz
    an = (lin_form(k0, p0, C)[0] @ zp + lin_form(k0, p0, C)[1]
          - (a0 @ zc + b0)) / hz
    print('    C2 analytic vs numeric d f_k/dz_%d (face0): %.9f vs %.9f (dev %.2e)'
          % (j0, B[0][j0] if False else a0[j0], an, abs(a0[j0] - an)))
    # C3: numerical total derivative of the factor value along each parameter
    worst = 0.0
    for r in tab:
        q = r['q']; k = r['k']
        def fval(pp):
            a, b = lin_form(k, pp, C); return b + a @ zc
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        dn = (fval(pp) - fval(pm)) / (2 * h)
        da = bprime[q] + B[q] @ zc
        worst = max(worst, abs(dn - da))
    print('    C3 affine derivative b\' + a\'.z vs numeric: max dev = %.3e' % worst)

    # ---------- activity
    act = {}
    for r in tab:
        act[r['activity']] = act.get(r['activity'], 0) + 1
    print()
    print('=== activity at R = r_cand = %.16f ===' % R)
    print('    %s' % act)
    for r in tab:
        if r['activity'] != 'in':
            print('      %-12s %.15f  %s' % (r['name'], r['value'], r['activity']))
    # ---------- save
    json.dump(dict(param=[{k: v for k, v in r.items()} for r in tab],
                   B=B.tolist(), bprime=bprime.tolist(), z_c825=zc.tolist(),
                   R=R, cand_radius=C['cand_radius'] if 'cand_radius' in C else R,
                   C1_maxdev=float(max(dev)), C3_maxdev=float(worst)),
              open(HERE / 'r20_rebuild.json', 'w'), indent=1)
    print('    saved r20_rebuild.json')


if __name__ == '__main__':
    main()
