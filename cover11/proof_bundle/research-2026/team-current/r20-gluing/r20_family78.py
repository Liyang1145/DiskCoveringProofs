"""R20-AC: the 78-column instrument, done right.

THE FAMILY (exactly the original 29 independent factors of `lead/q0_lower375_dual.py` /
`r20_factor_probe.py`):
   11 face factors   : parameters (a_t, b_t, y_face_t)                        -> 33
    9 switch factors : parameters (b_i, y_sw_i), both RR terms use y_sw_i     -> 18
    9 ring factors   : parameters (alpha_i, u_i, v_i)                         -> 27
  Total 78 free parameters.  Each factor's derivative row touches only the columns that appear in
  ITS OWN formula (the "pressure" variables), so the stationarity rows are derived analytically:

      face t, vertex k with opposite angle theta_k, incident edge e, sign sgn:
          dF/dtheta_k = -z_i - z_KAP[e]  + 2*y*sgn*sin(theta_k)*z_SIDE[e]
                        + 2*R^2*y*prod_{l!=k}sin(theta_l)  + y*sgn*cos(theta_k)*z_LIN[e]
          dF/dy       =  4*R^2*y*prod sin(theta) + 2*y*sum sgn*sin^2*z_SIDE + sum sgn*sin*z_LIN
      switch i (edge e, RR indices 2i+1 and 2j, LIN indices 21+2i+1 and 21+2j):
          dF/db = 2*z_CL[i] + z_j + z_i - z_KAP[e] - y*sin(2b)*z_SIDE[e] - y*cos(b)*z_LIN[e]
          dF/dy = 2*R^2*y*sin(2b) - 2*y*sin^2(b)*z_SIDE[e] - sin(b)*z_LIN[e]
                  + 2*y*(z_RR[2i+1] + z_RR[2j]) + (z_LIN[21+2i+1] + z_LIN[21+2j])
      ring i:
          dF/dalpha = A1 + A2 - z_i + w_a*(B1+B2) - mu  - hr      (mu = z_i again below)
          dF/du     = A3 + w_u*(B1+B2) - 2*d*u - dl + A4
          dF/dv     = A5 + w_v*(B1+B2) - 2*e*v - el + A6
      with the abbreviations of `ring_pressure()` below.
The same code path is also calibrated against numerical differentiation (C3 row in r20_rebuild).

Then: affine stationarity (b' + a'.z), correct boundary signs, cone, sampled validity rows, LP.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_family78.py
"""
import json, math, sys
import numpy as np
from pathlib import Path

HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
PI = math.pi
NZ = 121                     # pressure-variable columns (the 121-column z of the saved dual)
NPAR = 78                    # independent factor parameters
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112
R_CAND = 0.3799838531198388
I_FACE, I_BSW, I_RNG = 0, 33, 51
NP = NPAR


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


def lin_form(k, p, C):
    """(a_k, b_k), f_k = b_k + a_k . z, a_k of length 78."""
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
        a[RR + 2 * i + 1] += y ** 2
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
        if i >= 3:                       # lead: factor_probe ring_coefs C = z[lam] + z[eta] if ri>=3
            a[ETA] += w                  # ETA atom: sum_{i>=3} w_i - 2pi + 2 asin(2R)
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
    for r in rows:
        v = r['value']; j = r['j']
        hi = (1.0 if (r['kind'] == 'face' and j == 2) or (r['kind'] == 'switch' and j == 1)
              or (r['kind'] == 'ring' and j > 0) else (PI / 2 if r['kind'] == 'switch' else PI))
        r['hi'] = hi
        r['activity'] = 'lo' if abs(v) < 1e-9 else ('up' if abs(hi - v) < 1e-9 else 'in')
    return rows


# ------------------------------------------------------- analytic stationarity rows
def stationarity_analytic(C, p):
    """78 x 78 matrix B (d f_k/d xi) and the affine constants bp (d b_k/d xi).

    The max of the (univariate) radius quadratic A*y^2 + B*y enters through its own derivative,
    which is what makes the stationarity condition AFFINE in z (the lead's audit point).
    """
    B = np.zeros((NP, NZ)); bp = np.zeros(NP)
    R = C['R']; faces = C['faces']; edges = C['edges']; adj = C['adj']
    # ---------------------------------------------------------------- faces
    for t in range(11):
        a1, b1, y = p[3 * t], p[3 * t + 1], p[3 * t + 2]
        c1 = PI - a1 - b1
        th = np.array([a1, b1, c1]); s = np.sin(th); cs = np.cos(th)
        f = faces[t]
        row_th = []
        for m, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ei = edges.index(e)
            sgn = 1.0 if adj[e][0][0] == t else -1.0
            v = np.zeros(NZ)
            v[i] += -1.0                      # vertex angle-sum multiplier
            v[KAP + ei] += -1.0               # ear-capacity multiplier
            v[SIDE + ei] = 2 * sgn * y ** 2 * s[m] * cs[m]
            v[LIN + ei] = sgn * y * cs[m]
            row_th.append(v)
        B[3 * t] = row_th[0] - row_th[2]      # d/da  (theta_2 = pi - a - b)
        B[3 * t + 1] = row_th[1] - row_th[2]  # d/db
        vy = np.zeros(NZ)
        for m, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ei = edges.index(e)
            sgn = 1.0 if adj[e][0][0] == t else -1.0
            vy[SIDE + ei] += 2 * y * sgn * s[m] ** 2
            vy[LIN + ei] += sgn * s[m]
        B[3 * t + 2] = vy
        prod3 = s[0] * s[1] * s[2]
        bp[3 * t] = 2 * R * R * y ** 2 * (cs[0] * s[1] * s[2]) - 2 * R * R * y ** 2 * (s[0] * s[1] * cs[2])
        bp[3 * t + 1] = 2 * R * R * y ** 2 * (s[0] * cs[1] * s[2]) - 2 * R * R * y ** 2 * (s[0] * s[1] * cs[2])
        bp[3 * t + 2] = 4 * R * R * y * prod3
    # ---------------------------------------------------------------- switches
    for i in range(9):
        j = (i + 1) % 9
        e = tuple(sorted((i, j))); ei = edges.index(e)
        bb = p[I_BSW + i]; y = p[I_BSW + 9 + i]
        v = np.zeros(NZ)
        v[CL + i] += 2.0; v[i] += 1.0; v[j] += 1.0; v[KAP + ei] += -1.0
        v[SIDE + ei] += -y * math.sin(2 * bb)
        v[LIN + ei] += -y * math.cos(bb)
        B[I_BSW + i] = v
        vy = np.zeros(NZ)
        vy[SIDE + ei] += -2 * y * math.sin(bb) ** 2
        vy[LIN + ei] += -math.sin(bb)
        vy[RR + 2 * i + 1] += 2 * y
        vy[RR + 2 * j] += 2 * y
        vy[LIN + 21 + 2 * i + 1] += 1.0
        vy[LIN + 21 + 2 * j] += 1.0
        B[I_BSW + 9 + i] = vy
        bp[I_BSW + i] = R * R * y ** 2 * math.cos(2 * bb)
        bp[I_BSW + 9 + i] = 2 * R * R * y * math.sin(2 * bb)
    # ---------------------------------------------------------------- rings
    for i in range(9):
        aa = p[I_RNG + 3 * i]; uu = p[I_RNG + 3 * i + 1]; vv = p[I_RNG + 3 * i + 2]
        q = (uu - vv) ** 2 + 4 * uu * vv * math.sin(aa / 2) ** 2
        w = 2 * math.asin(min(1.0, R * math.sqrt(max(q, 0)) / 2))
        den = (uu - vv * math.cos(aa)) ** 2 + (vv * math.sin(aa)) ** 2
        sq = math.sqrt(max(q, 1e-300))
        rad = math.sqrt(max(1 - R * R * q / 4, 1e-300))
        w_a = R * (2 * uu * vv * math.sin(aa)) / (sq * rad) if q > 1e-12 else 0.0
        w_u = R * (2 * (uu - vv) + 4 * vv * math.sin(aa / 2) ** 2) / (sq * rad) if q > 1e-12 else 0.0
        w_v = R * (-2 * (uu - vv) + 4 * uu * math.sin(aa / 2) ** 2) / (sq * rad) if q > 1e-12 else 0.0
        L_a = -(uu * vv * math.cos(aa) - vv * vv) / den
        L_u = vv * math.sin(aa) / den
        L_v = -uu * math.sin(aa) / den
        T_a, T_u, T_v = -1 - L_a, -L_u, -L_v
        ra = np.zeros(NZ)
        ra[CL + (i - 1) % 9] += L_a; ra[CL + i] += T_a
        ra[i] += -1.0; ra[LAM] += w_a
        B[I_RNG + 3 * i] = ra
        ru = np.zeros(NZ)
        ru[CL + (i - 1) % 9] += L_u; ru[CL + i] += T_u
        ru[RR + 2 * i] += -2 * uu; ru[LAM] += w_u; ru[LIN + 21 + 2 * i] += -1.0
        B[I_RNG + 3 * i + 1] = ru
        rv = np.zeros(NZ)
        rv[CL + (i - 1) % 9] += L_v; rv[CL + i] += T_v
        rv[RR + 2 * i + 1] += -2 * vv; rv[LAM] += w_v; rv[LIN + 21 + 2 * i + 1] += -1.0
        B[I_RNG + 3 * i + 2] = rv
        bp[I_RNG + 3 * i] = R * R * uu * vv * math.cos(aa) / 2 + (1 - math.cos(w)) / 2 * w_a
        bp[I_RNG + 3 * i + 1] = R * R * vv * math.sin(aa) / 2 + (1 - math.cos(w)) / 2 * w_u
        bp[I_RNG + 3 * i + 2] = R * R * uu * math.sin(aa) / 2 + (1 - math.cos(w)) / 2 * w_v
    return B, bp


if __name__ == '__main__':
    C = load_candidate(R_CAND); p0 = C['p']
    tab = param_table(p0)
    B, bp = stationarity_analytic(C, p0)
    # numerical control
    h = 1e-6
    Bnum = np.zeros((NP, NZ)); bpnum = np.zeros(NP)
    for r in tab:
        q = r['q']; k = r['k']
        pp = p0.copy(); pm = p0.copy(); pp[q] += h; pm[q] -= h
        ap, b1 = lin_form(k, pp, C); am, b2 = lin_form(k, pm, C)
        Bnum[q] = (ap - am) / (2 * h); bpnum[q] = (b1 - b2) / (2 * h)
    print('analytic vs numeric:  max |B - Bnum| = %.3e   max |bp - bpnum| = %.3e'
          % (np.abs(B - Bnum).max(), np.abs(bp - bpnum).max()))
    bad = np.argwhere(np.abs(B - Bnum) > 1e-5)
    print('rows with deviation > 1e-5: %d' % len(bad))
    for r, c in bad[:10]:
        print('   row %s  col %d   analytic %.6e  numeric %.6e'
              % (tab[r]['name'], c, B[r, c], Bnum[r, c]))
