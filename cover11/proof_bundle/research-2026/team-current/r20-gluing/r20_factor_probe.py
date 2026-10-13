"""R20-A: restore factor/shared-variable residuals of a saved 29-factor relaxation solution.

Object (units): unit closed disk boundary, 9 inward-root ring sites + 2 inner hubs,
q0(6,7) = span-4 graph, allowance R (ring/site circumradius <= R, endpoint distances <= R),
frozen 9-decimal dual coefficients z (121 columns, z[50:73]=0).

Factors (lead kernel satisfy_q0_closure.py / certify_q0_lower375.py structure, re-derived here):
  face t   : value = sum_m co_m*angle_m + max_{y in [0,1]} (A y^2 + B y),
             A = 2 R^2 prod sin(angles) + sum_m dd_m sin^2(angle_m), B = sum_m ll_m sin(angle_m)
  switch i : value = c_i*b + max_{y in [0,1]} (A y^2 + B y),
             A = R^2 sin(2b)/2 - d sin^2 b + e, B = g sin b + h
  ring i   : value = R^2 u v sin(a)/2 + (w - sin w)/2 + C w
                     - mu a - d u^2 - e v^2 - dl u - el v
                     + (hl-hr)beta - hr a + hr*pi + (hl+hr) w/2 ,
             beta = atan2(v sin a, u - v cos a), w = 2 asin(R sqrt(q)/2),
             q = (u-v)^2 + 4 u v sin^2(a/2),  q >= qmin = 4 sin^2(pi - 8 asin R)/R^2.

Diagnostic only. No claim registered, no lead file modified. Writes only in this directory.
"""
import json, math, sys
import numpy as np
from pathlib import Path

PI = math.pi
HERE = Path(__file__).parent
LEAD = HERE.parent / 'lead'
SIDE, RR, KAP, LAM, ETA, LIN, CL = 11, 32, 50, 71, 72, 73, 112


# ---------------------------------------------------------------- factor kernels
def quad(A, B):
    """max_{y in [0,1]} (A y^2 + B y); returns (value, chosen argmax)."""
    v0 = 0.0; y0 = 0.0
    v1 = A + B
    if v1 > v0: v0, y0 = v1, 1.0
    if A < 0.0:
        yv = -B / (2.0 * A)
        if 0.0 < yv < 1.0:
            vv = A * yv * yv + B * yv
            if vv > v0: v0, y0 = vv, yv
    return v0, y0


class Model:
    def __init__(self, zfile, R, key='z'):
        raw = json.loads((LEAD / zfile).read_text(encoding='utf-8'))
        self.zname = zfile
        zv = raw[key] if key in raw else raw['coefficients']
        self.z = np.array([float(f'{v:.9f}') for v in zv])
        self.faces = raw['faces']
        self.edges = [tuple(e) for e in raw['edges']]
        self.R = float(R); self.R2 = self.R * self.R
        self.qmin = 4.0 * math.sin(PI - 8.0 * math.asin(self.R)) ** 2 / self.R2
        self.adj = {e: [(t, next(v for v in f if v not in e))
                        for t, f in enumerate(self.faces) if e[0] in f and e[1] in f]
                    for e in self.edges}
        z = self.z
        self.const = PI * (z[:9].sum() + 2 * z[9:11].sum() + z[KAP:LAM].sum()
                           - 2 * z[LAM] - 2 * z[ETA]) + 2 * z[ETA] * math.asin(2 * self.R) \
                     - PI * z[CL:].sum()

    # -- face
    def face_coefs(self, t):
        f = self.faces[t]; co = []; dd = []; ll = []; ee = []
        for k, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ei = self.edges.index(e); ee.append(ei)
            co.append(-self.z[i] - self.z[KAP + ei])
            sgn = 1.0 if self.adj[e][0][0] == t else -1.0
            dd.append(self.z[SIDE + ei] * sgn); ll.append(self.z[LIN + ei] * sgn)
        return np.array(co), np.array(dd), np.array(ll), ee

    def face_val(self, t, a, b, co=None, dd=None, ll=None):
        if co is None: co, dd, ll, _ = self.face_coefs(t)
        c = PI - a - b
        if a < 0 or b < 0 or c < 0: return -np.inf, 0.0
        s = (math.sin(a), math.sin(b), math.sin(c))
        base = co[0] * a + co[1] * b + co[2] * c
        A = 2 * self.R2 * s[0] * s[1] * s[2] + sum(dd[k] * s[k] ** 2 for k in range(3))
        B = sum(ll[k] * s[k] for k in range(3))
        q, y = quad(A, B)
        return base + q, y

    # -- switch
    def switch_coefs(self, bi):
        i = bi; j = (bi + 1) % 9; e = tuple(sorted((i, j))); ei = self.edges.index(e)
        c = self.z[i] + self.z[j] - self.z[KAP + ei] + 2 * self.z[CL + bi]
        d = self.z[SIDE + ei]
        ee = self.z[RR + 2 * i + 1] + self.z[RR + 2 * j]
        g = -self.z[LIN + ei]
        h = self.z[LIN + 21 + 2 * i + 1] + self.z[LIN + 21 + 2 * j]
        return c, d, ee, g, h, ei

    def switch_val(self, bi, b, cf=None):
        if cf is None: cf = self.switch_coefs(bi)
        c, d, ee, g, h, _ = cf
        A = self.R2 * math.sin(2 * b) / 2 - d * math.sin(b) ** 2 + ee
        B = g * math.sin(b) + h
        q, y = quad(A, B)
        return c * b + q, y

    # -- ring
    def ring_coefs(self, ri):
        z = self.z
        return dict(mu=z[ri], d=z[RR + 2 * ri], e=z[RR + 2 * ri + 1],
                    C=z[LAM] + (z[ETA] if ri >= 3 else 0.0),
                    dl=z[LIN + 21 + 2 * ri], el=z[LIN + 21 + 2 * ri + 1],
                    hl=z[CL + (ri - 1) % 9], hr=z[CL + ri])

    def ring_val(self, ri, a, u, v, cf=None):
        if cf is None: cf = self.ring_coefs(ri)
        if not (0.0 <= a <= PI and 0.0 <= u <= 1.0 and 0.0 <= v <= 1.0):
            return -np.inf
        q = (u - v) ** 2 + 4 * u * v * math.sin(a / 2) ** 2
        if q < self.qmin: return -np.inf
        w = 2 * math.asin(min(1.0, self.R * math.sqrt(q) / 2))
        val = self.R2 * u * v * math.sin(a) / 2 + ((cf['C'] + 0.5) * w - math.sin(w) / 2)
        val += -cf['mu'] * a - cf['d'] * u * u - cf['e'] * v * v - cf['dl'] * u - cf['el'] * v
        beta = math.atan2(v * math.sin(a), u - v * math.cos(a))
        val += (cf['hl'] - cf['hr']) * beta - cf['hr'] * a + cf['hr'] * PI \
               + (cf['hl'] + cf['hr']) * w / 2
        return val


# ---------------------------------------------------------------- deterministic maximization
def pattern_search(f, x0, lo, hi, steps, iters=400):
    x = np.array(x0, float); fx = f(x); st = np.array(steps, float)
    for _ in range(iters):
        moved = False
        for k in range(len(x)):
            for s in (+1.0, -1.0):
                cand = x.copy()
                cand[k] = min(hi[k], max(lo[k], x[k] + s * st[k]))
                fc = f(cand)
                if fc > fx: x, fx, moved = cand, fc, True
        if not moved:
            st = st * 0.4
            if st.max() < 1e-11: break
    return x, fx


def grid_quad(A2, B1):
    """vectorized max_{y in [0,1]} (A2 y^2 + B1 y)."""
    val = np.maximum(0.0, A2 + B1)
    with np.errstate(divide='ignore', invalid='ignore'):
        yv = np.where(A2 < 0, -B1 / (2 * np.where(A2 < 0, A2, -1.0)), -1.0)
        vv = A2 * yv * yv + B1 * yv
    vert = np.where((A2 < 0) & (yv > 0) & (yv < 1), vv, -np.inf)
    return np.maximum(val, vert)


def max_face(m, t):
    co, dd, ll, _ = m.face_coefs(t)
    f = lambda x: m.face_val(t, x[0], x[1], co, dd, ll)[0]
    n = 300
    g = np.arange(n + 1) * PI / n
    A, B = np.meshgrid(g, g, indexing='ij')
    c = PI - A - B
    ok = c >= 0
    S1, S2, S3 = np.sin(A), np.sin(B), np.sin(c)
    base = co[0] * A + co[1] * B + co[2] * c
    a2 = 2 * m.R2 * S1 * S2 * S3 + dd[0] * S1 ** 2 + dd[1] * S2 ** 2 + dd[2] * S3 ** 2
    b1 = ll[0] * S1 + ll[1] * S2 + ll[2] * S3
    val = np.where(ok, base + grid_quad(a2, b1), -np.inf)
    idx = np.unravel_index(np.argmax(val), val.shape)
    x0 = np.array([A[idx], B[idx]])
    x, fx = pattern_search(f, x0, [0.0, 0.0], [PI, PI], [PI / 300, PI / 300])
    return x, fx


def max_switch(m, bi):
    cf = m.switch_coefs(bi)
    f = lambda x: m.switch_val(bi, x[0], cf)[0]
    g = np.linspace(0, PI / 2, 40001)
    vals = np.array([m.switch_val(bi, b, cf)[0] for b in g])
    x, fx = pattern_search(f, [g[int(np.argmax(vals))]], [0.0], [PI / 2], [PI / 400])
    return x, fx


def max_ring(m, ri):
    cf = m.ring_coefs(ri)
    f = lambda x: m.ring_val(ri, x[0], x[1], x[2], cf)
    n = 45
    A = np.linspace(1e-9, PI - 1e-9, n)
    U = np.linspace(0, 1, n)
    V = np.linspace(0, 1, n)
    best = (-1e30, None)
    for a in A:
        Q = (U[:, None] - V[None, :]) ** 2 + 4 * U[:, None] * V[None, :] * math.sin(a / 2) ** 2
        base = m.R2 * U[:, None] * V[None, :] * math.sin(a) / 2
        W = 2 * np.arcsin(np.clip(m.R * np.sqrt(np.maximum(Q, 0)) / 2, 0, 1))
        seg = (cf['C'] + 0.5) * W - np.sin(W) / 2
        beta = np.arctan2(V[None, :] * math.sin(a), U[:, None] - V[None, :] * math.cos(a))
        val = base + seg - cf['mu'] * a - cf['d'] * U[:, None] ** 2 - cf['e'] * V[None, :] ** 2 \
              - cf['dl'] * U[:, None] - cf['el'] * V[None, :] \
              + (cf['hl'] - cf['hr']) * beta - cf['hr'] * a + cf['hr'] * PI \
              + (cf['hl'] + cf['hr']) * W / 2
        val = np.where(Q >= m.qmin, val, -np.inf)
        i, j = np.unravel_index(np.argmax(val), val.shape)
        if val[i, j] > best[0]: best = (float(val[i, j]), (a, U[i], V[j]))
    x, fx = pattern_search(f, list(best[1]), [1e-9, 0.0, 0.0], [PI - 1e-9, 1.0, 1.0],
                           [PI / 200, 1 / 200, 1 / 200])
    return x, fx


def maximize_all(m, tag):
    out = []
    for t in range(11):
        x, fx = max_face(m, t)
        out.append(dict(name=f'face{t}', idx=t, kind='face', x=list(map(float, x)),
                        a=float(x[0]), b=float(x[1]), val=float(fx)))
    for bi in range(9):
        x, fx = max_switch(m, bi)
        out.append(dict(name=f'switch{bi}', idx=11 + bi, kind='switch', x=list(map(float, x)),
                        b=float(x[0]), val=float(fx)))
    for ri in range(9):
        x, fx = max_ring(m, ri)
        out.append(dict(name=f'ring{ri}', idx=20 + ri, kind='ring', x=list(map(float, x)),
                        a=float(x[0]), u=float(x[1]), v=float(x[2]), val=float(fx)))
    for r in out:
        if r['kind'] == 'face':
            vv, y = m.face_val(r['idx'], r['a'], r['b']); r['y'] = float(y)
        elif r['kind'] == 'switch':
            vv, y = m.switch_val(r['idx'] - 11, r['b']); r['y'] = float(y)
    print(f'[{tag}] sum factor values = {sum(r["val"] for r in out):.12f}  '
          f'const = {m.const:.12f}  total = {m.const + sum(r["val"] for r in out):.12f}')
    return out


def main():
    Rmain = 19 / 50
    jobs = [
        ('c825_z_at_375', 'q0_lower375_dual_0_4.json', 3 / 8, 'z'),
        ('c825_z_at_38', 'q0_lower375_dual_0_4.json', Rmain, 'z'),
        ('frozen_z_at_38', 'joint_nested_frozen.json', Rmain, 'z'),
    ]
    report = {}
    for tag, zfile, R, key in jobs:
        if not (LEAD / zfile).exists():
            print('missing', zfile); continue
        m = Model(zfile, R, key)
        print(f'=== {tag}: {zfile} R={R!r} qmin={m.qmin:.6f} const={m.const:.9f}')
        fac = maximize_all(m, tag)
        report[tag] = dict(zfile=zfile, R=R, qmin=m.qmin, const=m.const, factors=fac,
                           total=m.const + sum(r['val'] for r in fac))
    # certified reference (C825) for the calibration leg
    cert = json.loads((LEAD / 'q0_lower375_dual_certificate_0_4.json').read_text(encoding='utf-8'))
    report['certified_c825_uppers'] = {f['factor']: f['upper'] for f in cert['factors']}
    report['certified_c825_total'] = cert['upper']
    (HERE / 'r20_factor_probe.json').write_text(json.dumps(report, indent=1))
    print('written', HERE / 'r20_factor_probe.json')


if __name__ == '__main__':
    main()
