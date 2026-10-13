"""r20-geometry: non-flat (alpha_2 < pi) patch analysis for the surviving q0(6,7) graph.

Read-only inputs from ../lead/ (joint_nested_frozen.json). No claim is registered here.
Conventions (identical to lead):
  R  = 0.38 (fixed normalization of the compact necessary domain)
  r  = R*t, t in [75/76, 1]  (actual allowance)
  sectors i=1,2,3 : triangle (P_(i-1), c_i, P_i) with normalized endpoint distances
                    u_i = |P_(i-1)-c_i|/R   and   v_i = |P_i - c_i|/R
  switch distances: v_1 = u_2 = s_1 , v_2 = u_3 = s_2 (same physical point)
  closure (C820):   b_i = (pi - T_i - L_(i+1) - (w_i + w_(i+1))/2)/2
  atoms: 11 faces (0..10), 9 switches (11..19), 9 sectors (20..28)
  seven-factor group = faces {1,2}, switches {12,13}, sectors {21,22,23}
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / "lead"
R = 0.38
PI = math.pi
TAU = 75.0 / 76.0
QMIN = 4 * math.sin(PI - 8 * math.asin(R)) ** 2 / R ** 2
SEVEN_FACES = [1, 2]
SEVEN_SWITCH = [12, 13]
SEVEN_SECTOR = [21, 22, 23]

FR = json.loads((LEAD / "joint_nested_frozen.json").read_text())
FACES = [list(f) for f in FR["faces"]]
EDGES = [tuple(e) for e in FR["edges"]]
ZF = np.array(FR["z"], dtype=float)          # current frozen dual (SHA 5671967c...)
ADJ = {e: [t for t, f in enumerate(FACES) if all(i in f for i in e)] for e in EDGES}


def atom(fi, x):
    """Exact copy of lead/exchange_middle_inward_dual.py atom(); fi is a factor index."""
    m = np.zeros(len(ZF))
    if fi < 11:
        a, b, tt = x
        aa = [a, b, PI - a - b]
        sn = np.sin(aa)
        v = 2 * R * R * tt * tt * np.prod(sn)
        for k, i in enumerate(FACES[fi]):
            e = tuple(sorted(j for j in FACES[fi] if j != i))
            ee = EDGES.index(e)
            sgn = 1 if ADJ[e][0] == fi else -1
            m[i] -= aa[k]
            m[50 + ee] -= aa[k]
            m[11 + ee] += sgn * tt * tt * sn[k] ** 2
            m[73 + ee] += sgn * tt * sn[k]
    elif fi < 20:
        bi = fi - 11
        b, tt = x
        i, j = bi, (bi + 1) % 9
        ee = EDGES.index(tuple(sorted((i, j))))
        v = R * R * tt * tt * math.sin(2 * b) / 2
        m[i] += b
        m[j] += b
        m[50 + ee] -= b
        m[112 + bi] += 2 * b
        m[11 + ee] -= tt * tt * math.sin(b) ** 2
        m[73 + ee] -= tt * math.sin(b)
        m[33 + 2 * i] += tt * tt
        m[32 + 2 * j] += tt * tt
        m[95 + 2 * i] += tt
        m[94 + 2 * j] += tt
    else:
        i = fi - 20
        a, u, vv = x
        Q = (u - vv) ** 2 + 4 * u * vv * math.sin(a / 2) ** 2
        w = 2 * math.asin(min(1.0, R * math.sqrt(Q) / 2))
        L = math.atan2(vv * math.sin(a), u - vv * math.cos(a))
        T = PI - a - L
        v = R * R * u * vv * math.sin(a) / 2 + (w - math.sin(w)) / 2
        m[i] -= a
        m[32 + 2 * i] -= u * u
        m[33 + 2 * i] -= vv * vv
        m[94 + 2 * i] -= u
        m[95 + 2 * i] -= vv
        m[71] += w
        m[112 + (i - 1) % 9] += L + w / 2
        m[112 + i] += T + w / 2
    return float(v), m


def value(fi, x, z=None):
    if z is None:
        z = ZF
    v, m = atom(fi, x)
    return v + float(m @ z)


def sector_data(a, u, v):
    """(alpha,u,v) -> Q, w, h=sin(w/2), k=cos(w/2), L (base angle at P_(i-1)), T (at P_i)."""
    Q = (u - v) ** 2 + 4 * u * v * math.sin(a / 2) ** 2
    h = R * math.sqrt(Q) / 2
    if h > 1:
        return None
    w = 2 * math.asin(h)
    k = math.sqrt(max(0.0, 1 - h * h))
    L = math.atan2(v * math.sin(a), u - v * math.cos(a))
    T = PI - a - L
    return dict(Q=Q, w=w, h=h, k=k, L=L, T=T)


def sector_margin(a, u, v, t):
    """actual-r C844: [chord floor, inward norm + endpoint bound with actual r].
    With u,v <= t (enforced separately as t-u, t-v) the combined C844 condition is
        uv sin(alpha-omega) >= max(t^2,u^2,v^2) sin(omega)  =  t^2 sin(omega)."""
    d = sector_data(a, u, v)
    if d is None:
        return None
    return [d["Q"] - QMIN,
            u * v * (d["k"] * math.sin(a) - d["h"] * math.cos(a)) - t * t * d["h"],
            t - u, t - v]


# ----------------------------------------------------------------------------------
# flat chart (alpha2 = pi => s1 = s2 = t): verbatim reimplementation of
# lead/probe_seven_factor_actualr.py patch() on top of the 5-parameter cluster.
# ----------------------------------------------------------------------------------
def flat_args(x):
    """x = (t, a1, u1, a3, v3, Afrac, Hfrac).  Returns dict with 7 atom arguments or None."""
    t, a1, u1, a3, v3 = x[0], x[1], x[2], x[3], x[4]
    r = R * t
    sd1 = sector_data(a1, u1, t)
    sd3 = sector_data(a3, t, v3)
    if sd1 is None or sd3 is None:
        return None
    w2 = 2 * math.asin(R * t)
    b1 = (PI - sd1["T"] - 0.0 - (sd1["w"] + w2) / 2) / 2
    b2 = (PI - 0.0 - sd3["L"] - (w2 + sd3["w"]) / 2) / 2
    A = x[5] * (b1 + b2)
    B = b1 + b2 - A
    delta = b1 - A
    if min(A, B, b1, b2) <= 0 or max(A, B) >= PI:
        return None
    s = math.sqrt(1 - r * r)
    dd = s * s * math.cos(delta) ** 2 - 2 * r * (1 - r)
    if dd < 0:
        return None
    root = math.sqrt(dd)
    lo = max(2 * r * abs(math.sin(delta)), s * math.cos(delta) - root)
    hi = min(2 * r * math.sin(b1 + A), 2 * r * math.sin(b2 + B), s * math.cos(delta) + root)
    if lo > hi or hi <= 0:
        return None
    H = lo + x[6] * (hi - lo)
    fargs = []
    for j, (a, b) in enumerate([(A, b1), (B, b2)]):
        D = 2 * r * math.sin(b)
        hub = math.atan2(D * math.sin(a), H - D * math.cos(a))
        other = PI - a - hub
        rho = math.sqrt(max(0.0, H * H + D * D - 2 * H * D * math.cos(a))) / (2 * math.sin(a))
        if other <= 0:
            return None
        # lead ordering: j=0 -> [hub, other, rho/R] ; j=1 -> [hub, a, rho/R]
        fargs.append([hub, other if j == 0 else a, rho / R])
    return dict(t=t, r=r, b1=b1, b2=b2, A=A, B=B, H=H, lo=lo, hi=hi,
                sectors=[[a1, u1, t], [PI, t, t], [a3, t, v3]],
                switches=[[b1, t], [b2, t]], faces=[[fargs[0][0], fargs[0][1], fargs[0][2]],
                                                    [fargs[1][0], fargs[1][1], fargs[1][2]]])


def flat_args_from_dict(d):
    """from a dict t,a1,u1,a3,v3,A,H (A,H absolute)."""
    # reuse flat_args by inverting Afrac,Hfrac
    base = dict(t=d["t"], a1=d["a1"], u1=d["u1"], a3=d["a3"], v3=d["v3"])
    t, a1, u1, a3, v3 = base["t"], base["a1"], base["u1"], base["a3"], base["v3"]
    sd1 = sector_data(a1, u1, t)
    sd3 = sector_data(a3, t, v3)
    if sd1 is None or sd3 is None:
        return None
    w2 = 2 * math.asin(R * t)
    b1 = (PI - sd1["T"] - (sd1["w"] + w2) / 2) / 2
    b2 = (PI - sd3["L"] - (w2 + sd3["w"]) / 2) / 2
    if not (0 < b1 < PI / 2 and 0 < b2 < PI / 2):
        return None
    Afrac = d["A"] / (b1 + b2)
    r = R * t
    s = math.sqrt(1 - r * r)
    delta = b1 - d["A"]
    dd = s * s * math.cos(delta) ** 2 - 2 * r * (1 - r)
    if dd < 0:
        return None
    root = math.sqrt(dd)
    lo = max(2 * r * abs(math.sin(delta)), s * math.cos(delta) - root)
    hi = min(2 * r * math.sin(b1 + d["A"]), 2 * r * math.sin(b2 + b1 - d["A"]), s * math.cos(delta) + root)
    if hi <= lo or not (lo <= d["H"] <= hi):
        return None
    return flat_args([t, a1, u1, a3, v3, Afrac, (d["H"] - lo) / (hi - lo)])


def flat_value(d):
    if d is None:
        return None
    tot = 0.0
    for fi, x in zip(SEVEN_FACES, d["faces"]):
        tot += value(fi, x)
    for fi, x in zip(SEVEN_SWITCH, d["switches"]):
        tot += value(fi, x)
    for fi, x in zip(SEVEN_SECTOR, d["sectors"]):
        tot += value(fi, x)
    return tot


# ----------------------------------------------------------------------------------
# general (non-flat) chart: alpha2 <= pi, switch distances s1,s2 <= t free
# parameters: t, a1,u1,s1, a2,s2, a3,v3, A, H      (10 scalars; s1=v1=u2, s2=v2=u3)
# ----------------------------------------------------------------------------------
def closure_b(p):
    """b1,b2 from the sector data by the C820 boundary closure (independent of A,H)."""
    sd1 = sector_data(p["a1"], p["u1"], p["s1"])
    sd2 = sector_data(p["a2"], p["s1"], p["s2"])
    sd3 = sector_data(p["a3"], p["s2"], p["v3"])
    if sd1 is None or sd2 is None or sd3 is None:
        return None
    b1 = (PI - sd1["T"] - sd2["L"] - (sd1["w"] + sd2["w"]) / 2) / 2
    b2 = (PI - sd2["T"] - sd3["L"] - (sd2["w"] + sd3["w"]) / 2) / 2
    return b1, b2


def gen_args(p):
    t = p["t"]
    r = R * t
    sd1 = sector_data(p["a1"], p["u1"], p["s1"])
    sd2 = sector_data(p["a2"], p["s1"], p["s2"])
    sd3 = sector_data(p["a3"], p["s2"], p["v3"])
    if sd1 is None or sd2 is None or sd3 is None:
        return None
    b1 = (PI - sd1["T"] - sd2["L"] - (sd1["w"] + sd2["w"]) / 2) / 2
    b2 = (PI - sd2["T"] - sd3["L"] - (sd2["w"] + sd3["w"]) / 2) / 2
    if not (0 < b1 < PI / 2 and 0 < b2 < PI / 2):
        return None
    A = p["A"]
    # GENERAL identity: A+B = pi + b1 + b2 - alpha2  (flat: alpha2=pi -> A+B=b1+b2)
    B = PI + b1 + b2 - p["a2"] - A
    H = p["H"]
    if not (0 < A < PI and 0 < B < PI and H > 0):
        return None
    D1 = 2 * R * p["s1"] * math.sin(b1)
    D2 = 2 * R * p["s2"] * math.sin(b2)
    if not (0 < D1 <= 2 * r and 0 < D2 <= 2 * r):
        return None
    def _face(a, D):
        """triangle (c9,c1,c2) [or (c9,c2,c3)]: sides H (at c2), D (at c2), angle a at c2.
        Returns None or (angle at c9, angle opposite H, rho/R)."""
        disc = 4 * r * r - D * D
        if disc < 0:
            return None
        rt = math.sqrt(disc)
        if not (D * math.cos(a) - math.sin(a) * rt <= H <= D * math.cos(a) + math.sin(a) * rt):
            return None
        hub = math.atan2(D * math.sin(a), H - D * math.cos(a))
        other = PI - a - hub
        if not (0 < hub < PI and 0 < other < PI):
            return None
        rho = math.sqrt(max(0.0, H * H + D * D - 2 * H * D * math.cos(a))) / (2 * math.sin(a))
        return hub, other, rho / R

    fa1 = _face(A, D1)
    fa2 = _face(B, D2)
    if fa1 is None or fa2 is None:
        return None
    # ordering identical to lead flat chart:  face1 -> [angle@9, angle@1, rho/R]
    #                                         face2 -> [angle@9, angle@2, rho/R]
    fargs = [[fa1[0], fa1[1], fa1[2]], [fa2[0], B, fa2[2]]]
    # coordinates in the canonical frame (sector-2 chord midpoint on +x axis, P1 below)
    wt = sd2["w"] / 2
    if math.sin(wt) <= 0:
        return None
    P1 = (math.cos(wt), -math.sin(wt))
    P2 = (math.cos(wt), math.sin(wt))
    d1 = R * p["s1"]
    d2 = R * p["s2"]
    y2 = R * R * (p["s1"] ** 2 - p["s2"] ** 2) / (4 * math.sin(wt))
    val = d1 * d1 - (y2 + math.sin(wt)) ** 2
    if val < 0:
        return None
    c2 = (math.cos(wt) - math.sqrt(val), y2)

    def rot(v, th):
        return (v[0] * math.cos(th) - v[1] * math.sin(th), v[0] * math.sin(th) + v[1] * math.cos(th))

    def unit(v):
        n = math.hypot(*v)
        return (v[0] / n, v[1] / n)

    c1 = (P1[0] + R * p["s1"] * rot(unit((c2[0] - P1[0], c2[1] - P1[1])), 2 * b1)[0],
          P1[1] + R * p["s1"] * rot(unit((c2[0] - P1[0], c2[1] - P1[1])), 2 * b1)[1])
    c3 = (P2[0] + R * p["s2"] * rot(unit((c2[0] - P2[0], c2[1] - P2[1])), -2 * b2)[0],
          P2[1] + R * p["s2"] * rot(unit((c2[0] - P2[0], c2[1] - P2[1])), -2 * b2)[1])
    c9 = (c2[0] + H * rot(unit((c1[0] - c2[0], c1[1] - c2[1])), -A)[0],
          c2[1] + H * rot(unit((c1[0] - c2[0], c1[1] - c2[1])), -A)[1])
    return dict(t=t, r=r, b1=b1, b2=b2, A=A, B=B, H=H, D1=D1, D2=D2,
                sectors=[[p["a1"], p["u1"], p["s1"]], [p["a2"], p["s1"], p["s2"]], [p["a3"], p["s2"], p["v3"]]],
                switches=[[b1, p["s1"]], [b2, p["s2"]]],
                faces=fargs, coords=dict(P1=P1, P2=P2, c1=c1, c2=c2, c3=c3, c9=c9),
                hubnorm=math.hypot(*c9), w2=sd2["w"])


def gen_value(d):
    if d is None:
        return None
    tot = 0.0
    for fi, x in zip(SEVEN_FACES, d["faces"]):
        tot += value(fi, x)
    for fi, x in zip(SEVEN_SWITCH, d["switches"]):
        tot += value(fi, x)
    for fi, x in zip(SEVEN_SECTOR, d["sectors"]):
        tot += value(fi, x)
    return tot


def gen_margins(p, d=None):
    """All legality margins of the general chart (>=0 required). Returns (names,margins)."""
    names, mg = [], []
    t = p["t"]
    r = R * t
    for j, (a, u, v) in enumerate([[p["a1"], p["u1"], p["s1"]],
                                   [p["a2"], p["s1"], p["s2"]],
                                   [p["a3"], p["s2"], p["v3"]]]):
        m = sector_margin(a, u, v, t)
        if m is None:
            return ["sector%d-data" % j], [-1.0]
        names += ["Q%d" % j, "norm%d" % j, "t-u%d" % j, "t-v%d" % j]
        mg += m
    bb = closure_b(p)
    if bb is None:
        return ["closure"], [-1.0]
    b1, b2 = bb
    A = p["A"]
    B = PI + b1 + b2 - p["a2"] - A
    H = p["H"]
    names += ["b1", "b2", "pi/2-b1", "pi/2-b2", "A", "B", "pi-A", "pi-B", "H"]
    mg += [b1, b2, PI / 2 - b1, PI / 2 - b2, A, B, PI - A, PI - B, H]
    names += ["sw1", "sw2"]
    mg += [2 * p["s1"] * math.cos(b1) - R * (t * t + p["s1"] ** 2),
           2 * p["s2"] * math.cos(b2) - R * (t * t + p["s2"] ** 2)]
    D1 = 2 * R * p["s1"] * math.sin(b1)
    D2 = 2 * R * p["s2"] * math.sin(b2)
    for tag, a, D in [("f1", A, D1), ("f2", B, D2)]:
        disc = 4 * r * r - D * D
        names += [tag + "-disc", tag + "-lo", tag + "-hi"]
        if disc <= 0:
            mg += [disc, -1.0, -1.0]
            continue
        rt = math.sqrt(disc)
        lo = D * math.cos(a) - math.sin(a) * rt
        hi = D * math.cos(a) + math.sin(a) * rt
        mg += [disc, H - lo, hi - H]
    if d is None:
        d = gen_args(p)
    if d is None:
        names += ["chart"]
        mg += [-1.0]
    else:
        names += ["hubnorm", "|c2|<=s"]
        mg += [1 - r - d["hubnorm"], math.sqrt(1 - r * r) - math.hypot(*d["coords"]["c2"])]
        for tag, a, D in [("f1", A, D1), ("f2", B, D2)]:
            hub = math.atan2(D * math.sin(a), H - D * math.cos(a))
            other = PI - a - hub
            names += [tag + "-hubang", tag + "-othang"]
            mg += [hub, other]
    return names, mg


def consistency(p, d=None):
    """independent geometric consistency checks of the coordinate construction."""
    if d is None:
        d = gen_args(p)
    if d is None:
        return None
    C = d["coords"]
    out = {}
    out["|c1-c2|"] = math.hypot(C["c1"][0] - C["c2"][0], C["c1"][1] - C["c2"][1])
    out["D1"] = d["D1"]
    out["|c3-c2|"] = math.hypot(C["c3"][0] - C["c2"][0], C["c3"][1] - C["c2"][1])
    out["D2"] = d["D2"]
    # angle at c2 between c1 and c3 must equal b1+b2 (closure consistency)
    v1 = (C["c1"][0] - C["c2"][0], C["c1"][1] - C["c2"][1])
    v3 = (C["c3"][0] - C["c2"][0], C["c3"][1] - C["c2"][1])
    ang = math.atan2(v1[0] * v3[1] - v1[1] * v3[0], v1[0] * v3[0] + v1[1] * v3[1])
    out["angle(c1,c3)@c2"] = ang
    out["b1+b2"] = d["b1"] + d["b2"]
    # endpoint norms
    out["|P1|"] = math.hypot(*C["P1"])
    out["|P2|"] = math.hypot(*C["P2"])
    out["|c1-P1|"] = math.hypot(C["c1"][0] - C["P1"][0], C["c1"][1] - C["P1"][1])
    out["|c2-P1|"] = math.hypot(C["c2"][0] - C["P1"][0], C["c2"][1] - C["P1"][1])
    out["|c2-P2|"] = math.hypot(C["c2"][0] - C["P2"][0], C["c2"][1] - C["P2"][1])
    out["|c3-P2|"] = math.hypot(C["c3"][0] - C["P2"][0], C["c3"][1] - C["P2"][1])
    out["|c2|"] = math.hypot(*C["c2"])
    out["s(r)"] = math.sqrt(1 - d["r"] ** 2)
    return out


def flat_to_gen(x7):
    """embed a flat 7-vector into the general parameter dict (alpha2=pi, s1=s2=t)."""
    d = flat_args(x7)
    if d is None:
        return None
    t = x7[0]
    return dict(t=t, a1=x7[1], u1=x7[2], s1=t, a2=PI, s2=t, a3=x7[3], v3=x7[4],
                A=d["A"], H=d["H"])
