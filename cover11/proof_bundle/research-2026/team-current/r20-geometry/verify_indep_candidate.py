"""r20-geometry / independent high-precision re-verification of the nonflat witness.

Purpose (check existing outputs first, then verify by a DIFFERENT inference):
  cand_full29.py / exp4_witness.py produced, on one code path (float64 + r20_lib),
      J(x*) = 28.114478844683   for the certified cover's own patch data,
      const + sum29 = pi + 7.1e-15 (tight dual identity at the certified cover).
  This script recomputes the same two numbers from the SAME read-only inputs with
  (a) mpmath 50-digit arithmetic seeded from the exact rational centre data (int/1e17),
  (b) switch points by high-precision BISECTION of the nearest-distance tie along the
      boundary circle (no radical-line formula, no float64 radical discriminant),
  (c) my own transcription of the frozen atom formula (lead/exchange_middle_inward_dual.py:13-25),
  (d) a byte-level re-check of the coefficient SHA256.
  It also reports the LOCAL slope dJ/d(alpha2) at the certificate data point (fixed A,H),
  which is the infinitesimal form of the "deformation onto the flat slice" premise.

Scope: calibration + witness arithmetic only. No claim is registered; no lead file is modified.
All inputs read-only: ../lead/joint_nested_frozen.json, ../../../n11/upper/certified_object.json.
"""
import hashlib, io, json, sys
from pathlib import Path
from mpmath import mp, mpf, sin, cos, asin, atan2, sqrt, pi as MP_PI

mp.dps = 50
HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / "lead"
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
R0 = mpf(19) / 50
SCALED = mpf(10) ** 17

# ---------------------------------------------------------------- frozen relaxation data
FR = json.loads((LEAD / "joint_nested_frozen.json").read_text())
Z = [mpf(repr(float(v))) for v in FR["z"]]          # 9-decimal exact literals -> float64 -> mpf
FACES = [list(f) for f in FR["faces"]]
EDGES = [tuple(e) for e in FR["edges"]]
ADJ = {e: [t for t, f in enumerate(FACES) if all(i in f for i in e)] for e in EDGES}
print("frozen SHA256 :", hashlib.sha256((LEAD / "joint_nested_frozen.json").read_bytes()).hexdigest())
print("expected SHA  : 5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb")

OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
DEC = int(OBJ["decimals"])
C = [[mpf(int(a)) / (mpf(10) ** DEC), mpf(int(b)) / (mpf(10) ** DEC)] for a, b in OBJ["centers_scaled_1e17"]]
HI = mpf(repr(float(OBJ["certified_interval"]["hi"])))
LO = mpf(repr(float(OBJ["certified_interval"]["lo"])))
print("candidate certified radius interval : [%s, %s]" % (mp.nstr(LO, 25), mp.nstr(HI, 25)))


def d2(i, th):
    return (cos(th) - C[i][0]) ** 2 + (sin(th) - C[i][1]) ** 2


def owner(th):
    vals = [d2(i, th) for i in range(len(C))]
    k = min(range(len(vals)), key=lambda i: vals[i])
    return k, vals[k]


# ------------------------------------------------------- 1. nearest-owner arcs on S^1
NS = 4096
owns = []
prev = None
for j in range(NS):
    th = 2 * MP_PI * j / NS
    k, _ = owner(th)
    if k != prev:
        owns.append((k, mpf(j)))
        prev = k
# merge first/last run
if len(owns) > 1 and owns[0][0] == owns[-1][0]:
    k0, _ = owns.pop(0)
ring_order = [k for k, _ in owns]
hubs = [i for i in range(len(C)) if i not in set(ring_order)]
print("ring owners (cyclic order) :", ring_order)
print("hubs (no boundary arc)     :", hubs)


# ------------------------------------------------- 2. switch points by mpmath bisection
def tie_theta(ka, kb, lo_th, hi_th):
    """root of f=d2(ka,.)-d2(kb,.) in [lo,hi]; robust: locate a sign change on a
    fine sub-grid of [lo,hi], then bisect.  ka owns the lo side, kb the hi side."""
    lo_th, hi_th = min(lo_th, hi_th), max(lo_th, hi_th)
    M = 256
    prev_t = lo_th
    prev_f = d2(ka, lo_th) - d2(kb, lo_th)
    root = None
    for j in range(1, M + 1):
        t = lo_th + (hi_th - lo_th) * mpf(j) / M
        f = d2(ka, t) - d2(kb, t)
        if prev_f == 0:
            return prev_t
        if prev_f * f < 0:
            a_, b_, fa = prev_t, t, prev_f
            for _ in range(220):
                mid = (a_ + b_) / 2
                fm = d2(ka, mid) - d2(kb, mid)
                if fm * fa <= 0:
                    b_ = mid
                else:
                    a_, fa = mid, fm
            cand = (a_ + b_) / 2
            if root is None or abs(d2(ka, cand) - d2(kb, cand)) < abs(d2(ka, root) - d2(kb, root)):
                root = cand
        prev_t, prev_f = t, f
    return root


SW = []          # (pair, theta, P, radius)
n_r = len(ring_order)
span = 2 * MP_PI / NS
for j in range(n_r):
    ka = ring_order[j]
    kb = ring_order[(j + 1) % n_r]
    start = mpf(owns[j][1]) * span          # approx. start of the arc owned by ka
    end = mpf(owns[(j + 1) % n_r][1]) * span if j + 1 < n_r else 2 * MP_PI + mpf(owns[0][1]) * span
    t = tie_theta(ka, kb, start, end)
    if t is None:
        raise RuntimeError("no tie bracket for %s in [%s,%s]" % ((ka, kb), start, end))
    P = (cos(t), sin(t))
    SW.append(dict(pair=(ka, kb), th=t, P=P, rad=sqrt(d2(ka, t))))

print("\nswitch points (pair, angle deg, radius vs certified interval):")
for s in SW:
    print("  %-8s theta=%10.5f  rad=%s  r/lo=%s hi=%s"
          % (str(s["pair"]), float(s["th"] * 180 / MP_PI), mp.nstr(s["rad"], 22),
             "ok" if s["rad"] >= LO - mpf("1e-18") else "LOW",
             "ok" if s["rad"] <= HI + mpf("1e-18") else "HIGH"))


# ------------------------------------- 3. abstract index map (data taken from cand_full29.py,
#    itself the label map that makes the frozen dual identity tight; verified below)
AMAP = {0: 5, 1: 7, 2: 1, 3: 8, 4: 6, 5: 4, 6: 9, 7: 10, 8: 3, 9: 2, 10: 0}
# rings in abstract order 0..8 must be the cyclic boundary order (up to rotation)
abs_of = {v: k for k, v in AMAP.items()}
seq = [abs_of[k] for k in ring_order]
rots = [seq[i:] + seq[:i] for i in range(9)]
REV = list(reversed(seq))
rots += [REV[i:] + REV[:i] for i in range(9)]
best_rot = min(range(18), key=lambda i: sum(1 for x, y in zip(rots[i], list(range(9))) if x != y))
abs_seq = rots[best_rot]
print("\nabstract ring order (rotation/reflection of the boundary cycle) :", abs_seq,
      "  [frozen graph wants 0,1,...,8]")
if abs_seq != list(range(9)):
    print("  WARNING: boundary cycle is not the frozen 0..8 order; faces/sectors are mapped via AMAP only.")

# sector i (abstract i) = ring AMAP[i], endpoints = switch (i-1) -> switch i
sw_by_pair = {s["pair"]: s for s in SW}
sectors = {}
switches = {}
for i in range(9):
    ci = C[AMAP[i]]
    left = sw_by_pair[(AMAP[(i - 1) % 9], AMAP[i])]
    right = sw_by_pair[(AMAP[i], AMAP[(i + 1) % 9])]
    Pl, Pr = left["P"], right["P"]
    u = sqrt((Pl[0] - ci[0]) ** 2 + (Pl[1] - ci[1]) ** 2) / R0
    v = sqrt((Pr[0] - ci[0]) ** 2 + (Pr[1] - ci[1]) ** 2) / R0
    va = (Pl[0] - ci[0], Pl[1] - ci[1])
    vb = (Pr[0] - ci[0], Pr[1] - ci[1])
    al = atan2(abs(va[0] * vb[1] - va[1] * vb[0]), va[0] * vb[0] + va[1] * vb[1])
    sectors[i] = (al, u, v)
    cj = C[AMAP[(i + 1) % 9]]
    wi = (ci[0] - Pr[0], ci[1] - Pr[1])
    wj = (cj[0] - Pr[0], cj[1] - Pr[1])
    b = atan2(abs(wi[0] * wj[1] - wi[1] * wj[0]), wi[0] * wj[0] + wi[1] * wj[1]) / 2
    switches[i] = (b, right["rad"] / R0)

faces = {}
for fi, f in enumerate(FACES):
    pts = [C[AMAP[k]] for k in f]
    ang = []
    for k in range(3):
        o, a, b_ = pts[k], pts[(k + 1) % 3], pts[(k + 2) % 3]
        uu = (a[0] - o[0], a[1] - o[1])
        vv = (b_[0] - o[0], b_[1] - o[1])
        ang.append(atan2(abs(uu[0] * vv[1] - uu[1] * vv[0]), uu[0] * vv[0] + uu[1] * vv[1]))
    rhos = [sqrt((pts[(k + 1) % 3][0] - pts[(k + 2) % 3][0]) ** 2 + (pts[(k + 1) % 3][1] - pts[(k + 2) % 3][1]) ** 2)
            / (2 * sin(ang[k])) for k in range(3)]
    faces[fi] = (ang, sum(rhos) / 3 / R0)

print("\nseven-factor group data (mpmath):")
for i in [1, 2, 3]:
    print("  sector %d: alpha=%s u=%s v=%s" % (i, mp.nstr(sectors[i][0], 18), mp.nstr(sectors[i][1], 18), mp.nstr(sectors[i][2], 18)))
for i in [1, 2]:
    print("  switch %d: b=%s s=%s" % (i, mp.nstr(switches[i][0], 18), mp.nstr(switches[i][1], 18)))
for fi in [1, 2]:
    print("  face   %d: angles=%s rho/R=%s" % (fi, [mp.nstr(x, 15) for x in faces[fi][0]], mp.nstr(faces[fi][1], 15)))


# ------------------------------------------------------- 4. my transcription of the atom map
def atom(fi, x):
    m = [mpf(0)] * len(Z)
    if fi < 11:
        a, b, t = x
        aa = [a, b, MP_PI - a - b]
        sn = [sin(z) for z in aa]
        v = 2 * R0 * R0 * t * t * sn[0] * sn[1] * sn[2]
        for k, i in enumerate(FACES[fi]):
            e = tuple(sorted(j for j in FACES[fi] if j != i))
            ee = EDGES.index(e)
            sgn = 1 if ADJ[e][0] == fi else -1
            m[i] -= aa[k]
            m[50 + ee] -= aa[k]
            m[11 + ee] += sgn * t * t * sn[k] ** 2
            m[73 + ee] += sgn * t * sn[k]
    elif fi < 20:
        bi = fi - 11
        b, t = x
        i, j = bi, (bi + 1) % 9
        ee = EDGES.index(tuple(sorted((i, j))))
        v = R0 * R0 * t * t * sin(2 * b) / 2
        m[i] += b
        m[j] += b
        m[50 + ee] -= b
        m[112 + bi] += 2 * b
        m[11 + ee] -= t * t * sin(b) ** 2
        m[73 + ee] -= t * sin(b)
        m[33 + 2 * i] += t * t
        m[32 + 2 * j] += t * t
        m[95 + 2 * i] += t
        m[94 + 2 * j] += t
    else:
        i = fi - 20
        a, u, vv = x
        Q = (u - vv) ** 2 + 4 * u * vv * sin(a / 2) ** 2
        if R0 * sqrt(Q) / 2 > 1:
            return None, None
        w = 2 * asin(R0 * sqrt(Q) / 2)
        L = atan2(vv * sin(a), u - vv * cos(a))
        T = MP_PI - a - L
        v = R0 * R0 * u * vv * sin(a) / 2 + (w - sin(w)) / 2
        m[i] -= a
        m[32 + 2 * i] -= u * u
        m[33 + 2 * i] -= vv * vv
        m[94 + 2 * i] -= u
        m[95 + 2 * i] += -vv if False else -vv
        m[71] += w
        m[112 + (i - 1) % 9] += L + w / 2
        m[112 + i] += T + w / 2
    return v, m


def value(fi, x):
    v, m = atom(fi, x)
    if v is None:
        return None
    return v + sum(mm * zz for mm, zz in zip(m, Z))


CONST = MP_PI * sum(Z[0:9]) + 2 * MP_PI * sum(Z[9:11]) - MP_PI * sum(Z[112:121])
tot = mpf(0)
vals = {}
for fi in range(11):
    vals[fi] = value(fi, [faces[fi][0][0], faces[fi][0][1], faces[fi][1]])
for i in range(9):
    vals[11 + i] = value(11 + i, [switches[i][0], switches[i][1]])
for i in range(9):
    vals[20 + i] = value(20 + i, list(sectors[i]))
tot = sum(vals.values())
J = vals[1] + vals[2] + vals[12] + vals[13] + vals[21] + vals[22] + vals[23]
S22 = tot - J

print("\n--- mpmath 50-digit reconstruction ---")
print("const                     = %s" % mp.nstr(CONST, 30))
print("sum of 29 atom values     = %s" % mp.nstr(tot, 30))
print("const + sum               = %s" % mp.nstr(CONST + tot, 30))
print("pi                        = %s" % mp.nstr(MP_PI, 30))
print("slack (const+sum-pi)      = %s" % mp.nstr(CONST + tot - MP_PI, 6))
print("seven-factor J(x*)        = %s" % mp.nstr(J, 25))
print("22-factor part            = %s" % mp.nstr(S22, 25))

THRESH = mpf("28.10704541577262956809")
FLAT_HB = mpf("28.1069488227408612601720960810780525207519531")
FLAT_NUM = mpf("28.104237014746577")
print("J - threshold T           = %s" % mp.nstr(J - THRESH, 8))
print("J - certified flat ub (high bearing) = %s" % mp.nstr(J - FLAT_HB, 8))
print("J - numeric flat max (3 starts)      = %s" % mp.nstr(J - FLAT_NUM, 8))

# --------------------------------------- 5. local slope dJ/d(alpha2) at fixed (A,H) data
p0 = dict(t=sectors[2][1], a1=sectors[1][0], u1=sectors[1][1], s1=sectors[1][2],
          a2=sectors[2][0], s2=sectors[2][2], a3=sectors[3][0], v3=sectors[3][2],
          A=faces[1][0][2], H=None)
# frozen face order FACES[1]=[9,1,2]=(hub, ring_left, ring_mid): the chart parameter A is the
# angle at the MIDDLE ring (vertex 2 of that triangle) = ang[2]; H = |c_hub - c_middle|.
hm = C[2]
cm = C[AMAP[2]]
p0["H"] = sqrt((hm[0] - cm[0]) ** 2 + (hm[1] - cm[1]) ** 2)
print("\nchart data      : alpha2 = %s" % mp.nstr(p0["a2"], 20))
print("                  A (face1 middle angle) = %s" % mp.nstr(p0["A"], 20))
print("                  H = |c_hub - c_2| = %s" % mp.nstr(p0["H"], 20))


def chart_parts(pp):
    """(b1,b2,B,D1,D2,face1(hub,other,rho),face2(hub,other,rho)) or None; no clipping."""
    sd = {}
    for tag, (a, u, v) in [("s1", (pp["a1"], pp["u1"], pp["s1"])),
                           ("s2", (pp["a2"], pp["s1"], pp["s2"])),
                           ("s3", (pp["a3"], pp["s2"], pp["v3"]))]:
        Q = (u - v) ** 2 + 4 * u * v * sin(a / 2) ** 2
        if R0 * sqrt(Q) / 2 > 1:
            return None
        w = 2 * asin(R0 * sqrt(Q) / 2)
        L = atan2(v * sin(a), u - v * cos(a))
        sd[tag] = dict(w=w, L=L, T=MP_PI - a - L, Q=Q)
    b1 = (MP_PI - sd["s1"]["T"] - sd["s2"]["L"] - (sd["s1"]["w"] + sd["s2"]["w"]) / 2) / 2
    b2 = (MP_PI - sd["s2"]["T"] - sd["s3"]["L"] - (sd["s2"]["w"] + sd["s3"]["w"]) / 2) / 2
    B = MP_PI + b1 + b2 - pp["a2"] - pp["A"]
    D1 = 2 * R0 * pp["s1"] * sin(b1)
    D2 = 2 * R0 * pp["s2"] * sin(b2)
    rr = R0 * pp["t"]
    F = []
    for a, D in [(pp["A"], D1), (B, D2)]:
        disc = 4 * rr * rr - D * D
        if disc <= 0:
            return None
        rt = sqrt(disc)
        hub = atan2(D * sin(a), pp["H"] - D * cos(a))
        other = MP_PI - a - hub
        rho = sqrt(max(mpf(0), pp["H"] ** 2 + D * D - 2 * pp["H"] * D * cos(a))) / (2 * sin(a))
        F.append(dict(a=a, D=D, disc=disc, rt=rt, hub=hub, other=other, rho=rho,
                      lo=D * cos(a) - sin(a) * rt, hi=D * cos(a) + sin(a) * rt))
    return dict(sd=sd, b1=b1, b2=b2, B=B, D1=D1, D2=D2, F=F, rr=rr)


def margins(pp):
    """independent re-implementation of the general-chart legality margins (>=0 required)."""
    if pp["s1"] > pp["t"] or pp["s2"] > pp["t"]:
        return None
    g = chart_parts(pp)
    if g is None:
        return None
    names, mg = [], []
    for j, (a, u, v) in enumerate([(pp["a1"], pp["u1"], pp["s1"]),
                                   (pp["a2"], pp["s1"], pp["s2"]),
                                   (pp["a3"], pp["s2"], pp["v3"])]):
        Q = (u - v) ** 2 + 4 * u * v * sin(a / 2) ** 2
        h = R0 * sqrt(Q) / 2
        if h > 1:
            return None
        w = 2 * asin(h)
        k = sqrt(1 - h * h)
        QMIN = 4 * sin(MP_PI - 8 * asin(R0)) ** 2 / R0 ** 2
        names += ["Q%d" % j, "norm%d" % j, "t-u%d" % j, "t-v%d" % j]
        mg += [Q - QMIN, u * v * (k * sin(a) - h * cos(a)) - pp["t"] * pp["t"] * h,
               pp["t"] - u, pp["t"] - v]
    names += ["b1", "b2", "pi/2-b1", "pi/2-b2", "A", "B", "pi-A", "pi-B", "H"]
    mg += [g["b1"], g["b2"], MP_PI / 2 - g["b1"], MP_PI / 2 - g["b2"], pp["A"], g["B"],
           MP_PI - pp["A"], MP_PI - g["B"], pp["H"]]
    names += ["sw1", "sw2"]
    mg += [2 * pp["s1"] * cos(g["b1"]) - R0 * (pp["t"] ** 2 + pp["s1"] ** 2),
           2 * pp["s2"] * cos(g["b2"]) - R0 * (pp["t"] ** 2 + pp["s2"] ** 2)]
    for f in g["F"]:
        names += ["disc", "lo", "hi"]
        mg += [f["disc"], pp["H"] - f["lo"], f["hi"] - pp["H"]]
        names += ["hubang", "othang"]
        mg += [f["hub"], f["other"]]
    c2 = C[AMAP[2]]          # middle ring of the A-chain (abstract ring 2)
    hub = C[2]               # A-chain hub (abstract site 9)
    # in the chart's canonical frame |c9| and |c2| are unchanged (rigid motion of the actual data)
    names += ["hubnorm", "|c2|<=s"]
    mg += [1 - g["rr"] - sqrt(hub[0] ** 2 + hub[1] ** 2),
           sqrt(1 - g["rr"] ** 2) - sqrt(c2[0] ** 2 + c2[1] ** 2)]
    return names, mg


def seven_from_params(pp):
    """J as a function of the 10 chart scalars (closure b1,b2 recomputed each time)."""
    g = chart_parts(pp)
    if g is None:
        return None
    f1, f2 = g["F"]
    if not (0 < g["b1"] < MP_PI / 2 and 0 < g["b2"] < MP_PI / 2 and 0 < pp["A"] < MP_PI
            and 0 < g["B"] < MP_PI and pp["H"] > 0):
        return None
    return (value(1, [f1["hub"], f1["other"], f1["rho"] / R0])
            + value(2, [f2["hub"], g["B"], f2["rho"] / R0])
            + value(12, [g["b1"], pp["s1"]]) + value(13, [g["b2"], pp["s2"]])
            + value(21, [pp["a1"], pp["u1"], pp["s1"]])
            + value(22, [pp["a2"], pp["s1"], pp["s2"]])
            + value(23, [pp["a3"], pp["s2"], pp["v3"]]))


names, mg = margins(p0)
print("\nindependent chart-legality check at the certificate patch point:")
print("   min margin = %s at %s" % (mp.nstr(min(mg), 6), names[mg.index(min(mg))]))
print("   tight (<1e-9):", [(n, mp.nstr(m, 3)) for n, m in zip(names, mg) if m < mpf("1e-9")])

J_chart = seven_from_params(p0)
print("\nJ from chart parameters (same point, closure recomputed) = %s" % mp.nstr(J_chart, 25))
print("difference to atom-list J                                = %s" % mp.nstr(J_chart - J, 6))

for h in [mpf("1e-9"), mpf("1e-7"), mpf("1e-5"), mpf("1e-3")]:
    for sgn, tag in [(-1, "toward flat  (a2+h)"), (+1, "away from flat (a2-h)")]:
        pp = dict(p0)
        pp["a2"] = p0["a2"] - sgn * h
        mm = margins(pp)
        if mm is None:
            print("h=%-8s %s : chart undefined" % (mp.nstr(h, 3), tag))
            continue
        mn = min(mm[1])
        Jv = seven_from_params(pp)
        print("h=%-8s %s : min margin %+ .3e  J = %s   dJ = %+ .6e"
              % (mp.nstr(h, 3), tag, mn, ("%s" % mp.nstr(Jv, 20)) if Jv is not None else "n/a",
                 (Jv - J_chart) if Jv is not None else mpf("nan")))

# one-sided slope over a WIDE legal-ish step, using the maximum over the legal (A,H) fibre
# (grid + local refinement in mpmath; deterministic, no random restarts)
def fiber_max(pp, nA=61, nH=61, refine=3, tol=mpf("1e-12")):
    """max of J over the legal (A,H) fibre; deterministic grid + box refinement, no random start.
    tol=1e-12: the chart data are float64-precision reconstructions of the exact rational
    centre data, so geometrically-zero margins (t-s=0, face-circle equality) appear at 1e-17."""
    g = chart_parts(pp)
    if g is None:
        return None
    b1, b2 = g["b1"], g["b2"]
    Th = MP_PI + b1 + b2 - pp["a2"]
    Alo, Ahi = Th / 1000, Th * mpf("0.999")
    Hlo, Hhi = mpf("0.02"), 2 * R0
    best = (None, None)
    for it in range(refine):
        dA = (Ahi - Alo) / nA
        dH = (Hhi - Hlo) / nH
        for i in range(nA + 1):
            A = Alo + (Ahi - Alo) * mpf(i) / nA
            for j in range(nH + 1):
                H = Hlo + (Hhi - Hlo) * mpf(j) / nH
                q = dict(pp, A=A, H=H)
                mm = margins(q)
                if mm is None or min(mm[1]) < -tol:
                    continue
                Jv = seven_from_params(q)
                if Jv is None:
                    continue
                if best[0] is None or Jv > best[0]:
                    best = (Jv, (A, H))
        if best[1] is None:
            return None
        A0, H0 = best[1]
        Alo, Ahi = A0 - dA, A0 + dA
        Hlo, Hhi = H0 - dH, H0 + dH
    return best


print("\nfibre maxima over legal (A,H) at fixed outer data (deterministic grid+refine):")
for eps in [mpf(0), mpf("0.005"), mpf("0.02"), mpf("0.05"), mpf("0.07"), mpf("0.1"),
            mpf("0.1742386138"), mpf("0.4")]:
    pp = dict(p0)
    pp["a2"] = MP_PI - eps
    r = fiber_max(pp, nA=41, nH=41, refine=3)
    if r is None:
        print("  pi-alpha2=%-10s infeasible" % mp.nstr(eps, 6))
        continue
    print("  pi-alpha2=%-10s  J_fibre = %s   J-T = %+ .5e   (A,H)=(%s,%s)"
          % (mp.nstr(eps, 6), mp.nstr(r[0], 20), r[0] - THRESH,
             mp.nstr(r[1][0], 12), mp.nstr(r[1][1], 12)))

json.dump(dict(sha256=hashlib.sha256((LEAD / "joint_nested_frozen.json").read_bytes()).hexdigest(),
               J_mpmath=mp.nstr(J, 30), sum29=mp.nstr(tot, 30), const=mp.nstr(CONST, 30),
               slack=mp.nstr(CONST + tot - MP_PI, 6),
               J_minus_T=mp.nstr(J - THRESH, 10), J_minus_flat_hb=mp.nstr(J - FLAT_HB, 10),
               alpha2=mp.nstr(p0["a2"], 20), J_chart=mp.nstr(J_chart, 25)),
          open(HERE / "verify_indep_candidate.json", "w"), indent=1)
print("\nwrote verify_indep_candidate.json")
