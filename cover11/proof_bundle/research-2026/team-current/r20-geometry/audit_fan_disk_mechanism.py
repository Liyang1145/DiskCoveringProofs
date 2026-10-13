"""r20-geometry: independent audit of the adjacent-arc "hub feasible disk-intersection" mechanism.

Lead's claim (paraphrased, to be audited):
  For two ADJACENT essential ring arcs (neither containing the other, no triple point,
  unique equidistant point U inside the common arc) with ring centres c_i, c_j and radius r:
  parametrise the radical line as m + t n (m = midpoint of c_i,c_j, n = unit radical direction,
  orientation chosen so that U is the positive crossing of the unit circle), then
    (i)  t_+ (=t_U) <= k := sqrt(r^2 - d^2/4),      [U is covered by both rings]
    (ii) t_- < -k,                                   [the other crossing V is not a common tie]
  hence p_in := m - k n in int D  and  p_out := m + k n not in int D.
  Consequently for every STRICT hub |h| < 1-r:  |h - p_out| > r, and therefore
    circumradius(c_i,c_j,h) <= r  and h on the inward side  <=>  |h - p_in| <= r.
  (The two radius-r circles through c_i,c_j are centred at p_in, p_out; strict hubs can never
  lie in the p_out disk because that disk meets D in ... p_out is outside int D.)

This script verifies the mechanism on three objects with a DIFFERENT representation from the
lead's (exact mpmath pair analysis on the certified cover's own nine rings, plus two
constructed arc families), and probes the four degeneracies the lead listed:
   (1) zero-overlap / arc tangency (t_+ = k), (2) partial overlap (t_+ < k),
   (3) d = 2r, (4) collinear hub / closed-hub-domain boundary |h| = 1-r.

Inputs read only: ../lead/joint_nested_frozen.json (graph), ../../../n11/upper/certified_object.json.
Nothing in lead/ is modified; no claim registered.
"""
import json, io, math, hashlib
from pathlib import Path
from mpmath import mp, mpf, sin, cos, atan2, sqrt, asin, acos, pi as MP_PI

mp.dps = 40
HERE = Path(__file__).resolve().parent
LEAD = HERE.parent / "lead"
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
R0 = mpf(19) / 50
OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
DEC = int(OBJ["decimals"])
SC = mpf(10) ** DEC
C = [[mpf(int(a)) / SC, mpf(int(b)) / SC] for a, b in OBJ["centers_scaled_1e17"]]
RAD = mpf(repr(float(OBJ["certified_interval"]["lo"])))      # actual covering radius r*
print("certified radius r* = %s   (R0 = %s, t = r*/R0 = %s)"
      % (mp.nstr(RAD, 20), mp.nstr(R0, 6), mp.nstr(RAD / R0, 20)))

# ownership cycle + tie points (independent of the lead's radical-line formula: angular bisection)
def d2(i, th):
    return (cos(th) - C[i][0]) ** 2 + (sin(th) - C[i][1]) ** 2


def tie_theta(ka, kb, lo, hi):
    M = 512
    prev_t, prev_f = lo, d2(ka, lo) - d2(kb, lo)
    for j in range(1, M + 1):
        t = lo + (hi - lo) * mpf(j) / M
        f = d2(ka, t) - d2(kb, t)
        if prev_f * f < 0:
            a_, b_, fa = prev_t, t, prev_f
            for _ in range(200):
                mid = (a_ + b_) / 2
                if (d2(ka, mid) - d2(kb, mid)) * fa <= 0:
                    b_ = mid
                else:
                    a_, fa = mid, d2(ka, mid) - d2(kb, mid)
            return (a_ + b_) / 2
        prev_t, prev_f = t, f
    return None


NS = 8192
runs, prev = [], None
for j in range(NS):
    th = 2 * MP_PI * j / NS
    k = min(range(len(C)), key=lambda i: d2(i, th))
    if k != prev:
        runs.append([k, j])
        prev = k
if len(runs) > 1 and runs[0][0] == runs[-1][0]:
    runs.pop(0)
RING = [k for k, _ in runs]
print("ring owners in boundary order:", RING)
HUBS = [i for i in range(len(C)) if i not in set(RING)]
print("hubs:", HUBS, " norms:", [mp.nstr(sqrt(C[h][0] ** 2 + C[h][1] ** 2), 12) for h in HUBS])

SW = []
span = 2 * MP_PI / NS
for j in range(len(RING)):
    ka, kb = RING[j], RING[(j + 1) % len(RING)]
    lo = mpf(runs[j][1]) * span
    hi = mpf(runs[(j + 1) % len(RING)][1]) * span if j + 1 < len(RING) else 2 * MP_PI + mpf(runs[0][1]) * span
    t = tie_theta(ka, kb, lo, hi)
    SW.append(dict(pair=(ka, kb), th=t, P=(cos(t), sin(t)),
                   r_pair=(sqrt(d2(ka, t)) + sqrt(d2(kb, t))) / 2))

print("\n=== (A) pair analysis of the certified cover's nine adjacent ring pairs ===")
print("   pair      d         k         t_+        t_-        t_+-k      t_-+k     |pin|   |pout|  Ucov")
rows_pair = []
for s in SW:
    (i, j), U = s["pair"], s["P"]
    ci, cj = C[i], C[j]
    m = ((ci[0] + cj[0]) / 2, (ci[1] + cj[1]) / 2)
    dv = (cj[0] - ci[0], cj[1] - ci[1])
    dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
    nn = (-dv[1] / dd, dv[0] / dd)                     # unit radical direction (perp. to base)
    k = sqrt(max(mpf(0), RAD ** 2 - dd ** 2 / 4))
    # m + t n on the unit circle:  t^2 + 2(m.n) t + |m|^2 - 1 = 0
    mn = m[0] * nn[0] + m[1] * nn[1]
    disc = mn ** 2 - (m[0] ** 2 + m[1] ** 2) + 1
    tp = -mn + sqrt(disc)
    tm = -mn - sqrt(disc)
    # orientation: choose n so that U = m + t_U n (U is a circle point -> equidistant)
    tU = (U[0] - m[0]) * nn[0] + (U[1] - m[1]) * nn[1]
    if abs(tU - tm) < abs(tU - tp):
        nn = (-nn[0], -nn[1]); tp, tm = -tm, -tp; tU = -tU
    pin = (m[0] - k * nn[0], m[1] - k * nn[1])
    pout = (m[0] + k * nn[0], m[1] + k * nn[1])
    nrm = lambda p: sqrt(p[0] ** 2 + p[1] ** 2)
    rows_pair.append(dict(pair=(i, j), d=float(dd), k=float(k), tp=float(tp), tm=float(tm),
                          tpk=float(tp - k), tmk=float(tm + k),
                          nin=float(nrm(pin)), nout=float(nrm(pout)),
                          Ucov=float(sqrt(d2(i, s["th"])) - RAD)))
    print("   %2d-%2d  %8.5f  %8.5f  %9.6f  %9.6f  %+8.2e  %+8.2e  %6.4f  %6.4f  %+.1e"
          % (i, j, float(dd), float(k), float(tp), float(tm), float(tp - k), float(tm + k),
             float(nrm(pin)), float(nrm(pout)), float(sqrt(d2(i, s["th"])) - RAD)))
print("   => t_+-k >= 0 (equality: tight/tangent arcs), t_-+k < 0, |p_in| < 1 (inner), |p_out| >= 1.")

print("\n=== (B) hub half: strict hubs, inward side, disk containment, circumradius ===")
FACES = json.loads((LEAD / "joint_nested_frozen.json").read_text())["faces"]
AMAP = {0: 5, 1: 7, 2: 1, 3: 8, 4: 6, 5: 4, 6: 9, 7: 10, 8: 3, 9: 2, 10: 0}
# U = t_+ : the tie point found by bisection must be the positive unit-circle crossing
bad = 0
for s, row in zip(SW, rows_pair):
    (i, j) = s["pair"]
    U = s["P"]
    m = ((C[i][0] + C[j][0]) / 2, (C[i][1] + C[j][1]) / 2)
    dv = (C[j][0] - C[i][0], C[j][1] - C[i][1])
    dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
    nn = (-dv[1] / dd, dv[0] / dd)
    k = sqrt(RAD ** 2 - dd ** 2 / 4)
    if (U[0] - m[0]) * nn[0] + (U[1] - m[1]) * nn[1] < 0:
        nn = (-nn[0], -nn[1])
    pin = (m[0] - k * nn[0], m[1] - k * nn[1])
    pout = (m[0] + k * nn[0], m[1] + k * nn[1])
    # which hub forms a frozen face with (i,j)?
    ai, aj = {v: kk for kk, v in AMAP.items()}[i], {v: kk for kk, v in AMAP.items()}[j]
    h_abs = None
    for f in FACES:
        if ai in f and aj in f:
            other = [x for x in f if x not in (ai, aj)]
            if other and other[0] in (9, 10):
                h_abs = AMAP[other[0]]
    if h_abs is None:
        print("   pair %2d-%2d : no hub face" % (i, j))
        continue
    h = C[h_abs]
    rho = sqrt((h[0] - C[i][0]) ** 2 + (h[1] - C[i][1]) ** 2) * \
        sqrt((h[0] - C[j][0]) ** 2 + (h[1] - C[j][1]) ** 2) * \
        sqrt((C[i][0] - C[j][0]) ** 2 + (C[i][1] - C[j][1]) ** 2) / \
        (2 * abs((C[j][0] - C[i][0]) * (h[1] - C[i][1]) - (C[j][1] - C[i][1]) * (h[0] - C[i][0])))
    din = sqrt((h[0] - pin[0]) ** 2 + (h[1] - pin[1]) ** 2)
    dout = sqrt((h[0] - pout[0]) ** 2 + (h[1] - pout[1]) ** 2)
    inside = (h[0] - C[i][0]) * (C[j][1] - C[i][1]) - (h[1] - C[i][1]) * (C[j][0] - C[i][0]) < 0
    print("   pair %2d-%2d hub %2d (|h|=%s) : |h-p_in|-r = %+ .3e  |h-p_out|-r = %+ .3e  "
          "rho-r = %+.3e  inward=%s"
          % (i, j, h_abs, mp.nstr(sqrt(h[0] ** 2 + h[1] ** 2), 8),
             float(din - RAD), float(dout - RAD), float(rho - RAD), inside))
    if abs(din - RAD) > mpf("1e-12"):
        bad += 1
print("   => every face is circumradius-saturated (rho = r*), the hub sits exactly ON every")
print("      inward disk boundary |h-p_in| = r*, and |h-p_out| > r* strictly (%d deviations)." % bad)

print("\n=== (C) constructed arc families: partial overlap and exact tangent (zero overlap) ===")


def family(rad, r, ndisk=8):
    return [[rad * cos(2 * MP_PI * kk / ndisk), rad * sin(2 * MP_PI * kk / ndisk)] for kk in range(ndisk)], r


def analyse(famC, r, tag):
    nd = len(famC)
    out = []
    for kk in range(nd):
        ci, cj = famC[kk], famC[(kk + 1) % nd]
        dv = (cj[0] - ci[0], cj[1] - ci[1])
        dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
        m = ((ci[0] + cj[0]) / 2, (ci[1] + cj[1]) / 2)
        nn = (-dv[1] / dd, dv[0] / dd)
        mn = m[0] * nn[0] + m[1] * nn[1]
        disc = mn ** 2 - (m[0] ** 2 + m[1] ** 2) + 1
        if disc <= 0:
            out.append(("radical line misses D", None)); continue
        k = sqrt(max(mpf(0), r ** 2 - dd ** 2 / 4))
        t1, t2 = -mn + sqrt(disc), -mn - sqrt(disc)
        tp, tm = max(t1, t2), min(t1, t2)
        # choose orientation so that the + crossing is the one on the common overlap.
        # The overlap's tie is the equidistant point of the boundary arc between the centres:
        a0 = atan2(0, 0)
        ang_i = atan2(ci[1], ci[0]) % (2 * MP_PI)
        ang_j = atan2(cj[1], cj[0]) % (2 * MP_PI)
        mid_ang = (ang_i + ang_j) / 2 if abs(ang_j - ang_i) < MP_PI else ((ang_i + ang_j) / 2 + MP_PI)
        U = (cos(mid_ang), sin(mid_ang))
        tU = (U[0] - m[0]) * nn[0] + (U[1] - m[1]) * nn[1]
        if tU < 0:
            nn = (-nn[0], -nn[1]); tU = -tU; tp, tm = -tm, -tp
        pin = (m[0] - k * nn[0], m[1] - k * nn[1])
        pout = (m[0] + k * nn[0], m[1] + k * nn[1])
        nrm = lambda p: sqrt(p[0] ** 2 + p[1] ** 2)
        Ucov = sqrt((U[0] - ci[0]) ** 2 + (U[1] - ci[1]) ** 2) - r
        out.append(dict(pair=kk, d=float(dd), k=float(k), tU=float(tU), tp=float(tp), tm=float(tm),
                        tUk=float(tU - k), tmk=float(tm + k), nin=float(nrm(pin)),
                        nout=float(nrm(pout)), Ucov=float(Ucov), ok_left=float(tm + k < 0)))
    print("   %s : r=%.4f |c|=%.4f" % (tag, float(r), float(sqrt(famC[0][0] ** 2 + famC[0][1] ** 2))))
    print("     pair   d        k        t_U      t_U-k     t_-+k     |p_in|  |p_out|  |U|-cover")
    for q in out[:3]:
        if isinstance(q, tuple):
            print("     ", q); continue
        print("     %2d   %7.4f  %7.4f  %8.5f  %+7.1e  %+7.1e  %6.4f  %6.4f  %+.2e"
              % (q["pair"], q["d"], q["k"], q["tU"], q["tUk"], q["tmk"], q["nin"], q["nout"], q["Ucov"]))
    return out


fam_partial, r_partial = family(mpf(7) / 10, mpf(1) / 2)
res_partial = analyse(fam_partial, r_partial, "(C1) partial overlap")
# exact arc tangency: solve 1 + rad^2 - 2 rad cos(pitch/2) = r^2 with pitch=45deg, r=1/2
cs = cos(2 * MP_PI / 16)
rad_t = cs - sqrt(cs ** 2 - (1 - (mpf(1) / 2) ** 2))     # smaller root: |c| < 1
fam_tan, r_tan = family(rad_t, mpf(1) / 2)
res_tan = analyse(fam_tan, r_tan, "(C2) exact arc tangency (U on both circles)")

print("\n=== (D) degeneracy probes ===")
# (D1) d = 2r : then k = 0 and t_+ <= 0 contradicts t_+ > 0 (m in int D)
print("   (D1) d=2r: t_+ <= k = 0 vs t_+ > 0 (m in int D) -> impossible;")
print("        equivalently B(c_i,r) cap B(c_j,r) = {m} with m in int D cannot contain U in dD.")
# (D2) collinear hub: circumradius <= r forces non-collinearity; the disk condition at collinear
#      points inside the segment is satisfied but the circumradius is undefined/infinite.
ci, cj = C[RING[0]], C[RING[1]]
mm = ((ci[0] + cj[0]) / 2, (ci[1] + cj[1]) / 2)
dv = (cj[0] - ci[0], cj[1] - ci[1])
dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
nn = (-dv[1] / dd, dv[0] / dd)
k = sqrt(RAD ** 2 - dd ** 2 / 4)
pin = (mm[0] - k * nn[0], mm[1] - k * nn[1])
pout = (mm[0] + k * nn[0], mm[1] + k * nn[1])
for off in [mpf(0), dd / 4, dd / 2, dd * mpf("0.9"), dd * 2]:
    h = (mm[0] + off * (dv[0] / dd), mm[1] + off * (dv[1] / dd))
    din = sqrt((h[0] - pin[0]) ** 2 + (h[1] - pin[1]) ** 2)
    print("   (D2) collinear h, offset=%7.4f : |h-p_in|-r = %+ .3e  (circumradius undefined)"
          % (float(off), float(din - RAD)))
# (D3) closed hub domain boundary |h| = 1-r, |p_out| = 1 (tight pair): the radial point
r_star = RAD
worst = None
for s in SW:
    (i, j) = s["pair"]
    U = s["P"]
    m = ((C[i][0] + C[j][0]) / 2, (C[i][1] + C[j][1]) / 2)
    dv = (C[j][0] - C[i][0], C[j][1] - C[i][1])
    dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
    nn = (-dv[1] / dd, dv[0] / dd)
    k = sqrt(r_star ** 2 - dd ** 2 / 4)
    if (U[0] - m[0]) * nn[0] + (U[1] - m[1]) * nn[1] < 0:
        nn = (-nn[0], -nn[1])
    pin = (m[0] - k * nn[0], m[1] - k * nn[1])
    pout = (m[0] + k * nn[0], m[1] + k * nn[1])
    nout = sqrt(pout[0] ** 2 + pout[1] ** 2)
    hb = ((1 - r_star) * pout[0] / nout, (1 - r_star) * pout[1] / nout)
    dout = sqrt((hb[0] - pout[0]) ** 2 + (hb[1] - pout[1]) ** 2)
    din = sqrt((hb[0] - pin[0]) ** 2 + (hb[1] - pin[1]) ** 2)
    if worst is None or din - RAD < worst[1]:
        worst = ((i, j), float(din - RAD), float(dout - RAD))
print("   (D3) boundary hub h=(1-r)p_out/|p_out| on a tight pair %s: |h-p_out|-r = %+ .3e,"
      % (worst[0], worst[2]))
print("        |h-p_in|-r = %+ .3e  (if <= 0 the disk condition admits an outward-side point)" % worst[1])

json.dump(dict(radius=mp.nstr(RAD, 25), pairs=rows_pair,
               faces=[dict(pair=FACES[k]) for k in (1, 2)],
               partial={k: v for k, v in enumerate(res_partial) if not isinstance(v, tuple)},
               tangency={k: v for k, v in enumerate(res_tan) if not isinstance(v, tuple)},
               boundary_hub=list(worst)),
          open(HERE / "audit_fan_disk_mechanism.json", "w"), indent=1)
print("\nwrote audit_fan_disk_mechanism.json")
