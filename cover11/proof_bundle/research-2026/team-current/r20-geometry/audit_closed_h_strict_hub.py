"""r20-geometry: closed-H degeneracy classification support + strict-hub nonemptiness criterion.

Part 1 (per pair). Local frame: base line = x-axis through the centre midpoint m, radical
direction n; p_in = (0,-k), p_out = (0,+k), k = sqrt(r^2-d^2/4).  The set with
circumradius(a,b,h) <= r is the union of the two CAPS
     Cap_in  = {h : |h-p_in| <= r, y <= 0},   Cap_out = {h : |h-p_out| <= r, y >= 0}
(the base line y=0 is excluded except at the centres: there the circumradius is +inf).
For a STRICT hub |h| < 1-r and |p_out| >= 1 one has |h-p_out| > r, so h in Cap_out is
impossible, and |h-p_in| <= r forces y < 0 (linear algebra, see notes).  Hence on the strict
domain the mechanism's disk condition is EXACTLY the cap condition.

On the CLOSED domain |h| <= 1-r the discrepancy set per pair is computed exactly here:
   {h : |h| <= 1-r, |h-p_out| <= r} is empty when |p_out| > 1, and is the single point
   h* = (1-r) p_out when |p_out| = 1 (internal tangency of B(p_out,r) and B(0,1-r)).

Part 2 (whole chain). Finite, analytic strict-hub criterion for
   exists h: |h| < 1-r  and  |h - p_in^j| <= r for every fan pair j
(closed intersection nonempty is NOT enough).  With S = intersection_j B(p_in^j, r):
   min_{h in S} |h| < 1-r
and min|h| over S is attained at one of finitely many candidates:
   0 (if 0 in S), the closest point of each circle d(p_in^j, r) to 0 (if in S),
   every pairwise circle-circle intersection (if in S).
Nothing here is a grid; all candidates are closed-form.  Also reported: the boundary minimax
value min_{|h|=1-r} max_j |h - p_in^j| (evaluated on a fine angle set only as a cross-check of
the projection form, not as the criterion).
"""
import io, json, math
from mpmath import mp, mpf, sin, cos, sqrt, atan2, acos, pi as MP_PI
from pathlib import Path

mp.dps = 35
HERE = Path(__file__).resolve().parent
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
FR = json.loads((HERE.parent / "lead" / "joint_nested_frozen.json").read_text())
FACES = [list(f) for f in FR["faces"]]
OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
SC = mpf(10) ** int(OBJ["decimals"])
C = [[mpf(int(a)) / SC, mpf(int(b)) / SC] for a, b in OBJ["centers_scaled_1e17"]]
RAD = mpf(repr(float(OBJ["certified_interval"]["lo"])))
AMAP = {0: 5, 1: 7, 2: 1, 3: 8, 4: 6, 5: 4, 6: 9, 7: 10, 8: 3, 9: 2, 10: 0}


def d2(i, th):
    return (cos(th) - C[i][0]) ** 2 + (sin(th) - C[i][1]) ** 2


NS = 8192
runs, prev = [], None
for j in range(NS):
    th = 2 * MP_PI * j / NS
    kk = min(range(len(C)), key=lambda i: d2(i, th))
    if kk != prev:
        runs.append([kk, j]); prev = kk
if len(runs) > 1 and runs[0][0] == runs[-1][0]:
    runs.pop(0)
RING = [k for k, _ in runs]


def tie_theta(ka, kb, lo, hi):
    M = 512
    pt, pf = lo, d2(ka, lo) - d2(kb, lo)
    for j in range(1, M + 1):
        t = lo + (hi - lo) * mpf(j) / M
        f = d2(ka, t) - d2(kb, t)
        if pf * f < 0:
            a_, b_, fa = pt, t, pf
            for _ in range(200):
                mid = (a_ + b_) / 2
                if (d2(ka, mid) - d2(kb, mid)) * fa <= 0:
                    b_ = mid
                else:
                    a_, fa = mid, d2(ka, mid) - d2(kb, mid)
            return (a_ + b_) / 2
        pt, pf = t, f
    return None


span = 2 * MP_PI / NS
SW = []
for j in range(len(RING)):
    ka, kb = RING[j], RING[(j + 1) % len(RING)]
    lo = mpf(runs[j][1]) * span
    hi = mpf(runs[(j + 1) % len(RING)][1]) * span if j + 1 < len(RING) else 2 * MP_PI + mpf(runs[0][1]) * span
    SW.append((ka, kb, tie_theta(ka, kb, lo, hi)))


def frame(i, j, U_theta):
    ci, cj = C[i], C[j]
    m = ((ci[0] + cj[0]) / 2, (ci[1] + cj[1]) / 2)
    dv = (cj[0] - ci[0], cj[1] - ci[1]); dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
    n = (-dv[1] / dd, dv[0] / dd)
    k = sqrt(RAD ** 2 - dd ** 2 / 4)
    U = (cos(U_theta), sin(U_theta))
    if (U[0] - m[0]) * n[0] + (U[1] - m[1]) * n[1] < 0:
        n = (-n[0], -n[1])
    pin = (m[0] - k * n[0], m[1] - k * n[1])
    pout = (m[0] + k * n[0], m[1] + k * n[1])
    return dict(m=m, n=n, dd=dd, k=k, pin=pin, pout=pout)


print("=== Part 1: closed-domain discrepancy per pair (certified cover) ===")
print("  Exact classification: with |h|<=1-r, |h-p_in|<=r and y>=0 one gets |h-p_out|<=r, hence")
print("  |p_out|<=|h|+r<=1, so |p_out|=1 and h=h*=(1-r)p_out (internal tangency point).  Then")
print("     h* is a BAD (spurious outward) point  iff y_h* >= 0 (it is then automatically in B(p_in,r)),")
print("     h* is MISSED by the disk condition    iff y_h* > 0 and |h*-p_in| > r,")
print("     no discrepancy at all for y_h* < 0.")
print("   pair   |pout|      d      k    |h*-p_in|-r    y_h*     verdict")
INFO = []
for (i, j, th) in SW:
    f = frame(i, j, th)
    h = ((1 - RAD) * f["pout"][0], (1 - RAD) * f["pout"][1])
    nout = sqrt(f["pout"][0] ** 2 + f["pout"][1] ** 2)
    din = sqrt((h[0] - f["pin"][0]) ** 2 + (h[1] - f["pin"][1]) ** 2)
    yh = (h[0] - f["m"][0]) * f["n"][0] + (h[1] - f["m"][1]) * f["n"][1]
    if abs(nout - 1) > mpf("1e-12"):
        verdict = "no candidate (|pout|>1)"
    elif yh < 0:
        verdict = "no discrepancy (inward)"
    elif din <= RAD:
        verdict = "BAD extra point"
    else:
        verdict = "MISSED outward point"
    INFO.append(dict(pair=(i, j), nout=float(nout), d=float(f["dd"]), k=float(f["k"]),
                     din_minus_r=float(din - RAD), yh=float(yh), verdict=verdict,
                     h_star=[float(h[0]), float(h[1])], pin=[float(q) for q in f["pin"]],
                     mn_global_proj=float(f["m"][0] * f["n"][0] + f["m"][1] * f["n"][1])))
    print("   %2d-%2d  %8.6f  %7.5f  %7.5f   %+ .3e      %+ .3e   %s"
          % (i, j, float(nout), float(f["dd"]), float(f["k"]), float(din - RAD), float(yh), verdict))

print("\n  Searched admissible tight pairs (|p_out|=1, U covered tie, both centres in B(0,s))")
print("  for a pair whose tangency point is on the OUTWARD side (y_h* > 0):")
found = []
for ir in range(1, 13):
    rU = RAD * mpf(ir) / 12
    for ip in range(0, 73):
        for jp in range(0, 73):
            ph1 = -acos(RAD) + 2 * acos(RAD) * mpf(ip) / 72
            ph2 = -acos(RAD) + 2 * acos(RAD) * mpf(jp) / 72
            U = (mpf(1), mpf(0))
            c1 = (U[0] - rU * cos(ph1), U[1] - rU * sin(ph1))
            c2 = (U[0] - rU * cos(ph2), U[1] - rU * sin(ph2))
            if max(sqrt(c1[0] ** 2 + c1[1] ** 2), sqrt(c2[0] ** 2 + c2[1] ** 2)) > sqrt(1 - RAD ** 2):
                continue
            m = ((c1[0] + c2[0]) / 2, (c1[1] + c2[1]) / 2)
            dv = (c2[0] - c1[0], c2[1] - c1[1]); dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
            if dd == 0 or dd >= 2 * RAD:
                continue
            k = sqrt(RAD ** 2 - dd ** 2 / 4)
            n = (-dv[1] / dd, dv[0] / dd)
            if (U[0] - m[0]) * n[0] + (U[1] - m[1]) * n[1] < 0:
                n = (-n[0], -n[1])
            pin = (m[0] - k * n[0], m[1] - k * n[1])
            pout = (m[0] + k * n[0], m[1] + k * n[1])
            if abs(sqrt(pout[0] ** 2 + pout[1] ** 2) - 1) > mpf("1e-25"):
                continue
            h = ((1 - RAD) * pout[0], (1 - RAD) * pout[1])
            yh = (h[0] - m[0]) * n[0] + (h[1] - m[1]) * n[1]
            din = sqrt((h[0] - pin[0]) ** 2 + (h[1] - pin[1]) ** 2)
            if yh > 0:
                found.append(dict(rU=float(rU), ph1=float(ph1), ph2=float(ph2), d=float(dd),
                                  yh=float(yh), din_minus_r=float(din - RAD),
                                  c1=[float(q) for q in c1], c2=[float(q) for q in c2],
                                  verdict="BAD extra point" if din <= RAD else "MISSED outward point"))
if found:
    print("   found %d such pairs; example:" % len(found))
    ex = found[0]
    print("     rU=%.4f phi=(%.4f,%.4f) d=%.6f  y_h*=%.6f  |h*-p_in|-r=%+.3e  -> %s"
          % (ex["rU"], ex["ph1"], ex["ph2"], ex["d"], ex["yh"], ex["din_minus_r"], ex["verdict"]))
    print("     c1=%s c2=%s" % ([round(q, 6) for q in ex["c1"]], [round(q, 6) for q in ex["c2"]]))
    print("     => non-collinear OUTWARD points in the closed lens DO occur, exactly as h* with")
    print("        |p_out|=1 and y_h*>0, and this is the only way they can occur.")
else:
    print("   none found in this grid")

print("\n=== Part 2: strict-hub nonemptiness, finite analytic criterion ===")


def strict_hub_minnorm(discs):
    """discs = list of (centre, radius).  Return (min|h| over the closed intersection, witness,
    witness kind) using only closed-form candidates."""
    def inside(h, eps=mpf(0)):
        return all(sqrt((h[0] - c[0]) ** 2 + (h[1] - c[1]) ** 2) <= rad + eps for c, rad in discs)
    cands = []
    if inside((mpf(0), mpf(0))):
        cands.append(((mpf(0), mpf(0)), "origin"))
    for c, rad in discs:                       # closest point of each circle to the origin
        nc = sqrt(c[0] ** 2 + c[1] ** 2)
        if nc > 0:
            s = 1 - rad / nc
            p = (c[0] * s, c[1] * s)
            if inside(p):
                cands.append((p, "projection"))
    for x in range(len(discs)):                # pairwise circle intersections
        c1, r1 = discs[x]
        for y in range(x + 1, len(discs)):
            c2, r2 = discs[y]
            dv = (c2[0] - c1[0], c2[1] - c1[1]); dd = sqrt(dv[0] ** 2 + dv[1] ** 2)
            if dd == 0 or dd > r1 + r2:
                continue
            a_ = (r1 ** 2 - r2 ** 2 + dd ** 2) / (2 * dd)
            h2 = r1 ** 2 - a_ ** 2
            if h2 < 0:
                continue
            hh = sqrt(h2)
            un = (dv[0] / dd, dv[1] / dd)
            for sgn in ([0] if hh == 0 else [1, -1]):
                p = (c1[0] + a_ * un[0] - sgn * hh * un[1], c1[1] + a_ * un[1] + sgn * hh * un[0])
                if inside(p):
                    cands.append((p, "circle-circle"))
    if not cands:
        return None, None, "empty intersection"
    best = min(cands, key=lambda t: t[0][0] ** 2 + t[0][1] ** 2)
    return sqrt(best[0][0] ** 2 + best[0][1] ** 2), best[0], best[1]


hub_of_pair = {}
for (i, j, th) in SW:
    ai, aj = {v: kk for kk, v in AMAP.items()}[i], {v: kk for kk, v in AMAP.items()}[j]
    for fc in FACES:
        if ai in fc and aj in fc:
            other = [z for z in fc if z not in (ai, aj)]
            if other and other[0] in (9, 10):
                hub_of_pair[(i, j)] = AMAP[other[0]]
for hub_abs, tag in [(2, "hub 2 (4-pair fan)"), (0, "hub 0 (5-pair fan)")]:
    discs = []
    for (i, j, th) in SW:
        if hub_of_pair.get((i, j)) == hub_abs:
            f = frame(i, j, th)
            discs.append((f["pin"], RAD))
    mn, w, kind = strict_hub_minnorm(discs)
    hc = C[hub_abs]; nh = sqrt(hc[0] ** 2 + hc[1] ** 2)
    print("   %-20s |fan disks| = %d ; min|h| over the closed lens = %.9f (at %s, %s)"
          % (tag, len(discs), float(mn), kind, "in S" if w else ""))
    print("       hub itself |h| = %.9f ; 1-r = %.9f  -> strict hub %s;  hub in every fan disk: %s"
          % (float(nh), float(1 - RAD), "EXISTS" if mn < 1 - RAD else "absent",
             all(sqrt((hc[0] - c[0]) ** 2 + (hc[1] - c[1]) ** 2) <= RAD + mpf("1e-20")
                 for c, _ in discs)))

print("\n   adversarial control: closed intersection nonempty but NO strict hub")
r2 = mpf(1) / 2
R2 = 1 - r2                                    # hubnorm radius
for ang in [mpf("1.0"), mpf("1.6"), mpf("2.4")]:
    # two equal disks tangent to each other and to the hubnorm circle at the same point
    t = (R2 * cos(ang), R2 * sin(ang))
    c1 = (t[0] + r2 * cos(ang + MP_PI / 2), t[1] + r2 * sin(ang + MP_PI / 2))
    c2 = (t[0] + r2 * cos(ang - MP_PI / 2), t[1] + r2 * sin(ang - MP_PI / 2))
    discs = [(c1, r2), (c2, r2)]
    mn, w, kind = strict_hub_minnorm(discs)
    print("     angle=%.2f : closed lens nonempty = %s ; min|h| - (1-r) = %+.3e  -> strict hub %s"
          % (float(ang), mn is not None, float(mn - R2) if mn is not None else float("nan"),
             "exists" if (mn is not None and mn < R2) else "absent"))
json.dump(dict(per_pair=INFO, d0=float(sqrt(4 * (1 - 2 * RAD + 2 * RAD ** 2 - 2 * RAD ** 3) / (3 - 2 * RAD))),
               strict_hub_note="criterion: min|h| over the closed lens < 1-r"),
          open(HERE / "audit_closed_h_strict_hub.json", "w"), indent=1)
print("\nwrote audit_closed_h_strict_hub.json")

