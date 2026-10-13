"""r20-geometry Round-4: strict-hub finite disjunction (Theorem A / Theorem B) — support computation.

NO grids, NO optimisation, NO sampling: every number below comes from a closed-form finite
candidate set (Theorem A) or from the finite Helly disjunction of pairs/triples (Theorem B).
Nothing here proves the theorems (they are analytic, see STRICT-HUB-FINITE-DISJUNCTION.md);
this script (i) instantiates them on the certified q0(6,7) object, (ii) cross-checks the two
independent decision routes against each other, (iii) runs hand-constructed exact controls for
every disjunct class and for the two CQ-failure degeneracies.

Object (n11/upper/certified_object.json, exact-rational centres, certified radius interval):
  11 equal radius-r disks; ring sites {1,3,4,5,6,7,8,9,10}, hubs {0,2} (certified-object labels);
  lead labels: rings 0..8, hubs 9,10.  Absolute->lead: 0->5,1->7,2->1,3->8,4->6,5->4,6->9,7->10,8->3,9->2,10->0.
  Fan of hub 2 (lead 9): 4 edges, pairs (5,7),(7,1),(1,8),(8,6)   [lead chain 0-1-2-3-4]
  Fan of hub 0 (lead 10): 5 edges, pairs (6,4),(4,9),(9,10),(10,3),(3,5) [lead chain 4-5-6-7-8-0]
  shared "central" ring endpoints: absolute 5 (=lead 0) and absolute 6 (=lead 4).

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/strict_hub_finite_disjunction.py
"""
import io, json
from mpmath import mp, mpf, sqrt, cos, sin, pi as MP_PI
from pathlib import Path

mp.dps = 50
HERE = Path(__file__).resolve().parent
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


def V(x, y):
    return (mpf(x), mpf(y))


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def mul(s, a):
    return (s * a[0], s * a[1])


def nrm(a):
    return sqrt(a[0] ** 2 + a[1] ** 2)


def n2(a):
    return a[0] ** 2 + a[1] ** 2


def fl(x):
    """float for JSON/printing; None for +/-inf."""
    if x is None:
        return None
    try:
        f = float(x)
    except (OverflowError, ValueError):
        return None
    return f


# ---------------------------------------------------------------- Theorem A
def circle_intersections(c1, r1, c2, r2):
    dv = sub(c2, c1)
    d = nrm(dv)
    if d == 0:
        return []
    if d > r1 + r2 or d < abs(r1 - r2):
        return []
    a = (r1 ** 2 - r2 ** 2 + d ** 2) / (2 * d)
    h2 = r1 ** 2 - a ** 2
    if h2 < 0:
        return []
    hh = sqrt(h2)
    u = (dv[0] / d, dv[1] / d)
    base = add(c1, mul(a, u))
    if hh == 0:
        return [base]
    perp = (-u[1], u[0])
    return [add(base, mul(hh, perp)), sub(base, mul(hh, perp))]


TOL = mpf("1e-30")          # tolerance for weak-inequality tests; all genuine margins here are >=1e-4,
                            # equality controls are reported with their raw rounding-level slack


def min_norm(discs):
    """Theorem A: min |h| over S = intersection of closed disks (centre, radius).
    Candidates: origin; projection of each centre onto its own circle; pairwise circle-circle
    intersections.  Returns (min|h| or None, witness, kind, ncand).  None <=> S empty.
    (Weak tests carry the documented tolerance TOL; exact/interval arithmetic is needed only if a
    certificate is built directly on an equality case.)"""
    ds = []
    for c, rad in discs:                                    # dedupe identical disks
        if not any(n2(sub(c, c0)) == 0 and rad == rad0 for c0, rad0 in ds):
            ds.append((c, rad))

    def inside(h):
        return all(nrm(sub(h, c)) <= rad + TOL for c, rad in ds)

    cands = []
    o = (mpf(0), mpf(0))
    if inside(o):
        cands.append((o, "origin"))
    for i, (c, rad) in enumerate(ds):
        nc = nrm(c)
        if nc == 0:
            continue
        p = mul(1 - rad / nc, c)
        if inside(p):
            cands.append((p, "projection#%d" % i))
    for i in range(len(ds)):
        for j in range(i + 1, len(ds)):
            for z in circle_intersections(ds[i][0], ds[i][1], ds[j][0], ds[j][1]):
                if inside(z):
                    cands.append((z, "circle-circle#%d-%d" % (i, j)))
    if not cands:
        return None, None, "empty (no candidate)", 0
    best = min(cands, key=lambda t: n2(t[0]))
    return nrm(best[0]), best[0], best[1], len(cands)


# ---------------------------------------------------------------- MEC of 3 points
def mec3(pts):
    """Minimum enclosing circle of three points.  Returns (radius, centre, branch).
    branch = 'diameter' (obtuse/right: longest side is the diameter) or 'circumcircle'."""
    A, B, C = pts
    a2, b2, c2 = n2(sub(B, C)), n2(sub(C, A)), n2(sub(A, B))
    dA, dA2 = sub(B, A), sub(C, A)
    dB, dB2 = sub(A, B), sub(C, B)
    dC, dC2 = sub(A, C), sub(B, C)
    ip = [dA[0] * dA2[0] + dA[1] * dA2[1],
          dB[0] * dB2[0] + dB[1] * dB2[1],
          dC[0] * dC2[0] + dC[1] * dC2[1]]
    if min(ip) <= 0:                                        # obtuse or right
        sides = [(a2, B, C), (b2, C, A), (c2, A, B)]
        s2, P, Q = max(sides, key=lambda t: t[0])
        cen = mul(mpf(1) / 2, add(P, Q))
        return sqrt(s2) / 2, cen, "diameter"
    al = a2 * (b2 + c2 - a2)
    be = b2 * (c2 + a2 - b2)
    ga = c2 * (a2 + b2 - c2)
    cen = mul(1 / (al + be + ga), add(add(mul(al, A), mul(be, B)), mul(ga, C)))
    rad = nrm(sub(cen, A))
    assert abs(nrm(sub(cen, B)) - rad) < mpf("1e-40") and abs(nrm(sub(cen, C)) - rad) < mpf("1e-40")
    return rad, cen, "circumcircle"


# ---------------------------------------------------------------- Theorem B
def pair_mu(p_j, p_k, r):
    """mu_jk = min{|h| : h in closed lens} ; None means the lens is EMPTY (mu = +inf)."""
    if nrm(sub(p_j, p_k)) > 2 * r + TOL:
        return None
    mn, w, kind, nc = min_norm([(p_j, r), (p_k, r)])
    assert mn is not None
    return mn


def disjunction(pins, r, rho):
    """Theorem B report.  Returns dict with slacks and per-class witness values.
    fires:  W1 (|p_j| >= rho+r)  <=> w1_slack <= 0
            W2/W3 pair lens misses the open ball (mu_jk >= rho) <=> pair_slack <= 0
            W4   3 disks empty (psi_jkl > r)                      <=> triple_slack < 0
    Equality cases are reported via the raw slack (rounding-level, <=TOL, not a margin)."""
    m = len(pins)
    w1_slack = (rho + r) - max((nrm(p) for p in pins), default=mpf(0))
    pair = {}
    for i in range(m):
        for j in range(i + 1, m):
            pair[(i, j)] = pair_mu(pins[i], pins[j], r)
    pair_slack = mpf("inf")
    pair_argmin = None
    for ij, mu in pair.items():
        if mu is None:
            pair_slack = mpf("-inf")                       # empty lens: a 2-set witness
            pair_argmin = ij
            break
        if rho - mu < pair_slack:
            pair_slack, pair_argmin = rho - mu, ij
    tri = {}
    for i in range(m):
        for j in range(i + 1, m):
            for k in range(j + 1, m):
                tri[(i, j, k)] = mec3([pins[i], pins[j], pins[k]])
    triple_slack = mpf("inf")
    tri_argmin = None
    for ijk, (psi, cen, br) in tri.items():
        if r - psi < triple_slack:
            triple_slack, tri_argmin = r - psi, ijk
    fires = {"W1": w1_slack <= TOL, "W_pair": pair_slack <= TOL, "W4": triple_slack < -TOL}
    return dict(w1_slack=w1_slack, pair_slack=pair_slack, triple_slack=triple_slack,
                pair=pair, tri=tri, pair_argmin=pair_argmin, tri_argmin=tri_argmin,
                fires=fires, no_hub=any(fires.values()))


def report_case(tag, pins, r, rho, note=""):
    mn, w, kind, nc = min_norm([(p, r) for p in pins])
    dj = disjunction(pins, r, rho)
    exists_A = (mn is not None) and (mn < rho - TOL)
    agree = (exists_A == (not dj["no_hub"]))
    say("  [%s]" % tag)
    say("    m=%d r=%s rho=%s %s" % (len(pins), mp.nstr(r, 12), mp.nstr(rho, 12), note))
    say("    A) min|h| over S = %s  (kind %s, %d candidates);  rho - min = %s  -> strict hub %s"
        % (mp.nstr(mn, 20) if mn is not None else "S = EMPTY", kind, nc,
           mp.nstr(rho - mn, 6) if mn is not None else "-inf",
           "EXISTS" if exists_A else "ABSENT"))
    say("    B) slacks: W1 %s | pair(mu>=rho) %s | triple(psi>r) %s  -> no-hub %s ; routes agree: %s"
        % (mp.nstr(dj["w1_slack"], 6), mp.nstr(dj["pair_slack"], 6), mp.nstr(dj["triple_slack"], 6),
           dj["no_hub"], agree))
    if dj["pair_argmin"] is not None and dj["pair_slack"] < mpf("1e-12"):
        say("       tight pair %s: mu = %s (rho - mu = %s)"
            % (dj["pair_argmin"], mp.nstr(dj["pair"][dj["pair_argmin"]], 20), mp.nstr(dj["pair_slack"], 6)))
    if dj["tri_argmin"] is not None:
        psi, cen, br = dj["tri"][dj["tri_argmin"]]
        flag = "   <-- EQUALITY class: nonempty triple with psi = r" if abs(dj["triple_slack"]) < mpf("1e-12") else ""
        say("       tight triple %s: psi = %s (branch %s), r - psi = %s%s"
            % (dj["tri_argmin"], mp.nstr(psi, 20), br, mp.nstr(dj["triple_slack"], 6), flag))
    if not agree:
        raise SystemExit("ROUTE DISAGREEMENT on %s" % tag)
    return dict(tag=tag, m=len(pins), r=str(r), rho=str(rho), min_norm=fl(mn), kind=kind, ncand=nc,
                exists=bool(exists_A), no_hub=bool(dj["no_hub"]),
                w1_slack=fl(dj["w1_slack"]), pair_slack=fl(dj["pair_slack"]),
                triple_slack=fl(dj["triple_slack"]), pair_argmin=dj["pair_argmin"],
                tri_argmin=dj["tri_argmin"], fires={k: bool(v) for k, v in dj["fires"].items()})


# ================================================================ Part A: certified object
say("=" * 100)
say("PART A.  Certified q0(6,7) object: nine inner intersections, both fan chains (no grid, no hub solve)")
say("=" * 100)
OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
SC = mpf(10) ** int(OBJ["decimals"])
C = [V(mpf(int(a)) / SC, mpf(int(b)) / SC) for a, b in OBJ["centers_scaled_1e17"]]
R_LO = mpf(OBJ["certified_interval"]["lo"])
R_HI = mpf(OBJ["certified_interval"]["hi"])
say("  r in [%s , %s] (width %s)" % (mp.nstr(R_LO, 30), mp.nstr(R_HI, 30), OBJ["certified_interval"]["width"]))
say("  hub norms: |c_0| = %s (lead 10), |c_2| = %s (lead 9)"
    % (mp.nstr(nrm(C[0]), 20), mp.nstr(nrm(C[2]), 20)))
say("  ring norms (min,max) = (%s, %s)  vs rho = 1-r = %s"
    % (mp.nstr(min(nrm(C[i]) for i in [1, 3, 4, 5, 6, 7, 8, 9, 10]), 15),
       mp.nstr(max(nrm(C[i]) for i in [1, 3, 4, 5, 6, 7, 8, 9, 10]), 15), mp.nstr(1 - R_LO, 15)))

PAIRS = [(5, 7), (7, 1), (1, 8), (8, 6), (6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]   # cyclic, recorded
FAN4 = [(5, 7), (7, 1), (1, 8), (8, 6)]                    # hub absolute 2 (lead 9)
FAN5 = [(6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]          # hub absolute 0 (lead 10)


def frame(i, j, r):
    ci, cj = C[i], C[j]
    m = ((ci[0] + cj[0]) / 2, (ci[1] + cj[1]) / 2)
    dv = sub(cj, ci)
    d = nrm(dv)
    n = (-dv[1] / d, dv[0] / d)
    k = sqrt(r ** 2 - d ** 2 / 4)
    p1 = sub(m, mul(k, n))
    p2 = add(m, mul(k, n))
    return ((p1, p2) if nrm(p1) < nrm(p2) else (p2, p1)), d, k


REC = json.load(io.open(HERE / "audit_closed_h_strict_hub.json", encoding="utf-8"))
rec_pin = {tuple(e["pair"]): e["pin"] for e in REC["per_pair"]}
say("  per-edge pins (absolute pair, |p_in|, |p_out|, max |pin - recorded float64|):")
PIN = {}
for (i, j) in PAIRS:
    (pin, pout), d, k = frame(i, j, R_LO)
    PIN[(i, j)] = pin
    diff = max(abs(fl(pin[0]) - rec_pin[(i, j)][0]), abs(fl(pin[1]) - rec_pin[(i, j)][1]))
    say("    %2d-%2d  |p_in|=%-22s |p_out|=%-24s  cross-check %s   d=%s  k=%s"
        % (i, j, mp.nstr(nrm(pin), 15), mp.nstr(nrm(pout), 18), "%.1e" % diff, mp.nstr(d, 10), mp.nstr(k, 10)))

def angular_gap_report(pins, hub, r, rho, tol=mpf("1e-12")):
    """Escape-direction / singleton test at the hub (closed convexity, no grid).
    Let W = {p_j - hub : |hub-p_j| = r} (active pins).  A direction v leaves the hub inside S
    iff v.w > 0 for all w in W; such v exists iff 0 not in conv(W), iff the angles of W do not
    surround the full circle iff max cyclic gap <= pi.  Hence:
        max gap <= pi   ==>  S = {hub}  (no Slater point, and the closed intersection is a
                                          singleton provided the saturations are exact);
        max gap >  pi   ==>  an escape direction exists, S is nondegenerate at the hub, and a
                             Slater point (strictly inside every disk, |h| < rho) can be tested
                             explicitly in the escape cone.
    Returns (n_active, gaps_deg, surrounded, slater_point_or_None)."""
    act = [p for p in pins if abs(nrm(sub(p, hub)) - r) <= tol]
    dirs = [sub(p, hub) for p in act]
    if not dirs:
        return 0, [], None, None
    angs = sorted([mp.atan2(d[1], d[0]) for d in dirs])
    gaps = []
    for i in range(len(angs)):
        nxt = angs[i + 1] if i + 1 < len(angs) else angs[0] + 2 * MP_PI
        gaps.append(nxt - angs[i])
    gmax = max(gaps)
    ig = gaps.index(gmax)
    surrounded = (gmax <= MP_PI)
    slater = None
    if not surrounded:                                     # W lies in an arc of span < pi: the dual
        a0 = angs[ig]                                      # cone is the opposite arc, centred at
        v = (cos(a0 + gmax / 2 + MP_PI), sin(a0 + gmax / 2 + MP_PI))   # the cluster midpoint
        for e in ("1e-3", "1e-4"):                         # two explicit step sizes
            cand = add(hub, mul(mpf(e), v))
            if (nrm(cand) < rho and all(nrm(sub(cand, p)) < r for p in pins)):
                slater = cand
                break
    return len(act), [float(g * 180 / MP_PI) for g in gaps], surrounded, slater


CASES = {}
for r, tag in ((R_LO, "lo"), (R_HI, "hi")):
    rho = 1 - r
    for fan, hub in ((FAN4, 2), (FAN5, 0)):
        pins = [PIN[p] for p in fan]
        hc = C[hub]
        dmargin = min(r - nrm(sub(hc, p)) for p in pins)
        rec = report_case("certified %s, hub abs %d (fan m=%d)" % (tag, hub, len(fan)), pins, r, rho)
        say("      hub |h| = %s ; min_j (r - |h - p_j|) = %s (hub inside every fan disk: %s)"
            % (mp.nstr(nrm(hc), 20), mp.nstr(dmargin, 6), dmargin >= 0))
        na, gaps, surr, slater = angular_gap_report(pins, hc, r, rho)
        say("      active pins at the hub: %d of %d ; angular gaps (deg): %s"
            % (na, len(fan), ", ".join("%.2f" % g for g in gaps)))
        if surr:
            say("      max gap <= 180 deg  ==>  0 in conv(p_j - hub)  ==>  S = {hub}: closed"
                " intersection is the SINGLETON {hub} (at the object's saturation level),"
                " NO Slater point; the strict verdict comes from min|h| = |hub| < rho only.")
        else:
            say("      max gap > 180 deg  ==>  escape direction exists (S not a singleton);"
                " explicit Slater point with |h| = %s < rho and strict disk margins: %s"
                % (mp.nstr(nrm(slater), 12) if slater is not None else "NOT FOUND",
                   "yes" if slater is not None else "no"))
        rec["hub_norm"] = fl(nrm(hc))
        rec["hub_disk_margin"] = fl(dmargin)
        rec["pins_active_at_hub"] = na
        rec["angular_gaps_deg"] = gaps
        rec["closed_intersection_singleton"] = bool(surr)
        rec["slater_point_found"] = (slater is not None)
        CASES[rec["tag"]] = rec
    # whole-chain (all nine edges, no hub grouping) as an over-constrained cross-check
    pins9 = [PIN[p] for p in PAIRS]
    mn, w, kind, nc = min_norm([(p, r) for p in pins9])
    say("  (cross-check, all nine edges in ONE intersection: min|h| = %s, %s -> %s)"
        % ("S = EMPTY" if mn is None else mp.nstr(mn, 20), kind,
           "consistent: no joint hub required, the two fans are served separately" if mn is None or mn >= rho
           else "WARNING: single hub would suffice"))

# ================================================================ Part B: controls
say("")
say("=" * 100)
say("PART B.  Constructed exact controls: every disjunct class + both CQ-failure degeneracies")
say("=" * 100)
CTRL = []
# B1 two disjoint disks (W2 pair witness, 2-set)
r, rho = mpf(1) / 2, mpf(1)
CTRL.append(report_case("B1 pair-disjoint (2-set witness W2)", [V(0, 0), V("1.2", 0)], r, rho,
                        "|p1-p2|=1.2>2r=1"))
# B2 one disk tangent to the open norm ball from outside (W1 with EQUALITY, >= is essential)
r, rho = mpf(1) / 2, mpf(1)
CTRL.append(report_case("B2 ball-disk tangency (W1 equality)", [V("1.5", 0)], r, rho,
                        "|p1| = 1.5 = rho+r exactly"))
CTRL.append(report_case("B2' ball-disk strict (W1 strict)", [V("1.6", 0)], r, rho, "|p1| = 1.6 > 1.5"))
# B3 two tangent disks touching the norm circle at one point (closed singleton, CQ-fail).
#     rational construction: r = rho = 1/2, tangency point t = (1/2,0), centres (1/2,+-1/2).
r, rho = mpf(1) / 2, mpf(1) / 2
t = (mpf(1) / 2, mpf(0))
c1, c2 = add(t, (mpf(0), r)), add(t, (mpf(0), -r))
CTRL.append(report_case("B3 tangent lens touching |h|=rho (closed singleton, CQ fails)",
                        [c1, c2], r, rho, "lens = {t}, |t| = rho exactly -> pair witness with equality"))
# B3' same but lens strictly outside the open ball
t = (mpf("1.2"), mpf(0))
c1, c2 = add(t, (mpf(0), r)), add(t, (mpf(0), -r))
CTRL.append(report_case("B3' lens strictly outside the open ball (pair witness strict)", [c1, c2], r, rho,
                        "pair lens = {t}, |t| = 1.2 > rho"))
# B3'' same but lens strictly inside -> strict hub exists
t = (mpf("0.3"), mpf(0))
c1, c2 = add(t, (mpf(0), r)), add(t, (mpf(0), -r))
CTRL.append(report_case("B3'' lens strictly inside (strict hub exists, no witness)", [c1, c2], r, rho,
                        "pair lens = {t}, |t| = 0.3 < rho"))
# B4 three disks with SINGLETON intersection inside the ball: strict hub exists, NO Slater point
r, rho = mpf(1) / 2, mpf(1) / 2
for qq, tag in ((mpf("0.3"), "inside"), (mpf("0.6"), "outside")):
    q = (qq, mpf(0))
    us = [(cos(2 * MP_PI * k / 3), sin(2 * MP_PI * k / 3)) for k in range(3)]
    assert abs(us[0][0] + us[1][0] + us[2][0]) < mpf("1e-45")      # sum of the three unit directions = 0
    pins = [add(q, mul(r, u)) for u in us]
    CTRL.append(report_case("B4 3 disks, S = {q} singleton, |q|=%s (CQ fails)" % qq, pins, r, rho,
                            "sum-condition forces S = {q}; no Slater point either way"))
# B5 triple-empty with pairwise intersections (W4 witness, 3-set, no norm ball needed)
r, rho = mpf(1), mpf(1)
s = mpf("1.9")
Rc = s / sqrt(3)                                                    # circumradius, acute triangle
us = [(cos(2 * MP_PI * k / 3), sin(2 * MP_PI * k / 3)) for k in range(3)]
pins = [mul(Rc, u) for u in us]
psi, cen, br = mec3(pins)
say("      (B5 MEC check: psi=%s branch=%s, |centre|=%s, side=%s, r=%s)"
    % (mp.nstr(psi, 20), br, mp.nstr(nrm(cen), 10), mp.nstr(s, 10), mp.nstr(r, 10)))
CTRL.append(report_case("B5 triple empty, pairwise nonempty (3-set witness W4)", pins, r, rho,
                        "psi = side/sqrt3 = %s > r" % mp.nstr(psi, 10)))
# B6 obtuse triangle: MEC = longest side diameter, triple NONempty, projection witness exists
r, rho = mpf("1.4"), mpf("1.3")
pins = [V(0, 0), V(1, 0), V("2.5", "0.05")]
psi, cen, br = mec3(pins)
say("      (B6 MEC check: psi=%s branch=%s, |centre|=%s; longest side/2=%s)"
    % (mp.nstr(psi, 20), br, mp.nstr(nrm(cen), 10), mp.nstr(nrm(sub(V("2.5", "0.05"), V(0, 0))) / 2, 20)))
CTRL.append(report_case("B6 obtuse MEC branch, triple nonempty (projection witness)", pins, r, rho,
                        "psi = longest/2 = %s <= r" % mp.nstr(psi, 10)))
# B7 acute MEC branch, triple contains the origin
r, rho = mpf("1.2"), mpf(1)
pins = [mul(Rc, u) for u in us]
psi, cen, br = mec3(pins)
CTRL.append(report_case("B7 acute MEC branch, 0 in S (origin witness)", pins, r, rho,
                        "psi = %s <= r, centre = origin" % mp.nstr(psi, 10)))
# B8 three disks in a line, disjoint triple (diameter branch of W4)
r, rho = mpf(1), mpf(1)
pins = [V(0, 0), V("1.5", 0), V("3.0", 0)]
CTRL.append(report_case("B8 collinear triple (diameter MEC)", pins, r, rho, "psi = 1.5 > r"))

say("")
say("  control summary: %d cases, all route-agreement checks passed" % len(CTRL))
for c in CTRL:
    say("    %-62s exists=%-5s no_hub=%-5s fires=%s"
        % (c["tag"][:62], c["exists"], c["no_hub"], ",".join(k for k, v in c["fires"].items() if v) or "-"))

json.dump(dict(note="Theorem A / Theorem B instantiation + controls; no grid, no claim",
               r_interval=[str(R_LO), str(R_HI)], certified=CASES, controls=CTRL),
          io.open(HERE / "strict_hub_finite_disjunction.json", "w"), indent=1)
(HERE / "strict_hub_finite_disjunction.out.txt").write_text("\n".join(OUT) + "\n", encoding="utf-8")
say("")
say("wrote strict_hub_finite_disjunction.json / .out.txt")
