"""r20-geometry Round-5b (lead-directed, bounded): does the radial inward move reach a TIGHT tie
before the cover breaks?  (2-ring+hub local read, instantiated on the certified q0(6,7) geometry.)

For ring i at centre c_i (s = |c_i|) moved to t c_i (t <= 1) and a point x in the private region
Q_i = { x in D : |x - c_k| > r  for all k != i }  (points only ring i can cover):
    x in B(t c_i, r)  <=>  t in [t_-(x), t_+(x)],   t_-(x) = ( p - sqrt(p^2 - s^2(q - r^2)) ) / s^2
with p = x.c_i, q = |x|^2.  Hence
    t_fail(i) = max_{x in Q_i} t_-(x)
is the largest t at which the whole-D cover still holds (cover fails for t < t_fail), and
    t_bdy(i)  = the value of t_-(x) at the endpoint of i's PRIVATE BOUNDARY ARC (the point where
                the neighbour ring's boundary arc starts): at t = t_bdy that point is at distance
                exactly r from the moved ring, i.e. the two arcs are head-to-tail -- a TIGHT tie.
Verdict per ring:  t_fail <= t_bdy  -> the inward move can be continued exactly to a tight tie;
                   t_fail >  t_bdy  -> the cover breaks strictly BEFORE any tie tightens
                                        (the saturation move is blocked; witness recorded).
t_fail is computed from the finite candidate set of the closure of Q_i: circle-circle crossings of
the 11 disks and ring/boundary crossings, kept when no other disk contains them strictly, then
validated by an explicit outward perturbation (a genuine strictly-private witness).  The value at
a candidate is t_-(x') for the validated witness x'.  No grid, no optimisation, no claim.

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/radial_tightening.py
"""
import io, json
from mpmath import mp, mpf, sqrt, acos, cos, sin, atan2, pi as MP_PI
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


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]


OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
SC = mpf(10) ** int(OBJ["decimals"])
CC = [V(mpf(int(a)) / SC, mpf(int(b)) / SC) for a, b in OBJ["centers_scaled_1e17"]]
R_LO = mpf(OBJ["certified_interval"]["lo"])
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
HUBS = [0, 2]
ALL = list(range(11))
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def circle_crossings(c1, r1, c2, r2):
    dv = sub(c2, c1)
    d = nrm(dv)
    if d == 0 or d > r1 + r2 or d < abs(r1 - r2):
        return []
    a = (r1 ** 2 - r2 ** 2 + d ** 2) / (2 * d)
    h2 = r1 ** 2 - a ** 2
    hh = sqrt(max(mpf(0), h2))
    u = (dv[0] / d, dv[1] / d)
    base = add(c1, mul(a, u))
    if hh == 0:
        return [base]
    perp = (-u[1], u[0])
    return [add(base, mul(hh, perp)), sub(base, mul(hh, perp))]


def tminus(x, c, r, tol=mpf("1e-30")):
    """lower root of |x - t c|^2 = r^2 ; None if x has no constraint (|x|<r region)."""
    s2 = dot(c, c)
    p = dot(x, c)
    q = dot(x, x)
    if q <= r * r:
        return None
    D = p * p - s2 * (q - r * r)
    if D < -tol:
        return None
    D = max(mpf(0), D)
    return (p - sqrt(D)) / s2


def boundary_arcs(r):
    arcs = {}
    for i in RINGS:
        s = nrm(CC[i])
        c = max(mpf(-1), min(mpf(1), (s * s + 1 - r * r) / (2 * s)))
        al = acos(c)
        th = atan2(CC[i][1], CC[i][0])
        arcs[i] = (th - al, th + al)
    return arcs


def covered_arcs_union(arcs, exclude):
    """union of arcs (i != exclude) as merged intervals, with +/-2pi copies (cyclic coverage)."""
    iv = []
    for i, (a, b) in arcs.items():
        if i == exclude:
            continue
        while a < 0:
            a += 2 * MP_PI
            b += 2 * MP_PI
        while a >= 2 * MP_PI:
            a -= 2 * MP_PI
            b -= 2 * MP_PI
        for k in (-1, 0, 1):
            iv.append((a + k * 2 * MP_PI, b + k * 2 * MP_PI))
    iv.sort()
    out = []
    for (a, b) in iv:
        if out and a <= out[-1][1] + mpf("1e-25"):
            out[-1][1] = max(out[-1][1], b)
        else:
            out.append([a, b])
    return out


def private_boundary_endpoints(i, r):
    """Endpoints (angles, in ring i's own frame) of the part of ring i's boundary arc that no
    other ring covers.  Robust formulation: rotate so that c_i points along angle 0, so ring i's
    arc is [-alpha_i, alpha_i] with alpha_i < pi; clip every other arc (with +-2pi copies) to this
    window and merge."""
    arcs = boundary_arcs(r)
    s = nrm(CC[i])
    c = max(mpf(-1), min(mpf(1), (s * s + 1 - r * r) / (2 * s)))
    al = acos(c)
    th_i = atan2(CC[i][1], CC[i][0])
    iv = []
    for j, (a, b) in arcs.items():
        if j == i:
            continue
        for k in (-2, -1, 0, 1, 2):
            aa, bb = a + k * 2 * MP_PI - th_i, b + k * 2 * MP_PI - th_i
            lo, hi = max(aa, -al), min(bb, al)
            if hi > lo:
                iv.append([lo, hi])
    iv.sort()
    merged = []
    for (a, b) in iv:
        if merged and a <= merged[-1][1] + mpf("1e-25"):
            merged[-1][1] = max(merged[-1][1], b)
        else:
            merged.append([a, b])
    pts = []
    pos = -al
    for (a, b) in merged:
        if a > pos + mpf("1e-25"):
            pts += [pos, a]                          # private piece from pos to a
        pos = max(pos, b)
    if pos < al - mpf("1e-25"):
        pts += [pos, al]
    return sorted(set([round(float(t), 14) for t in pts]))


def wedge_direction(constraints):
    """Intersect angular windows: for each (d, sense) require v.d > 0 (sense=+1) or v.d < 0
    (sense=-1).  Returns a direction in the (open) intersection, or None if empty."""
    lo, hi = mpf(-2 * MP_PI), mpf(2 * MP_PI)
    for (d, sense) in constraints:
        nd = nrm(d)
        if nd == 0:
            return None
        base = atan2(d[1], d[0]) if sense > 0 else atan2(d[1], d[0]) + MP_PI
        a, b = base - MP_PI / 2, base + MP_PI / 2
        while b <= lo:
            a += 2 * MP_PI
            b += 2 * MP_PI
        while a >= hi:
            a -= 2 * MP_PI
            b -= 2 * MP_PI
        lo, hi = max(lo, a), min(hi, b)
        if lo >= hi - mpf("1e-30"):
            return None
    phi = (lo + hi) / 2
    return (cos(phi), sin(phi))


def valid_witness(x, i, r, eps=mpf("1e-9"), tol=mpf("1e-9")):
    """try to perturb x into the strictly private region Q_i; return (x', tminus(x')) or None."""
    weak = [k for k in ALL if k != i and abs(nrm(sub(x, CC[k])) - r) <= tol]
    if any(k != i and nrm(sub(x, CC[k])) < r - tol for k in ALL):
        return None                                     # a nbhd of x stays covered by k
    cons = [(sub(x, CC[k]), +1) for k in weak]           # leave every weakly covering disk
    if nrm(sub(x, CC[i])) >= r - tol:                    # enter ring i's disk
        cons.append((sub(x, CC[i]), -1))
    if nrm(x) >= 1 - tol:                                # stay inside D
        cons.append((x, -1))
    v = wedge_direction(cons)
    if v is None:
        return None
    for e in (eps, eps / 100, eps / 10000):
        xp = add(x, mul(e, v))
        if nrm(xp) > 1:
            continue
        if nrm(sub(xp, CC[i])) >= r:
            continue
        if any(nrm(sub(xp, CC[k])) <= r for k in ALL if k != i):
            continue
        tm = tminus(xp, CC[i], r)
        if tm is None:
            continue
        return xp, tm
    return None


def candidates(r):
    """Complete candidate set for max_{x in cl Q_i} t_-(x), given the monotonicity lemma
    (t_- = F(lambda,phi) is increasing in lambda on the outward half and in |phi| for lambda > r):
    the maximum over a boundary arc of cl Q_i is attained at
      (i)  an arrangement crossing (circle-circle or circle-boundary), or
      (ii) a Pareto point of (lambda,|phi|) on the arc, i.e. lambda'=0 or phi'=0, which on a full
           circle are the farthest point c(1+r/|c|) and the two radial-tangency points
           (x = c + r w with w.(c/|c|) = -r/|c|).
    Endpoints of the arcs are exactly the crossings (i)."""
    pts = []
    for a in range(11):
        for b in range(a + 1, 11):
            pts += circle_crossings(CC[a], r, CC[b], r)
    for i in RINGS:                                     # ring circle / unit boundary crossings
        pts += circle_crossings(CC[i], r, (mpf(0), mpf(0)), mpf(1))
    for k in ALL:                                       # Pareto points on each circle
        c = CC[k]
        sk = nrm(c)
        if sk > 0:
            e = (c[0] / sk, c[1] / sk)
            pts.append(add(c, mul(r, e)))               # farthest point from the origin
            if sk >= r:
                t = sqrt(1 - (r / sk) ** 2)
                perp = (-e[1], e[0])
                for sgn in (1, -1):
                    w = add(mul(-r / sk, e), mul(sgn * t, perp))
                    pts.append(add(c, mul(r, w)))
    return pts


RES = {}
for r in [R_LO, mpf("0.40"), mpf("0.43"), mpf("0.50"), mpf("0.55")]:
    say("")
    say("=" * 112)
    say("r = %s   (rho = %s)" % (mp.nstr(r, 10), mp.nstr(1 - r, 8)))
    say("=" * 112)
    arcs = boundary_arcs(r)
    cts = candidates(r)
    say("  %d structural crossings (circle-circle + ring-circle/boundary)" % len(cts))
    per = {}
    for i in ORDER:
        # t_bdy : value of t_-(x) at the private boundary-arc endpoints (angles in ring i's frame)
        ends = private_boundary_endpoints(i, r)
        th_i = atan2(CC[i][1], CC[i][0])
        tb = []
        for dth in ends:
            x = (cos(th_i + dth), sin(th_i + dth))
            if nrm(sub(x, CC[i])) > r + mpf("1e-9"):
                continue
            tm = tminus(x, CC[i], r)
            if tm is not None:
                tb.append((tm, dth, x))
        t_bdy = max([t for (t, th, x) in tb], default=None)
        # t_fail : max over validated private witnesses of t_-(x')
        best = None
        for x in cts:
            if nrm(x) > 1 + mpf("1e-12"):
                continue
            if nrm(sub(x, CC[i])) > r + mpf("1e-9"):
                continue
            wv = valid_witness(x, i, r)
            if wv is None:
                continue
            xp, tm = wv
            if best is None or tm > best[0]:
                best = (tm, xp, x)
        t_fail = best[0] if best else None
        verdict = None
        if t_bdy is None:
            verdict = "no private boundary arc (boundary already covered by the other rings)"
        elif t_fail is None:
            verdict = "no private interior witness found"
        elif best[1] is not None and nrm(best[1]) > 1 - mpf("1e-6"):
            verdict = ("OK: binding event is a BOUNDARY point -> the inward move runs exactly to a tight tie"
                       " (t_fail = t_bdy = %s)" % mp.nstr(t_fail, 10) if t_bdy is not None and abs(t_fail - t_bdy) < mpf("1e-5")
                       else "OK: binding event is a BOUNDARY point (tie saturates before any interior gap)")
        else:
            verdict = "BLOCKED: binding witness is INTERIOR -> cover breaks before any tie tightens"
        say("  ring %-2d |c|=%.6f  t_bdy=%s  t_fail=%s  |x*|=%s  -> %s"
            % (i, float(nrm(CC[i])),
               mp.nstr(t_bdy, 12) if t_bdy is not None else "n/a",
               mp.nstr(t_fail, 12) if t_fail is not None else "n/a",
               mp.nstr(nrm(best[1]), 12) if best else "n/a", verdict))
        if best is not None:
            xp = best[1]
            marg = {k: nrm(sub(xp, CC[k])) - r for k in ALL if k != i}
            loc = sorted(marg, key=lambda k: marg[k])[:3]
            inside = [k for k in ALL if k != i and nrm(sub(xp, CC[k])) < r]
            say("        binding witness x=(%.6f,%.6f)  margins: %s   (nearest: %s)%s"
                % (float(xp[0]), float(xp[1]),
                   ", ".join("c_%d:%+.2e" % (k, float(marg[k])) for k in loc),
                   "boundary/private" if not inside else "covered by c_%d" % inside[0],
                   "" if len(inside) == 0 else "  <-- not a genuine failure witness (covered)"))
            locR = [k for k in RINGS + HUBS if k != i]
            nb = min(locR, key=lambda k: nrm(sub(xp, CC[k])))
            say("        local read: nearest local disk is c_%d (margin %+.3e); moving ring %d inward uncovers this point"
                % (nb, float(marg[nb]), i))
        per[i] = dict(t_bdy=str(t_bdy) if t_bdy is not None else None,
                      t_fail=str(t_fail) if t_fail is not None else None,
                      witness=[float(best[1][0]), float(best[1][1])] if best else None,
                      witness_norm=float(nrm(best[1])) if best else None,
                      verdict=verdict)
    RES[mp.nstr(r, 12)] = per

json.dump(dict(note="radial tightening test; no grid, no claim", results=RES),
          io.open(HERE / "radial_tightening.json", "w"), indent=1)
(HERE / "radial_tightening.out.txt").write_text("\n".join(OUT) + "\n", encoding="utf-8")
say("")
say("wrote radial_tightening.json / .out.txt")
