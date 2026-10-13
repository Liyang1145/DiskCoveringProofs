"""r20-geometry Round-5 (lead-directed, bounded): radial inward move of one ring — local 2-ring+hub test.

Question (lead): with the nine ring inward roots having ACTUAL arc overlap, can one move rings
radially inward one by one until some boundary tie becomes tight WITHOUT losing the whole-D cover?
General radial inward is not a dominance (C464 covers only the two roots of the SAME boundary arc).

Analytic content (proved in RADIAL-INWARD-LOCAL.md, instantiated here):
  * one-ring exact arithmetic: for x with |x-c| = r,
        |x - t c|^2 - r^2 = (1-t) [ 2 x.c - (1+t) s^2 ] ,    s = |c| ,
    and max_{x in B(c,r) cap D} (x.e) = min( s + r , (1+s^2-r^2)/(2s) )  (e = c/s).
    Hence   B(c,r) cap D  subset  B(tc,r)   <=>   1 - r^2 <= t s^2      (when s + r > 1)
    so the inward move is a DOMINANCE for t >= (1-r^2)/s^2 ; at an OUTER root s = rho_+ >= sqrt(1-r^2)
    the endpoint t = (1-r^2)/s^2 is exactly C464's inner root rho_- = (1-r^2)/rho_+.  Below the
    inner-root level (s < sqrt(1-r^2)) the lost set
        L(t) cap D -> { x in dB(c,r) cap D : x.c > s^2 }   (t -> 1-)
    is a nonempty sliver (the "outer sliver"), and:
        if some x in that sliver lies in NO other disk (|x-c_j| > r for all j != i) then
        EVERY inward radial move of ring i uncovers x  =>  no cover-preserving inward move exists.
  * coverage of the sliver by the other disks is decided exactly by arc-union on the circle
    dB(c_i,r) (each other disk cuts an arc [gamma_j - delta_j, gamma_j + delta_j], delta_j =
    arccos(d_j/(2r))).

Instantiation: the certified q0(6,7) centres at enlarged radii r > r* (disks only grow, so the
cover persists by monotonicity from the certified r* cover; arcs then genuinely overlap), plus a
"steep ring" dominance control.  No grid, no optimisation, no claim.

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/radial_inward_local.py
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


def deg(x):
    return float(x * 180 / MP_PI)


# ---------------------------------------------------------------- object data
OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
SC = mpf(10) ** int(OBJ["decimals"])
CC = [V(mpf(int(a)) / SC, mpf(int(b)) / SC) for a, b in OBJ["centers_scaled_1e17"]]
R_LO = mpf(OBJ["certified_interval"]["lo"])
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]                       # certified-object ring labels
HUBS = [0, 2]
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]                        # cyclic ring order (recorded)
NEXT = {ORDER[i]: ORDER[(i + 1) % 9] for i in range(9)}
PREV = {ORDER[(i + 1) % 9]: ORDER[i] for i in range(9)}


def arcs_and_gaps(r):
    """Boundary arcs of the nine rings + coverage check of the unit circle."""
    arcs = []
    for i in RINGS:
        s = nrm(CC[i])
        assert s > 0
        if s + r < 1:                                       # disk does not meet the boundary
            return None
        c = (s * s + 1 - r * r) / (2 * s)
        c = max(mpf(-1), min(mpf(1), c))
        al = acos(c)
        th = atan2(CC[i][1], CC[i][0])
        arcs.append((i, th - al, th + al))
    return arcs


def circle_cover(arcs, rho=0):
    """Return list of uncovered angles (mod 2pi) of the circle by the given arcs."""
    iv = []
    for (i, a, b) in arcs:
        while a < 0:
            a += 2 * MP_PI
            b += 2 * MP_PI
        iv.append((a, b, i))
        iv.append((a + 2 * MP_PI, b + 2 * MP_PI, i))
    iv.sort()
    # sweep from the first arc start
    a0 = min(a for a, b, i in iv)
    pos = a0
    out = []
    for (a, b, i) in iv:
        if a > pos:
            out.append((pos, min(a, a0 + 2 * MP_PI)))
        pos = max(pos, b)
        if pos >= a0 + 2 * MP_PI:
            break
    return out


def overlap_report(r):
    arcs = arcs_and_gaps(r)
    if arcs is None:
        return None
    gaps = circle_cover(arcs)
    gv = {t: (a, b) for (t, a, b) in arcs}
    ov = []
    for k in range(9):
        i = ORDER[k]
        j = ORDER[(k + 1) % 9]
        a_i, b_i = gv[i]
        a_j, b_j = gv[j]
        best = mpf(0)
        for s in (-1, 0, 1):                      # cyclic intersection length
            lo = max(a_i, a_j + s * 2 * MP_PI)
            hi = min(b_i, b_j + s * 2 * MP_PI)
            if hi > lo:
                best = max(best, hi - lo)
        ov.append((i, j, deg(best)))
    return arcs, gaps, ov


def sliver_coverage(i, r, tol=mpf("1e-25")):
    """Exact arc-union test on dB(c_i,r): is the outer sliver
       S_i = { x in dB(c_i,r) cap D : x.c_i > s^2 }
       covered by the other ten disks?
       Local parameter beta = angle of w=x-c_i measured from e_i=c_i/s:
           S_i = { beta : beta_end <= |beta| <= pi/2 },   beta_end = acos(W), W=(1-s^2-r^2)/(2 r s).
       Disk j cuts the arc [gamma_j - delta_j, gamma_j + delta_j], delta_j = acos(d/(2r)).
       Returns dict with the uncovered spans and a witness point."""
    ci = CC[i]
    s = nrm(ci)
    assert s + r > 1
    W = (1 - s * s - r * r) / (2 * r * s)
    if W <= 0:
        return dict(shallow=False, W=float(W), covered=True, gaps=[], witness=None)
    beta_end = acos(W)
    S = [(-MP_PI / 2, -beta_end), (beta_end, MP_PI / 2)]     # the two sliver arcs (beta range)
    e = (ci[0] / s, ci[1] / s)
    cov = []
    for j in list(RINGS) + HUBS:
        if j == i:
            continue
        dv = sub(CC[j], ci)
        d = nrm(dv)
        if d == 0 or d > 2 * r + tol:
            continue
        dl = acos(min(mpf(1), d / (2 * r)))
        gam = atan2(e[0] * dv[1] - e[1] * dv[0], e[0] * dv[0] + e[1] * dv[1])
        cov.append((gam - dl, gam + dl, j))
    gaps = []
    for (lo, hi) in S:
        segs = sorted([(max(lo, a), min(hi, b), j) for (a, b, j) in cov if min(hi, b) > max(lo, a)])
        pos = lo
        for (a, b, j) in segs:
            if a > pos + tol:
                gaps.append((pos, a, "uncovered"))
            pos = max(pos, b)
        if pos < hi - tol:
            gaps.append((pos, hi, "uncovered"))
    wit = None
    if gaps:
        g = max(gaps, key=lambda t: t[1] - t[0])
        bstar = (g[0] + g[1]) / 2
        w = (cos(bstar), sin(bstar))
        x = add(ci, mul(r, (e[0] * w[0] - e[1] * w[1], e[0] * w[1] + e[1] * w[0])))
        marg = {j: nrm(sub(x, CC[j])) - r for j in list(RINGS) + HUBS if j != i}
        wit = dict(x=[float(x[0]), float(x[1])], beta_star=deg(bstar), gap_span=deg(g[1] - g[0]),
                   norm=float(nrm(x)), xdotc=float(x[0] * ci[0] + x[1] * ci[1]), s2=float(s * s),
                   min_other_margin=float(min(marg.values())),
                   nearest=[(j, float(marg[j])) for j in sorted(marg, key=lambda t: marg[t])[:3]],
                   neighbour_margin={j: float(nrm(sub(x, CC[j])) - r) for j in (NEXT[i], PREV[i])},
                   hub_margin={h: float(nrm(sub(x, CC[h])) - r) for h in HUBS})
        xc = (x[0] * ci[0] + x[1] * ci[1])
        assert nrm(x) <= 1 + tol and abs(nrm(sub(x, ci)) - r) < tol and xc > s * s
        assert wit["min_other_margin"] > 0
    return dict(shallow=True, W=float(W), beta_end_deg=deg(beta_end), covered=not gaps,
                gaps=[(deg(a), deg(b)) for (a, b, _) in gaps], witness=wit)


# ================================================================ Part 1
say("=" * 112)
say("PART 1.  Certified q0(6,7) centres at enlarged radii (genuine covers by monotonicity; arcs overlap)")
say("=" * 112)
RES = {}
for r in [R_LO, mpf("0.39"), mpf("0.40"), mpf("0.43"), mpf("0.45")]:
    rep = overlap_report(r)
    if rep is None:
        say("  r=%s : a ring disk stops meeting the boundary -- outside the local domain" % mp.nstr(r, 8))
        continue
    arcs, gaps, ov = rep
    srt = sorted(RINGS, key=lambda i: nrm(CC[i]))
    sha = sum(1 for i in RINGS if nrm(CC[i]) < sqrt(1 - r * r))
    say("")
    say("  r = %s   (rho = 1-r = %s, sqrt(1-r^2) = %s)" % (mp.nstr(r, 10), mp.nstr(1 - r, 8), mp.nstr(sqrt(1 - r * r), 8)))
    say("    boundary arcs: %s" % ("COVER the circle exactly" if not gaps else
                                   "GAPS remain: " + ", ".join("%.2f..%.2f deg" % (deg(a), deg(b)) for a, b in gaps)))
    say("    consecutive arc overlaps (deg): " + ", ".join("%d-%d:%+.2f" % (i, j, g) for i, j, g in ov))
    say("    shallow rings (s < sqrt(1-r^2), inward move loses a sliver): %d of 9 ; ring norms %.4f..%.4f"
        % (sha, float(nrm(CC[srt[0]])), float(nrm(CC[srt[-1]]))))
    rows = {}
    for i in ORDER:
        res = sliver_coverage(i, r)
        rows[i] = res
        if not res["shallow"]:
            txt = "STEEP: inward move is a dominance (t >= (1-r^2)/s^2)"
        elif res["covered"]:
            txt = "outward sliver COVERED by the other ten disks (no obstruction at the infinitesimal level)"
        else:
            w = res["witness"]
            txt = ("OBSTRUCTED: uncovered sliver span %.2f deg, witness x=(%.6f,%.6f) |x|=%.6f, "
                   "min_{j!=i}(|x-c_j|-r)=%+.3e" % (w["gap_span"], w["x"][0], w["x"][1], w["norm"],
                                                    w["min_other_margin"]))
        say("      ring %-2d |c|=%.6f  W=%+.4f  %s" % (i, float(nrm(CC[i])), res["W"], txt))
        if (not res["shallow"] or not res["covered"]) and res.get("witness"):
            say("               local 2-ring+hub read: neighbour margins %s, hub margins %s -> local disks cannot compensate"
                % ({k: round(v, 4) for k, v in res["witness"]["neighbour_margin"].items()},
                   {k: round(v, 4) for k, v in res["witness"]["hub_margin"].items()}))
    RES[mp.nstr(r, 12)] = dict(gaps=[[deg(a), deg(b)] for a, b in gaps],
                               overlaps=[[i, j, g] for i, j, g in ov],
                               shallow=sha, per_ring={int(i): {k: v for k, v in rows[i].items() if k != "witness"} |
                                                      ({"witness": rows[i]["witness"]} if rows[i].get("witness") else {})
                                                      for i in ORDER})

# ================================================================ Part 2
say("")
say("=" * 112)
say("PART 2.  Controls: the exact dominance criterion and its C464 endpoint")
say("=" * 112)
say("  criterion: B(c,r) cap D subset B(tc,r)  <=>  1 - r^2 <= t s^2   (s+r>1), checked on the")
say("  extreme point of B(c,r)cap D (the circle-circle crossing, x.e = (1+s^2-r^2)/(2s)):")


def dominance_check(c, r, t):
    s = nrm(c)
    e = (c[0] / s, c[1] / s)
    xstar = mul((1 + s * s - r * r) / (2 * s), e)          # farthest point of B(c,r)cap D along e
    lhs = nrm(sub(xstar, mul(t, c))) - r
    return lhs, (1 - r * r <= t * s * s), float(nrm(sub(xstar, c)) - r)


for (rr, ss, tag) in [(mpf("0.4"), mpf("0.95"), "steep ring (s > sqrt(1-r^2))"),
                      (mpf("0.4"), mpf("0.80"), "shallow ring (s < sqrt(1-r^2))")]:
    c = (ss, mpf(0))
    s_ = sqrt(1 - rr * rr)
    tcrit = (1 - rr * rr) / (ss * ss)
    for t in [mpf(1), (mpf(1) + tcrit) / 2 if tcrit < 1 else mpf("0.99"), tcrit, tcrit - mpf("0.01")]:
        if t <= 0:
            continue
        lhs, ok, sl = dominance_check(c, rr, t)
        say("    r=%.2f s=%.2f (%s): t=%.6f  max|x-tc|-r over B(c,r)capD = %+.3e  criterion(1-r^2<=t s^2)=%s"
            % (float(rr), float(ss), tag, float(t), float(lhs), ok))
    say("      -> t_crit = (1-r^2)/s^2 = %.6f ; at s = sqrt(1-r^2)=%.6f one has t_crit = 1 (C464 endpoint:"
        " outer root rho_+ -> inner root rho_-)" % (float(tcrit), float(s_)))
    if tcrit > 1:
        say("      -> t_crit > 1: no inward move is a dominance at all (this is the inner-root level)")
    # C464 identity check: rho_+ rho_- = 1 - r^2 for the root pair
    rho_p = mpf("0.95")
    rho_m = (1 - rr * rr) / rho_p
    say("      C464 control: rho_+=%.6f, rho_-=(1-r^2)/rho_+=%.6f, product=%.10f (=1-r^2=%.10f)"
        % (float(rho_p), float(rho_m), float(rho_p * rho_m), float(1 - rr * rr)))

json.dump(dict(note="radial inward local test; no grid, no claim", r=R_LO, results=RES),
          io.open(HERE / "radial_inward_local.json", "w"), indent=1, default=str)
(HERE / "radial_inward_local.out.txt").write_text("\n".join(OUT) + "\n", encoding="utf-8")
say("")
say("wrote radial_inward_local.json / .out.txt")
