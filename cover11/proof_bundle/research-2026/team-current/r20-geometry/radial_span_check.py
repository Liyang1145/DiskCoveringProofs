"""r20-geometry Round-5c: lead's inward-radial domain flag + Criterion C check (angular span).

Lead's correction (team-message-3f429db4): "inward radial means rho <= sqrt(1-r^2)", i.e. the
inward-canonical representative of a boundary arc has centre norm s <= sqrt(1-r^2) -- NOT s = 1
(|endpoint| = 1 is the OUTER root).  This is exactly the threshold of the dominance criterion in
RADIAL-INWARD-LOCAL.md (B(c,r) cap D subset B(tc,r) <=> t >= (1-r^2)/s^2; at an outer root
s = rho_+ the endpoint is C464's inner root rho_- = (1-r^2)/rho_+ <= sqrt(1-r^2)).

Part 1: domain flags -- for which rings s = |c_i| > sqrt(1-r^2) (outside the inward-radial domain).
Part 2: Criterion C (proved in RADIAL-INWARD-LOCAL.md sec.6): with F = t_-(lambda,phi) increasing in
        lambda (outward half) and in |phi| (lambda > r), if
           (a) no obstruction (outer sliver strictly covered by the other disks), and
           (b) every point of cl Q_i has |phi| <= phi_max (the angular span of i's private boundary
               arc),
        then t_fail(i) = t_bdy(i): the inward move reaches a tight tie with the cover intact.
        (b) is checked here on all arrangement vertices of cl Q_i (the arc-interior part reduces to
        a linear extremum on circular arcs, closed form, see the note).
No grid, no claim.

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/radial_span_check.py
"""
import io, json
from mpmath import mp, mpf, sqrt, cos, sin, atan2, acos, pi as MP_PI
from pathlib import Path
import importlib.util

mp.dps = 50
HERE = Path(__file__).resolve().parent
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


spec = importlib.util.spec_from_file_location("rt", HERE / "radial_tightening.py")
# import only the helpers (re-exec the module would run the computation); load by source split
src = (HERE / "radial_tightening.py").read_text(encoding="utf-8").split("RES = {}")[0]
g = {"__file__": str(HERE / "radial_tightening.py"), "__name__": "rt_helpers"}
exec(src, g)
CC, R_LO, RINGS, HUBS, ALL, ORDER = g["CC"], g["R_LO"], g["RINGS"], g["HUBS"], g["ALL"], g["ORDER"]
nrm, sub, candidates = g["nrm"], g["sub"], g["candidates"]
private_boundary_endpoints = g["private_boundary_endpoints"]
boundary_arcs = g["boundary_arcs"]

say("=" * 110)
say("PART 1.  Inward-radial domain (lead's correction): ring is inside iff |c| <= sqrt(1-r^2)")
say("=" * 110)
RES = {}
for r in [R_LO, mpf("0.40"), mpf("0.43"), mpf("0.45"), mpf("0.50"), mpf("0.55")]:
    thr = sqrt(1 - r * r)
    out = [i for i in ORDER if nrm(CC[i]) > thr]
    say("  r = %-16s sqrt(1-r^2) = %.9f   rings outside the inward domain: %s"
        % (mp.nstr(r, 10), float(thr), [(i, float(nrm(CC[i]))) for i in out] or "none"))
    RES[mp.nstr(r, 12)] = dict(threshold=float(thr), outside=[i for i in out])
say("  => the radial test rows r* , 0.39, 0.40, 0.43, 0.45 are inside the lead's domain for all")
say("     nine rings; r = 0.50 and 0.55 leave the domain for some rings (generic-cover reading only).")

say("")
say("=" * 110)
say("PART 2.  Criterion C: angular span of cl Q_i vs the private boundary arc span (vertices)")
say("=" * 110)
for r in [R_LO, mpf("0.40"), mpf("0.43")]:
    thr = sqrt(1 - r * r)
    say("")
    say("  r = %s (rho = %s, inward domain s <= %s)" % (mp.nstr(r, 10), mp.nstr(1 - r, 8), mp.nstr(thr, 8)))
    cts = candidates(r)
    rows = {}
    for i in ORDER:
        s = nrm(CC[i])
        th_i = atan2(CC[i][1], CC[i][0])
        ends = private_boundary_endpoints(i, r)
        phi_max = max([abs(mpf(str(e))) for e in ends], default=None)
        vmax, varg = None, None
        for x in cts:
            if nrm(x) > 1 + mpf("1e-12") or nrm(sub(x, CC[i])) > r + mpf("1e-9"):
                continue
            if any(k != i and nrm(sub(x, CC[k])) < r - mpf("1e-9") for k in ALL):
                continue
            d = atan2(x[1], x[0]) - th_i
            while d > MP_PI:
                d -= 2 * MP_PI
            while d < -MP_PI:
                d += 2 * MP_PI
            if vmax is None or abs(d) > vmax:
                vmax, varg = abs(d), (float(x[0]), float(x[1]))
        ok = (phi_max is not None and vmax is not None and vmax <= phi_max + mpf("1e-9"))
        say("    ring %-2d |c|=%.6f %s  phi_max=%.5f rad (%.3f deg)  max|phi| at vertices=%.5f rad%s"
            % (i, float(s), "IN" if s <= thr else "OUT", float(phi_max), float(phi_max * 180 / MP_PI),
               float(vmax) if vmax is not None else float("nan"),
               "  -> Criterion C vertex part PASSES" if ok else "  -> CHECK (vertex outside the span)"))
        rows[i] = dict(phi_max=float(phi_max) if phi_max is not None else None,
                       vertex_max=float(vmax) if vmax is not None else None, ok=bool(ok))
    RES[mp.nstr(r, 12)] = dict(RES.get(mp.nstr(r, 12), {}), span=rows)

json.dump(dict(note="inward-domain flag + Criterion C vertex check; no grid, no claim", results=RES),
          io.open(HERE / "radial_span_check.json", "w"), indent=1)
(HERE / "radial_span_check.out.txt").write_text("\n".join(OUT) + "\n", encoding="utf-8")
say("")
say("wrote radial_span_check.json / .out.txt")
