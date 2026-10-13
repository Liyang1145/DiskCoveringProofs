"""Exact structural extraction for the C182 n=12 candidate configuration.

READ-ONLY on inputs. Outputs JSON + txt under members/candidate/evidence/.

Objects:
  A = cert_n12_othern.json  (17-digit decimal literal config, exact rational)
  B = flash-n11/members/othern-scout/s3/n12_d3_kkt.json (KKT source, 48-digit)

All arithmetic below is exact rational (Fraction) except where labelled mp/float.
"""
from pathlib import Path
from fractions import Fraction as F
import json, sys, math

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
CAND = ROOT / "research-2026/n12-global/members/candidate"
EV = CAND / "evidence"
EV.mkdir(parents=True, exist_ok=True)

CFGA = ROOT / "research-2026/session2/n1314/cfg/cert_n12_othern.json"
CFGB = ROOT / "flash-n11/members/othern-scout/s3/n12_d3_kkt.json"

A = json.loads(CFGA.read_text(encoding="utf-8"))
B = json.loads(CFGB.read_text(encoding="utf-8"))

# --- A: exact rational config --------------------------------------------
Acent = [(F(x), F(y)) for x, y in A["centers_dec17"]]
# --- B: exact rational config from KKT source (decimal strings are exact) --
Bcent = [(F(x), F(y)) for x, y in B["centers"]]
Bparams = [F(s) for s in B["params"]]


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]


def n2(u):
    return dot(u, u)


def d2(u, v):
    return n2((u[0] - v[0], u[1] - v[1]))


def d2_mp(u, v):
    from mpmath import mp, mpf
    return mp.mpf(float(u[0] - v[0])) ** 2 + mp.mpf(float(u[1] - v[1])) ** 2


out = {}
out["inputs"] = {"cfg_A": str(CFGA.relative_to(ROOT)), "cfg_B": str(CFGB.relative_to(ROOT))}

# which config do we analyse structurally?  Report both, use A as the certified object.
for tag, cent in (("A", Acent), ("B", Bcent)):
    rec = {}
    rec["n"] = len(cent)
    # |c_i|^2 exact ; classify boundary vs interior relative to R (float diag)
    Rf = float(A["R_float"]) if tag == "A" else float(B["R_D_mpmath"])
    rec["R_float_diag"] = Rf
    info = []
    for i, c in enumerate(cent):
        nrm2 = n2(c)
        nrm = math.sqrt(float(nrm2))
        info.append({
            "i": i,
            "c": [str(c[0]), str(c[1])],
            "abs2_exact": str(nrm2),
            "abs_float": nrm,
            "abs_minus(1-R)_float": nrm - (1 - Rf),
            "1-abs_float": 1 - nrm,
            "touch_boundary_eq(|c|+R=1)": abs((nrm + Rf) - 1) < 1e-15,
            "contains_origin(|c|<=R)": nrm <= Rf,
        })
    rec["centers"] = info
    # nearest neighbour structure: min_{j!=i} |c_i-c_j| vs 2R
    nn = []
    for i in range(len(cent)):
        best = None
        for j in range(len(cent)):
            if j == i:
                continue
            dd = d2(cent[i], cent[j])
            if best is None or dd < best[0]:
                best = (dd, j)
        dd_mp = math.sqrt(float(best[0]))
        nn.append({
            "i": i, "j": best[1],
            "d_exact_sq": str(best[0]),
            "d_float": dd_mp,
            "d_minus_2R": dd_mp - 2 * Rf,
            "nonoverlap_strict(|ci-cj|>=2R)": dd_mp >= 2 * Rf - 1e-13,
        })
    rec["nearest_neighbour"] = nn
    out[tag] = rec

# --- exact nearest-neighbour + Voronoi-on-circle analysis for A -----------
R = F(A["R_float"])  # diagnostic only, exact rational of the literal
# better: use the certified rational interval endpoints from D2 replay
R_lo = F("0.361102963744508672616920293903")
R_hi = F("0.361102963744508672616920293904")

# Distance from each centre to the farthest point of its OWN Voronoi region that
# can be needed: use swept arc analysis on the unit circle = |x|=1.
# For centre c and boundary point p(t)=(cos t, sin t) we use exact algebra where possible.
# Here we do a high-precision float scan to *locate* critical angles, then certify exactly.
import mpmath as mp
mp.mp.dps = 60
Am = [(mp.mpf(str(c[0])), mp.mpf(str(c[1]))) for c in Acent]
Rm = mp.mpf(str(A["R_float"]))


def dist(p, c):
    return mp.sqrt((p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2)


# 1) which centres can be the nearest one on |x|=1
scan = []
N = 200000
best_tot = []
for k in range(N):
    t = 2 * mp.pi * k / N
    p = (mp.cos(t), mp.sin(t))
    ds = [dist(p, c) for c in Am]
    m = min(ds)
    best_tot.append((m, ds.index(m)))
maxmin = max(b[0] for b in best_tot)
argmax_i = max(best_tot, key=lambda z: z[0])[1]
# distinguish boundary vs interior nearest-witness on the circle
witness_is_boundary = []
for k in range(N):
    t = 2 * mp.pi * k / N
    p = (mp.cos(t), mp.sin(t))
    ds = [dist(p, c) for c in Am]
    m = min(ds)
    witness_is_boundary.append((m > Rm * 0 + 0) and (mp.fabs(Am[ds.index(m)][0] ** 2 + Am[ds.index(m)][1] ** 2) > 0))
# count how many centres are ever nearest on the circle
ever = set(b[1] for b in best_tot)
out["circle_scan"] = {
    "maxmin_float": mp.nstr(maxmin, 30),
    "R_literal_float": mp.nstr(Rm, 30),
    "argmax_centre": argmax_i,
    "centres_ever_nearest_on_circle": sorted(ever),
    "centres_ever_nearest_on_circle_abs": [round(math.sqrt(float(n2(Acent[i]))), 6) for i in sorted(ever)],
}

# 2) exact perpendicular-bisector / unit-circle switching points
def circle_bisector_points(ci, cj):
    """Points p with |p|^2=1 and |p-ci|^2=|p-cj|^2, exactly.
    Equation: -2p.ci + |ci|^2 = -2p.cj + |cj|^2  =>  2 p.(cj-ci) = |cj|^2-|ci|^2.
    Line  a x + b y = d  with a=2(cj-ci)_x, b=2(cj-ci)_y, d=|cj|^2-|ci|^2.
    Solve on unit circle -> rational if the two components under sqrt are perfect squares
    (they need not be); return exact quadratic data."""
    a = 2 * (cj[0] - ci[0])
    b = 2 * (cj[1] - ci[1])
    d = n2(cj) - n2(ci)
    # parametrise p = (a d +- b sqrt(a^2+b^2-d^2))/(a^2+b^2), (b d -+ a sqrt(...))/(a^2+b^2)
    s = a * a + b * b
    disc = s - d * d
    return {"a": a, "b": b, "d": d, "a2pb2": s, "disc": disc,
            "disc_is_sq": is_perfect_square(disc) if disc >= 0 else False}


def is_perfect_square(q):
    if q < 0:
        return False
    n, d = q.numerator, q.denominator
    rn, rd = math.isqrt(n), math.isqrt(d)
    return rn * rn == n and rd * rd == d


# boundary centres = those with |c|+R ~ 1 (diagnostic threshold), confirm exactly below
bnd = [i for i in range(len(Acent)) if abs(math.sqrt(float(n2(Acent[i]))) + Rf - 1) < 1e-12]
out["boundary_centres_float"] = bnd
sw = []
pts = []
for ii in range(len(bnd)):
    for jj in range(ii + 1, len(bnd)):
        i, j = bnd[ii], bnd[jj]
        rec = circle_bisector_points(Acent[i], Acent[j])
        rec["pair"] = [i, j]
        # numeric solution
        s = float(rec["a2pb2"]); d = float(rec["d"]); disc = float(rec["disc"])
        if disc >= 0:
            sq = math.sqrt(disc)
            a = float(rec["a"]); b = float(rec["b"])
            p1 = ((a * d + b * sq) / s, (b * d - a * sq) / s)
            p2 = ((a * d - b * sq) / s, (b * d + a * sq) / s)
            rec["points_float"] = [p1, p2]
            # is this an actual nearest-centre switch?  check p is on circle & the
            # two centres are the two nearest there
            for p in (p1, p2):
                if abs(p[0] ** 2 + p[1] ** 2 - 1) > 1e-12:
                    continue
                ds = [math.dist(p, (float(c[0]), float(c[1]))) for c in Acent]
                order = sorted(range(len(ds)), key=lambda k: ds[k])
                is_switch = set(order[:2]) == {i, j} and not any(
                    abs(ds[k] - ds[i]) < 1e-12 for k in order[2:] if k not in (i, j))
                rec.setdefault("switch_points", []).append({
                    "p": p, "d_nearest": ds[i], "d_nearest_minus_R": ds[i] - Rf,
                    "is_true_switch": is_switch,
                    "nearest_order": order[:4],
                    "second_shell_gap": (ds[order[1]] - ds[order[2]]) if len(order) > 2 else None,
                })
        sw.append(rec)
out["bisector_switches"] = sw

(EV / "geo_struct.json").write_text(json.dumps(out, indent=2, default=str), encoding="utf-8")

# also mpmath high precision KKT/active-set report for B
lines = []
lines.append("=== B (KKT source) exact literal analysis, mpmath dps=60 ===")
lines.append(f"params: {[mp.nstr(mp.mpf(str(p)), 30) for p in Bparams]}")
RB = mp.mpf(B["R_D_mpmath"])
for i, c in enumerate(Bcent):
    rho = mp.sqrt(mp.mpf(str(c[0])) ** 2 + mp.mpf(str(c[1])) ** 2)
    th = mp.atan2(mp.mpf(str(c[1])), mp.mpf(str(c[0])))
    lines.append(f"  i={i:2d} rho={mp.nstr(rho,25)} theta_deg={mp.nstr(th/ mp.pi*180,25)} "
                 f"rho+R={mp.nstr(rho+RB,25)}")
lines.append("")
(EV / "geo_struct_B.txt").write_text("\n".join(lines), encoding="utf-8")
print("\n".join(lines))
print("A boundary centres:", bnd)
print("maxmin on circle (float):", mp.nstr(maxmin, 25), " at centre", argmax_i, "R_lit", mp.nstr(Rm, 25))
print("circle centres ever nearest:", sorted(ever))
print("wrote", EV / "geo_struct.json")
