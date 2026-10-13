"""r20-chain DECISIVE EXPERIMENT (corrected edition).

NECESSARY CONDITION, exact setup: unit closed disk D covered by 11 congruent disks of
radius R; nine essential boundary ("ring") disks + two interior hubs A,B; ring sites
c_0..c_8 listed counterclockwise about the ORIGIN; ring edge i joins c_i to c_{i+1}.

For hub H and ring edge i:
    s_H(c)   = arccos(|H-c|/(2R))            [defined only when |H-c| <= 2R]
    A_i = s_A(c_i)+s_A(c_{i+1}),  B_i = s_B(c_i)+s_B(c_{i+1})     (inf when undefined)
    theta_i^H = the (unsigned) turn at H from spoke (H,c_i) to spoke (H,c_{i+1}).

FACT 1 (circumradius criterion).  If both spokes are defined, the triangle (H,c_i,c_{i+1})
has circumradius <= R  <=>  theta_i^H <= s_H(c_i) + s_H(c_{i+1}).
FACT 2 (ring arithmetic).  Any hub H whose cell is surrounded once by the ring sees
sum_i theta_i^H = 2*pi.  (Verified at the candidate on both hubs.)

SOUND NECESSARY CONDITION.  Every ring edge must be "served" by at least one hub that can
see both of its endpoints (otherwise no interior face/boundary cover is built there).  If
the ring edges split into S (served by A) and S^c (served by B), then
       sum_{i in S} A_i >= 2*pi        and        sum_{i in S^c} B_i >= 2*pi .
Hence any legal configuration must admit a partition (S,S^c) with both sums >= 2*pi.
"no partition works" is a certified arithmetic exclusion (cluster capacity).
"""
import json, numpy as np
from pathlib import Path
from scipy.optimize import differential_evolution, minimize

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
OBJ = HERE.parent.parent / "cline2-sharp-fan" / "out" / "certified_object_copy.json"
log = []
def P(*a):
    s = " ".join(str(x) for x in a); print(s); log.append(s)

obj = json.loads(OBJ.read_text(encoding="utf-8"))
C = np.array([[int(a) / 1e17, int(b) / 1e17] for a, b in obj["centers_scaled_1e17"]])
Rcert = float(obj["certified_interval"]["lo"])
HA, HB = C[0], C[2]
ring0 = C[[1, 3, 4, 5, 6, 7, 8, 9, 10]]
ord0 = np.argsort(np.arctan2(ring0[:, 1], ring0[:, 0]))
ring0 = ring0[ord0]
lab0 = np.array([1, 3, 4, 5, 6, 7, 8, 9, 10])[ord0]
INF = np.inf

def edge_tables(ring, hA, hB, R):
    nxt = np.roll(np.arange(9), -1)
    dA = np.linalg.norm(ring - hA, axis=1); dB = np.linalg.norm(ring - hB, axis=1)
    # NOTE: np.where evaluates BOTH branches; arccos(clip(inf))=0, so build with a mask.
    sA = np.full(9, INF); sB = np.full(9, INF)
    mA = dA <= 2 * R; mB = dB <= 2 * R
    sA[mA] = np.arccos(np.clip(dA[mA] / (2 * R), -1, 1))
    sB[mB] = np.arccos(np.clip(dB[mB] / (2 * R), -1, 1))
    a = sA + sA[nxt]; b = sB + sB[nxt]
    def turns(H):
        t = np.arctan2(*(ring - H).T)
        d = np.diff(np.append(t, t[0] + 2 * np.pi))
        return np.minimum(d, 2 * np.pi - d)
    return a, b, turns(hA), turns(hB), sA, sB, dA, dB

def partition_margin(a, b):
    """max over subsets S (served by A, complement served by B) of min(sum_S a, sum_{S^c} b).
    S may be empty or everything (a degenerate partition is allowed as a limit; it then just
    says one hub serves the whole ring, which is stronger than needed, so nothing is lost).
    Sound exclusion: a legal cover requires SOME partition with both sums >= 2pi;
    margin < 2pi => no legal cover with these tables."""
    m = len(a)
    best = -INF
    for mask in range(0, 1 << m):
        idx = np.array([(mask >> i) & 1 for i in range(m)], dtype=bool)
        sa, sb = a[idx].sum(), b[~idx].sum()
        if np.isfinite(sa) and np.isfinite(sb):
            best = max(best, min(sa, sb))
    return best

P("certified R = %.17f" % Rcert)
P("\n=== (1) candidate calibration: exact, no optimisation ===")
for R in (Rcert, 0.38):
    a, b, thA, thB, sA, sB, dA, dB = edge_tables(ring0, HA, HB, R)
    P(f"\n  R = {R:.17f}")
    P("    edge     " + " ".join(f"{lab0[i]:>2d}-{lab0[(i+1)%9]:<2d}" for i in range(9)))
    P("    a_i      " + " ".join(("%6.3f" % v if np.isfinite(v) else "  --  ") for v in a))
    P("    b_i      " + " ".join(("%6.3f" % v if np.isfinite(v) else "  --  ") for v in b))
    P("    thA      " + " ".join("%6.3f" % v for v in thA))
    P("    thB      " + " ".join("%6.3f" % v for v in thB))
    P(f"    sum thA = {thA.sum():.12f}   sum thB = {thB.sum():.12f}   (2pi = {2*np.pi:.12f})")
    fa = np.isfinite(a); fb = np.isfinite(b)
    P(f"    A-servable edges {[i for i in range(9) if fa[i]]}   sum a there = {a[fa].sum():.10f}")
    P(f"    B-servable edges {[i for i in range(9) if fb[i]]}   sum b there = {b[fb].sum():.10f}")
    P(f"    edges served by neither hub: {[i for i in range(9) if not fa[i] and not fb[i]]}")
    P(f"    partition margin = {partition_margin(a,b):.10f}   (2pi = {2*np.pi:.10f})"
      f"   margin-2pi = {partition_margin(a,b)-2*np.pi:+.6f}")
    tt = [i for i in range(9) if fa[i] and abs(a[i] - thA[i]) < 1e-9]
    tt2 = [i for i in range(9) if fb[i] and abs(b[i] - thB[i]) < 1e-9]
    P(f"    served edges where the bound is TIGHT (a_i = thA_i): {tt}")
    P(f"    served edges where the bound is TIGHT (b_i = thB_i): {tt2}")

P("\n=== (2) global search: minimal partition margin over configurations ===")
def neg_margin(v, R):
    ring = v[0:18].reshape(9, 2); hA = v[18:20]; hB = v[20:22]
    if np.any(np.linalg.norm(ring, axis=1) > 1.0 + 1e-12):
        return 1e3
    if np.linalg.norm(hA) > 1 - R + 1e-12 or np.linalg.norm(hB) > 1 - R + 1e-12:
        return 1e3
    a, b, *_ = edge_tables(ring, hA, hB, R)
    mg = partition_margin(a, b)
    return 1e3 if not np.isfinite(mg) else -mg

def opt_margin(R, seeds=(0, 1), budget=(150, 16)):
    bounds = [(-1, 1)] * 18 + [(-(1 - R), 1 - R)] * 4
    x0 = np.concatenate([ring0.ravel(), HA, HB])
    best, bx = 1e9, x0
    for s in seeds:
        rng = np.random.default_rng(s)
        start = x0 + np.concatenate([rng.normal(0, .1, 18), rng.normal(0, .02, 4)])
        res = differential_evolution(neg_margin, bounds, args=(R,), seed=s, maxiter=budget[0],
                                     tol=1e-9, popsize=budget[1], mutation=(0.3, 1.2),
                                     recombination=0.9, polish=True, init='sobol', updating='deferred')
        if res.fun < best:
            best, bx = res.fun, res.x
    r2 = minimize(neg_margin, bx, args=(R,), method='Nelder-Mead',
                  options=dict(maxiter=40000, maxfev=80000, xatol=1e-13, fatol=1e-15))
    if r2.fun < best:
        best, bx = r2.fun, r2.x
    return -best, bx

summary = {}
for R in (0.375, 0.3799, 0.3799838, 0.38, 0.3805, 0.382, 0.385):
    mg, x = opt_margin(R)
    ring = x[0:18].reshape(9, 2); hA = x[18:20]; hB = x[20:22]
    summary[R] = mg
    P(f"  R = {R:.7f}: min margin = {mg:.8f}   margin-2pi = {mg-2*np.pi:+.6f}"
      f"   {'*** EXCLUDED ***' if mg < 2*np.pi else 'not excluded'}")
    P(f"             hA=({hA[0]:+.4f},{hA[1]:+.4f}) hB=({hB[0]:+.4f},{hB[1]:+.4f})")

(OUT / "decisive_experiment.json").write_text(json.dumps(
    {"certified_R": Rcert, "min_margin": {str(k): float(v) for k, v in summary.items()}}, indent=1))
(OUT / "decisive_experiment.txt").write_text("\n".join(log) + "\n")
P("\nwrote " + str(OUT / "decisive_experiment.txt"))
