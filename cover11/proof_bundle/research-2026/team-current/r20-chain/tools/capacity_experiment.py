"""r20-chain EXPERIMENT (single bounded mechanism experiment) -- v2, corrected algebra.

Setting: unit closed disk D, 11 congruent radius-R disks covering D. Nine ring sites (one
essential arc each) plus two interior hubs, in the established q0 two-hub structure. Ring
sites ordered counterclockwise about the ORIGIN; ring edge i joins ring site i to i+1.

For a hub H:  spoke deficit  s_H(c) = arccos(|H-c| / (2R))   [required: |H-c| <= 2R]
              edge angle     theta_H(c,c') = angle at H between spokes to c and c'
Face (H,c,c') of the nearest-site triangulation has circumradius <= R
        <=>   |s_H(c) - s_H(c')| <= theta_H(c,c') <= s_H(c) + s_H(c').
(Proof: fix normalisation 2R=1; then |H-c| = cos(s) etc., and circumradius <= R is exactly
 (cos t - cos s cos u)^2 <= sin^2 s sin^2 u, i.e. |s-u| <= t <= s+u.)

IDENTITY (ring arithmetic, same for both hubs -- both hubs see the ring points once each,
so the nine consecutive angular increments around either hub sum to 2pi):
        sum_i theta_{H}(c_i, c_{i+1}) = 2pi     for H = A and H = B.
Note theta_{A}(c_i,c_{i+1}) and theta_{B}(c_i,c_{i+1}) are DIFFERENT numbers, and BOTH are
constrained by each own hub.  Hence the necessary condition
        eta := sum_i min( a_i , b_i ) >= 2pi,
        a_i = s_A(c_i)+s_A(c_{i+1}),  b_i = s_B(c_i)+s_B(c_{i+1}).
A class is excluded as soon as  max over legal configurations of eta  <  2pi.

This script (1) calibrates eta on the certified candidate, (2) maximises eta globally for a
few R values with a bounded budget.
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
ring = C[[1, 3, 4, 5, 6, 7, 8, 9, 10]]
lab = np.array([1, 3, 4, 5, 6, 7, 8, 9, 10])
ang = np.arctan2(ring[:, 1], ring[:, 0]); order = np.argsort(ang)
ring = ring[order]; lab = lab[order]

def edge_data(c, hA, hB, R):
    """c: (9,2) ring sites in polar order. Returns a,b,mn,thA,thB,d."""
    nxt = np.roll(np.arange(len(c)), -1)
    dA = np.linalg.norm(c - hA, axis=1); dB = np.linalg.norm(c - hB, axis=1)
    sA = np.arccos(np.clip(dA / (2 * R), -1.0, 1.0))
    sB = np.arccos(np.clip(dB / (2 * R), -1.0, 1.0))
    a = sA + sA[nxt]; b = sB + sB[nxt]
    thA = (np.roll(np.arctan2(*(c - hA).T), -1) - np.arctan2(*(c - hA).T)) % (2 * np.pi)
    thB = (np.roll(np.arctan2(*(c - hB).T), -1) - np.arctan2(*(c - hB).T)) % (2 * np.pi)
    d = np.linalg.norm(c - np.roll(c, -1, axis=0), axis=1)
    return a, b, np.minimum(a, b), thA, thB, d

def eta_of(hA, hB, psi, R):
    """ring sites = hA + R*(cos psi, sin psi) with |c|>0; polar-ordered; bound eta."""
    c = hA + R * np.stack([np.cos(psi), np.sin(psi)], 1)
    if np.min(np.linalg.norm(c, axis=1)) < 1e-9:
        return -1e9, None
    ao = np.argsort(np.arctan2(c[:, 1], c[:, 0]))
    a, b, mn, thA, thB, d = edge_data(c[ao], hA, hB, R)
    return mn.sum(), dict(a=a, b=b, mn=mn, thA=thA, thB=thB, d=d, c=c[ao])

# ---------------- 1. calibration on the certified candidate ----------------
P("certified R = %.16f" % Rcert)
P("\n=== (1) calibration on the certified candidate (exact geometry, no optimisation) ===")
for R in (Rcert, 0.38):
    a, b, mn, thA, thB, d = edge_data(ring, HA, HB, R)
    P(f"\n  R = {R:.16f}")
    P("    i  edge        a_i          b_i        min(a,b)    theta_A      theta_B    A-tight  B-tight")
    for i in range(9):
        P(f"    {i}  {lab[i]:>2d}-{lab[(i+1)%9]:<2d}  {a[i]:.11f}  {b[i]:.11f}  {mn[i]:.11f}  {thA[i]:.11f}  {thB[i]:.11f}"
          f"   {'Y' if abs(mn[i]-thA[i])<1e-9*(1+abs(thA[i])) or mn[i]>=thA[i]-1e-12 and a[i]<=b[i] else '.'}"
          f"        {'Y' if b[i]<=a[i] else '.'}")
    P(f"    sum theta_A = {thA.sum():.12f}   sum theta_B = {thB.sum():.12f}   (2*pi = {2*np.pi:.12f})")
    P(f"    per-edge feasibility  min(a,b) >= theta_A: {bool(np.all(mn>=thA-1e-12))}"
      f"    min(a,b) >= theta_B: {bool(np.all(mn>=thB-1e-12))}")
    P(f"    eta = sum min(a_i,b_i) = {mn.sum():.12f}    eta - 2*pi = {mn.sum()-2*np.pi:+.6e}"
      f"   ({100*(mn.sum()-2*np.pi)/(2*np.pi):+.4f} %)")

# ---------------- 2. global maximisation of eta ----------------
P("\n=== (2) global max of eta(R) = max sum_i min(a_i,b_i)  [bounded budget] ===")
def neg_eta(v, R):
    hA = v[0:2]; hB = v[2:4]; psi = v[4:13]
    val, _ = eta_of(hA, hB, psi, R)
    return -val

def eta_global(R, seeds=(0, 1, 2)):
    lim = 1 - R
    bounds = [(-lim, lim)] * 4 + [(0, 2 * np.pi)] * 9
    best, bx = -1e9, None
    for s in seeds:
        res = differential_evolution(neg_eta, bounds, args=(R,), seed=s, maxiter=300,
                                     tol=1e-9, popsize=20, mutation=(0.3, 1.2),
                                     recombination=0.9, polish=True, init='sobol',
                                     updating='deferred')
        if -res.fun > best:
            best, bx = -res.fun, res.x
    r2 = minimize(neg_eta, bx, args=(R,), method='Nelder-Mead',
                  options=dict(maxiter=40000, maxfev=80000, xatol=1e-12, fatol=1e-14))
    if -r2.fun > best:
        best, bx = -r2.fun, r2.x
    return best, bx

summary = {}
for R in (0.375, 0.3798, 0.3799838, 0.38, 0.3805, 0.382, 0.385):
    val, x = eta_global(R)
    summary[R] = val
    P(f"  R = {R:.7f}:  max eta = {val:.10f}   eta - 2pi = {val-2*np.pi:+.6e}"
      f"   {'***  EXCLUDED (eta<2pi) ***' if val < 2*np.pi else 'not excluded'}")
    P(f"              argmax: hA=({x[0]:.6f},{x[1]:.6f}) hB=({x[2]:.6f},{x[3]:.6f})")

(OUT / "capacity_experiment.json").write_text(json.dumps(
    {"certified_R": Rcert, "max_eta": {str(k): v for k, v in summary.items()}}, indent=1))
(OUT / "capacity_experiment.txt").write_text("\n".join(log) + "\n")
P("\nwrote " + str(OUT / "capacity_experiment.txt"))
