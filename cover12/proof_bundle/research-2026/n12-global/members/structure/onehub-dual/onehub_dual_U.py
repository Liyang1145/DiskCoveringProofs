"""n12 one-hub directional dual LP at the FIXED radius U (numeric scout only).

Adapted (read-only) from research-2026/solo-20260922/scout_directional_dual.py
per instruction: same instrument, threshold R -> U, structure = k=11
(11 boundary-active 'ring' discs + 1 hub disc B(h,R), |h| = e).
Single point calibration: e = 0.04.

Setting.  At radius R the hub cannot touch S^1 (|h|+R <= 3R-1+R = 4R-1 < 1),
so the 11 ring discs alone must cover S^1; and for every eps>0 the hub covers
nothing on the circle |x-h| = R+eps, so the ring alone must cover that circle
too.  Hence for each of these target circles and for every NONNEGATIVE weight
function w on it,
      sum_{i=1..11} (arc integral of w over disc i's arc)  >=  integral of w.
Columns = candidate ring centres on a grid (rho in [1-R,1+R], phi);
rows = the functionals  half,  half +- (sin(k half)/k) cos(k theta),
half +- (sin(k half)/k) sin(k theta)  for the two circles.

Primal LP:  min sum_p x_p  s.t.  A x >= pi * 1,  x >= 0.
Dual (as used): weights w = -marginals;  for every centre p, sum_r w_r A[r,p]
is >= pi, so summing over the 11 discs gives  11 * sup_p(sum_r w_r A[r,p])
>= pi * sum_r w_r,  i.e.  the rescaled bound  pi*sum w / sup  <= 11 is
required.  A bound > 11 would exclude the k=11 structure (numeric only: the
sup is evaluated on a grid, so continuous certification is still missing).

Output: members/structure/onehub-dual/onehub_dual_U_<e>.json  (numeric only).
"""
from pathlib import Path
import json
import sys
import time
import numpy as np
from scipy.optimize import linprog

U = 0.361102963744508672616920293904
EMAX = 3.0 * U - 1.0                       # 0.083308891233526017850760881712
ROOT = Path(__file__).parent


def atoms(R, e, nr, nphi, K):
    rho = np.linspace(1.0 - R, 1.0 + R, nr)
    phi = np.arange(nphi) * 2.0 * np.pi / nphi
    rho, phi = np.meshgrid(rho, phi, indexing="ij")
    rho = rho.ravel()
    phi = phi.ravel()
    t = np.arccos(np.clip((1.0 + rho * rho - R * R) / (2.0 * rho), -1, 1))
    cx = rho * np.cos(phi)
    cy = rho * np.sin(phi)
    ell = np.hypot(cx - e, cy)                      # distance to the hub centre
    psi = np.arctan2(cy, cx - e)
    beta = np.arccos(np.minimum(1.0, ell / (2.0 * R)))   # arc half-width on
    rows, names = [], []                             # |x-h| = R+eps, eps->0
    for tag, half, angle in (("boundary", t, phi), ("hub", beta, psi)):
        rows.append(half)
        names.append(tag + "_uniform")
        for k in range(1, K + 1):
            for kind, phase in (("cos", np.cos(k * angle)),
                                ("sin", np.sin(k * angle))):
                moment = np.sin(k * half) / k * phase
                for sign in (-1, 1):
                    rows.append(half + sign * moment)
                    names.append(f"{tag}_{kind}{k}_{sign}")
    return np.array(rows), names, rho, phi


def run_e(R, e, K, nr=161, nphi=180, nrf=401, nphif=360, tol=1e-7):
    A, names, rho, phi = atoms(R, e, nr, nphi, K)
    res = linprog(np.ones(A.shape[1]), A_ub=-A, b_ub=-np.pi * np.ones(len(A)),
                  bounds=(0, None), method="highs")
    if not res.success:
        return dict(e=e, K=K, status="LP failure: " + str(res.message))
    weights = -res.ineqlin.marginals
    fine, namesf, _, _ = atoms(R, e, nrf, nphif, K)
    vals = weights @ fine
    sup = float(np.max(vals))
    ratio = float(np.pi * np.sum(weights) / max(sup, 1e-300))
    supp = np.flatnonzero(res.x > tol)
    return dict(
        e=e, K=K, R=R, grid=[nr, nphi], fine_grid=[nrf, nphif],
        lp_objective=float(res.fun),
        sum_weights=float(np.sum(weights)),
        fine_max_atom=sup, minmax_ratio=float(sup / np.pi),
        rescaled_dual_bound=ratio, bound_over_11=float(ratio / 11.0),
        weights=[dict(row=names[i], weight=float(w))
                 for i, w in enumerate(weights) if w > 1e-9],
        primal_support=[dict(rho=float(rho[i]), phi=float(phi[i]),
                             mass=float(res.x[i])) for i in supp],
        note="numeric grid relaxation; continuous sup not certified")


def main():
    R = U
    e = float(sys.argv[1]) if len(sys.argv) > 1 else 0.04
    Ks = [int(x) for x in sys.argv[2:]] if len(sys.argv) > 2 else [0, 1, 2, 3]
    t0 = time.time()
    out = dict(U=U, e_max=EMAX, structure="k=11 ring + 1 hub",
               instrument="directional two-circle Fourier dual (numeric)",
               runs=[])
    for K in Ks:
        r = run_e(R, e, K)
        out["runs"].append(r)
        print("e=%.4f K=%d  sum_w=%.4f  fine_max=%.6f  minmax=%.6f  "
              "bound=%.4f  bound/11=%.4f  (%.1fs)"
              % (e, K, r.get("sum_weights", float('nan')),
                 r.get("fine_max_atom", float('nan')),
                 r.get("minmax_ratio", float('nan')),
                 r.get("rescaled_dual_bound", float('nan')),
                 r.get("bound_over_11", float('nan')), time.time() - t0),
              flush=True)
        for rec in r.get("weights", []):
            print("      w[%s] = %.6f" % (rec["row"], rec["weight"]))
    fn = ROOT / ("onehub_dual_U_e%.3f.json" % e)
    fn.write_text(json.dumps(out, indent=1), encoding="utf8")
    print("wrote", fn)


if __name__ == "__main__":
    main()
