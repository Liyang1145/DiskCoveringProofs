"""r20-chain: THE TWO-HUB RESIDUAL CRITERION (exact/exhaustive form) and its chain reading.

Res := D \\ (union of the 9 ring disks).  A closed disk of radius R covers a compact set S iff
S has diameter <= 2R (the minimal enclosing disk has radius = diam/2).  Therefore

  **Two-hub criterion (necessary and sufficient at the level of the residual set)**
   A legal cover with hubs in H = B(0,1-R) exists  <=>  there is a line ell splitting
   Res into closed pieces Res^-, Res^+ and points h^-, h^+ in H with
        diam(Res^-) <= 2R,  diam(Res^+) <= 2R,  and dist(h^-, conv Res^-) <= R, dist(h^+, conv Res^+) <= R.
   (The hub-centre constraint dist(h, conv S) <= R is exactly the circumradius condition; the
    splitting line is the perpendicular bisector, cf. R20-RESIDUAL-TWO-CENTER.md.)

This file computes, for the certified candidate, the exact diameter of the uncovered set on each
side of the candidate's bisector, and then the CHAIN quantities that the reduction actually needs:
for each of the two chains (contiguous runs of ring sites served by one hub), the maximal distance
from that hub to the residual boundary arc it must cover.
"""
import numpy as np
from scipy.optimize import minimize
from r20geom import load_certified, polar_order, OUT

LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def main():
    C, R, ring_ids = load_certified()
    HA, HB = C[0], C[2]
    ring = C[ring_ids]
    o = polar_order(ring)
    ring, ring_ids = ring[o], ring_ids[o]
    P(f"certified R = {R!r}")

    P("\n=== 1. certified candidate: exact residual quantities ===")
    # dense sample of Res
    NT, NR = 8001, 1201
    th = np.linspace(0, 2 * np.pi, NT, endpoint=False)
    rr = np.linspace(0, 1, NR)
    T, Rg = np.meshgrid(th, rr, indexing="ij")
    pts = np.stack([Rg.ravel() * np.cos(T.ravel()), Rg.ravel() * np.sin(T.ravel())], 1)
    d = np.linalg.norm(pts[:, None, :] - ring[None, :, :], axis=2)
    unc = np.all(d > R, axis=1)
    Res = pts[unc]
    P(f"  residual sample: {Res.shape[0]} points of {pts.shape[0]}")
    dA = np.linalg.norm(Res - HA, axis=1)
    dB = np.linalg.norm(Res - HB, axis=1)
    P(f"  max_{Res} min(d_A,d_B) = {np.minimum(dA,dB).max():.9f}   R = {R:.9f}"
      f"   slack = {R - np.minimum(dA,dB).max():+.3e}")
    # diameter of the two sides of the candidate bisector
    n = (HB - HA) / np.linalg.norm(HB - HA)
    t = float(n @ (HB - HA)) / 2.0
    proj = Res @ n
    for nm, M in (("A-side", proj <= t), ("B-side", proj >= t)):
        S = Res[M]
        if len(S) == 0:
            P(f"  {nm}: empty")
            continue
        # exact-ish diameter by convex hull (scipy) then max pairwise over hull vertices
        from scipy.spatial import ConvexHull
        try:
            H_ = ConvexHull(S)
            V = S[H_.vertices]
        except Exception:
            V = S
        dd = np.linalg.norm(V[:, None, :] - V[None, :, :], axis=2)
        P(f"  {nm}: {len(S)} pts, hull vertices {len(V)}, diameter (sampled) = {dd.max():.9f}"
          f"   2R = {2*R:.9f}   diam - 2R = {dd.max()-2*R:+.6e}")
        for lab, H in (("A", HA), ("B", HB)):
            P(f"        max |{lab} - x| over {nm} = {np.linalg.norm(S-H,axis=1).max():.9f}"
              f"   R - that = {R - np.linalg.norm(S-H,axis=1).max():+.6e}")

    P("\n=== 2. the same residuals expressed per ring-circle (chain reading) ===")
    P("  For each ring i: the residual boundary arcs of Lambda_i (exact) and, for each hub,")
    P("  the maximum distance from the hub to those arcs.")
    from arcs import truly_uncovered_arcs
    P("   ring   arc(centre,hw)           maxdist_A    maxdist_B   single-hub-cover")
    for i in range(len(ring)):
        arcs = truly_uncovered_arcs(ring, i, R)
        if not arcs:
            P(f"   {ring_ids[i]:>4d}   (none)")
            continue
        s = "; ".join(f"({c:.4f},{hw:.4f})" for c, hw in arcs)
        da = db = 0.0
        for (c, hw) in arcs:
            for tt in np.linspace(c - hw, c + hw, 2001):
                x = ring[i] + R * np.array([np.cos(tt), np.sin(tt)])
                da = max(da, float(np.linalg.norm(x - HA)))
                db = max(db, float(np.linalg.norm(x - HB)))
        tag = "A" if da <= R + 1e-9 else ("B" if db <= R + 1e-9 else "NEITHER")
        P(f"   {ring_ids[i]:>4d}   {s:<26s}  {da:.6f}   {db:.6f}   {tag}")

    P("\n=== 3. bisector scan: is the candidate's split the best one? ===")
    P("  (minimise, over directions n and offsets t, the max of the two sides' hub-slacks;")
    P("   slack_side := R - max_x |H - x| with H the free best centre of that side)")

    def side_slack(S, free=True):
        if len(S) == 0:
            return 0.0
        if free:
            # minimal enclosing circle radius of S (approximated on the sampled hull)
            from scipy.spatial import ConvexHull
            try:
                V = S[ConvexHull(S).vertices]
            except Exception:
                V = S
            f = lambda z: np.max(np.linalg.norm(V - z, axis=1))
            r = minimize(f, V.mean(0), method="Nelder-Mead",
                         options=dict(maxiter=20000, maxfev=40000, xatol=1e-11, fatol=1e-13))
            return R - r.fun
        return None

    best = -1e9
    bestpar = None
    for ang in np.linspace(0, np.pi, 37):
        nv = np.array([np.cos(ang), np.sin(ang)])
        pr = Res @ nv
        for frac in np.linspace(0.05, 0.95, 19):
            tt = np.quantile(pr, frac)
            S1 = Res[pr <= tt]
            S2 = Res[pr >= tt]
            v = min(side_slack(S1), side_slack(S2))
            if v > best:
                best, bestpar = v, (ang, tt, len(S1), len(S2))
    P(f"  best bisector (free centres): slack = {best:+.6f}  (ang={bestpar[0]:.4f}, |S1|={bestpar[2]},"
      f" |S2|={bestpar[3]})")

    (OUT / "two_hub_criterion.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "two_hub_criterion.txt"))


if __name__ == "__main__":
    main()
