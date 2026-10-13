"""Final check of the counterexample: premises, high-precision residual, cell-sector tiling,
robust covering radius."""
import json, math, sys
from pathlib import Path
import numpy as np
from mpmath import mp, mpf, atan2, sqrt, sin, cos, acos, pi, matrix, lu_solve

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from geom_exact import anchor_records, anchors_exact
mp.dps = 60

def cover_radius(S, G=900, topk=12):
    xs = np.linspace(-1, 1, G)
    X, Y = np.meshgrid(xs, xs)
    keep = X ** 2 + Y ** 2 <= 1.0
    P = np.stack([X[keep], Y[keep]], 1)
    d = np.linalg.norm(P[:, None, :] - S[None, :, :], axis=2)
    mn = d.min(1)
    idx = np.argsort(mn)[-topk:]
    best = float(mn[idx[-1]])
    # local refinement (bounded box search around each top point)
    for i0 in idx:
        x = P[i0].copy()
        step = 0.004
        for _ in range(200):
            cand = [x + np.array([dx, dy]) for dx in (-step, 0, step) for dy in (-step, 0, step)]
            vals = [(float(np.min(np.linalg.norm(S - c, axis=1))), c) for c in cand
                    if c[0] ** 2 + c[1] ** 2 <= 1.0]
            v, c = max(vals, key=lambda t: t[0])
            if v > best:
                best = v; x = c
            else:
                step *= 0.6
                if step < 1e-14:
                    break
    return best

def hp_resid(S, A, u, v, Aprev, Anext, s_cw, s_ccw):
    """60-digit residual of 2*gamma + delta_cw + delta_ccw + (theta_cw+theta_ccw)/2 - pi,
    recomputed from raw coordinates (no shared floating point with the numpy path)."""
    Z = [mp.matrix([mpf(float(p[0])), mpf(float(p[1]))]) for p in S]
    Az = mp.matrix([mpf(float(A[0])), mpf(float(A[1]))])
    Pz = mp.matrix([mpf(float(Aprev[0])), mpf(float(Aprev[1]))])
    Nz = mp.matrix([mpf(float(Anext[0])), mpf(float(Anext[0]))])
    Nz = mp.matrix([mpf(float(Anext[0])), mpf(float(Anext[1]))])
    def ang(x, y):
        dot = x[0] * y[0] + x[1] * y[1]
        nx = sqrt(x[0] ** 2 + x[1] ** 2); ny = sqrt(y[0] ** 2 + y[1] ** 2)
        return acos(dot / (nx * ny))
    m = (Z[u] + Z[v]) / 2
    gam = ang(Z[u] - Az, m - Az)
    d_cw = ang(Z[s_cw] - Az, Pz - Az)
    d_ccw = ang(Z[s_ccw] - Az, Nz - Az)
    th_cw = acos((Az[0] * Pz[0] + Az[1] * Pz[1]))
    th_ccw = acos((Az[0] * Nz[0] + Az[1] * Nz[1]))
    return 2 * gam + d_cw + d_ccw + (th_cw + th_ccw) / 2 - pi

if __name__ == "__main__":
    cfgs = json.loads((HERE / "violating-configs.json").read_text())
    cand = np.array([[float(__import__("fractions").Fraction(x)) for x in p]
                     for p in json.loads((HERE.parent.parent / "lead" / "improved-upper-test.json")
                                         .read_text())["centers"]])
    out = open(HERE / "final-check.txt", "w")
    for name, S in (("candidate", cand), ("counterexample(pert 1e-6,rep0)", np.array(cfgs[0]["sites"]))):
        recs, anch = anchor_records(S)
        rc = cover_radius(S, 700)
        print(f"### {name}: n={len(S)} q={len(recs)} robust covering radius = {rc:.9f} "
              f"(U=0.33173203427623414)")
        out.write(f"### {name}: n={len(S)} q={len(recs)} robust covering radius={rc!r}\n")
        nfail = 0
        for r in recs:
            o = r["facet"]
            oz = None if o is None else float(np.linalg.norm(o[0]))
            # direct h_A sign: signed height of A over the line through the two owners,
            # positive on the side of the third site of the closing triple
            u, v = r["pair"]
            w = None if o is None else o[1]
            if w is not None:
                e2 = S[v] - S[u]
                nrm = np.array([-e2[1], e2[0]]) / np.linalg.norm(e2)
                hA = float((r["A"] - S[u]) @ nrm)
                hW = float((S[w] - S[u]) @ nrm)
                hsign = "hA<0 (opposite side to w)" if hA * hW < 0 else "hA>=0"
            else:
                hA, hW, hsign = None, None, "no interior facet vertex"
            fail = abs(r["resid"]) > 1e-9
            if fail: nfail += 1
            th_cw, th_ccw, gam = r["theta_cw"], r["theta_ccw"], r["gam"]
            # cell cone angle at A on the CW side, measured directly: angle between the
            # facet ray and the tangent ray at A pointing CW along the circle
            A = r["A"]
            tangent_cw = np.array([A[1], -A[0]])   # CW tangent (unit)
            m2 = (S[u] + S[v]) / 2
            cellcone = math.acos(max(-1, min(1, float(tangent_cw @ (m2 - A)) /
                                             np.linalg.norm(m2 - A))))
            print(f"  k={r['k']:2d} owners={r['pair']} arcs cw/ccw={r['arc_cw'][0]}/{r['arc_ccw'][0]} "
                  f"gam={gam:.9f} {hsign:26s} |O|={None if oz is None else round(oz,6)} "
                  f"facet_len={None if o is None else round(o[2],6)} nest=({r['nest_ccw']:+.3e},"
                  f"{r['nest_cw']:+.3e}) resid={r['resid']:+.4e} {'FAIL' if fail else ''}")
            print(f"        cell-cone(cw side)={cellcone:.9f} vs delta_cw+gam+theta_cw/2="
                  f"{r['delta_cw'] + gam + th_cw/2:.9f}   |delta_cw|={r['delta_cw']:.6e}")
            out.write(f"  k={r['k']} owners={r['pair']} gam={gam!r} {hsign} |O|={oz!r} "
                      f"resid={r['resid']!r} nest=({r['nest_ccw']!r},{r['nest_cw']!r}) "
                      f"delta_cw={r['delta_cw']!r} cellcone={cellcone!r} "
                      f"delta_cw+gam+th_cw/2={r['delta_cw'] + gam + th_cw/2!r}\n")
        print(f"  -> {nfail} of {len(recs)} claimed cyclicity equations fail (|resid|>1e-9)")
        print()
        out.write(f"  -> {nfail} of {len(recs)} fail\n\n")
    # high precision residual at the worst anchor of the counterexample
    S = np.array(cfgs[0]["sites"])
    recs, anch = anchor_records(S)
    bad = [r for r in recs if abs(r["resid"]) > 1e-9]
    r = bad[0]
    k = r["k"]
    A, u, v = r["A"], r["pair"][0], r["pair"][1]
    Aprev = anch[(k - 1) % len(anch)]["A"]; Anext = anch[(k + 1) % len(anch)]["A"]
    hp = hp_resid(S, A, u, v, Aprev, Anext, r["arc_cw"][0], r["arc_ccw"][0])
    print(f"60-digit residual at k={k} of the counterexample: {mp.nstr(hp, 25)}  "
          f"(float64 path: {r['resid']!r})")
    out.write(f"60-digit residual at k={k}: {mp.nstr(hp, 25)} float64={r['resid']!r}\n")
    # candidate degeneracies
    recsC, anchC = anchor_records(cand)
    print("\ncandidate endpoint angles (deg):")
    for r in recsC:
        print(f"  k={r['k']:2d} delta_cw={math.degrees(r['delta_cw']):.9f} "
              f"delta_ccw={math.degrees(r['delta_ccw']):.9f} gam={math.degrees(r['gam']):.9f} "
              f"nest_cw={r['nest_cw']:+.3e} nest_ccw={r['nest_ccw']:+.3e}")
    out.close()
