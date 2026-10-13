"""Exact covering radius: max of (nearest-site distance) over the critical set
  * circumcentres of triples that lie in the disk,
  * bisector-cap S1 points of every pair,
  * radial S1 points (both directions) of every site.
For a finite site set the covering radius is attained on this set."""
import json, math, sys, itertools
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

def candidates(S):
    S = np.asarray(S, float)
    n = len(S)
    pts = []
    tags = []
    for i, j, k in itertools.combinations(range(n), 3):
        A = 2 * np.array([S[j] - S[i], S[k] - S[i]])
        b = np.array([S[j] @ S[j] - S[i] @ S[i], S[k] @ S[k] - S[i] @ S[i]])
        det = A[0, 0] * A[1, 1] - A[0, 1] * A[1, 0]
        if abs(det) < 1e-14:
            continue
        x = np.linalg.solve(A, b)
        if x @ x <= 1.0:
            pts.append(x); tags.append(("circ", (i, j, k)))
    for i, j in itertools.combinations(range(n), 2):
        d = S[j] - S[i]
        ra = np.linalg.norm(d)
        if ra < 1e-14: continue
        b = float(S[j] @ S[j] - S[i] @ S[i]) / 2
        if abs(b) > ra: continue
        phi = math.atan2(d[1], d[0]); c = math.acos(max(-1, min(1, b / ra)))
        for th in (phi + c, phi - c):
            x = np.array([math.cos(th % (2 * math.pi)), math.sin(th % (2 * math.pi))])
            pts.append(x); tags.append(("bis", (i, j)))
    for i in range(n):
        r = np.linalg.norm(S[i])
        if r > 1e-14:
            for s in (1, -1):
                pts.append(s * S[i] / r); tags.append(("rad", (i, s)))
    return np.array(pts), tags

def cover_radius_exact(S):
    P, tags = candidates(S)
    d = np.linalg.norm(P[:, None, :] - np.asarray(S)[None, :, :], axis=2)
    mn = d.min(1)
    j = int(np.argmax(mn))
    return float(mn[j]), P[j], tags[j], len(P)

if __name__ == "__main__":
    U = 0.33173203427623414
    cand = np.array([[float(__import__("fractions").Fraction(x)) for x in p]
                     for p in json.loads((HERE.parent.parent / "lead" / "improved-upper-test.json")
                                         .read_text())["centers"]])
    cfgs = json.loads((HERE / "violating-configs.json").read_text())
    pushed = json.loads((HERE / "pushed-config.json").read_text())
    for name, S in (("campaign candidate", cand),
                    ("counterexample (cand+1e-6 noise, rep0)", np.array(cfgs[0]["sites"])),
                    ("pushed (descent) config", np.array(pushed["sites"])),
                    ("counterexample #2 (scale 1e-6 rep1)", np.array(cfgs[1]["sites"]))):
        r, x, tag, npts = cover_radius_exact(S)
        print(f"{name:42s} r_exact={r:.12f}  r-U={r-U:+.3e}  argmax={np.round(x,6)} via {tag} "
              f"(candidates={npts})")
