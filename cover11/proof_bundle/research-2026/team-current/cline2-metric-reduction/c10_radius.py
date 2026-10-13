"""C10: decisive numeric value of the candidate's covering radius R(C).

R(C) = max over sites i of max_{x in cell(i) cap D} |x - c_i|.
We compute the min-over-sites distance function on a fine polar grid, refine the
argmax by local maximisation, and compare with the exact "tight point" claim
R = 0.37998385311983884.  Also computes max over the circle only.
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def main():
    P = load()
    n = len(P)

    def f(x):
        return np.hypot(*(P - x[None, :]).T).min()

    # --- 1. fine polar grid in the disk
    best = (0.0, None)
    for nr in (400, 1200):
        rs = np.linspace(0, 1, nr + 1)
        nt = max(800, 8 * nr)
        ths = np.linspace(0, 2 * pi, nt + 1)[:-1]
        for r in rs:
            xs = np.stack([r * np.cos(ths), r * np.sin(ths)], 1)
            d = np.hypot(xs[:, 0:1] - P[None, :, 0], xs[:, 1:2] - P[None, :, 1]).min(1)
            k = int(np.argmax(d))
            if d[k] > best[0]:
                best = (float(d[k]), xs[k].copy())
    print("grid best:", best)

    # --- refine with Nelder-Mead from the best grid point and from all exact tight points
    cands = [best[1]]
    tight = json.loads((OUT / "c5_tight.json").read_text())
    for e in tight["vor_tight"]:
        cands.append(np.array(e["p"]))
    for e in tight["switch_tight"]:
        cands.append(np.array(e["p"]) * (1 - 1e-12))
    bestref = (0.0, None)
    for c0 in cands:
        r = minimize(lambda x: -f(x), c0, method="Nelder-Mead",
                     options={"xatol": 1e-14, "fatol": 1e-16, "maxiter": 20000, "maxfev": 20000})
        x = r.x
        if x @ x > 1.0:
            x = x / math.sqrt(x @ x) * (1 - 1e-15)
        if -r.fun > bestref[0]:
            bestref = (float(-r.fun), x.copy())
    print("refined best:", bestref)

    # --- circle-restricted max (very fine, local refinement)
    N = 4000001
    t = np.linspace(0, 2 * pi, N)
    xs = np.stack([np.cos(t), np.sin(t)], 1)
    d = np.hypot(xs[:, 0:1] - P[None, :, 0], xs[:, 1:2] - P[None, :, 1]).min(1)
    k = int(np.argmax(d))
    q = xs[k]
    r = minimize(lambda s: -(np.hypot(*(P - np.array([math.cos(s[0]), math.sin(s[0])])[None, :]).T).min()),
                 [t[k]], method="Nelder-Mead", options={"xatol": 1e-15, "fatol": 1e-17, "maxiter": 5000})
    xr = np.array([math.cos(r.x[0]), math.sin(r.x[0])])
    print("circle max (grid):", d[k], " refined:", -r.fun, "at theta =", r.x[0])

    print("\nR(C) numeric =", max(best[0], bestref[0], -r.fun))
    print("claimed R    = 0.37998385311983884")
    print("difference   =", max(best[0], bestref[0], -r.fun) - 0.37998385311983884)


if __name__ == "__main__":
    main()
