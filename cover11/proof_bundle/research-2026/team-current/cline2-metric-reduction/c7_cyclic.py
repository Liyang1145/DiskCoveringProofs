"""C7: corrected cyclic core sequence.

Fixes the wrap bug of C6: boundary arc runs are computed on a cyclic grid and
merged across theta = 0.  Then the cyclic sequence (owner_i, tight S_i) is
printed and the incidence pattern between consecutive tight points is recorded.
"""
import json, math
from pathlib import Path
import numpy as np

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
    R = 0.37998385311983884

    N = 720000
    th = np.linspace(0, 2 * pi, N + 1)[:-1]
    circ = np.stack([np.cos(th), np.sin(th)], 1)
    dd = np.hypot(circ[:, 0:1] - P[None, :, 0], circ[:, 1:2] - P[None, :, 1])
    own = np.argmin(dd, 1)
    # cyclic run decomposition starting at index 0
    runs = []
    start = 0
    for k in range(1, N):
        if own[k] != own[k - 1]:
            runs.append((int(own[k - 1]), th[start], th[k]))
            start = k
    runs.append((int(own[-1]), th[start], th[-1] + 2 * pi))
    if len(runs) > 1 and runs[0][0] == runs[-1][0]:
        s0, a0, b0 = runs.pop(0)
        sN, aN, bN = runs.pop(-1)
        runs.insert(0, (s0, aN - 2 * pi, b0))
    print("=== boundary owned arcs, cyclic order (site, theta0, theta1, width) ===")
    tot = 0.0
    for s, a, b in runs:
        w = b - a
        tot += w
        print(f"  site {s:2d}: [{a:+.9f},{b:+.9f}] w={w:.9f}")
    print("  #arcs =", len(runs), " sum w =", tot, " 2pi =", 2 * pi)

    # switch point between consecutive arcs: outermost point of the shared boundary
    tight = json.loads((OUT / "c5_tight.json").read_text())
    S = {tuple(e["sites"]): np.array(e["p"]) for e in tight["switch_tight"]}
    V = {tuple(e["sites"]): np.array(e["p"]) for e in tight["vor_tight"]}

    print("\n=== cyclic core sequence ===")
    seq = []
    for k, (s, a, b) in enumerate(runs):
        s2 = runs[(k + 1) % len(runs)][0]
        key = tuple(sorted((s, s2)))
        sp = S.get(key)
        seq.append(("S", key, sp))
        # attached tight interior vertices (V) involving site s that are adjacent to s's cell
        for kk, v in V.items():
            if s in kk:
                seq.append(("V", kk, v))
    def ang(p):
        return math.atan2(p[1], p[0])
    seq.sort(key=lambda e: (ang(e[2]) % (2 * pi)))
    prev = None
    for kind, sites, p in seq:
        t = ang(p) % (2 * pi)
        share = "" if prev is None else f" shared_with_prev={sorted(set(prev[1]) & set(sites))}"
        print(f"  {kind} theta={t:.9f} |p|={np.hypot(*p):.9f} sites={list(sites)}{share}")
        prev = (kind, sites, p)

    # consecutive sharing pattern including wrap
    print("\n=== consecutive sharing pattern (incl. wrap) ===")
    m = len(seq)
    for k in range(m):
        a = set(seq[k][1])
        b = set(seq[(k + 1) % m][1])
        print(f"  {k:2d}->{(k+1)%m:2d}: {seq[k][0]}{sorted(a)} -> {seq[(k+1)%m][0]}{sorted(b)}  |cap|={len(a & b)}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c7_cyclic.json").write_text(json.dumps({
        "arcs": [{"site": int(s), "t0": a, "t1": b, "w": b - a} for s, a, b in runs],
        "seq": [{"kind": k, "sites": list(s), "p": p.tolist()} for k, s, p in seq],
    }, indent=2))
    print("\nwrote", OUT / "c7_cyclic.json")


if __name__ == "__main__":
    main()
