"""C16: measure the owned arc widths directly (owner runs on the unit circle)
and determine the exact relation between the switch angular gap g_i and the
owned arc width w_i.

For a site c (|c| = t) whose owned arc is the NEAR arc of the unit circle:
  the arc is the set of unit vectors x with |x-c| <= |x-c'| for neighbours c'.
Sampling gives w_i directly; we test the two candidate closed forms
  (a) tan(w/2) = tan(g/2)/t      (b) tan(w/2) = t*tan(g/2).
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
    C = load()
    N = 7200000
    t0 = np.linspace(0, 2 * pi, N + 1)[:-1]
    c0 = np.stack([np.cos(t0), np.sin(t0)], 1)
    d0 = np.hypot(c0[:, 0:1] - C[None, :, 0], c0[:, 1:2] - C[None, :, 1])
    own = np.argmin(d0, 1)
    # ownership runs, merged cyclically
    runs = []
    start = 0
    for k in range(1, N + 1):
        if k == N or own[k % N] != own[k - 1]:
            runs.append([int(own[k - 1]), k - start, start])
            start = k
    if len(runs) > 1 and runs[0][0] == runs[-1][0]:
        runs[-1][1] += runs[0][1]
        runs.pop(0)
    print("owner runs (site, #grid points, start idx):")
    dth = 2 * pi / N
    widths = {}
    for s, cnt, st in runs:
        print(f"  site {s:2d} width={cnt*dth:.9f}  (theta {st*dth:.9f})")
        widths[s] = cnt * dth
    print("sum widths =", sum(widths.values()), " 2pi =", 2 * pi)

    # switches (recompute) and gaps
    R = 0.37998385311983884
    order = [s for s, _, _ in runs]
    sw = []
    for i in range(len(order)):
        s, s2 = order[i], order[(i + 1) % len(order)]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        h = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - h * h))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= R - 1e-9:
                sw.append(p)
                break
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    m = len(order)
    g = np.array([((th[(i + 1) % m] - th[i]) % (2 * pi)) for i in range(m)])
    t = np.array([float(np.hypot(*C[order[i]])) for i in range(m)])
    wmeas = np.array([widths[order[i]] for i in range(m)])
    print("\ni site   g(rad)     w_meas    tan(w/2)  tan(g/2)  t       ratio tan(w/2)/tan(g/2)  1/t    t")
    for i in range(m):
        A = math.tan(wmeas[i] / 2)
        B = math.tan(g[i] / 2)
        print(f"{i} {order[i]:4d} {g[i]:.9f} {wmeas[i]:.9f} {A:9.6f} {B:9.6f} {t[i]:.7f}  {A/B:9.6f}  {1/t[i]:.6f} {t[i]:.6f}")
    print("\nratio vs 1/t max err:", max(abs(math.tan(wmeas[i]/2)/math.tan(g[i]/2) - 1/t[i]) for i in range(m)))
    print("ratio vs t     max err:", max(abs(math.tan(wmeas[i]/2)/math.tan(g[i]/2) - t[i]) for i in range(m)))
    OUT.mkdir(exist_ok=True)
    (OUT / "c16_arcs.json").write_text(json.dumps({
        "order": order, "g": g.tolist(), "w_meas": wmeas.tolist(), "t": t.tolist(),
        "ratio": [math.tan(wmeas[i] / 2) / math.tan(g[i] / 2) for i in range(m)],
    }, indent=2))
    print("wrote", OUT / "c16_arcs.json")


if __name__ == "__main__":
    main()
