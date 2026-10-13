"""C30: audit-response computations.

(1) Is the OWNED ARC WIDTH equal to the SWITCH GAP?  (lead says yes by definition)
    Measured directly: gap = angular distance between the two switches bounding the
    owned arc; width = angular measure of the owned run.  Both measured.
(2) Correct closure residual with the switch gaps.
(3) Radial antipodal check: for each site, is its antipodal direction inside its own
    cell?  Exact criterion:  x = -c_i/|c_i| is in cell(i) iff for all j
        (x - c_i).(c_j - c_i) <= 0.
(4) Boundary maxima: the max of the nearest-site distance over the circle is
    attained at a switch (owner changes) unless the antipodal point of the owner
    lies in the owned arc.  Report both.
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def main():
    C = load()
    R = 0.37998385311983884
    N = 2880000
    t = np.linspace(0, 2 * pi, N + 1)[:-1]
    X = np.stack([np.cos(t), np.sin(t)], 1)
    Dm = np.hypot(X[:, 0:1] - C[None, :, 0], X[:, 1:2] - C[None, :, 1])
    own = np.argmin(Dm, 1)
    mn = Dm.min(1)

    runs = []
    start = 0
    for k in range(1, N):
        if own[k] != own[k - 1]:
            runs.append((int(own[k - 1]), t[start], t[k]))
            start = k
    runs.append((int(own[-1]), t[start], t[-1] + 2 * pi))
    if runs[0][0] == runs[-1][0]:
        s0, a0, b0 = runs.pop(0)
        sN, aN, bN = runs.pop()
        runs.insert(0, (s0, aN - 2 * pi, b0))

    print("(1) OWNED ARC WIDTH vs SWITCH GAP")
    print("   site   arc span(deg)   neighbour gaps(deg)   diff")
    for idx, (s, a, b) in enumerate(runs):
        span = b - a
        s_prev = runs[(idx - 1) % len(runs)][0]
        gp = a - runs[(idx - 1) % len(runs)][1]      # gap between previous switch and this one
        print(f"   {s:4d}   {math.degrees(span):12.8f}   {math.degrees(gp):12.8f}   "
              f"{math.degrees(span - gp):+.2e}")

    print("\n(2) closure residual with TRUE switch gaps (no grid measurement)")
    sw = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
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
    sw = np.array(sw)
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    gaps = np.array([((th[i] - th[(i - 1) % 9]) % (2 * pi)) for i in range(9)])

    def ang(V, A, B):
        u = A - V
        w = B - V
        return math.acos(np.clip(u @ w / (np.hypot(*u) * np.hypot(*w)), -1, 1))

    worst = 0.0
    res = []
    for i in range(9):
        c = C[ORDER[i]]
        pL = sw[(i - 1) % 9]
        pR = sw[i]
        T = ang(pL, c, pR)
        Ln = ang(pR, C[ORDER[(i + 1) % 9]], pL)       # base angle at P_i in triangle (P_i, c_{i+1}, P_{i-1})
        two_b = ang(pR, c, C[ORDER[(i + 1) % 9]])
        r = T + Ln + two_b + (gaps[i] + gaps[(i + 1) % 9]) / 2 - pi
        res.append(r)
        worst = max(worst, abs(r))
    print("   per-site residuals (rad):", [f"{x:+.3e}" for x in res])
    print("   max|residual| =", worst, "  sum =", sum(res))

    print("\n(3) RADIAL ANTIPODAL CHECK (exact criterion)")
    print("   site  |c|       is -c/|c| in cell(i)?   min_j [(x-c_i).(c_j-c_i)]  (<=0 means yes)")
    for i in range(11):
        c = C[i]
        rho = np.hypot(*c)
        x = -c / rho
        vals = [float((x - c) @ (C[j] - c)) for j in range(11) if j != i]
        mx = max(vals)
        print(f"   {i:4d} {rho:.6f}   {'YES' if mx <= 0 else 'no '}                    {mx:+.6f}")

    print("\n(4) where is the max of the nearest-site distance on the circle?")
    k = int(np.argmax(mn))
    print("   global max over circle =", mn.max(), " at theta =", th and math.degrees(t[k]) % 360)
    print("   (switch angles deg):", np.round(np.degrees(th) % 360, 5).tolist())
    # check each owned arc: is the owner's antipode inside?
    print("\n   per owned arc: owner, its |c|, whether its antipode lies in the arc,")
    print("   and the arc's max of the nearest-site distance")
    for idx, (s, a, b) in enumerate(runs):
        ph_ant = (math.atan2(C[s][1], C[s][0]) + pi) % (2 * pi)
        inarc = (a % (2 * pi)) <= ph_ant <= (b % (2 * pi)) if b > a else True
        # max over grid points in this run
        lo = int((((a % (2 * pi))) / (2 * pi)) * N)
        hi = int((((b % (2 * pi))) / (2 * pi)) * N)
        if hi <= lo:
            hi = N
        seg = mn[lo:hi]
        am = float(seg.max()) if len(seg) else float('nan')
        print(f"     site {s:2d}: |c|={np.hypot(*C[s]):.6f}  antipode_in_arc={inarc}"
              f"   arc max = {am:.9f}  (rho+1 = {np.hypot(*C[s])+1:.6f})")

    OUT.mkdir(exist_ok=True)
    (OUT / "c30_audit.json").write_text(json.dumps({
        "runs": [[int(s), a, b] for s, a, b in runs],
        "gaps": gaps.tolist(), "closure": res,
    }, indent=2))
    print("\nwrote", OUT / "c30_audit.json")


if __name__ == "__main__":
    main()
