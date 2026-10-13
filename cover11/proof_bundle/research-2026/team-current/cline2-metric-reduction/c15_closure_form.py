"""C15: identify the exact closure equation satisfied by the candidate.

For each owned ring site i (exact candidate coordinates):
  g_i  = angular gap between its two switches on the unit circle
  w_i  = angular width of the site's OWNED arc (the locus with this site
         nearest), which satisfies  tan(w_i/2) = tan(g_i/2)/t_i  with
         t_i = |c_i| ;  equivalently w_i = g_i only when the site is interior
         and the arc arc is the "far" arc.
  T_i  = base angle at the LEFT switch, L_i at the RIGHT switch, 2b_i the
         angle at the right switch of the site triangle.
Tested residuals:
  R1 = T_i + L_(i+1) + 2 b_i + (g_i + g_(i+1))/2 - pi
  R2 = T_i + L_(i+1) + 2 b_i + (w_i + w_(i+1))/2 - pi
  R3 = T_i + L_(i+1) + 2 b_i + (r_i + r_(i+1))/2 - pi, with r_i = 2atan(t tan(g/2))
Reporting exact algebraic identities for their sums.
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
    R = 0.37998385311983884
    N0 = 1440000
    t0 = np.linspace(0, 2 * pi, N0 + 1)[:-1]
    c0 = np.stack([np.cos(t0), np.sin(t0)], 1)
    d0 = np.hypot(c0[:, 0:1] - C[None, :, 0], c0[:, 1:2] - C[None, :, 1])
    own = np.argmin(d0, 1)
    order = []
    for k in range(N0):
        if own[k] != own[k - 1]:
            order.append(int(own[k]))
    m = len(order)
    print("ring order:", order)
    # switches
    sw = []
    for i in range(m):
        s, s2 = order[i], order[(i + 1) % m]
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
    g = np.array([((th[(i + 1) % m] - th[i]) % (2 * pi)) for i in range(m)])
    t = np.array([float(np.hypot(*C[order[i]])) for i in range(m)])
    w = 2 * np.arctan(np.tan(g / 2) / t)
    def ang(V, A, B):
        u = A - V
        wv = B - V
        return math.acos(np.clip(u @ wv / (np.hypot(*u) * np.hypot(*wv)), -1, 1))
    T = []; L = []; b2 = []
    for i in range(m):
        c = C[order[i]]
        pL = sw[(i - 1) % m]
        pR = sw[i]
        T.append(ang(pL, c, pR))
        L.append(ang(pR, c, pL))
        b2.append(ang(pR, c, C[order[(i + 1) % m]]))
    T = np.array(T); L = np.array(L); b2 = np.array(b2)
    print("\ni  site  g(deg)   w(deg)   |c|      T(deg)   L(deg)   2b(deg)")
    for i in range(m):
        print(f"{i} {order[i]:4d} {math.degrees(g[i]):8.5f} {math.degrees(w[i]):8.5f} {t[i]:.7f} "
              f"{math.degrees(T[i]):9.5f} {math.degrees(L[i]):9.5f} {math.degrees(b2[i]):9.5f}")
    for tag, sq in (("R1 (gaps g)", (g + np.roll(g, -1)) / 2),
                    ("R2 (owned w)", (w + np.roll(w, -1)) / 2)):
        r = T + np.roll(L, -1) + b2 + sq - pi
        print(f"\n{tag}: max|res| = {max(abs(r)):.3e}  sum = {sum(r):.12f}")
        print("   per-i (deg):", [f"{math.degrees(x):+.2e}" for x in r])
    print("\nsum g =", sum(g), " sum w =", sum(w), " 2pi =", 2 * pi)
    print("sum (g - w) =", sum(g - w))
    print("sum(alpha_i) + sum(L_i) + sum(w)/1 : alpha_i = pi - T_i - L_i")
    alpha = pi - T - L
    print("   sum alpha =", sum(alpha), " sum 2b =", sum(b2), " pi =", pi)
    print("   identity check: sum(alpha) - 2pi - sum(b2) + pi =", sum(alpha) - 2 * pi - sum(b2) + pi)
    print("   sum R2 =", sum(T + np.roll(L, -1) + b2 + (w + np.roll(w, -1)) / 2 - pi))
    print("   sum g + sum w =", sum(g) + sum(w))
    OUT.mkdir(exist_ok=True)
    (OUT / "c15_closure_form.json").write_text(json.dumps({
        "order": order, "g": g.tolist(), "w": w.tolist(), "t": t.tolist(),
        "T": T.tolist(), "L": L.tolist(), "b2": b2.tolist(),
        "R1": (T + np.roll(L, -1) + b2 + (g + np.roll(g, -1)) / 2 - pi).tolist(),
        "R2": (T + np.roll(L, -1) + b2 + (w + np.roll(w, -1)) / 2 - pi).tolist(),
    }, indent=2))
    print("\nwrote", OUT / "c15_closure_form.json")


if __name__ == "__main__":
    main()
