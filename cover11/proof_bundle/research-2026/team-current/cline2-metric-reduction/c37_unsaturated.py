"""C37: UNSATURATED global ring model, correct conventions (final).

ORDERING FIX.  The switches must be listed in the cyclic order induced by the
sites: site i lies between switch i-1 and switch i, so
    w_i = angle(switch_(i-1), switch_i)   (the owned width of site i)
and the switches are sorted by angle.  (My earlier scripts picked, for each
adjacent site pair, the bisector-circle intersection closest to the candidate's
own switch, which mixed the cyclic order.)

Per-site reconstruction (lead's formulas, re-derived):
    n = dir(P_(i-1) + P_i)   (perpendicular to the chord, towards the sites)
    e = rotate(n, 90 deg)    (along the chord)
    k = cos(w_i/2), d = 2 sin(w_i/2)
    x = (a_i^2 - b_i^2)/(2d),  h = (d^2 + b_i^2 - a_i^2)/(2d)
    c_i = (k - h) n + x e
with  |c_i - P_(i-1)| = a_i, |c_i - P_i| = b_i,  |c_i|^2 = (k-h)^2 + x^2.
Feasibility: h >= 0  <=>  |a_i - b_i| <= d <= a_i + b_i  (triangle inequality).

Free data: 9 widths (sum 2 pi) + 9 left radii + 9 right radii + 2 hubs = 21 after
rotation; the bound r is an extra variable.  Covering gives a_i, b_i <= r.
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


def sorted_switches(C, R):
    """switch between site ORDER[i] and ORDER[i+1], then sorted by angle."""
    raw = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        hh = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - hh * hh))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= R - 1e-9:
                raw.append((p, s, s2))
                break
    return raw


def main():
    C = load()
    R = 0.37998385311983884
    raw = sorted_switches(C, R)
    # cyclic order: follow the ring order
    order_of_sw = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        p = [q for (q, x, y) in raw if (x, y) == (s, s2)][0]
        order_of_sw.append(p)
    sw = np.array(order_of_sw)
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    # check cyclic monotonicity
    dth = np.array([((th[(i + 1) % 9] - th[i]) % (2 * pi)) for i in range(9)])
    print("cyclic gaps between consecutive switches (deg):", np.round(np.degrees(dth), 5).tolist())
    print("all positive and sum 2pi:", abs(sum(dth) - 2 * pi) < 1e-12)

    # site i lies between switch i-1 and switch i => width_i = angle(sw_(i-1), sw_i)
    ws = np.array([math.acos(np.clip(sw[(i - 1) % 9] @ sw[i], -1, 1)) for i in range(9)])
    aa = np.array([float(np.hypot(*(C[ORDER[i]] - sw[(i - 1) % 9]))) for i in range(9)])
    bb = np.array([float(np.hypot(*(C[ORDER[i]] - sw[i]))) for i in range(9)])
    print("\ncandidate ring data")
    print("  i site  w_i(deg)    a_i(left)     b_i(right)   max-R")
    for i in range(9):
        print(f"  {i} {ORDER[i]:4d} {math.degrees(ws[i]):9.5f}  {aa[i]:.12f}  {bb[i]:.12f}  {max(aa[i],bb[i])-R:+.2e}")

    th0 = float(th[0])
    P = np.stack([np.cos(th), np.sin(th)], 1)
    Z = np.zeros((9, 2))
    okall = True
    for i in range(9):
        pL = P[(i - 1) % 9]
        pR = P[i]
        nvec = pL + pR
        n = nvec / np.hypot(*nvec)
        e = np.array([-n[1], n[0]])
        d = 2 * math.sin(ws[i] / 2)
        k = math.cos(ws[i] / 2)
        x = (aa[i] ** 2 - bb[i] ** 2) / (2 * d)
        # h from the radical  h^2 = a^2 - (x + d/2)^2 :  with x = (d/2) tan(alpha)
        # one gets the exact rational form (d*k + b^2 - a^2)/(2d)
        h = (d * k + bb[i] ** 2 - aa[i] ** 2) / (2 * d)
        if h < -1e-12:
            okall = False
        Z[i] = (k - h) * n + x * e
    print("\nreconstruction from (w, a, b):")
    err = 0.0
    for i in range(9):
        e = float(np.hypot(*(Z[i] - C[ORDER[i]])))
        err = max(err, e)
        print(f"   i={i} site {ORDER[i]:2d} err={e:.2e}   |c|={np.hypot(*Z[i]):.9f}"
              f"  cand |c|={np.hypot(*C[ORDER[i]]):.9f}")
    print("   max error:", err, " all radicals ok:", okall)

    print("\ncheck |c-P_left| = a, |c-P_right| = b:")
    worst = 0.0
    for i in range(9):
        worst = max(worst, abs(float(np.hypot(*(Z[i] - P[(i - 1) % 9]))) - aa[i]),
                    abs(float(np.hypot(*(Z[i] - P[i]))) - bb[i]))
    print("   max deviation:", worst)

    print("\ndomain: triangle inequality per site")
    for i in range(9):
        d = 2 * math.sin(ws[i] / 2)
        print(f"   i={i}: d={d:.9f} |a-b|={abs(aa[i]-bb[i]):.2e} a+b={aa[i]+bb[i]:.9f}"
              f"  ok={abs(aa[i]-bb[i]) <= d <= aa[i]+bb[i] + 1e-12}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c37_unsaturated.json").write_text(json.dumps({
        "order": ORDER, "w": ws.tolist(), "a": aa.tolist(), "b": bb.tolist(),
        "theta": th.tolist(), "recon_err": err, "radicals_ok": bool(okall),
    }, indent=2))
    print("\nwrote", OUT / "c37_unsaturated.json")


if __name__ == "__main__":
    main()
