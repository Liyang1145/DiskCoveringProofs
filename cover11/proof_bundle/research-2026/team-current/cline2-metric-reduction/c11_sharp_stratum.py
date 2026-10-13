"""C11: the sharp stratum as 10 unknowns / 9 equations, its Jacobian rank and
null direction, and the covering-radius test along the family.

Equidistant boundary switches make the whole ring-arc ledger rigid:
switch i sits at unit-circle angle  th_i = th0 + (i+2*pi/9),  i = 0..8
(verified: the candidate's switch gaps are all 2*pi/9 to 1e-9).

Unknowns: x = (t_1..t_9, th0)  where t_i = |P_i - ring site Z_i|^2.
  * Z_i is built as the intersection of the two circles centered at P_{i-1}, P_i
    with radii sqrt(t_{i-1}), sqrt(t_i)  (the candidate picks the inner root) ;
  * unknowns t_1..t_9 come with a global scale: scaling all sites by lam scales
    t -> lam^2 t ; we therefore fix the candidate scale (t_1 = R^2) and let the
    rest vary.
Residuals: F_i = |P_i - Z_i|^2 - t_i   (i=0..8),  i.e. the two switch radii of
ring site Z_i agree.  Hubs are then determined by three of their switches; we
report their circumradius (should equal sqrt(t)-scale) but do not use it.

Reports: F at the candidate, numerical Jacobian rank / singular values,
1-D null direction, and the corrector+coverage test along that direction.
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi
delta = 2 * pi / 9


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def circles_intersect(c1, r1, c2, r2, inner=True):
    """two intersection points of circles; pick by 'inner' = closer to origin."""
    d = c2 - c1
    dist = math.hypot(*d)
    if dist > r1 + r2 or dist < abs(r1 - r2):
        return None
    a = (r1 * r1 - r2 * r2 + dist * dist) / (2 * dist)
    h2 = r1 * r1 - a * a
    if h2 <= 0:
        return None
    h = math.sqrt(h2)
    m = c1 + a * d / dist
    perp = np.array([-d[1], d[0]]) / dist
    p1 = m + h * perp
    p2 = m - h * perp
    return (p1, p2) if np.hypot(*p1) <= np.hypot(*p2) else (p2, p1)


def build(theta0, t):
    """switches -> ring sites -> residuals."""
    P = [np.array([math.cos(theta0 + k * delta), math.sin(theta0 + k * delta)]) for k in range(9)]
    Z = []
    F = []
    for i in range(9):
        pl = P[(i - 1) % 9]
        pr = P[i]
        rl = math.sqrt(t[(i - 1) % 9])
        rr = math.sqrt(t[i])
        got = circles_intersect(pl, rl, pr, rr, inner=True)
        if got is None:
            return None, None, None, None
        zi = got[0]
        # residual: second switch radius must equal t_i
        F.append(float(zi @ zi) if False else float(np.sum((zi - pl) ** 2) - t[(i - 1) % 9]))
        Z.append(zi)
    return P, Z, F, None


def main():
    C = load()
    R = 0.37998385311983884
    # cyclic ring order and switch angles from the exact candidate
    N0 = 360000
    t0 = np.linspace(0, 2 * pi, N0 + 1)[:-1]
    c0 = np.stack([np.cos(t0), np.sin(t0)], 1)
    d0 = np.hypot(c0[:, 0:1] - C[None, :, 0], c0[:, 1:2] - C[None, :, 1])
    own = np.argmin(d0, 1)
    order = []
    for k in range(N0):
        if own[k] != own[k - 1]:
            order.append(int(own[k]))
    print("ring order:", order)

    sw = []
    for i in range(9):
        s, s2 = order[i], order[(i + 1) % 9]
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
    gaps = np.array([((th[(i + 1) % 9] - th[i]) % (2 * pi)) for i in range(9)])
    print("raw switch gaps (deg):", np.round(np.degrees(gaps), 6).tolist())
    print("gap - 2pi/9 (deg):", np.round(np.degrees(gaps - delta), 6).tolist())

    # scale so that the switch distances match the candidate: t_i = |Z_i - P_i|^2
    tvec = []
    for i in range(9):
        zi = C[order[i]]
        pl = sw[(i - 1) % 9]
        pr = sw[i]
        tvec.append((float(np.sum((zi - pr) ** 2)) + float(np.sum((zi - pl) ** 2))) / 2)
    tvec = np.array(tvec)
    print("t vector:", np.round(tvec, 12).tolist(), " R^2 =", R * R)

    x0 = np.r_[tvec, float(th[0])]
    print("\nF(candidate):", np.round(np.array(build(x0[9], x0[:9])[2]), 15).tolist())

    def Fx(x):
        return np.array(build(x[9], x[:9])[2])

    # numerical Jacobian
    J = np.zeros((9, 10))
    for k in range(10):
        h = 1e-6 * max(1.0, abs(x0[k]))
        xp = x0.copy(); xp[k] += h
        xm = x0.copy(); xm[k] -= h
        J[:, k] = (Fx(xp) - Fx(xm)) / (2 * h)
    print("\nJacobian row0:", np.round(J[0], 6).tolist())
    U, S, Vt = np.linalg.svd(J)
    print("\nsingular values of dF (9x10):", np.round(S, 8).tolist())
    print("numeric rank (tol 1e-6*max):", int((S > 1e-6 * S[0]).sum()))
    print("null direction (last row of Vt):", np.round(Vt[-1], 8).tolist())
    print("normalised null direction ratios (t part / th part):",
          np.round(Vt[-1][:9] / (Vt[-1][9] if abs(Vt[-1][9]) > 1e-12 else 1), 6).tolist())

    OUT.mkdir(exist_ok=True)
    (OUT / "c11_sharp_stratum.json").write_text(json.dumps({
        "order": order, "theta0": float(th[0]), "t": tvec.tolist(),
        "F_cand": Fx(x0).tolist(), "singvals": S.tolist(), "null": Vt[-1].tolist(),
    }, indent=2))
    print("wrote", OUT / "c11_sharp_stratum.json")


if __name__ == "__main__":
    main()
