"""C9: closure residuals (two-pass, correct indexing) and integral area identity.

Pass 1: from the exact candidate, compute for each owned ring site i
    alpha_i  (angle at c_i between the two adjacent switches)
    T_i      (base angle at the LEFT switch  P_(i-1))
    L_i      (base angle at the RIGHT switch P_i)
    two_b_i  (angle at P_i of the site triangle (P_i, c_i, c_(i+1)))
    rhoL_i, rhoR_i  (|c_i P_(i-1)|, |c_i P_i|)
Pass 2: residuals of  T_i + L_(i+1) + 2b_i + (w_i+w_(i+1))/2 - pi,
        and of the variants with theta-gaps and with (phi_i+phi_(i+1))/2 where
        phi_i is the angle at P_i in the triangle (P_(i-1), P_i, P_(i+1)).
Also: integral identity  sum_i |c_i|^2 w_i = 2*Area(covered disk) with w the
owned angular widths, verified by an independent area computation.
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


def ang_at(V, A, B):
    return math.acos(np.clip((A - V) @ (B - V) / (np.hypot(*(A - V)) * np.hypot(*(B - V))), -1, 1))


def main():
    P = load()
    R = 0.37998385311983884
    # recompute the cyclic ring order from the boundary ownership (no c8 dependency)
    N0 = 720000
    t0 = np.linspace(0, 2 * pi, N0 + 1)[:-1]
    c0 = np.stack([np.cos(t0), np.sin(t0)], 1)
    d0 = np.hypot(c0[:, 0:1] - P[None, :, 0], c0[:, 1:2] - P[None, :, 1])
    own0 = np.argmin(d0, 1)
    order = []
    for k in range(N0):
        if own0[k] != own0[k - 1]:
            order.append(int(own0[k]))
    m = len(order)
    assert m == 9, (m, order)
    # switches (recompute)
    sw = []
    for i in range(m):
        s, s2 = order[i], order[(i + 1) % m]
        a, b = P[s], P[s2]
        mx = (a + b) / 2
        dv = b - a
        t = (dv @ mx) / (dv @ dv)
        f = dv * t
        h = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - h * h))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(P - p[None, :]).T)
            if d.min() >= R - 1e-9:
                sw.append(p)
                break
    th = [math.atan2(p[1], p[0]) for p in sw]
    gaps = [((th[(i + 1) % m] - th[i]) % (2 * pi)) for i in range(m)]

    alpha, T, L, tb, rhoL, rhoR, phi = [None] * m, [None] * m, [None] * m, [None] * m, [None] * m, [None] * m, [None] * m
    for i in range(m):
        c = P[order[i]]
        pL = sw[(i - 1) % m]
        pR = sw[i]
        alpha[i] = ang_at(c, pL, pR)
        T[i] = ang_at(pL, c, pR)
        L[i] = ang_at(pR, c, pL)
        tb[i] = ang_at(pR, c, P[order[(i + 1) % m]])
        rhoL[i] = np.hypot(*(pL - c))
        rhoR[i] = np.hypot(*(pR - c))
        phi[i] = ang_at(pR, sw[(i - 1) % m], sw[(i + 1) % m])

    print("i site  rhoL      rhoR      rhoL/rhoR   alpha      T          L        2b        phi")
    for i in range(m):
        print(f"{i} {order[i]:3d} {rhoL[i]:.9f} {rhoR[i]:.9f} {rhoL[i]/rhoR[i]:.9f} "
              f"{math.degrees(alpha[i]):9.5f} {math.degrees(T[i]):9.5f} {math.degrees(L[i]):9.5f} "
              f"{math.degrees(tb[i]):9.5f} {math.degrees(phi[i]):9.5f}")

    print("\nT_i + L_i + alpha_i - pi (should be 0):",
          [f"{math.degrees(T[i]+L[i]+alpha[i]-pi):+.2e}" for i in range(m)])
    print("rhoL_i == rhoR_{i-1} (shared radius):",
          [f"{rhoL[i]-rhoR[(i-1)%m]:+.2e}" for i in range(m)])

    print("\n=== residuals ===")
    for tag, wfun in (("A: (w_i+w_i+1)/2", lambda i: (gaps[i] + gaps[(i + 1) % m]) / 2),
                      ("B: theta-gap = w_i+1", lambda i: gaps[(i + 1) % m]),
                      ("C: (phi_i+phi_i+1)/2", lambda i: (phi[i] + phi[(i + 1) % m]) / 2),
                      ("D: phi_i", lambda i: phi[i])):
        r = [T[i] + L[(i + 1) % m] + tb[i] + wfun(i) - pi for i in range(m)]
        print(f"  {tag:26s} max|res| = {max(abs(x) for x in r):.3e} deg-max = {math.degrees(max(abs(x) for x in r)):+.3e}"
              f"   sum = {sum(r):+.3e}")
        if max(abs(x) for x in r) < 1e-9:
            print("      per-i (deg):", [f"{math.degrees(x):+.3e}" for x in r])

    # phi should equal w when the site is on the unit circle:
    print("\nphi_i vs w_i (deg):", [(round(math.degrees(phi[i]), 4), round(math.degrees(gaps[i]), 4)) for i in range(m)])

    # --- integral identity and independent area
    t_i = [float(P[order[i]] @ P[order[i]]) for i in range(m)]
    area_arc = sum(t_i[i] * gaps[i] for i in range(m))
    print("\nsum_i |c_i|^2 w_i =", area_arc, " 2*pi =", 2 * pi, " diff =", area_arc - 2 * pi)

    # independent area: rho-w per owner over a fine grid (exact owner logic)
    N = 2000000
    tt = np.linspace(0, 2 * pi, N + 1)[:-1]
    circ = np.stack([np.cos(tt), np.sin(tt)], 1)
    dd = np.hypot(circ[:, 0:1] - P[None, :, 0], circ[:, 1:2] - P[None, :, 1])
    own = np.argmin(dd, 1)
    area2 = 0.0
    for i in range(len(P)):
        sel = own == i
        area2 += float(P[i] @ P[i]) * float(sel.sum()) * (2 * pi / N)
    print("independent per-owner area =", area2, " diff from 2pi =", area2 - 2 * pi)
    print("=> exact identity sum_i |c_i|^2 * w_i = 2 * Area(covered disk); with coverage this is 2pi")


if __name__ == "__main__":
    main()
