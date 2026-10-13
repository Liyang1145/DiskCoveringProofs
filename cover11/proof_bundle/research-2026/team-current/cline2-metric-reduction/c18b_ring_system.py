"""C18b: low-dimensional exact ring formulation, correctness-controlled.

Unknowns  x = (theta_0..theta_8, t_0..t_8):
    switch i  = (cos theta_i, sin theta_i) on the unit circle;
    ring site i  = the point of the perpendicular bisector of the chord
        (switch i-1, switch i) at distance sqrt(t_i) from the origin (the
        branch closest to the candidate);
    F_i(x) = |site_i - switch_(i-1)|^2 - t_(i-1)          (want 0)

Controls printed first:
   C1  F(candidate) = 0  (with the candidate theta and t)
   C2  the two named root branches give |z - c| = 0 one of them
   C3  the identity  tan(w_i/2) * sqrt(t_i) = tan(gap/2) at the solution
Then the Jacobian, its rank, kernel, and the effect of the kernel on R.
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


ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def candidate_switches(C, R):
    m = 9
    sw = []
    for i in range(m):
        s, s2 = ORDER[i], ORDER[(i + 1) % m]
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
    return np.array(sw)


def build(x, C):
    m = 9
    ths = x[:m]
    ts = x[m:]
    P = [np.array([math.cos(ths[k]), math.sin(ths[k])]) for k in range(m)]
    Z = []
    F = np.zeros(m)
    for i in range(m):
        pL = P[(i - 1) % m]
        pR = P[i]
        d = pR - pL
        nd = math.hypot(*d)
        mid = (pL + pR) / 2
        dirv = np.array([-d[1], d[0]]) / nd
        rho = math.sqrt(max(ts[i], 1e-300))
        alpha = float(dirv @ mid)
        beta = float(mid @ mid) - rho * rho
        disc = alpha * alpha - beta
        if disc < 0:
            Z.append(np.array([0.0, 0.0]))
            F[i] = 1e3
            continue
        sq = math.sqrt(disc)
        cands = [mid + (-alpha + sq) * dirv, mid + (-alpha - sq) * dirv]
        zi = min(cands, key=lambda q: np.hypot(*(q - C[ORDER[i]])))
        Z.append(zi)
        F[i] = float(np.sum((zi - pL) ** 2) - ts[(i - 1) % m])
    return P, Z, F


def main():
    C = load()
    R = 0.37998385311983884
    sw = candidate_switches(C, R)
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    t = np.array([float(C[ORDER[i]] @ C[ORDER[i]]) for i in range(9)])
    x0 = np.r_[th, t]

    # control C1
    P, Z, F = build(x0, C)
    print("C1  F(candidate) max|F| =", np.abs(F).max())
    # control C2
    print("C2  |Z_i - c_i| :", [f"{np.hypot(*(Z[i]-C[ORDER[i]])):.2e}" for i in range(9)])
    # control C3: identity tan(w/2)*sqrt(t) = tan(gap/2)
    print("C3  tan(w_i/2)*rho_i - tan(gap_i/2):")
    for i in range(9):
        pL = P[(i - 1) % 9]
        pR = P[i]
        gap = math.acos(np.clip(pL @ pR, -1, 1))
        w = 2 * math.atan(math.tan(gap / 2) / math.sqrt(t[i]))
        print(f"     i={i}  lhs={math.tan(w/2)*math.sqrt(t[i]):.15f}  rhs={math.tan(gap/2):.15f}"
              f"  diff={math.tan(w/2)*math.sqrt(t[i])-math.tan(gap/2):+.2e}")

    # analytic Jacobian (F_i depends on theta_(i-1), theta_i, t_(i-1), t_i)
    def Fx(x):
        return build(x, C)[2]

    J = np.zeros((9, 18))
    for k in range(18):
        h = 1e-7 * max(1e-6, abs(x0[k]))
        xp = x0.copy(); xp[k] += h
        xm = x0.copy(); xm[k] -= h
        J[:, k] = (Fx(xp) - Fx(xm)) / (2 * h)
    U, S, Vt = np.linalg.svd(J)
    rank = int((S > 1e-7 * S[0]).sum())
    print("\nC4  singular values:", np.round(S, 8).tolist())
    print("    rank =", rank, " of 9 rows; kernel dim =", 18 - rank)

    print("\n=== kernel directions ===")
    kern = Vt[rank:]
    for k in range(len(kern)):
        v = kern[k]
        dR = v[9:] / (2 * math.sqrt(t[0])) if False else v[9:] / (2 * np.sqrt(t))
        print(f"  k={k}: dtheta={np.round(v[:9], 5).tolist()}")
        print(f"        dt    ={np.round(v[9:], 5).tolist()}   d sqrt(t)={np.round(dR,5).tolist()}")

    # rigid gauge directions, for comparison
    print("\n=== comparison: rigid-motion directions (should be in the kernel) ===")
    for name, v in (("d theta all +1", np.r_[np.ones(9), np.zeros(9)]),
                    ("translation x", None)):
        if v is None:
            continue
        print(f"  {name}: F change = {np.abs(Fx(x0 + 1e-6 * v) - Fx(x0)).max():.2e}")

    # numeric check of a genuine kernel direction: move along it and re-solve
    print("\n=== numeric: F along the first kernel direction (step s) ===")
    v = kern[0]
    for s in (1e-6, 1e-4, 1e-3):
        xs = x0 + s * v * 1.0
        Fs = Fx(xs)
        Rs = max(math.sqrt(max(q, 0)) for q in xs[9:])
        print(f"  s={s:.0e}  max|F|={np.abs(Fs).max():.4e}  max sqrt(t)={Rs:.15f}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c18b_ring_system.json").write_text(json.dumps({
        "theta": th.tolist(), "t": t.tolist(), "F": F.tolist(),
        "singvals": S.tolist(), "rank": rank, "kernel": Vt[rank:].tolist(),
    }, indent=2))
    print("\nwrote", OUT / "c18b_ring_system.json")


if __name__ == "__main__":
    main()
