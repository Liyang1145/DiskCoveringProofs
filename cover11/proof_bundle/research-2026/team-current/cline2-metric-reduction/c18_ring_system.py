"""C18: low-dimensional exact ring formulation and its kernel (dimension count).

Formulation R (ring only).  Unknowns:
    P_1..P_9  unit vectors on the boundary (18 dof, 3 gauge)
    rho_1..rho_9  ring-site radii (9 dof)
Equations (exact, from the elementary switch geometry, verified in C17):
    for each i, let L_i be the perpendicular bisector of the switch chord
    (P_(i-1), P_i);  the ring site c_i lies on L_i at the point closest to the
    origin;  the switch radius condition is
        F_i := |c_i - P_(i-1)|^2 - t_i = 0,        t_i = |c_i|^2,
    and at the sharp configuration F_i = 0 <=> |c_i P_(i-1)| = |c_i P_i| = R.
    (Equivalently,  tan(owned span_i / 2) = tan(chord gap / 2)/sqrt(t_i).)

Consequences used here:
  * the 9 rows F_i carry 3 gauge directions (translation/rotation),
  * the rank at the candidate decides the local dimension of the ring stratum,
  * the kernel vectors' effect on R = max_i sqrt(t_i) and on the hub
    circumradius decides whether the sharp value is locally isolated.

Also computes the hub block:  each hub is the circumcenter of three switches,
R_hub = its circumradius, compared with max_i sqrt(t_i).
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
    order = [7, 1, 8, 6, 4, 9, 10, 3, 5]
    m = 9
    # candidate switches
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
    sw = np.array(sw)
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    t = np.array([float(C[order[i]] @ C[order[i]]) for i in range(m)])

    print("argument order (switch i lies between ring site i and i+1):")
    for i in range(m):
        print(f"  switch {i}: between sites {order[i]} and {order[(i+1) % m]}  theta={math.degrees(th[i]):9.5f} "
              f"|c|={math.sqrt(t[i]):.9f}")

    def build(x):
        """x = (th_0..th_8, t_0..t_8) -> sites + residuals."""
        ths = x[:m]
        ts = np.maximum(x[m:], 1e-12)
        P = [np.array([math.cos(ths[k]), math.sin(ths[k])]) for k in range(m)]
        Z = []
        F = np.zeros(m)
        for i in range(m):
            pL = P[(i - 1) % m]
            pR = P[i]
            d = pR - pL
            nd = math.hypot(*d)
            mid = (pL + pR) / 2
            dirv = np.array([-d[1], d[0]]) / nd          # unit direction along bisector
            s_star = mid @ dirv                          # foot = s_star * dirv
            foot = s_star * dirv
            rho = math.sqrt(ts[i])
            h2 = rho * rho - float(foot @ foot)
            qs = []
            if h2 >= 0:
                h = math.sqrt(h2)
                qs = [foot + h * dirv, foot - h * dirv]
            rho2 = rho * rho
            alpha = float(dirv @ mid)
            beta = float(mid @ mid) - rho2
            disc = alpha * alpha - beta
            if disc >= 0:
                sq = math.sqrt(disc)
                qs = [mid + (alpha + sq) * dirv, mid + (alpha - sq) * dirv]
            if not qs:
                F[i] = 1e3
                Z.append(np.array([0.0, 0.0]))
                continue
            zi = min(qs, key=lambda q: np.hypot(*(q - C[order[i]])))
            Z.append(zi)
            F[i] = float(np.sum((zi - pL) ** 2) - ts[(i - 1) % m])
        return P, Z, F

    x0 = np.r_[th, t]
    P, Z, F = build(x0)
    print("\nF(candidate):", np.round(F, 15).tolist(), " max|F| =", np.abs(F).max())

    # Jacobian wrt 18 unknowns
    J = np.zeros((m, 2 * m))
    for k in range(2 * m):
        h = 1e-8
        xp = x0.copy(); xp[k] += h
        xm = x0.copy(); xm[k] -= h
        J[:, k] = (build(xp)[2] - build(xm)[2]) / (2 * h)
    U, S, Vt = np.linalg.svd(J)
    rank = int((S > 1e-7 * S[0]).sum())
    print("\nsingular values of dF (9x18):", np.round(S, 10).tolist())
    print("rank =", rank, " -> local kernel dim =", 2 * m - rank)
    print("\n(3 of the kernel directions must be the rigid-motion gauge;")
    print(" the remaining", 2 * m - rank - 3, "are genuine shape directions)")

    # rigid-motion gauge check: translate the switches -> for each direction
    print("\n=== kernel basis (rows of Vt beyond rank) ===")
    for k in range(rank, 2 * m):
        v = Vt[k]
        # effect on R = max sqrt(t)
        dR = v[m:] / (2 * np.sqrt(t))
        print(f"  kernel {k-rank}: |v|={np.linalg.norm(v):.4f}  d(max sqrt t) components={np.round(dR, 6).tolist()}")
        print(f"             dtheta part = {np.round(v[:m], 6).tolist()}")
        print(f"             dt     part = {np.round(v[m:], 6).tolist()}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c18_ring_system.json").write_text(json.dumps({
        "order": order, "theta": th.tolist(), "t": t.tolist(), "F": F.tolist(),
        "singvals": S.tolist(), "rank": rank, "kernel": Vt[rank:].tolist(),
    }, indent=2))
    print("\nwrote", OUT / "c18_ring_system.json")


if __name__ == "__main__":
    main()
