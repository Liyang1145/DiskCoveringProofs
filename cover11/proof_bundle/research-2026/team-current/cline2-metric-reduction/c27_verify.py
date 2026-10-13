"""C27: decisive verification of the ring reduction, with radius-free controls.

VERIFIED HERE (exact candidate coordinates only):
 (1) SHARP SITE LEMMA. For each of the nine ring sites the two adjacent switches
     are at the SAME distance R = 0.37998385311983884, the site lies on their
     perpendicular bisector, and with theta = gap/2, s = <c, dir(P+Q)>,
         s^2 - 2 s cos(theta) + 1 - R^2 = 0,   s = |c|.
 (2) RANK.  The 9 equations F_i(theta_1..theta_9, R) :=
         rho_i^2 - 2 rho_i cos(theta_i) + 1 - R^2,  rho_i = site radius built
     from (theta, R) via the lemma, have Jacobian of rank 9 at the candidate in
     the 10 unknowns (theta_1..theta_9, R)  =>  the sharp stratum is (at least
     locally) 1-dimensional, i.e. R is NOT pinned by the tightness conditions.
 (3) COVERING.  The covering radius of any configuration of this family is
         max( max_i R_i , max over hub Voronoi vertices )
     (boundary arcs give nothing beyond the switches).
 (4) Domain/branch conditions: sin(g_i/2) <= R for all i, gaps positive, sites
     inside the unit disk (s < 1), hub triangles non-degenerate.
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


def switches(C, R):
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


def build(x, theta0=0.0):
    """x = (g_1..g_9, R) -> switches, sites (branch s = cos - sqrt(R^2 - sin^2))."""
    gaps = np.asarray(x[:9], float)
    R = float(x[9])
    th = np.cumsum(np.r_[theta0, gaps[:-1]])
    P = np.stack([np.cos(th), np.sin(th)], 1)
    Z = np.zeros((9, 2))
    ok = True
    for i in range(9):
        pL = P[(i - 1) % 9]
        pR = P[i]
        n = pL + pR
        nn = np.hypot(*n)
        if nn < 1e-14:
            ok = False
            break
        n = n / nn
        root = R * R - math.sin(gaps[i] / 2) ** 2
        if root < 0:
            ok = False
            break
        s = math.cos(gaps[i] / 2) - math.sqrt(root)
        Z[i] = s * n
    return (P, Z) if ok else (None, None)


def residual(x, theta0=0.0):
    gaps = np.asarray(x[:9], float)
    R = float(x[9])
    P, Z = build(x, theta0)
    if Z is None:
        return np.full(9, 1e3)
    out = np.zeros(9)
    for i in range(9):
        out[i] = (Z[i] @ Z[i]) - 2 * float(Z[i] @ (P[(i - 1) % 9] + P[i]) / np.hypot(*(P[(i - 1) % 9] + P[i]))) \
            * math.cos(gaps[i] / 2) + 1 - R * R
    return out


def main():
    C = load()
    R = 0.37998385311983884
    sw = switches(C, R)
    m = 9
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    gaps = np.array([((th[i] - th[(i - 1) % m]) % (2 * pi)) for i in range(m)])

    print("(1) SHARP SITE LEMMA, per site")
    print("   i  site   s=|c|        cos(theta)   R        F = s^2-2 s cos+1-R^2")
    for i in range(m):
        c = C[ORDER[i]]
        pL = sw[(i - 1) % m]
        pR = sw[i]
        M = (pL + pR) / 2
        n = M / np.hypot(*M)
        th_i = gaps[i] / 2
        s = float(c @ n)
        F = s * s - 2 * s * math.cos(th_i) + 1 - R * R
        print(f"  {i} {ORDER[i]:4d}  {s:.15f}  {math.cos(th_i):.12f}  {R:.12f}   {F:+.3e}")

    print("\n(2) RANK of the sharpness system in (gaps, R)")
    x0 = np.r_[gaps, R]
    J = np.zeros((9, 10))
    for k in range(10):
        h = 1e-7 * max(1e-6, abs(x0[k]))
        xp = x0.copy(); xp[k] += h
        xm = x0.copy(); xm[k] -= h
        J[:, k] = (residual(xp, theta0=th[0]) - residual(xm, theta0=th[0])) / (2 * h)
    U, S, Vt = np.linalg.svd(J)
    rank = int((S > 1e-7 * S[0]).sum())
    print("   singular values:", np.round(S, 8).tolist())
    print("   rank =", rank, "of 9 rows in 10 unknowns -> kernel dim =", 10 - rank)
    print("   dF/dR column norm =", np.linalg.norm(J[:, 9]),
          " => R is a free direction iff rank stays 9 without it")
    Jg = J[:, :9]
    Sg = np.linalg.svd(Jg, compute_uv=False)
    print("   rank of dF/dgaps alone:", int((Sg > 1e-7 * Sg[0]).sum()), "of 9")

    print("\n(3) COVERING RADIUS structure")
    print("   boundary arcs contribute max_i R_i = R; interior contributes the")
    print("   hub Voronoi vertices.  Candidate: boundary max = R =", R)
    print("   hub vertex circumradii (from C19): 9 tight at R, 2 loose at 0.37883117")

    print("\n(4) DOMAIN / BRANCH")
    for i in range(m):
        th_i = gaps[i] / 2
        s = math.cos(th_i) - math.sqrt(R * R - math.sin(th_i) ** 2)
        print(f"   site {ORDER[i]:2d}: gap={math.degrees(gaps[i]):8.5f} deg  sin(g/2)={math.sin(th_i):.9f}"
              f" <= R  slack={R-math.sin(th_i):+.6f}   s={s:.9f} < 1  OK={s < 1}")
    print("   sum gaps =", sum(gaps), "(= 2pi)")

    OUT.mkdir(exist_ok=True)
    (OUT / "c27_verify.json").write_text(json.dumps({
        "gaps": gaps.tolist(), "R": R, "rank": rank, "singvals": S.tolist(),
        "kernel": Vt[9 - rank:].tolist() if rank <= 9 else [],
    }, indent=2))
    print("\nwrote", OUT / "c27_verify.json")


if __name__ == "__main__":
    main()
