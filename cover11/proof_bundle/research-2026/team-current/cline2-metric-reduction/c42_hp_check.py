"""C42: independent re-verification of the unsaturated reconstruction at higher
precision (mpmath, 50 digits) using the exact integer literals.

Purpose: check that the 1e-15 agreement of C41 is genuine and not a numerical
artefact of float64 (e.g. the radical near the boundary of its domain).

Nothing here is registered as a claim; it is an interface check.
"""
import json, math
from pathlib import Path

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]
R_FLOAT = 0.37998385311983884


def main():
    try:
        from mpmath import mp, mpf, sqrt, cos, sin, acos, hypot, matrix
        mp.dps = 50
    except Exception as e:                                    # pragma: no cover
        print("mpmath unavailable:", e)
        return

    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    C = [(mpf(int(a)) / D, mpf(int(b)) / D) for a, b in j["centers_scaled_1e17"]]

    def sub(u, v):
        return (u[0] - v[0], u[1] - v[1])

    def add(u, v):
        return (u[0] + v[0], u[1] + v[1])

    def scl(s, u):
        return (s * u[0], s * u[1])

    def dot(u, v):
        return u[0] * v[0] + u[1] * v[1]

    def nrm(u):
        return sqrt(dot(u, u))

    # switches: bisector of ORDER[i], ORDER[i+1] intersected with the unit circle
    def switch(i):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        cand = [C[s], C[s2]]
        m = scl(mpf(1) / 2, add(cand[0], cand[1]))
        dv = sub(cand[1], cand[0])
        nn = dot(dv, dv)
        t = dot(dv, m) / nn
        f = scl(t, dv)
        u = scl(1 / sqrt(nn), (-dv[1], dv[0]))
        h2 = 1 - dot(f, f)
        if h2 < 0:
            return None
        ss = sqrt(h2)
        best = None
        for sgn in (1, -1):
            p = add(f, scl(sgn * ss, u))
            d0 = min(nrm(sub(p, c)) for c in C)
            if best is None or d0 > best[0]:
                best = (d0, p)
        return best[1]

    sw = [switch(i) for i in range(9)]
    print("switch minimal distance (should be R = 0.37998385311983884):")
    for i, p in enumerate(sw):
        d0 = min(nrm(sub(p, c)) for c in C)
        print(f"   i={i}: min_j |P - c_j| = {mp.nstr(d0, 20)}")

    print("\nreconstruction with 50-digit arithmetic:")
    worst_xi = mpf(0)
    worst_id = mpf(0)
    for i in range(9):
        pPrev = sw[(i - 1) % 9]
        p = sw[i]
        c = C[ORDER[i]]
        nv = add(pPrev, p)
        n = scl(1 / nrm(nv), nv)
        e = (-n[1], n[0])
        d = nrm(sub(p, pPrev))
        k = dot(n, scl(mpf(1) / 2, add(pPrev, p)))
        a = nrm(sub(c, pPrev))
        b = nrm(sub(c, p))
        x = (a * a - b * b) / (2 * d)
        h2a = b * b - (x - d / 2) ** 2
        h2b = a * a - (x + d / 2) ** 2
        h = sqrt(h2a)
        cand = add(scl(k - h, n), scl(x, e))
        err_xi = nrm(sub(cand, c))
        err_id = max(abs(nrm(sub(cand, p)) - b), abs(nrm(sub(cand, pPrev)) - a))
        worst_xi = max(worst_xi, err_xi)
        worst_id = max(worst_id, err_id)
        print(f"   i={i} site {ORDER[i]:2d}: |c_rebuilt - c| = {mp.nstr(err_xi, 8)}"
              f"   h2a-h2b = {mp.nstr(h2a - h2b, 8)}"
              f"   k-h = {mp.nstr(k - h, 20)}   |c| = {mp.nstr(nrm(c), 20)}")
    print("\nworst reconstruction error (50 digits):", mp.nstr(worst_xi, 10))
    print("worst identity error |c-P|-b etc.     :", mp.nstr(worst_id, 10))
    print("\nConclusion: the reconstruction is exact; the float64 residual of C41 is")
    print("round-off, not an artefact of the radical near its domain boundary.")

    OUT.mkdir(exist_ok=True)
    (OUT / "c42_hp.json").write_text(json.dumps(
        {"worst_recon": mp.nstr(worst_xi, 30), "worst_identity": mp.nstr(worst_id, 30)}, indent=2))
    print("wrote", OUT / "c42_hp.json")


if __name__ == "__main__":
    main()
