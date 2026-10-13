"""C34: all-site saturation system — is the 9-ring sharp stratum really 8-dimensional?

Unknowns: the nine ring-site coordinates (18) ; the switches are functions of them
(the bisector x unit-circle intersection), so the saturation conditions are

    Saw_i(theta_1..theta_9) := (|c_i - P_(i-1)|^2 - |c_i - P_i|^2) / R^2 = 0
    Srad_i := (|c_i - P_(i-1)|^2 - R^2) / R^2 = 0

Here we ONLY use Saw (9 conditions) and show that the set
    { sites : all switches equidistant }  is what the gap construction realises
with |c_i - P| = R being automatic, i.e. we measure the rank and check whether
R remains a free direction.

Outputs: Jacobian rank, kernel directions, and the movement of R along them.
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]
R = 0.37998385311983884


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def switch_of(c1, c2, hint):
    """intersection of the bisector of (c1,c2) with the unit circle near hint."""
    mx = (c1 + c2) / 2
    dv = c2 - c1
    nn = dv @ dv
    tt = (dv @ mx) / nn
    f = dv * tt
    h = math.hypot(*f)
    if h > 1:
        return None
    u = np.array([-dv[1], dv[0]]) / math.sqrt(nn)
    ss = math.sqrt(max(0.0, 1 - h * h))
    cands = [f + ss * u, f - ss * u]
    return min(cands, key=lambda p: np.hypot(*(p - hint)))


def main():
    C = load()
    sites = C[ORDER]                     # the nine ring sites, in cyclic order
    sw_hint = []
    for i in range(9):
        a, b = sites[i], sites[(i + 1) % 9]
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
                sw_hint.append(p)
                break
    sw_hint = np.array(sw_hint)

    def F(x):
        """x = 18 coords of the nine sites (cyclic order)."""
        S = x.reshape(9, 2)
        out = np.zeros(9)
        for i in range(9):
            pL = switch_of(S[(i - 1) % 9], S[i], sw_hint[(i - 1) % 9])
            pR = switch_of(S[i], S[(i + 1) % 9], sw_hint[i])
            if pL is None or pR is None:
                return None
            # equidistance of c_i to its two switches, normalised
            out[i] = (np.sum((S[i] - pR) ** 2) - np.sum((S[i] - pL) ** 2)) / (R * R)
        return out

    x0 = sites.ravel().copy()
    F0 = F(x0)
    print("F(candidate) max:", np.abs(F0).max())

    J = np.zeros((9, 18))
    for k in range(18):
        h = 1e-7
        xp = x0.copy(); xp[k] += h
        xm = x0.copy(); xm[k] -= h
        Fp, Fm = F(xp), F(xm)
        if Fp is None or Fm is None:
            continue
        J[:, k] = (Fp - Fm) / (2 * h)
    U, S, Vt = np.linalg.svd(J)
    rank = int((S > 1e-6 * S[0]).sum())
    print("singular values:", np.round(S, 6).tolist())
    print("rank =", rank, "of 9 rows in 18 unknowns -> kernel dim =", 18 - rank)

    # effect of kernel directions on R = max |c_i|
    rho = np.hypot(*sites.T)
    imax = int(np.argmax(rho))
    print("max |c| at site index", imax, "value", rho[imax])
    print("\nkernel directions and their effect on |c| of the largest site:")
    for k in range(rank, 18):
        v = Vt[k]
        dv = v.reshape(9, 2)
        # d |c_imax|
        dR = float(dv[imax] @ sites[imax] / rho[imax])
        # does the direction rotate/translate all sites (gauge)?
        print(f"  k={k}: d|c_max| = {dR:+.6e}   coords = {np.round(v, 5).tolist()}")

    OUT.mkdir(exist_ok=True)
    (OUT / "c34_saturation_system.json").write_text(json.dumps({
        "rank": rank, "singvals": S.tolist(), "kernel": Vt[rank:].tolist()}, indent=2))
    print("\nwrote", OUT / "c34_saturation_system.json")


if __name__ == "__main__":
    main()
