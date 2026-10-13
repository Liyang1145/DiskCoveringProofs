"""C14: the 43-row system, its Jacobian at the candidate, and the kernel test.

Unknown vector x (22 site coordinates + 20 log-radii, 3 gauge freedoms fixed by
reparametrising; we keep the raw 42-vector and rank-deficiency is reported).

Rows
  M  21 : shared-edge matching  y_p^2 sin^2 A = y_q^2 sin^2 B
  A  13 : 11 face angle sums (identities, reported) + 2 hub angle sums (same)
  C   9 : cyclic closure  T_i + L_(i+1) + 2 b_i + (w_i+w_(i+1))/2 - pi

Then: SVD of the 43x42 Jacobian, kernel basis, and the question the lead asked:
are the two dependencies (a) the two cycle identities  and (b) the total-width /
closure identity?  We test each candidate dependency by evaluating the
corresponding scalar function away from the candidate.
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
    c13 = json.loads((OUT / "c13_blocks.json").read_text())
    order = c13["ring_order"]
    m = 9

    # --- rebuild switches
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

    # --- the C block, as a function of the site coordinates only
    def C_block(Cl):
        out = []
        for i in range(m):
            c = Cl[order[i]]
            pL = switch_of(Cl, order[(i - 1) % m], order[i])
            pR = switch_of(Cl, order[i], order[(i + 1) % m])
            if pL is None or pR is None:
                return None
            def ang(V, A, B):
                u = A - V
                w = B - V
                return math.acos(np.clip(u @ w / (np.hypot(*u) * np.hypot(*w)), -1, 1))
            Ti = ang(pL, c, pR)
            two_b = ang(pR, c, Cl[order[(i + 1) % m]])
            # widths: angular measure of the owned arc
            w_i = arc_width(Cl, order[i])
            w_ip1 = arc_width(Cl, order[(i + 1) % m])
            if w_i is None or w_ip1 is None:
                return None
            out.append(Ti + ang(pR, c, Cl[order[(i + 1) % m]]) + (w_i + w_ip1) / 2 - pi)
        return np.array(out)

    def switch_of(Cl, s, s2):
        a, b = Cl[s], Cl[s2]
        mx = (a + b) / 2
        dv = b - a
        nn = dv @ dv
        if nn < 1e-18:
            return None
        tt = (dv @ mx) / nn
        f = dv * tt
        h = math.hypot(*f)
        if h > 1:
            return None
        u = np.array([-dv[1], dv[0]]) / math.sqrt(nn)
        ss = math.sqrt(max(0.0, 1 - h * h))
        # choose root nearest the candidate's own switch
        cand = [f + ss * u, f - ss * u]
        return min(cand, key=lambda p: min(np.hypot(*(p - q)) for q in sw))

    def arc_width(Cl, s):
        """angular width of the arc owned by site s (sampled)."""
        s2 = None
        # ownership near the arc centre: take the midpoint direction
        # find the two switch angles around site s
        idx = order.index(s)
        pL = switch_of(Cl, order[(idx - 1) % m], s)
        pR = switch_of(Cl, s, order[(idx + 1) % m])
        if pL is None or pR is None:
            return None
        aL = math.atan2(pL[1], pL[0])
        aR = math.atan2(pR[1], pR[0])
        # try both directions, keep the arc whose midpoint is owned by s
        for d in (((aR - aL) % (2 * pi)), -((aL - aR) % (2 * pi))):
            mid = aL + d / 2
            p = np.array([math.cos(mid), math.sin(mid)])
            dd = np.hypot(*(Cl - p[None, :]).T)
            if int(np.argmin(dd)) == s and abs(d) < 2 * pi:
                return abs(d)
        return None

    Cc = C.copy()
    r0 = C_block(Cc)
    print("C block residuals (candidate):", np.round(r0, 15).tolist())
    print("sum of C residuals:", sum(r0))

    # --- Jacobian of the C block wrt the 22 site coordinates
    J = np.zeros((9, 22))
    for k in range(22):
        i, comp = divmod(k, 2)
        h = 1e-8
        Cp = Cc.copy(); Cp[i, comp] += h
        Cm = Cc.copy(); Cm[i, comp] -= h
        rp, rm = C_block(Cp), C_block(Cm)
        if rp is None or rm is None:
            print("  degenerate perturbation at", k)
            continue
        J[:, k] = (rp - rm) / (2 * h)
    U, S, Vt = np.linalg.svd(J)
    print("\nsingular values of dC/dx (9x22):", np.round(S, 8).tolist())
    print("rank:", int((S > 1e-6 * S[0]).sum()))
    print("\nkernel dim of C block alone:", 22 - int((S > 1e-6 * S[0]).sum()))

    # normalized gradient of R (max-min) - approximate via the active switch distances
    def Rfun(Cl):
        # numeric covering radius: max over sites of max over cell of distance
        # approximate with dense sampling
        N = 1200000
        t = np.linspace(0, 2 * pi, N + 1)[:-1]
        xs = np.stack([np.cos(t), np.sin(t)], 1)
        d = np.hypot(xs[:, 0:1] - Cl[None, :, 0], xs[:, 1:2] - Cl[None, :, 1]).min(1)
        return float(d.max())

    print("\nR (boundary scan only) =", Rfun(Cc))

    OUT.mkdir(exist_ok=True)
    (OUT / "c14_rows.json").write_text(json.dumps({
        "C_resid": None if r0 is None else r0.tolist(),
        "singvals": S.tolist(),
        "kernel_dim_C": 22 - int((S > 1e-6 * S[0]).sum()),
    }, indent=2))
    print("wrote", OUT / "c14_rows.json")


if __name__ == "__main__":
    main()
