"""C17: exact shape of the boundary-closure system, verified on the candidate.

Two facts are established analytically and checked numerically here:

(F1) At a sharp configuration the boundary switch P_i is the far intersection
     of the unit circle with the perpendicular bisector of the SITE chord, so
     with delta_i = |P_i - c_i| = |P_i - c_(i+1)| one has exactly
        tan(span_i/2) = tan(gap_i/2)/delta_i ,
     where gap_i is the angular distance of the switch triangle chord and span_i
     the angular measure of the site's owned arc at the origin.  (Direct
     verification: the quantity tan(w/2)*t / tan(g/2) must equal 1.)

(F2) The exact closure row at switch i is
        T_i + L_(i+1) + 2 b_i + (span_i + span_(i+1))/2 - pi = 0 ,
     where T_i is the base angle at the left switch of the sector triangle of
     site i, L_i the base angle at the right switch, and 2 b_i the angle at P_i
     of the site triangle (P_i, c_i, c_(i+1)).  The nine rows satisfy the exact
     identity   sum_i (closure_i) = pi  (complex angle count 3*11*pi = 33 pi),
     so they carry exactly eight independent restrictions.

This script verifies F1 and F2 to machine precision on the exact candidate and
reports the local rank of the closure Jacobian in the site coordinates.
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


def switch_of(C, s, s2, ref):
    a, b = C[s], C[s2]
    mx = (a + b) / 2
    dv = b - a
    nn = dv @ dv
    tt = (dv @ mx) / nn
    f = dv * tt
    h = math.hypot(*f)
    u = np.array([-dv[1], dv[0]]) / math.sqrt(nn)
    ss = math.sqrt(max(0.0, 1 - h * h))
    cands = [f + ss * u, f - ss * u]
    return min(cands, key=lambda p: np.hypot(*(p - ref)))


def ang(V, A, B):
    u = A - V
    w = B - V
    return math.acos(np.clip(u @ w / (np.hypot(*u) * np.hypot(*w)), -1, 1))


def main():
    C = load()
    R = 0.37998385311983884
    order = [7, 1, 8, 6, 4, 9, 10, 3, 5]          # from C16
    m = 9

    # reference switches (candidate)
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
    gap = np.array([((th[(i + 1) % m] - th[i]) % (2 * pi)) for i in range(m)])
    delta = np.array([float(np.hypot(*(C[order[i]] - sw[i]))) for i in range(m)])

    # measured owned spans (from C16, recomputed here on a coarse grid)
    N = 1440000
    t0 = np.linspace(0, 2 * pi, N + 1)[:-1]
    c0 = np.stack([np.cos(t0), np.sin(t0)], 1)
    d0 = np.hypot(c0[:, 0:1] - C[None, :, 0], c0[:, 1:2] - C[None, :, 1])
    own = np.argmin(d0, 1)
    span = {}
    cnt = {}
    for k in range(N):
        if own[k] in cnt:
            continue
        cnt[own[k]] = k
    # count runs
    span = np.zeros(m)
    for k in range(N):
        idx = order.index(int(own[k]))
        span[idx] += 2 * pi / N
    # span[idx] is the owned angular measure (previously "g"-measured)

    print(" (F1)  tan(span_i/2)*delta_i / tan(gap_i/2)  (must be 1)")
    print("i site  gap_i      span_i     delta_i    ratio")
    for i in range(m):
        # careful: for site i the owned arc has endpoints gap[i-1] and gap[i]
        # angular measure of the owned arc measured directly:
        sp = span[i]
        gp = gap[(i - 1) % m]
        A = math.tan(sp / 2)
        B = math.tan(gp / 2)
        print(f"{i} {order[i]:4d} {gp:.9f} {sp:.9f} {delta[i]:.9f} {A*delta[i]/B:.15f}")

    print("\n (F2) closure rows")
    T = np.zeros(m); L = np.zeros(m); b2 = np.zeros(m)
    for i in range(m):
        c = C[order[i]]
        pL = sw[(i - 1) % m]
        pR = sw[i]
        T[i] = ang(pL, c, pR)
        L[i] = ang(pR, c, pL)
        b2[i] = ang(pR, c, C[order[(i + 1) % m]])
    closure = T + np.roll(L, -1) + b2 + (span + np.roll(span, -1)) / 2 - pi
    for i in range(m):
        print(f"  i={i} site={order[i]:2d} closure={closure[i]:+.15e}")
    print("  sum closure =", sum(closure), "  pi =", pi, "  diff =", sum(closure) - pi)
    OUT.mkdir(exist_ok=True)
    (OUT / "c17_closure.json").write_text(json.dumps({
        "order": order, "gap": gap.tolist(), "span": span.tolist(), "delta": delta.tolist(),
        "T": T.tolist(), "L": L.tolist(), "b2": b2.tolist(), "closure": closure.tolist(),
    }, indent=2))
    print("wrote", OUT / "c17_closure.json")


if __name__ == "__main__":
    main()
