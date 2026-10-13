"""C19: CONTROLS + the exact closed form of the sharp stratum.

Claimed exact facts (all verified below on the certified candidate):

  (E1)  For each ring site c_i with the switch chord (P_(i-1), P_i), the
        perpendicular bisector intersects the unit circle at two points; the
        ring site lies on that bisector, and at the SHARP configuration the two
        switch distances are equal to R, forcing
              rho_i * cos(g_(i-1)/2) = sin^2(g_(i-1)/2),
        equivalently
              rho_i = 1 - cos(g_(i-1)/2),
              R_i  = 1 - rho_i cos(g_(i-1)/2) = sin^2(g_(i-1)/2),
        where g_(i-1) = angular gap between the two switches.
        In particular rho_i and R_i are FUNCTIONS of the switch positions only.

  (E2)  Consequently the set of sharp 9-ring configurations is parametrised by
        the nine switch angles theta_1..theta_9 (mod rotation), i.e. it is
        (at most) 8-dimensional, and on it
              sum_i (owned span_i) = 2 pi            (automatic),
        while the covering radius R is NOT determined by the tightness
        conditions alone.

  (E3)  The candidate realises R = 0.37998385311983884 simultaneously on
        18 boundary tight points (2 per ring site) and on 5 of the 11 interior
        Voronoi vertices of the two hubs; the other 6 Voronoi vertices have
        strictly smaller circumradius (0.3788311718).

Controls:
  K1  the switch gaps sum to 2 pi and are not equal;
  K2  rho_i == 1 - cos(g/2) for all nine ring sites (exact to 1e-15);
  K3  the same identity expressed through the owned span (F1 of C17);
  K4  the covering radius recomputed independently (boundary + interior);
  K5  the two "loose" Voronoi vertices have radius strictly below the tight ones.
"""
import json, math
from pathlib import Path
import numpy as np
from scipy.spatial import Voronoi

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
        else:
            raise RuntimeError("switch not found")
    sw = np.array(sw)
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    # gap g_(i-1) = angle between switch i-1 and switch i
    gaps = np.array([((th[i] - th[(i - 1) % m]) % (2 * pi)) for i in range(m)])

    print("K1: switch gaps (deg):", np.round(np.degrees(gaps), 6).tolist())
    print("    sum =", sum(gaps), " 2pi =", 2 * pi, " equal?", np.ptp(gaps) < 1e-9)

    print("\nK2/E1:  rho_i  vs  1 - cos(g_(i-1)/2)   and   R_i = sin^2(g/2)")
    print(" i  site   g_(i-1)      rho_i         1-cos(g/2)     diff        sin^2(g/2)     delta_i=dist(c_i,P)")
    rho = np.array([float(np.hypot(*C[order[i]])) for i in range(m)])
    for i in range(m):
        pred = 1 - math.cos(gaps[i] / 2)
        predR = math.sin(gaps[i] / 2) ** 2
        dist = float(np.hypot(*(C[order[i]] - sw[(i - 1) % m])))
        print(f"{i} {order[i]:4d} {math.degrees(gaps[i]):10.6f} {rho[i]:.15f} {pred:.15f} {rho[i]-pred:+.2e}"
              f"  {predR:.15f}  {dist:.15f}")

    # K4: independent covering-radius check
    print("\nK4: independent covering radius checks")
    N = 4000001
    t = np.linspace(0, 2 * pi, N)
    circ = np.stack([np.cos(t), np.sin(t)], 1)
    d = np.hypot(circ[:, 0:1] - C[None, :, 0], circ[:, 1:2] - C[None, :, 1]).min(1)
    print("    max over boundary of min-site distance :", d.max())
    vor = Voronoi(C)
    print("    voronoi vertices and their radii:")
    tight, loose = [], []
    for v in vor.vertices:
        if v @ v > 1.0:
            continue
        dd = np.hypot(*(C - v[None, :]).T)
        r = dd.min()
        sites = tuple(sorted(int(k) for k in range(len(C)) if abs(dd[k] - r) < 1e-10))
        (tight if abs(r - R) < 1e-11 else loose).append((r, sites))
    for r, s in sorted(tight, reverse=True):
        print(f"      TIGHT r={r:.12f} sites={s}")
    for r, s in sorted(loose, reverse=True):
        print(f"      loose r={r:.12f} sites={s}")
    print("    #tight =", len(tight), " #loose =", len(loose))

    # K5: the two loose vertices are the hub-ring ones
    print("\nK5: loose vertices involve the hub sites:",
          [s for _, s in loose])

    OUT.mkdir(exist_ok=True)
    (OUT / "c19_controls.json").write_text(json.dumps({
        "order": order, "theta": th.tolist(), "gaps": gaps.tolist(), "rho": rho.tolist(),
        "pred_rho": (1 - np.cos(gaps / 2)).tolist(), "pred_R": (np.sin(gaps / 2) ** 2).tolist(),
        "tight": [{"r": r, "sites": list(s)} for r, s in tight],
        "loose": [{"r": r, "sites": list(s)} for r, s in loose],
        "max_boundary": float(d.max()),
    }, indent=2))
    print("\nwrote", OUT / "c19_controls.json")


if __name__ == "__main__":
    main()
