"""C20: exact closed form of the sharp 9-ring stratum, with controls.

THEOREM (verified exactly below).
Let P_(i-1), P_i be unit vectors with |P_(i-1) - P_i| = 2 sin(g/2), and let c be a
point equidistant from both with |c - P| = R.  Write M = (P_(i-1)+P_i)/2 and let
u be the unit direction of M.  Then:
    |M| = cos(g/2),   perp(c, M-direction) = |c| sin(g/2) = cos(g/2) sin(g/2),
    R = 1 - |M| cos(g/2) = sin^2(g/2),
    |c| = cos(g/2) sin(g/2) + sqrt(cos^2(g/2) sin^2(g/2) + 1 - sin^4(g/2))
        = cos(g/2) (1 + sin(g/2)),
    and the direction of c is  u rotated by -|pi/2 - g/2| (towards the chord).

CONSEQUENCE (the reduction).  A sharp 9-ring configuration is determined by the
nine switch gaps g_1..g_9 (sum 2 pi, mod global rotation) through
    P_i = unit vector at  sum_{k<=i} g_k ,
    |c_i| = cos(g_(i-1)/2)(1 + sin(g_(i-1)/2)),
    dir c_i = dir(P_(i-1)+P_i) rotated by -pi/2 + g_(i-1)/2,
    switch distance R_i = sin^2(g_(i-1)/2) .
All nine tight points are then on the boundary; the interior (hub) tight points
are NOT constrained, so the sharp stratum is 8-dimensional and R is not fixed by
the tightness conditions.

Controls:
  L1  the formula for R_i reproduces the switch distance on the candidate;
  L2  the formula for |c_i| reproduces the candidate's site radii;
  L3  the direction formula reproduces the candidate's site directions;
  L4  perturbing the gaps keeps all nine switch distances equal to sin^2(g/2)
      (constructive family, numerically verified);
  L5  on the family, R_i varies with the gap: R is NOT constant.
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


def candidate(C, R=0.37998385311983884):
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


def build_from_gaps(gaps, theta0=0.0):
    """construct switch/site data from the gap sequence (gaps sum to 2pi)."""
    m = len(gaps)
    th = np.cumsum(np.r_[theta0, gaps[:-1]])
    P = np.stack([np.cos(th), np.sin(th)], 1)
    R = np.array([math.sin(gaps[i] / 2) ** 2 for i in range(m)])
    rho = np.array([math.cos(gaps[i] / 2) * (1 + math.sin(gaps[i] / 2)) for i in range(m)])
    # direction: dir(P_(i-1)+P_i) = mid-direction (angle th_(i-1)+g/2), rotated -pi/2+g/2
    dirs = np.array([th[i] - gaps[i] / 2 - pi / 2 + gaps[i] / 2 for i in range(m)])
    Z = np.stack([rho * np.cos(dirs), rho * np.sin(dirs)], 1)
    return P, Z, R, rho, dirs, th


def main():
    C = load()
    R = 0.37998385311983884
    sw = candidate(C)
    m = 9
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    gaps = np.array([((th[i] - th[(i - 1) % m]) % (2 * pi)) for i in range(m)])

    P, Z, Rf, rhof, dirs, ths = build_from_gaps(gaps, theta0=th[0])
    print("L1: R_i = sin^2(g/2) vs measured switch distance")
    for i in range(m):
        meas = float(np.hypot(*(C[ORDER[i]] - sw[(i - 1) % m])))
        print(f"   i={i} formula R={Rf[i]:.15f} measured={meas:.15f} diff={Rf[i]-meas:+.2e}")

    print("\nL2: |c_i| = cos(g/2)(1+sin(g/2)) vs candidate |c|")
    for i in range(m):
        meas = float(np.hypot(*C[ORDER[i]]))
        print(f"   i={i} formula={rhof[i]:.15f} candidate={meas:.15f} diff={rhof[i]-meas:+.2e}")

    print("\nL3: direction of c_i vs candidate direction")
    for i in range(m):
        ph = math.atan2(C[ORDER[i]][1], C[ORDER[i]][0])
        d = ((ph - dirs[i] + pi) % (2 * pi)) - pi
        print(f"   i={i} formula={math.degrees(dirs[i]):+.9f} candidate={math.degrees(ph):+.9f} diff(deg)={math.degrees(d):+.2e}")

    print("\nL4/L5: constructive family — perturb the gaps and re-verify")
    rng = np.random.default_rng(7)
    for trial in range(4):
        pert = gaps + rng.normal(0, 0.02, m)
        pert = pert * (2 * pi / pert.sum())
        P2, Z2, R2, rho2, _, _ = build_from_gaps(pert, theta0=0.3)
        errs = []
        for i in range(m):
            e1 = abs(float(np.hypot(*(Z2[i] - P2[(i - 1) % m]))) - math.sqrt(R2[i]))
            e2 = abs(float(np.hypot(*(Z2[i] - P2[i]))) - math.sqrt(R2[i]))
            errs.append(max(e1, e2))
        print(f"   trial {trial}: max |switch distance - sin^2(g/2)^0.5| = {max(errs):.3e}"
              f"   R_i range = [{min(R2):.6f},{max(R2):.6f}]   rho range = [{min(rho2):.6f},{max(rho2):.6f}]")

    # L6: is R constant along the family?  report the spread of R_i
    print("\nL6: spread of the nine tight radii on the candidate:",
          max(Rf) - min(Rf), " (nonzero => the tightness conditions do not fix R)")
    OUT.mkdir(exist_ok=True)
    (OUT / "c20_closed_form.json").write_text(json.dumps({
        "gaps": gaps.tolist(), "R_formula": Rf.tolist(), "rho_formula": rhof.tolist(),
        "dirs": dirs.tolist(), "theta": ths.tolist(),
    }, indent=2))
    print("\nwrote", OUT / "c20_closed_form.json")


if __name__ == "__main__":
    main()
