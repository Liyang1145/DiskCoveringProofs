"""C21: exact closed form of the sharp 9-ring stratum (v2, corrected).

THEOREM (elementary; verified exactly on the certified candidate).
Let P, Q be unit-circle points with |PQ| = 2 sin(g/2), and let c be equidistant
from P and Q with |c - P| = |c - Q| = R, lying on the same side as the arc of
the gap.  Then necessarily
        |c| = 1 / cos(g/2)      and      R = tan(g/2) ,
and conversely this c realises those two distances.  Its direction is
        dir c = dir(P + Q) + pi/2 - g/2 .

CONSEQUENCE (the lower-dimensional reduction).
A sharp 9-ring configuration is determined by the nine switch gaps
g_1..g_9 (sum = 2 pi), i.e. by 8 free parameters modulo rotation:
        P_i     = (cos theta_i, sin theta_i),  theta_i = sum_{k<=i} g_k
        |c_i|   = sec(g_(i-1)/2)      (c_i is the ring site between P_(i-1), P_i)
        dir c_i = theta_(i-1) + g_(i-1) + pi/2 - g_(i-1)/2
        R_i     = tan(g_(i-1)/2)      (distance from c_i to its two switches)
In particular the nine boundary tight radii are R_i = tan(g_(i-1)/2), they differ
from each other, R is NOT determined by the tightness conditions, and the sharp
stratum is 8-dimensional.  The two hubs and the covering condition are the
remaining, genuinely nonlinear, obligations.

Controls:
  L1  |c_i| = sec(g/2) reproduces the candidate radii;
  L2  R_i = tan(g/2) reproduces the measured switch distances;
  L3  the direction formula reproduces the candidate angles;
  L4  a constructive family: perturb the gaps (keeping the sum) and verify that
      the constructed configuration has EXACTLY |c P| = |c Q| = tan(g/2);
  L5  R_i varies along the family while |c_i| stays ~1.. sec.
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


def candidate_switches(C, R=0.37998385311983884):
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


def construct(gaps, theta0=0.0):
    """gaps: array of 9 angular gaps summing to 2*pi. Returns switches, sites,
    and the tight radius of each ring site."""
    m = len(gaps)
    th = np.cumsum(np.r_[theta0, gaps[:-1]])          # theta_i = angle of switch i
    P = np.stack([np.cos(th), np.sin(th)], 1)
    # ring site i sits between switch i-1 and switch i; gap involved = gaps[i]
    # direction of P_(i-1) + P_i is theta_i - gaps[i]/2; site direction:
    psidir = th - gaps / 2
    rho = 1.0 / np.cos(gaps / 2)
    Z = np.stack([rho * np.cos(psidir), rho * np.sin(psidir)], 1)
    Rt = np.tan(gaps / 2)
    return P, Z, Rt, rho, psidir, th


def main():
    C = load()
    R = 0.37998385311983884
    sw = candidate_switches(C)
    m = 9
    th = np.array([math.atan2(p[1], p[0]) for p in sw])
    gaps = np.array([((th[i] - th[(i - 1) % m]) % (2 * pi)) for i in range(m)])

    P, Z, Rt, rho, psidir, ths = construct(gaps, theta0=th[0])

    print("gaps (deg):", np.round(np.degrees(gaps), 6).tolist())
    print("\nL1: |c_i| = sec(g/2)")
    for i in range(m):
        print(f"   i={i} site {ORDER[i]:2d}: formula={rho[i]:.15f} candidate={np.hypot(*C[ORDER[i]]):.15f}"
              f" diff={rho[i]-np.hypot(*C[ORDER[i]]):+.2e}")
    print("\nL2: R_i = tan(g/2) vs measured switch distance")
    for i in range(m):
        meas = float(np.hypot(*(C[ORDER[i]] - sw[(i - 1) % m])))
        print(f"   i={i} formula={Rt[i]:.15f} measured={meas:.15f} diff={Rt[i]-meas:+.2e}")
    print("\nL3: site direction formula")
    for i in range(m):
        ph = math.atan2(C[ORDER[i]][1], C[ORDER[i]][0])
        d = ((ph - psidir[i] + pi) % (2 * pi)) - pi
        print(f"   i={i} formula={math.degrees(psidir[i]):+.9f} candidate={math.degrees(ph):+.9f}"
              f" diff(deg)={math.degrees(d):+.2e}")
    print("\nL4: constructive family (gaps perturbed, sum preserved)")
    rng = np.random.default_rng(11)
    rows = []
    for trial in range(5):
        pert = gaps + rng.normal(0, 0.03, m)
        pert = pert * (2 * pi / pert.sum())
        P2, Z2, R2, rho2, _, _ = construct(pert, theta0=0.4)
        errs = []
        for i in range(m):
            d1 = float(np.hypot(*(Z2[i] - P2[(i - 1) % m])))
            d2 = float(np.hypot(*(Z2[i] - P2[i])))
            errs.append(max(abs(d1 - R2[i]), abs(d2 - R2[i]), abs(d1 - d2)))
        print(f"   trial {trial}: max err in |c P| = |c Q| = tan(g/2): {max(errs):.3e}"
              f"   R_i in [{R2.min():.6f},{R2.max():.6f}]  |c_i| in [{rho2.min():.6f},{rho2.max():.6f}]")
        rows.append({"gaps": pert.tolist(), "Rt": R2.tolist(), "rho": rho2.tolist(), "maxerr": max(errs)})

    print("\nL5: spread of R_i on the candidate:", Rt.max() - Rt.min(),
          " (nonzero => tightness does not fix R)")
    OUT.mkdir(exist_ok=True)
    (OUT / "c21_closed_form.json").write_text(json.dumps({
        "gaps": gaps.tolist(), "Rt": Rt.tolist(), "rho": rho.tolist(), "psidir": psidir.tolist(),
        "family": rows,
    }, indent=2))
    print("wrote", OUT / "c21_closed_form.json")


if __name__ == "__main__":
    main()
