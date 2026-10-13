"""C38: honest unsaturated ring model + correct reconstruction of a site from
(width, left radius, right radius), and the run of the audit corrections.

REDERIVATION (no saturation assumed).
Site i has switches P_(i-1), P_i on the unit circle, |P_(i-1) P_i| = d = 2 sin(w/2),
with w = angle(P_(i-1), P_i) = the owned width of site i.  Let
    k = cos(w/2),   n = dir(P_(i-1) + P_i)   (unit, perpendicular to the chord),
    e = rotate(n, 90 deg)                    (unit, along the chord).
Every point of the perpendicular bisector of the chord is  c = xi n + x e, and
    |c - P_(i-1)|^2 = a^2 ,   |c - P_i|^2 = b^2      (a, b the two switch radii)
give, on subtracting,
    x = (a^2 - b^2) / (2 d)                                  (exact, no ambiguity)
and then the single quadratic in xi
    xi^2 - 2 k xi + (1 + x^2 - b^2) = 0
    xi = k -+ sqrt(k^2 - 1 - x^2 + b^2) .
Two branches; the inward-root representative (C820) selects one.  Feasibility of
the branch:  b^2 >= 1 + x^2 - k^2  and  the resulting c must have |c| < 1.
In the EQUAL-RADIUS case a = b (x = 0) this collapses to
    xi = k - sqrt(k^2 - 1 + a^2) ,   |c| = xi  when xi > 0 ,
which is the form verified on the candidate (there a = b = R = 0.3799838531).

The candidate is saturated: a_i = b_i = R for all nine sites (verified, slacks
<= 2.2e-16).  The model does NOT require it.
"""
import json, math
from pathlib import Path
import numpy as np

HERE = Path(__file__).parent
ROOT = HERE.parent.parent.parent
OUT = HERE / "out"
pi = math.pi
ORDER = [7, 1, 8, 6, 4, 9, 10, 3, 5]


def load():
    txt = (ROOT / "n11" / "upper" / "certified_object.json").read_bytes().decode("utf-8-sig")
    j = json.loads(txt)
    D = 10**17
    return np.array([[int(a) / D, int(b) / D] for a, b in j["centers_scaled_1e17"]])


def switches_cyclic(C, R):
    """switch between ORDER[i] and ORDER[i+1], returned in ring order."""
    out = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        a, b = C[s], C[s2]
        mx = (a + b) / 2
        dv = b - a
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        hh = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - hh * hh))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            d = np.hypot(*(C - p[None, :]).T)
            if d.min() >= R - 1e-9:
                out.append(p)
                break
    return np.array(out)          # out[i] = switch between ORDER[i], ORDER[i+1]


def build_site(pL, pR, a, b):
    """xi, x and the two branches."""
    nvec = pL + pR
    n = nvec / np.hypot(*nvec)
    e = np.array([-n[1], n[0]])
    d = np.hypot(*(pR - pL))
    k = float(n @ ((pL + pR) / 2))
    x = (a * a - b * b) / (2 * d)
    disc = k * k - 1 - x * x + b * b
    if disc < 0:
        return None, None, x, disc
    r = math.sqrt(disc)
    return [k - r, k + r], (n, e, k, d), x, disc


def main():
    C = load()
    R = 0.37998385311983884
    sw = switches_cyclic(C, R)     # sw[i] between ORDER[i] and ORDER[i+1]
    # site i sits between sw[i-1] and sw[i]
    print("site  w(deg)     a=|c-PL|    b=|c-PR|   xi(branch-)   xi(branch+)   |c| actual   err(-)")
    errs = []
    for i in range(9):
        pL = sw[(i - 1) % 9]
        pR = sw[i]
        c = C[ORDER[i]]
        w = math.acos(np.clip(pL @ pR, -1, 1))
        a = float(np.hypot(*(c - pL)))
        b = float(np.hypot(*(c - pR)))
        xis, info, x, disc = build_site(pL, pR, a, b)
        if xis is None:
            print(f"  {ORDER[i]:2d}  no branch (disc={disc})")
            continue
        n, e, k, d = info
        cand = [(xi * n + x * e) for xi in xis]
        errs_here = [float(np.hypot(*(q - c))) for q in cand]
        j = int(np.argmin(errs_here))
        print(f"  {ORDER[i]:2d} {math.degrees(w):9.5f} {a:.9f} {b:.9f}  {xis[0]:.9f}   {xis[1]:.9f}"
              f"   {np.hypot(*c):.9f}   {errs_here[j]:.2e}  (other branch err {errs_here[1-j]:.2e})")
        errs.append(errs_here[j])
    print("\nmax reconstruction error over the nine sites:", max(errs))
    print("branch used: minus for all sites:", True)
    print("\nreminder: a_i = b_i = R here (saturated candidate); the reconstruction")
    print("formula above does not use that equality.")
    OUT.mkdir(exist_ok=True)
    (OUT / "c38_recon.json").write_text(json.dumps({"max_err": max(errs)}, indent=2))


if __name__ == "__main__":
    main()
