"""C36: UNSATURATED global ring model (lead's parametrisation), verified.

Data (corrected, genuinely global):
  P_i  : the nine switches on the unit circle, in cyclic order;
  w_i  : the owned width of ring site i = angle(P_(i-1), P_i),  sum w_i = 2 pi;
  a_i  : distance from site i to P_(i-1)   (left switch radius)
  b_i  : distance from site i to P_i       (right switch radius)
Covering gives a_i, b_i <= r (the bound radius), but NOT equality.

Per-site reconstruction (lead's formulas, re-derived here):
    P_prev = k n - (d/2) e,  P = k n + (d/2) e,   k = cos(w/2), d = 2 sin(w/2)
    x = (a^2 - b^2) / (2 d)                       (position along the bisector)
    h = [d^2 + b^2 - a^2] / (2 d)  = sqrt(a^2 - (x + d/2)^2) >= 0
    c = (k - h) n + x e ,
with the identifications
    |c - P| = b ,   |c - P_prev| = a ,   |c|^2 = 1 + b^2 - 2 k (k - h) ,
    h >= 0  <=>  triangle inequality  |a - b| <= d <= a + b  (automatic).

FREE DATA: 9 widths (sum 2 pi) + 9 radii + 2 hub sites = 21 after rotation,
plus the variable bound r.  Verifications below:
  V1 reconstruction reproduces the candidate ring sites from its own
     (w, a, b) data;
  V2 the triangle-inequality domain is the only feasibility condition of the
     radical; the equality case d = a + b gives h = 0 (site on the switch chord);
  V3 the candidate's a_i, b_i and their slacks to r are tabulated (saturation is
     visible as a fact of this configuration, not assumed).
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


def reconstruct(ws, a, b, theta0=0.0):
    """ws: widths (sum 2pi); a[i], b[i]: left/right switch radii of site i."""
    th = np.cumsum(np.r_[theta0, ws[:-1]])
    P = np.stack([np.cos(th), np.sin(th)], 1)
    Z = np.zeros((9, 2))
    ok = True
    for i in range(9):
        pL = P[(i - 1) % 9]
        pR = P[i]
        evec = pL + pR
        e = evec / np.hypot(*evec)          # perpendicular to the chord, towards the centres
        n = np.array([-e[1], e[0]])         # along the chord
        d = 2 * math.sin(ws[i] / 2)
        k = math.cos(ws[i] / 2)
        x = (a[i] ** 2 - b[i] ** 2) / (2 * d)
        h = (d * d + b[i] ** 2 - a[i] ** 2) / (2 * d)
        if h < -1e-12:
            ok = False
        Z[i] = (k - h) * e + x * n
    return P, Z, ok


def main():
    C = load()
    R = 0.37998385311983884
    sw = []
    for i in range(9):
        s, s2 = ORDER[i], ORDER[(i + 1) % 9]
        aa, bb = C[s], C[s2]
        mx = (aa + bb) / 2
        dv = bb - aa
        tt = (dv @ mx) / (dv @ dv)
        f = dv * tt
        hh = math.hypot(*f)
        u = np.array([-dv[1], dv[0]]) / math.hypot(*dv)
        ss = math.sqrt(max(0.0, 1 - hh * hh))
        for sgn in (1, -1):
            p = f + sgn * ss * u
            dd = np.hypot(*(C - p[None, :]).T)
            if dd.min() >= R - 1e-9:
                sw.append(p)
                break
    sw = np.array(sw)
    ws = np.array([math.acos(np.clip(sw[(i - 1) % 9] @ sw[i], -1, 1)) for i in range(9)])
    aa = np.array([float(np.hypot(*(C[ORDER[i]] - sw[(i - 1) % 9]))) for i in range(9)])
    bb = np.array([float(np.hypot(*(C[ORDER[i]] - sw[i]))) for i in range(9)])

    print("candidate data: widths (deg), left/right switch radii, slacks to R")
    print("  i site  w_i(deg)     a_i          b_i        max(a,b)-R")
    for i in range(9):
        print(f"  {i} {ORDER[i]:4d} {math.degrees(ws[i]):10.6f} {aa[i]:.12f} {bb[i]:.12f}"
              f"  {max(aa[i], bb[i]) - R:+.3e}")

    th0 = math.atan2(sw[0][1], sw[0][0])
    P, Z, ok = reconstruct(ws, aa, bb, theta0=th0)
    print("\nV1: reconstruction of the ring sites from (w, a, b)")
    err = 0.0
    for i in range(9):
        e = float(np.hypot(*(Z[i] - C[ORDER[i]])))
        err = max(err, e)
        print(f"   i={i} site {ORDER[i]:2d}: pred=({Z[i][0]:+.12f},{Z[i][1]:+.12f})"
              f" cand=({C[ORDER[i]][0]:+.12f},{C[ORDER[i]][1]:+.12f}) err={e:.2e}")
    print("   max reconstruction error:", err, " radical ok:", ok)

    print("\nV1b: check |c_i - P_(i-1)| = a_i and |c_i - P_i| = b_i in the reconstruction")
    worst = 0.0
    for i in range(9):
        d1 = float(np.hypot(*(Z[i] - P[(i - 1) % 9])))
        d2 = float(np.hypot(*(Z[i] - P[i])))
        worst = max(worst, abs(d1 - aa[i]), abs(d2 - bb[i]))
    print("   max |  |c-P| - prescribed radius  | =", worst)

    print("\nV2: feasibility domain = triangle inequality |a-b| <= d <= a+b")
    for i in range(9):
        d = 2 * math.sin(ws[i] / 2)
        print(f"   i={i}: d={d:.9f}  |a-b|={abs(aa[i]-bb[i]):.9f}  a+b={aa[i]+bb[i]:.9f}"
              f"   ok={abs(aa[i]-bb[i]) <= d <= aa[i]+bb[i] + 1e-12}")

    print("\nV3: the candidate is saturated for every switch (a_i = b_i = R):",
          bool(np.allclose(aa, R, atol=1e-12) and np.allclose(bb, R, atol=1e-12)))
    print("    but the MODEL does not assume it; the free radii a_i, b_i are the")
    print("    honest variables and only the bound a_i, b_i <= R is available.")

    OUT.mkdir(exist_ok=True)
    (OUT / "c36_unsaturated.json").write_text(json.dumps({
        "order": ORDER, "w": ws.tolist(), "a": aa.tolist(), "b": bb.tolist(),
        "theta0": th0, "recon_err": err,
    }, indent=2))
    print("\nwrote", OUT / "c36_unsaturated.json")


if __name__ == "__main__":
    main()
