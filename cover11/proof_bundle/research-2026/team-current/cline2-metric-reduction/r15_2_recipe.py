"""R15-2: corrected analytic derivation + implementable recipe + calibration.

Fiber structure (lead's code, coefficients in the code convention):
    fiber_j(b, w) = S_b(b) + G(w)  on the window  w in [g, W(r,b)]
    S_b(b) = -r s sin^2 b
    G(w)   = (1/2 - mu) w + x/2 + (mu+h) eta + quad_range(-d, -l, u)
with (c1 component of the chart, x0 = 2b - acos r, P(w) the clockwise rotation of P1)
    c = (s - 2r sin b cos b, -2r sin^2 b),   |c|^2 = 1 + r^2 - 2r sin(2b + phi)
    p = c.P(w) = D0 cos w + X0 sin w ,  x = cross(c,P(w)) = X0 cos w - D0 sin w
    D0 = 1 - r cos x0 ,  X0 = r sin x0 ,   eta = atan2(x, 1-p)
    u = |P(w) - c|/R0 ,  R0 = 19/50

EXACT DERIVED IDENTITIES (each is a pure derivative identity; no inequality):
  (D1) d eta/dw = (|c|^2 - p) / D ,        D := (1-p)^2 + x^2
       [from eta' = [(1-p) x' + x p']/D with x' = -p, p' = x, p^2 + x^2 = |c|^2]
  (D2) dG/dw = 1/2 - mu - p (mu+h)/D        [the d-term cancels: d u /dw = -x/R0^2 u]
  (D3) dW/db = 2 r (cos x0 - r) / (1 - r cos x0)^2  >= 0 on x0 <= acos r,
       and with the closed bound cos x0 >= r + (1-r^2)(1-cos(2(b_hi-b_lo))) it is
       W'(b) <= 2 r (cos x_lo - r)/(1 - r cos x_hi)^2 over the box.
  (D4) dS_b/db = -2 r s sin b cos b = -r s sin(2b) <= 0 on the domain
       (b <= acos r <= pi/4 when r >= 1/sqrt2; in the range r in [3/8,19/50] indeed
       acos r < pi/4), so max_{b in I} S_b = S_b(b_lo) exactly.

RECIPE (affine supporting majorant; one-dimensional, no sampling):
    max_{b in I} fiber_j(b) <= S_b(b_lo) + L_I (b_hi - b_lo) + max_{w in [g, W(b_hi)]} G(w)
    L_I := r s sin(2 b_lo) + |G|_max · W'_max ,
which removes the b-dependence of the window entirely (only W(b_hi) survives).
"""
import sys, math, json
from pathlib import Path

LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead")
sys.path.insert(0, str(LEAD))

import interval_joint_patch as k          # noqa: E402
from interval_joint_patch import iv, I, pi, R, z, asin, acos, lf, uf, clip, quad_range  # noqa: E402

HERE = Path(__file__).parent
OUT = HERE / "out"
R0 = 19.0 / 50.0


def chart(r, b):
    s = iv.sqrt(1 - r * r)
    phi = asin(r)
    x0 = 2 * b - (pi / 2 - phi)
    D0 = 1 - r * iv.cos(x0)
    X0 = r * iv.sin(x0)
    return s, phi, x0, D0, X0


def S_b(r, b):
    s = iv.sqrt(1 - r * r)
    return -r * s * iv.sin(b) ** 2


def W_of(r, b):
    s, phi, x0, D0, X0 = chart(r, b)
    return 2 * iv.atan2(X0, D0)


def dW_db(r, b):
    s, phi, x0, D0, X0 = chart(r, b)
    return 2 * r * (iv.cos(x0) - r) / D0 ** 2


def u_of(r, b, w):
    s, phi, x0, D0, X0 = chart(r, b)
    cp = D0 * iv.cos(w) + X0 * iv.sin(w)
    cnorm = 1 + r * r - 2 * r * iv.cos(x0)
    dsq = clip(1 + cnorm - 2 * cp, (R * I(19) / 100) ** 2, r * r)
    if dsq is None:
        return None
    return iv.sqrt(dsq) / R


def G_of(r, b, w, mu, h, d, l):
    s, phi, x0, D0, X0 = chart(r, b)
    cp = D0 * iv.cos(w) + X0 * iv.sin(w)
    xx = X0 * iv.cos(w) - D0 * iv.sin(w)
    u = u_of(r, b, w)
    if u is None:
        return None
    return (I(1) / 2 - mu) * w + xx / 2 + (mu + h) * iv.atan2(xx, 1 - cp) + quad_range(-d, -l, u)


def dG_dw(r, b, w, mu, h):
    """corrected: 1/2 - mu - p (mu+h)/D"""
    s, phi, x0, D0, X0 = chart(r, b)
    cp = D0 * iv.cos(w) + X0 * iv.sin(w)
    xx = X0 * iv.cos(w) - D0 * iv.sin(w)
    D = (1 - cp) ** 2 + xx ** 2
    return I(1) / 2 - mu - cp * (mu + h) / D


def main():
    g = k.g
    print("R15-2: calibration of (D1)-(D4)")

    # (D1) d eta/dw = (|c|^2 - p)/D
    worst1 = 0.0
    for rd in (0.376, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(rd)
        phi = math.asin(rd)
        s = math.sqrt(1 - rd * rd)
        for bd in (al / 2 + 0.05, al / 2 + 0.5 * (al - al / 2), al * 0.95):
            x0 = 2 * bd - al
            D0 = 1 - rd * math.cos(x0)
            X0 = rd * math.sin(x0)
            cnorm = 1 + rd * rd - 2 * rd * math.cos(x0)
            for wd in (0.05, 0.3, 0.8):
                h = 1e-8
                def eta(w):
                    cp = D0 * math.cos(w) + X0 * math.sin(w)
                    xx = X0 * math.cos(w) - D0 * math.sin(w)
                    return math.atan2(xx, 1 - cp)
                fd = (eta(wd + h) - eta(wd - h)) / (2 * h)
                cp = D0 * math.cos(wd) + X0 * math.sin(wd)
                xx = X0 * math.cos(wd) - D0 * math.sin(wd)
                pred = (cnorm - cp) / ((1 - cp) ** 2 + xx ** 2)
                worst1 = max(worst1, abs(fd - pred))
    print("  (D1) max |d eta/dw - (|c|^2-p)/D| =", worst1)

    # (D2) dG/dw vs finite difference of G
    worst2 = 0.0
    mu, h, dco, lco = z[1], z[112], z[34], z[96]
    for rd in (0.376, 0.38, 0.45):
        al = math.acos(rd)
        r = I(rd)
        for bd in (al / 2 + 0.1, al * 0.9):
            b = I(bd)
            for wd in (0.05, 0.3, 0.8):
                hh = 1e-7
                g1 = G_of(r, b, I(wd + hh), mu, h, dco, lco)
                g0 = G_of(r, b, I(wd - hh), mu, h, dco, lco)
                if g1 is None or g0 is None:
                    continue
                fd = (float(g1.a) - float(g0.a)) / (2 * hh)
                pred = float(dG_dw(r, b, I(wd), mu, h).a)
                worst2 = max(worst2, abs(fd - pred))
    print("  (D2) max |d G/dw - closed form| =", worst2)

    # (D3) dW/db
    worst3 = 0.0
    for rd in (0.376, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(rd)
        r = I(rd)
        for bd in (al / 2 + 0.01, al * 0.75, al * 0.98):
            hh = 1e-7
            fd = (float(W_of(r, I(bd + hh)).b) - float(W_of(r, I(bd - hh)).b)) / (2 * hh)
            pred = float(dW_db(r, I(bd)).b)
            worst3 = max(worst3, abs(fd - pred))
    print("  (D3) max |dW/db - closed form| =", worst3)

    # (D4) S_b decreasing on the domain
    worst4 = -1e9
    for rd in (0.376, 0.38, 0.45, 0.49):
        al = math.acos(rd)
        for t in (0.0, 0.25, 0.5, 0.75, 1.0):
            bd = al / 2 + t * (al - al / 2)
            s = math.sqrt(1 - rd * rd)
            worst4 = max(worst4, -2 * rd * s * math.sin(bd) * math.cos(bd))
    print("  (D4) max of dS_b/db over the domain (<=0 expected):", worst4)

    # (D5) W'(b) upper bound: natural enclosure vs the elementary cos-bound enclosure
    print("\n  (D5) W' interval enclosure test on sample boxes")
    for rd, (t0, t1) in ((0.38, (0.1, 0.3)), (0.38, (0.5, 0.6)), (0.45, (0.3, 0.5))):
        al = math.acos(rd)
        lo = al / 2 + t0 * (al / 2)
        hi = al / 2 + t1 * (al / 2)
        r = I(rd)
        dW_nat = dW_db(r, I(lo, hi))
        # elementary bound: cos x0 >= cos(hi)=cos x_hi on the positive side and
        # cos x0 <= cos(lo); numerator <= r(cos x_lo - r), denominator >= (1 - r cos x_lo)^2
        cxn = math.cos(2 * hi - al)
        cxl = math.cos(2 * lo - al)
        bd = 2 * rd * max(0.0, cxl - rd) / (1 - rd * cxn) ** 2
        print(f"    r={rd} b in [{lo:.4f},{hi:.4f}]: natural dW/db = [{float(dW_nat.a):.6f},{float(dW_nat.b):.6f}]"
              f"   elementary bound = {bd:.6f}")

    OUT.mkdir(exist_ok=True)
    (OUT / "r15_2.json").write_text(json.dumps(
        {"D1": worst1, "D2": worst2, "D3": worst3, "D4": worst4}, indent=2))
    print("\nwrote", OUT / "r15_2.json")


if __name__ == "__main__":
    main()
