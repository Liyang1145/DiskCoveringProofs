"""R15-1: analytic derivation + calibration of the width-fiber sensitivity recipe.

Structure (from lead/interval_cancel_fibers.py, coefficients in the code's convention):
  fiber_j(b, w) = S_b(b) + G(w)                on the window  w in [g, W(r,b)]
  S_b(b) = -r s sin^2 b                        (b-only part of the fiber)
  G(w)   = (1/2 - mu) w + x/2 + (mu+h) eta + quad_range(-d,-l, u)
  x = r sin x0(b,w), p = ..., eta = atan2(x, 1-p),
  x0 = 2b - alpha0, alpha0 = acos r, s = sqrt(1-r^2)

KEY EXACT SIMPLIFICATIONS (derived here, no inequality):
  (D1) d eta/dw = -(1-p)/[(1-p)^2 + x^2]                     [implicit differentiation of eta]
  (D2) quad_range(-d,-l,u) has u = |P-c|/R0 with du/dw = -x/(R0^2 u), so the d-term
       cancels in dG/dw and one gets the CLOSED FORM
           dG/dw = 1/2 - mu - (mu+h)(1-p)/[(1-p)^2 + x^2] .
  (D3) dW/db = 2 r (cos x0 - r)/(1 - r cos x0)^2  >= 0 on the domain (x0 <= alpha0),
       with the closed upper bound  W'(b) <= 2r(1-r)/(1-rsqrt(...))^2  -- see report.
  (D4) S_b'(b) = -r s sin(2b)  <= 0 on the domain, so max S_b = S_b(b_lo).

Recipe (affine majorant, no sampling):
  max_{b in I} fiber_j(b) <= [ max_{b in I} S_b(b) ] + [ max_{w in [g, W(b_hi)]} G(w) ]
via the one-sided Lipschitz/monotonicity decomposition; both bracket maxima are
one-dimensional and are enclosed by interval evaluation (the G-part moves its
endpoint only through W(b_hi), which is itself interval-bounded).
"""
import sys, math, json
from pathlib import Path

LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead")
sys.path.insert(0, str(LEAD))

import interval_joint_patch as k          # noqa: E402
from interval_joint_patch import iv, I, pi, R, z, asin, acos, lf, uf, clip, quad_range  # noqa: E402

HERE = Path(__file__).parent
OUT = HERE / "out"


def S_b(r, b):
    s = iv.sqrt(1 - r * r)
    return -r * s * iv.sin(b) ** 2

def dS_b(r, b):
    s = iv.sqrt(1 - r * r)
    return -2 * r * s * iv.sin(b) * iv.cos(b)

def W_bern(r, b):
    """W(r,b) = 2 atan2(r sin x0, 1 - r cos x0), x0 = 2b - acos r  (lead's chart)."""
    phi = asin(r)
    x0 = 2 * b - (pi / 2 - phi)
    X = r * iv.sin(x0)
    D = 1 - r * iv.cos(x0)
    return 2 * iv.atan2(X, D)

def dW_db(r, b):
    """2r(cos x0 - r)/(1 - r cos x0)^2"""
    phi = asin(r)
    x0 = 2 * b - (pi / 2 - phi)
    den = 1 - r * iv.cos(x0)
    return 2 * r * (iv.cos(x0) - r) / den ** 2

def dG_dw(r, b, w, mu, h):
    """1/2 - mu - (mu+h)(1-p)/[(1-p)^2+x^2]"""
    phi = asin(r)
    x0 = 2 * b - (pi / 2 - phi)
    D0 = 1 - r * iv.cos(x0)
    X0 = r * iv.sin(x0)
    cp = D0 * iv.cos(w) + X0 * iv.sin(w)
    xx = X0 * iv.cos(w) - D0 * iv.sin(w)
    den = 1 - cp
    return I(1) / 2 - mu - (mu + h) * den / (den ** 2 + xx ** 2)

def G_of(r, b, w, mu, h, d, l):
    phi = asin(r)
    x0 = 2 * b - (pi / 2 - phi)
    D0 = 1 - r * iv.cos(x0)
    X0 = r * iv.sin(x0)
    cp = D0 * iv.cos(w) + X0 * iv.sin(w)
    xx = X0 * iv.cos(w) - D0 * iv.sin(w)
    den = 1 - cp
    dsq = clip(1 + (1 + r * r - 2 * r * iv.cos(x0)) - 2 * cp, (R * I(19) / 100) ** 2, r * r)
    if dsq is None:
        return None
    u = iv.sqrt(dsq) / R
    return (I(1) / 2 - mu) * w + xx / 2 + (mu + h) * iv.atan2(xx, den) + quad_range(-d, -l, u)


def main():
    g = k.g
    print("R15-1 calibration: check (D1)-(D4) against finite differences and the old envelope")
    # --- (D1): d eta/dw  vs  -(1-p)/((1-p)^2+x^2)
    worst1 = 0.0
    for rd in (0.376, 0.38, 0.40, 0.45, 0.49):
        r = I(rd)
        phi = math.asin(rd)
        al = math.acos(rd)
        for bd in [al / 2 + (al / 2) * f for f in (0.2, 0.5, 0.8, 0.99)]:
            b = I(bd)
            for wd in (0.05, 0.2, 0.5, 1.0):
                h = 1e-7
                x0 = 2 * bd - al
                D0 = 1 - rd * math.cos(x0)
                X0 = rd * math.sin(x0)
                def eta(w):
                    cp = D0 * math.cos(w) + X0 * math.sin(w)
                    xx = X0 * math.cos(w) - D0 * math.sin(w)
                    return math.atan2(xx, 1 - cp)
                fd = (eta(wd + h) - eta(wd - h)) / (2 * h)
                cp = D0 * math.cos(wd) + X0 * math.sin(wd)
                xx = X0 * math.cos(wd) - D0 * math.sin(wd)
                pred = -(1 - cp) / ((1 - cp) ** 2 + xx ** 2)
                worst1 = max(worst1, abs(fd - pred))
    print("  (D1) max |d eta/dw - closed form| =", worst1)

    # --- (D2): dG/dw vs finite difference of G
    worst2 = 0.0
    mu, h, d, l = z[1], z[112], z[34], z[96]
    for rd in (0.376, 0.38, 0.45):
        phi = math.asin(rd)
        al = math.acos(rd)
        r = I(rd)
        for bd in (al / 2 + 0.1, al / 2 + 0.5 * al / 2):
            b = I(bd)
            for wd in (0.05, 0.3, 0.8):
                hh = 1e-7
                def Gp(w):
                    return float(G_of(r, b, I(w), mu, h, d, l).a)
                fd = (Gp(wd + hh) - Gp(wd - hh)) / (2 * hh)
                pred = float(dG_dw(r, b, I(wd), mu, h).a)
                worst2 = max(worst2, abs(fd - pred))
    print("  (D2) max |d G/dw - closed form| =", worst2)

    # --- (D3): dW/db vs finite difference, and positivity
    worst3 = 0.0
    for rd in (0.376, 0.38, 0.40, 0.45, 0.49):
        r = I(rd)
        al = math.acos(rd)
        for bd in (al / 2 + 0.01 * al / 2, al / 2 + al / 4, al * 0.95):
            hh = 1e-7
            def Wp(x):
                return float(W_bern(r, I(x)).b)
            fd = (Wp(bd + hh) - Wp(bd - hh)) / (2 * hh)
            pred = float(dW_db(r, I(bd)).b)
            worst3 = max(worst3, abs(fd - pred))
    print("  (D3) max |dW/db - closed form| =", worst3)

    # --- (D4): S_b decreasing
    worst4 = 0.0
    for rd in (0.376, 0.38, 0.45):
        r = I(rd)
        al = math.acos(rd)
        vals = [float(dS_b(r, I(al / 2 + t * (al - al / 2))).b) for t in (0.0, 0.25, 0.5, 0.75, 1.0)]
        worst4 = max(worst4, max(vals))
    print("  (D4) max of dS_b/db over the domain (should be <= 0):", worst4)

    # --- compare the recipe with the lead's envelope on a real box
    import interval_cancel_fibers as icf
    boxes = [(I(0.38), I(0.60), I(0.60), I(0.01)),
             (I(0.378), I(0.59), I(0.59), I(0.005))]
    print("\n  box -> lead bound vs recipe bound (fiber 1)")
    for box in boxes:
        st = icf.setup(box)
        if st is None:
            print("   box", box, "-> setup rejected")
            continue
        K, fs = st
        lead_upper = icf.bound(box, tol=1e-4, maxeval=400)
        if lead_upper is None:
            print("   box", box, "-> bound None")
            continue
        f1 = lead_upper['fibers'][0]['upper']
        r_, b1, b2, de = box
        # recipe: max_b S_b + max_{w in [g, W(b_hi)]} G
        Sbv = S_b(r_, I(uf(b1)))
        Wv = W_bern(r_, I(uf(b1)))
        wlo = min(uf(g), uf(Wv))
        Gv = G_of(r_, I(uf(b1)), I(wlo, uf(Wv)), z[1], z[112], z[34], z[96])
        rec = float(Sbv.b) + (float(Gv.b) if Gv is not None else float('nan'))
        print(f"   r={float(r_.a):.3f} b1={float(b1.a):.3f}..{float(b1.b):.3f}:"
              f" lead fiber1 upper={f1:.6f}   recipe={rec:.6f}   diff={rec-f1:+.6f}")

    OUT.mkdir(exist_ok=True)
    (OUT / "r15_1.json").write_text(json.dumps({
        "D1": worst1, "D2": worst2, "D3": worst3, "D4": worst4}, indent=2))
    print("\nwrote", OUT / "r15_1.json")


if __name__ == "__main__":
    main()
