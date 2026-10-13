"""R15-4: FINAL verified derivative recipe + calibration.

Chart (lead's code):
    c = (s - 2r sin b cos b, -2r sin^2 b),   |c|^2 = cn := 1 + r^2 - 2r sin(2b + phi)
    P(w) = clockwise rotation of P1=(s,-r):  P = (s cos w - r sin w, -s sin w - r cos w)
    p = c.P ,  x = cross(c,P) ,  eta = atan2(x, 1-p) ,  u = |P-c|/R0 ,  R0 = 19/50
    G(w) = (1/2 - mu) w + x/2 + (mu+h) eta + (-d u^2 - l u)

EXACT (verified):  p' = x ,  x' = -p ,  D := (1-p)^2 + x^2 = 1 + cn - 2p ,
    eta' = (cn - p)/D ,   u' = -x/(R0^2 u) ,
    dG/dw = (1/2 - mu) - p/2 + (mu+h)(cn - p)/D + (l + 2 d u) x/(R0^2 u) .
Also |c|^2 = cn exactly, and 0 < 1 - p <= 1 - sqrt(55)/8 (lead's bound), so no branch cut.

RECIPE (implementable, no sampling):
  fiber_j(b, w) = S_b(b) + G(w) on w in [g, W(r,b)]:
    max_{b in I} fiber_j(b)
      <= S_b(b_lo) + r s sin(2 b_lo) (b_hi - b_lo) + max( G(g) , G(W(b_hi)) )
  (S_b(b) = -r s sin^2 b is decreasing; G is evaluated only at the two window ends,
   with W(b_hi) an interval enclosure.)
"""
import sys, math, json
from pathlib import Path

LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead")
sys.path.insert(0, str(LEAD))
from interval_joint_patch import iv, I, pi, R, z, asin  # noqa: E402

HERE = Path(__file__).parent
OUT = HERE / "out"
R0 = 19.0 / 50.0


def coeffs(ii):
    return ((float(z[1].a), float(z[112].a), float(z[34].a), float(z[96].a)) if ii == 1
            else (float(z[3].a), float(z[115].a), float(z[39].a), float(z[101].a)))


def parts(r, b, w):
    al = math.acos(r)
    s = math.sqrt(1 - r * r)
    c1 = s - 2 * r * math.sin(b) * math.cos(b)
    c2 = -2 * r * math.sin(b) ** 2
    p1 = s * math.cos(w) - r * math.sin(w)
    p2 = -s * math.sin(w) - r * math.cos(w)
    p = c1 * p1 + c2 * p2
    x = c1 * p2 - c2 * p1
    u = math.hypot(p1 - c1, p2 - c2) / R0
    cn = c1 * c1 + c2 * c2
    return p, x, u, cn


def G(r, b, w, ii):
    mu, h, d, l = coeffs(ii)
    p, x, u, cn = parts(r, b, w)
    return (0.5 - mu) * w + x / 2 + (mu + h) * math.atan2(x, 1 - p) + (-d * u * u - l * u)


def dG(r, b, w, ii):
    mu, h, d, l = coeffs(ii)
    p, x, u, cn = parts(r, b, w)
    D = (1 - p) ** 2 + x ** 2
    return (0.5 - mu) - p / 2 + (mu + h) * (cn - p) / D + (l + 2 * d * u) * x / (R0 * R0 * u)


def fiber(r, b, w, ii):
    mu, h, d, l = coeffs(ii)
    return -r * math.sqrt(1 - r * r) * math.sin(b) ** 2 + G(r, b, w, ii)


def main():
    g = 2 * math.pi - 16 * math.asin(R0)
    print("step 1: exactness of the derivative formula")
    worst = 0.0
    for ii in (1, 3):
        for rd in (0.376, 0.38, 0.40, 0.45, 0.49):
            al = math.acos(rd)
            for bt in (0.3, 0.5, 0.75, 0.95):
                b = al / 2 + bt * (al / 2)
                for w in (0.05, 0.3, 0.6, 1.0, 1.5):
                    hh = 1e-8
                    fd = (G(rd, b, w + hh, ii) - G(rd, b, w - hh, ii)) / (2 * hh)
                    worst = max(worst, abs(fd - dG(rd, b, w, ii)))
    print("   max |finite difference - closed form| =", worst)

    print("\nstep 2: recipe bound vs the true fiber maximum (grid calibration)")
    print("   r      b in [lo,hi]          true max fiber   recipe bound     slack")
    rows = []
    for rd in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(rd)
        for (t0, t1) in ((0.1, 0.3), (0.4, 0.6), (0.7, 0.9), (0.5, 1.0)):
            lo = al / 2 + t0 * (al / 2)
            hi = al / 2 + t1 * (al / 2)
            for ii in (1, 3):
                # true max: dense grid in b, window computed per b
                best = -1e18
                for k in range(201):
                    b = lo + (hi - lo) * k / 200
                    x0 = 2 * b - al
                    Wv = 2 * math.atan2(rd * math.sin(x0), 1 - rd * math.cos(x0))
                    wlo = max(0.0, g)
                    whi = max(wlo, min(Wv, 2 * math.asin(rd)))
                    for m in range(41):
                        w = wlo + (whi - wlo) * m / 40
                        best = max(best, fiber(rd, b, w, ii))
                # recipe: S_b(b_lo) + r s sin(2 b_lo)(b_hi - b_lo) + max(G(g), G(W(b_hi)))
                s = math.sqrt(1 - rd * rd)
                Sb_lo = -rd * s * math.sin(lo) ** 2
                slope = rd * s * math.sin(2 * lo) * (hi - lo)
                x0h = 2 * hi - al
                Wh = 2 * math.atan2(rd * math.sin(x0h), 1 - rd * math.cos(x0h))
                Wh = min(Wh, 2 * math.asin(rd))
                cand = [G(rd, hi, g, ii)]
                if Wh > g:
                    cand.append(G(rd, hi, Wh, ii))
                ub = Sb_lo + slope + max(cand)
                rows.append((rd, lo, hi, ii, best, ub))
                print(f"   {rd:.3f}  [{lo:.4f},{hi:.4f}]  ii={ii}   {best:12.6f}   {ub:12.6f}   {ub-best:+.6f}")

    bad = [r for r in rows if r[5] < r[4] - 1e-9]
    print("\n   violations of the bound:", len(bad))
    print("   mean slack:", sum(r[5] - r[4] for r in rows) / len(rows))

    OUT.mkdir(exist_ok=True)
    (OUT / "r15_4.json").write_text(json.dumps(
        {"deriv_worst": worst, "slack_mean": sum(r[5] - r[4] for r in rows) / len(rows),
         "violations": len(bad)}, indent=2))
    print("\nwrote", OUT / "r15_4.json")


if __name__ == "__main__":
    main()
