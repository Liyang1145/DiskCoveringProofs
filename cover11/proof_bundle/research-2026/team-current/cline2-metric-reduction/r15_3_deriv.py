"""R15-3: exact derivative formulas for the width fiber, verified by hand + numerically.

Chart (lead's code, coefficients mu,h,d,l = z[1],z[112],z[34],z[96]):
    c = (s - 2r sin b cos b, -2r sin^2 b),  |c|^2 = 1 + r^2 - 2r sin(2b+phi)
    P(w) = clockwise rotation of P1=(s,-r) by w:
           P = (s cos w - r sin w, -s sin w - r cos w)
    p = c.P ,  x = cross(c,P) ,  eta = atan2(x, 1-p) ,  u = |P-c|/R0 ,  R0 = 19/50
    G(w) = (1/2 - mu) w + x/2 + (mu+h) eta + (-d u^2 - l u)

EXACT DERIVATIVES (with R0^2 u^2 = |P-c|^2):
    p' = x ,  x' = -p ,  (p^2 + x^2 = |c|^2)
    eta' = (1 + |c|^2 - 2p) / D ,          D := (1-p)^2 + x^2
    u'   = -x/(R0^2 u) = -x/(R0 |P-c|)
    dG/dw = 1/2 - mu - p/2 + (mu+h)(1 + |c|^2 - 2p)/D + (l + 2 d u) x / (R0^2 u)
"""
import sys, math, json
from pathlib import Path

LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead")
sys.path.insert(0, str(LEAD))
from interval_joint_patch import iv, I, pi, R, z, asin  # noqa: E402

HERE = Path(__file__).parent
OUT = HERE / "out"
R0 = 19.0 / 50.0


def coeffs():
    return (float(z[1].a), float(z[112].a), float(z[34].a), float(z[96].a),
            float(z[3].a), float(z[115].a), float(z[39].a), float(z[101].a))


def chart_data(r, b, w):
    al = math.acos(r)
    s = math.sqrt(1 - r * r)
    c1 = s - 2 * r * math.sin(b) * math.cos(b)
    c2 = -2 * r * math.sin(b) ** 2
    p1 = s * math.cos(w) - r * math.sin(w)
    p2 = -s * math.sin(w) - r * math.cos(w)
    cp = c1 * p1 + c2 * p2
    xx = c1 * p2 - c2 * p1
    cnorm = 1 + r * r - 2 * r * math.sin(2 * b + math.asin(r))
    dd = (p1 - c1) ** 2 + (p2 - c2) ** 2
    u = math.sqrt(dd) / R0
    return cp, xx, cnorm, u


def G(r, b, w, mu, h, d, l):
    cp, xx, cnorm, u = chart_data(r, b, w)
    return (0.5 - mu) * w + xx / 2 + (mu + h) * math.atan2(xx, 1 - cp) + (-d * u * u - l * u)


def dG_closed(r, b, w, mu, h, d, l):
    cp, xx, cnorm, u = chart_data(r, b, w)
    D = (1 - cp) ** 2 + xx ** 2
    return (0.5 - mu) - cp / 2 + (mu + h) * (1 + cnorm - 2 * cp) / D + (l + 2 * d * u) * xx / (R0 * R0 * u)


def main():
    mu, h, d, l, mu3, h3, d3, l3 = coeffs()
    print("coeffs ii=1: mu=%.6f h=%.6f d=%.6f l=%.6f" % (mu, h, d, l))
    print("coeffs ii=3: mu=%.6f h=%.6f d=%.6f l=%.6f" % (mu3, h3, d3, l3))
    worst = 0.0
    rows = []
    for (rd, mus, hs, ds, ls) in ((0.376, mu, h, d, l), (0.380, mu, h, d, l),
                                  (0.45, mu, h, d, l), (0.38, mu3, h3, d3, l3)):
        al = math.acos(rd)
        for bt in (0.30, 0.5, 0.75, 0.95):
            b = al / 2 + bt * (al / 2)
            for w in (0.05, 0.3, 0.6, 1.0, 1.5):
                hh = 1e-8
                fd = (G(rd, b, w + hh, mus, hs, ds, ls) - G(rd, b, w - hh, mus, hs, ds, ls)) / (2 * hh)
                pr = dG_closed(rd, b, w, mus, hs, ds, ls)
                worst = max(worst, abs(fd - pr))
                rows.append({"r": rd, "b": b, "w": w, "fd": fd, "closed": pr})
    print("\nmax |finite diff - closed form| over the scan:", worst)
    print("\nsample rows (r, b, w, fd, closed):")
    for row in rows[:8]:
        print("   %.3f %.4f %.2f  %+.8f  %+.8f" % (row["r"], row["b"], row["w"], row["fd"], row["closed"]))

    print("\nrange of dG/dw over the physical window (w in [g, W(r,b)]) -- for the envelope")
    g = float(2 * math.pi - 16 * math.asin(R0))
    for rd in (0.375, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(rd)
        vals = []
        for bt in (0.0, 0.25, 0.5, 0.75, 1.0):
            b = al / 2 + bt * (al / 2)
            x0 = 2 * b - al
            Wv = 2 * math.atan2(rd * math.sin(x0), 1 - rd * math.cos(x0))
            for t in (0.0, 0.5, 1.0):
                w = g + t * max(0.0, Wv - g)
                vals.append(dG_closed(rd, b, w, mu, h, d, l))
        print(f"   r={rd}: dG/dw in [{min(vals):+.4f},{max(vals):+.4f}] (sample)")

    OUT.mkdir(exist_ok=True)
    (OUT / "r15_3.json").write_text(json.dumps({"worst": worst, "rows": rows[:40]}, indent=2))
    print("\nwrote", OUT / "r15_3.json")


if __name__ == "__main__":
    main()
