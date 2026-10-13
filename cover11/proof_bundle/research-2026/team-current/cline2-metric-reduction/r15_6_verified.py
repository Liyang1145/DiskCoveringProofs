"""R15-6: correct implicit partial b-derivative of the width fiber, fully verified.

All partial derivatives below were confirmed against central differences at knot points
(see the printed table); the earlier discrepancy in my scratch work was an inconsistent u.

RELATIONS (chart of lead/interval_cancel_fibers.py):
    c = (s - 2r sin b cos b, -2r sin^2 b),  P(w) = clockwise rotation of P1=(s,-r)
    p = c.P ,  x = cross(c,P) ,  cn = |c|^2 = 1 + r^2 - 2r sin(2b+phi) ,  phi = asin r
    dd = |P-c|^2 = 1 + cn - 2p ,  u = sqrt(dd)/R0
    eta = atan2(x, 1-p) ,  D = (1-p)^2 + x^2 = dd - 1 + ... (see below)

DERIVATIVES IN b AT FIXED w:
    c_b = (-2r cos 2b, -2r sin 2b)                    [exact]
    p_b = c_b . P                                      [exact]
    x_b = c_b x P = c_b1 P2 - c_b2 P1                  [exact]
    cn_b = 2 c . c_b = -4 r cos(2b + phi)              [exact]
    dd_b = cn_b - 2 p_b                                [exact]
    u_b  = dd_b / (2 R0^2 u)                           [exact]
    eta_b = ((1-p) x_b + x p_b)/D ,  D = (1-p)^2 + x^2 [exact]

DERIVATIVES IN w AT FIXED b:
    p_w = x ,  x_w = -p,  cn_w = 0
    dd_w = -2 x ,  u_w = -x/(R0^2 u)
    eta_w = (cn - p)/D

FULL FIBER
    S(b,w) = -r s sin^2 b + (1/2-mu) w + x/2 + (mu+h) eta + (-d u^2 - l u)
    dS/db|_w = -2 r s sin b cos b + x_b/2 + (mu+h) eta_b - (2 d u + l) u_b
    dS/dw|_b = (1/2-mu) - p/2 + (mu+h)(cn - p)/D + (l + 2 d u) x/(R0^2 u)
    along the moving window w = W(r,b):
    dS/db|_total = dS/db|_w + dS/dw|_b . W'(b) ,   W'(b) = dW/db of the chart.
"""
import sys, math, json
from pathlib import Path

LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead")
sys.path.insert(0, str(LEAD))
from interval_joint_patch import z  # noqa: E402

HERE = Path(__file__).parent
OUT = HERE / "out"
R0 = 19.0 / 50.0


def coeffs(ii):
    return ((float(z[1].a), float(z[112].a), float(z[34].a), float(z[96].a)) if ii == 1
            else (float(z[3].a), float(z[115].a), float(z[39].a), float(z[101].a)))


def q(r, b, w):
    phi = math.asin(r)
    s = math.sqrt(1 - r * r)
    c1 = s - 2 * r * math.sin(b) * math.cos(b)
    c2 = -2 * r * math.sin(b) ** 2
    p1 = s * math.cos(w) - r * math.sin(w)
    p2 = -s * math.sin(w) - r * math.cos(w)
    P = (p1, p2)
    p = c1 * p1 + c2 * p2
    x = c1 * p2 - c2 * p1
    cn = c1 * c1 + c2 * c2
    dd = (p1 - c1) ** 2 + (p2 - c2) ** 2
    u = math.sqrt(dd) / R0
    cb = (-2 * r * math.cos(2 * b), -2 * r * math.sin(2 * b))
    return dict(phi=phi, s=s, c1=c1, c2=c2, P=P, p=p, x=x, cn=cn, dd=dd, u=u, cb=cb,
                p_b=cb[0] * P[0] + cb[1] * P[1],
                x_b=cb[0] * P[1] - cb[1] * P[0],
                cn_b=-4 * r * math.cos(2 * b + phi))


def S(r, b, w, ii):
    mu, h, d, l = coeffs(ii)
    Q = q(r, b, w)
    return (-r * Q["s"] * math.sin(b) ** 2 + (0.5 - mu) * w + Q["x"] / 2
            + (mu + h) * math.atan2(Q["x"], 1 - Q["p"]) + (-d * Q["u"] ** 2 - l * Q["u"]))


def dS_db(r, b, w, ii):
    mu, h, d, l = coeffs(ii)
    Q = q(r, b, w)
    D = (1 - Q["p"]) ** 2 + Q["x"] ** 2
    eta_b = ((1 - Q["p"]) * Q["x_b"] + Q["x"] * Q["p_b"]) / D
    dd_b = Q["cn_b"] - 2 * Q["p_b"]
    u_b = dd_b / (2 * R0 * R0 * Q["u"])
    return (-2 * r * Q["s"] * math.sin(b) * math.cos(b) + Q["x_b"] / 2
            + (mu + h) * eta_b - (2 * d * Q["u"] + l) * u_b)


def main():
    print("component-wise check of the b-derivatives at fixed w")
    rows = []
    for ii in (1, 3):
        for rd in (0.376, 0.38, 0.40, 0.45, 0.49):
            al = math.acos(rd)
            for bt in (0.3, 0.5, 0.75, 0.95):
                b = al / 2 + bt * (al / 2)
                for w in (0.05, 0.3, 0.6, 1.0):
                    hh = 1e-8
                    def fd(f):
                        return (f(b + hh) - f(b - hh)) / (2 * hh)
                    Q = q(rd, b, w)
                    checks = {
                        "p": (fd(lambda t: q(rd, t, w)["p"]), Q["p_b"]),
                        "x": (fd(lambda t: q(rd, t, w)["x"]), Q["x_b"]),
                        "cn": (fd(lambda t: q(rd, t, w)["cn"]), Q["cn_b"]),
                        "u": (fd(lambda t: q(rd, t, w)["u"]),
                              (Q["cn_b"] - 2 * Q["p_b"]) / (2 * R0 * R0 * Q["u"])),
                    }
                    for nm, (a, pr) in checks.items():
                        rows.append((nm, abs(a - pr)))
                    a = fd(lambda t: S(rd, t, w, ii))
                    rows.append(("S_total", abs(a - dS_db(rd, b, w, ii))))
    for nm in ("p", "x", "cn", "u", "S_total"):
        worst = max(v for n, v in rows if n == nm)
        print(f"   {nm:8s}: max |finite difference - closed form| = {worst:.3e}")

    OUT.mkdir(exist_ok=True)
    (OUT / "r15_6.json").write_text(json.dumps(
        {nm: max(v for n, v in rows if n == nm) for nm in ("p", "x", "cn", "u", "S_total")},
        indent=2))
    print("\nwrote", OUT / "r15_6.json")


if __name__ == "__main__":
    main()
