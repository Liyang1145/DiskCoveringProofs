"""R15-5: CORRECT implicit partial b-derivative of the fiber (at fixed w), verified.

The error I made: I treated G as depending on b only through the window. In fact
    G = (1/2-mu) w + x/2 + (mu+h) eta + (-d u^2 - l u),  eta = atan2(x,1-p), u = |P-c|/R0
and c, p, x, eta, u ALL depend on b. Correct treatment:

  (i)  partial derivatives at FIXED w, from  d/db c = (c_b1, c_b2):
          c_b1 = -2r cos 2b ,   c_b2 = -2r sin 2b
          P is b-independent at fixed w, so
          p_b := dp/db|_w = c_b . P
          x_b := dx/db|_w = c_b1 p2 - c_b2 p1 = -D_b p - X_b x   (identically)
       with D_b = -r cos x0 (d/db of D0 = 1 - r cos x0) and X_b = r cos x0.
  (ii) eta_b = (1-p)x_b/D + x p_b/D ,   D = (1-p)^2 + x^2 = 1 + cn - 2p
       (the same formula as eta_w with x_b, p_b in place of x', p')
  (iii) u_b = (p_b - cn_b/2)/(R0^2 u) ,  cn_b = -4r cos(2b+phi)
  (iv) dS/db|_w = -2 r s sin b cos b + x_b/2 + (mu+h) eta_b - (2 d u + l) u_b

This is the correct "implicit partial b-derivative" of the fiber.
"""
import sys, math, json
from pathlib import Path

LEAD = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead")
sys.path.insert(0, str(LEAD))
from interval_joint_patch import z, iv, I  # noqa: E402

HERE = Path(__file__).parent
OUT = HERE / "out"
R0 = 19.0 / 50.0


def coeffs(ii):
    return ((float(z[1].a), float(z[112].a), float(z[34].a), float(z[96].a)) if ii == 1
            else (float(z[3].a), float(z[115].a), float(z[39].a), float(z[101].a)))


def chart(r, b, w):
    phi = math.asin(r)
    s = math.sqrt(1 - r * r)
    c1 = s - 2 * r * math.sin(b) * math.cos(b)
    c2 = -2 * r * math.sin(b) ** 2
    p1 = s * math.cos(w) - r * math.sin(w)
    p2 = -s * math.sin(w) - r * math.cos(w)
    p = c1 * p1 + c2 * p2
    x = c1 * p2 - c2 * p1
    cn = c1 * c1 + c2 * c2
    u = math.hypot(p1 - c1, p2 - c2) / R0
    D0 = 1 - r * math.cos(2 * b - math.acos(r))       # 1 - r cos x0, x0 = 2b - alpha
    X0 = r * math.sin(2 * b - math.acos(r))
    return dict(c1=c1, c2=c2, p1=p1, p2=p2, p=p, x=x, cn=cn, u=u, D0=D0, X0=X0)


def eta_of(r, b, w):
    d = chart(r, b, w)
    return math.atan2(d["x"], 1 - d["p"])


def u_of(r, b, w):
    return chart(r, b, w)["u"]


def S_of(r, b, w, ii):
    mu, h, dco, l = coeffs(ii)
    d = chart(r, b, w)
    return -r * math.sqrt(1 - r * r) * math.sin(b) ** 2 \
        + (0.5 - mu) * w + d["x"] / 2 + (mu + h) * math.atan2(d["x"], 1 - d["p"]) \
        + (-dco * d["u"] ** 2 - l * d["u"])


def dS_db_fixed_w(r, b, w, ii):
    mu, h, dco, l = coeffs(ii)
    phi = math.asin(r)
    s = math.sqrt(1 - r * r)
    d = chart(r, b, w)
    c1b = -2 * r * math.cos(2 * b)
    c2b = -2 * r * math.sin(2 * b)
    p_b = c1b * d["p1"] + c2b * d["p2"]
    x_b = c1b * d["p2"] - c2b * d["p1"]
    cn_b = -4 * r * math.cos(2 * b + phi)
    D = (1 - d["p"]) ** 2 + d["x"] ** 2
    eta_b = ((1 - d["p"]) * x_b + d["x"] * p_b) / D
    u_b = (p_b - cn_b / 2) / (R0 * R0 * d["u"])
    return (-2 * r * s * math.sin(b) * math.cos(b) + x_b / 2
            + (mu + h) * eta_b - (2 * dco * d["u"] + l) * u_b)


def dS_dw_fixed_b(r, b, w, ii):
    mu, h, dco, l = coeffs(ii)
    d = chart(r, b, w)
    D = (1 - d["p"]) ** 2 + d["x"] ** 2
    return ((0.5 - mu) - d["p"] / 2 + (mu + h) * (d["cn"] - d["p"]) / D
            + (l + 2 * dco * d["u"]) * d["x"] / (R0 * R0 * d["u"]))


def main():
    print("check the identity x_b = -D_b p - X_b x and p_b = c_b.P")
    worst1 = worst2 = 0.0
    for rd in (0.376, 0.38, 0.40, 0.45, 0.49):
        al = math.acos(rd)
        for bt in (0.3, 0.5, 0.75, 0.95):
            b = al / 2 + bt * (al / 2)
            for w in (0.05, 0.3, 0.6, 1.0):
                d = chart(rd, b, w)
                c1b = -2 * rd * math.cos(2 * b)
                c2b = -2 * rd * math.sin(2 * b)
                x_b = c1b * d["p2"] - c2b * d["p1"]
                pred = -(d["D0"] * d["p"]) - d["X0"] * d["x"]
                worst1 = max(worst1, abs(x_b - pred))
    print("  max |x_b - (-D0 p - X0 x)| =", worst1)

    print("\ncheck dS/db (fixed w) and dS/dw (fixed b) against central differences")
    for ii in (1, 3):
        w1 = w2 = 0.0
        for rd in (0.376, 0.38, 0.40, 0.45, 0.49):
            al = math.acos(rd)
            for bt in (0.3, 0.5, 0.75, 0.95):
                b = al / 2 + bt * (al / 2)
                for w in (0.05, 0.3, 0.6, 1.0):
                    hh = 1e-8
                    fdb = (S_of(rd, b + hh, w, ii) - S_of(rd, b - hh, w, ii)) / (2 * hh)
                    w1 = max(w1, abs(fdb - dS_db_fixed_w(rd, b, w, ii)))
                    fdw = (S_of(rd, b, w + hh, ii) - S_of(rd, b, w - hh, ii)) / (2 * hh)
                    w2 = max(w2, abs(fdw - dS_dw_fixed_b(rd, b, w, ii)))
        print(f"  ii={ii}: max |fd_b - formula| = {w1:.3e}   max |fd_w - formula| = {w2:.3e}")

    print("\nfull derivative along the moving window (total derivative in b, w = w*(b)):")
    print("  dS/db|total = dS/db|_w + dS/dw|_b * (dw*/db),  dw*/db = -p_b/|c|")
    worst3 = 0.0
    for ii in (1, 3):
        for rd in (0.376, 0.38, 0.45):
            al = math.acos(rd)
            for bt in (0.3, 0.6, 0.9):
                b = al / 2 + bt * (al / 2)
                for w in (0.1, 0.4, 0.8):
                    d = chart(rd, b, w)
                    c1b = -2 * rd * math.cos(2 * b)
                    c2b = -2 * rd * math.sin(2 * b)
                    p_b = c1b * d["p1"] + c2b * d["p2"]
                    dwdb = -p_b / math.sqrt(d["cn"])
                    tot = dS_db_fixed_w(rd, b, w, ii) + dS_dw_fixed_b(rd, b, w, ii) * dwdb
                    hh = 1e-8
                    # move b and the window point together
                    def val(bb):
                        dd = chart(rd, bb, w)
                        return S_of(rd, bb, w, ii)
                    fd = (val(b + hh) - val(b - hh)) / (2 * hh)
                    worst3 = max(worst3, abs(fd - tot))
        print(f"  ii={ii}: residual of the total-derivative chain check = {worst3:.3e}")

    OUT.mkdir(exist_ok=True)
    (OUT / "r15_5.json").write_text(json.dumps(
        {"x_b_identity": worst1, "total_worst": worst3}, indent=2))
    print("\nwrote", OUT / "r15_5.json")


if __name__ == "__main__":
    main()
