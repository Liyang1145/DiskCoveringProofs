"""r20-geometry Round-13 (lead b43463af): deterministic linearized central-face search.

Fixes (per lead): r = 0.38, the nine certified rings fixed; hubs h_A (cert 2), h_B (cert 0); central
sites c0 = cert 5, c4 = cert 6; nine chain pins (4 fan-A + 5 fan-B).

Constraint functions:
  central faces (tight at the candidate):  phi_i(a,b) = angle(a, c_i, b) - arcsin(|a-b|/(2r))  >= 0
                                           (equivalently R_c(a,b,c_i) <= r;  phi_i = 0 at the candidate)
  pin (fan) faces:                          s_k(h) = r - |h - pin_k|  >= 0
  hub ball:                                 rho - |h| > 0

Method (deterministic, no blind sampling):
  1. gradients of phi_i wrt (a,b) and of s_k wrt the assigned hub, by central differences at 1e-6;
  2. take the direction d = normalised gradient of the most sensitive central face (scan of the
     perpendicular directions as a control); direction must not violate the pin first-order conditions
     for a step t in [1e-6, 1e-4];
  3. admissible step from the pin slack: t_max = min_k s_k / (-d.grad s_k) over pins that lose slack;
     take t = min(1e-4, 0.9 t_max);
  4. RECOMPUTE everything at the stepped point: all nine pin margins, both central phi values, hub ball.
A strict counterexample = pins all satisfied (strictly) while a central face is violated (phi_i < 0).
If the direction cone is empty this is reported as FIRST-ORDER ONLY (no proof).

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/linearized_central_search.py
"""
import io, json
from mpmath import mp, mpf, sqrt, asin, acos, atan2, cos, sin, pi as MP_PI
from pathlib import Path
mp.dps = 60
HERE = Path(__file__).resolve().parent
ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


OBJ = json.load(io.open(ROOT / "n11/upper/certified_object.json", encoding="utf-8"))
SC = mpf(10) ** int(OBJ["decimals"])
CENT = [(mpf(int(x)) / SC, mpf(int(y)) / SC) for x, y in OBJ["centers_scaled_1e17"]]
R = mpf("0.38")
RHO = 1 - R
HUBA, HUBB, C0, C4 = 2, 0, 5, 6
FAN_A = [(5, 7), (7, 1), (1, 8), (8, 6)]
FAN_B = [(6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]


def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def add(p, q):
    return (p[0] + q[0], p[1] + q[1])


def mul(t, p):
    return (t * p[0], t * p[1])


def nrm(p):
    return sqrt(p[0] ** 2 + p[1] ** 2)


def dot(p, q):
    return p[0] * q[0] + p[1] * q[1]


def roots(a, c, r):
    m = mul(mpf(1) / 2, add(a, c))
    dv = sub(c, a)
    d = nrm(dv)
    if d == 0 or d > 2 * r:
        return None
    nn = (-dv[1] / d, dv[0] / d)
    k = sqrt(r * r - d * d / 4)
    return (sub(m, mul(k, nn)), add(m, mul(k, nn)))


def near_pin(i, j, r):
    pr = roots(CENT[i], CENT[j], r)
    return pr[0] if nrm(pr[0]) < nrm(pr[1]) else pr[1]


pinsA = [near_pin(i, j, R) for (i, j) in FAN_A]
pinsB = [near_pin(i, j, R) for (i, j) in FAN_B]
hA, hB = CENT[HUBA], CENT[HUBB]
c0, c4 = CENT[C0], CENT[C4]


def phi(a, b, c):
    """central face violation function (>= 0 feasible); zero at the candidate."""
    ang = acos(dot(sub(a, c), sub(b, c)) / (nrm(sub(a, c)) * nrm(sub(b, c))))
    return ang - asin(nrm(sub(a, b)) / (2 * R))


def slack(h, p):
    return R - nrm(sub(h, p))


say("=== linearized central-face search (r = %s, nine certified rings fixed) ===" % R)
say("hub A = (%.12f, %.12f) ; hub B = (%.12f, %.12f)" % (float(hA[0]), float(hA[1]), float(hB[0]), float(hB[1])))
say("candidate readings:")
say("  phi_0 = %+.3e ; phi_4 = %+.3e (central faces; 0 = tight)" % (float(phi(hA, hB, c0)), float(phi(hA, hB, c4))))
say("  pin slacks A: %s" % ", ".join("%+.3e" % float(slack(hA, p)) for p in pinsA))
say("  pin slacks B: %s" % ", ".join("%+.3e" % float(slack(hB, p)) for p in pinsB))
say("  hub-ball slacks: A %+.3e ; B %+.3e" % (float(RHO - nrm(hA)), float(RHO - nrm(hB))))

EPS = mpf("1e-6")


def grad(f, x, y):
    fx = (f((x[0] + EPS, x[1]), y) - f((x[0] - EPS, x[1]), y)) / (2 * EPS)
    fy = (f((x[0], x[1] + EPS), y) - f((x[0], x[1] - EPS), y)) / (2 * EPS)
    return (fx, fy)


# gradients of the central faces wrt each hub
g = {}
for nm, c in (("0", c0), ("4", c4)):
    g[nm] = dict(
        a=grad(lambda x, y: phi(x, y, c), hA, hB),
        b=grad(lambda y, x: phi(x, y, c), hB, hA))
    say("  grad phi_%s wrt a = (%+.4f, %+.4f) ; wrt b = (%+.4f, %+.4f)"
        % (nm, float(g[nm]["a"][0]), float(g[nm]["a"][1]), float(g[nm]["b"][0]), float(g[nm]["b"][1])))
pin_gradA = [mul(-1 / nrm(sub(hA, p)), sub(hA, p)) for p in pinsA]
pin_gradB = [mul(-1 / nrm(sub(hB, p)), sub(hB, p)) for p in pinsB]

best = None
for nm, c in (("0", c0), ("4", c4)):
    for label, ga, gb in (("both-a", g[nm]["a"], (mpf(0), mpf(0))),
                          ("both-b", (mpf(0), mpf(0)), g[nm]["b"]),
                          ("a+b", g[nm]["a"], g[nm]["b"]),
                          ("a-then-b", g[nm]["a"], mul(mpf(0.5), g[nm]["b"]))):
        na, nb = nrm(ga), nrm(gb)
        for scale in (mpf(-1),):
            da = mul(scale / na, ga) if na > 0 else (mpf(0), mpf(0))
            db = mul(scale / nb, gb) if nb > 0 else (mpf(0), mpf(0))
            nd = sqrt(dot(da, da) + dot(db, db))
            if nd == 0:
                continue
            da, db = mul(1 / nd, da), mul(1 / nd, db)
            rate = -(dot(da, g[nm]["a"]) + dot(db, g[nm]["b"]))
            if rate <= 0:
                continue
            # admissible step from the pin first-order conditions (both hubs)
            tmax = mpf("1e-4")
            ok = True
            for h, d, pg in ((hA, da, pin_gradA), (hB, db, pin_gradB)):
                for p, pgr in zip(pinsA if h is hA else pinsB, pg):
                    loss = -dot(d, pgr)
                    if loss > 0:
                        tmax = min(tmax, slack(h, p) / loss)
            if tmax < mpf("1e-6"):
                ok = False
            if not ok:
                continue
            t = min(mpf("1e-4"), mpf("0.9") * tmax)
            if best is None or rate > best[0]:
                best = (rate, nm, label, da, db, t, tmax)
if best is None:
    say("direction cone empty at first order -> FIRST-ORDER obstruction only (no proof).")
else:
    rate, nm, label, da, db, t, tmax = best
    say("")
    say("chosen direction (steepest descent of phi = central violation growth): central face %s, pattern %s, rate = %+.6f" % (nm, label, float(rate)))
    say("  d_a = (%+.6f, %+.6f) ; d_b = (%+.6f, %+.6f) ; admissible t_max = %.3e -> step t = %.3e"
        % (float(da[0]), float(da[1]), float(db[0]), float(db[1]), float(tmax), float(t)))
    hA2, hB2 = add(hA, mul(t, da)), add(hB, mul(t, db))
    say("RECOMPUTED at the stepped point (all nine pins + both central faces + hub balls):")
    sa = [slack(hA2, p) for p in pinsA]
    sb = [slack(hB2, p) for p in pinsB]
    say("  pin slacks A: %s" % ", ".join("%+.6e" % float(z) for z in sa))
    say("  pin slacks B: %s" % ", ".join("%+.6e" % float(z) for z in sb))
    p0, p4 = phi(hA2, hB2, c0), phi(hA2, hB2, c4)
    say("  phi_0 = %+.6e ; phi_4 = %+.6e" % (float(p0), float(p4)))
    say("  hub balls: A %+.6e ; B %+.6e" % (float(RHO - nrm(hA2)), float(RHO - nrm(hB2))))
    pins_ok = min(sa + sb) > 0
    viol = min(p0, p4) < 0
    say("  => all nine pins satisfied (strict): %s ; some central face violated: %s" % (pins_ok, viol))
    if pins_ok and viol:
        say("  STRICT COUNTEREXAMPLE: the pin/vertex assignment is feasible but the central face is violated.")
        dump = dict(r=str(R), hubA=[mp.nstr(z, 30) for z in hA2], hubB=[mp.nstr(z, 30) for z in hB2],
                    direction_a=[mp.nstr(z, 30) for z in da], direction_b=[mp.nstr(z, 30) for z in db],
                    step=str(t), t_max=str(tmax), phi0=str(p0), phi4=str(p4),
                    pin_slacks_A=[str(z) for z in sa], pin_slacks_B=[str(z) for z in sb],
                    hub_ball_A=str(RHO - nrm(hA2)), hub_ball_B=str(RHO - nrm(hB2)),
                    central_face=str(nm), pattern=label)
        io.open(HERE / "linearized_central_search.json", "w").write(json.dumps(dump, indent=1))
        say("  dumped linearized_central_search.json")
    else:
        say("  no strict counterexample at this step (central faces not violated).")
io.open(HERE / "linearized_central_search.out.txt", "w", encoding="utf-8").write("\n".join(OUT) + "\n")
print()
print("wrote linearized_central_search.out.txt")
