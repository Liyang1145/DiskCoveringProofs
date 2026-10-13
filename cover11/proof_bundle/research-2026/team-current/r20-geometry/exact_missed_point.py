"""r20-geometry Round-14 (lead 04663b59): EXACT witness verification (no arcsin-branch argument).

Recipe (per lead):
 1. rationalise the two hubs (Fraction grid);
 2. p = the rational circumcentre of the violated central triangle (a, c0, b);
 3. verify EXACTLY, with Fractions, that |p - c_j|^2 - r^2 > 0 for all eleven covering centres
    (nine rings + the two hubs) and |p|^2 < 1  -> p is a point of the unit disk covered by none of the
    eleven radius-r disks.  This is the coverage counterexample, with no branch / Delaunay interface.
 4. verify the nine pin constraints exactly (Fraction + sqrt: |h - pin_k|^2 = alpha -/+ beta*sqrt(Q));
 5. two-representation comparison: the angular form (sign of phi_0 = angle(a,c0,b) - arcsin(|a-b|/2r),
    motivated only) versus the direct exact p-check (the certificate-grade statement).
Also: hub-ball slacks reported in the right units.

Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/exact_missed_point.py
"""
import io, json
from fractions import Fraction as F
from mpmath import mp, mpf, sqrt as msqrt, asin, acos, pi as MP_PI
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
DEN = 10 ** int(OBJ["decimals"])
RAW = [(int(x), int(y)) for x, y in OBJ["centers_scaled_1e17"]]
CEN = [(F(x, DEN), F(y, DEN)) for x, y in RAW]          # exact rational centres
R = F(19, 50)                                           # 0.38
RHO = 1 - R
C0 = RAW and 5
HUBA, HUBB = 2, 0
FAN_A = [(5, 7), (7, 1), (1, 8), (8, 6)]
FAN_B = [(6, 4), (4, 9), (9, 10), (10, 3), (3, 5)]


def fadd(p, q):
    return (p[0] + q[0], p[1] + q[1])


def fsub(p, q):
    return (p[0] - q[0], p[1] - q[1])


def fmul(t, p):
    return (t * p[0], t * p[1])


def fn2(p):
    return p[0] * p[0] + p[1] * p[1]


def pin_exact(i, j):
    """exact pin data: centre m (Fraction pair), direction offset o with |o|^2 = K (Fraction) so that
    pin = m +/- o where o = perp(delta) * sqrt(K)/sqrt(D) and D = |delta|^2, K = r^2 - D/4.
    Returns (m, perp_delta_dir_numerator, D, K)."""
    ci, cj = CEN[i], CEN[j]
    d = fsub(cj, ci)
    D = fn2(d)
    m = fmul(F(1, 2), fadd(ci, cj))
    K = R * R - D / 4
    return m, (-d[1], d[0]), D, K          # o = perp(delta)/|delta| * sqrt(K) = perp(d) * sqrt(K/D)


def pin_slack_sq(h, pin):
    """exact |h - pin|^2 = alpha -/+ beta*sqrt(Q) with Fractions; returns (alpha, beta, Q, K_over_D)."""
    m, perp, D, K = pin
    alpha = fn2(fsub(h, m)) + K            # |h-m|^2 + |o|^2,  |o|^2 = K
    w = fsub(h, m)
    # (h-m).perp(d) with perp = (-dy, dx):  w0*(-dy) + w1*(dx)
    dot = w[0] * perp[0] + w[1] * perp[1]
    beta = 2 * dot                          # coefficient of sqrt(K/D) (sign of the chosen root)
    Q = F(K, D)
    return alpha, beta, Q


def sign_of(alpha, beta, Q, target):
    """EXACT sign of  (alpha - beta*sqrt(Q)) - target,  alpha, beta, Q, target in Q, Q >= 0.
    Kernel repaired per lead 2c01d868: rhs must be +beta^2 Q (not -beta^2 Q) and Q == 0 is separate."""
    lhs = alpha - target
    if Q == 0:
        return (lhs > 0) - (lhs < 0)          # quantity = lhs exactly
    if beta == 0:
        return (lhs > 0) - (lhs < 0)
    rhs = beta * beta * Q                     # positive
    if beta > 0:
        # quantity = lhs - beta sqrt(Q)
        if lhs < 0:
            return -1
        if lhs == 0:
            return -1                         # Q > 0 here, so strictly negative
        return (lhs * lhs > rhs) - (lhs * lhs < rhs)
    else:
        # quantity = lhs + |beta| sqrt(Q)
        if lhs > 0:
            return 1
        if lhs == 0:
            return 1                          # Q > 0 here
        return (lhs * lhs < rhs) - (lhs * lhs > rhs)


def circumcentre(p1, p2, p3):
    """exact rational circumcentre (solves the two linear equations)."""
    ux, uy = fsub(p2, p1)
    vx, vy = fsub(p3, p1)
    b1 = (fn2(p2) - fn2(p1)) / 2
    b2 = (fn2(p3) - fn2(p1)) / 2
    det = ux * vy - uy * vx
    px = (b1 * vy - uy * b2) / det
    py = (ux * b2 - b1 * vx) / det
    return (px, py)


# --- rational hubs: round the mpmath-perturbed positions to a 1e-7 grid (from linearized search) ---
JSON = json.load(io.open(HERE / "linearized_central_search.json", encoding="utf-8")) if (HERE / "linearized_central_search.json").exists() else None
if JSON:
    hA_m = [mpf(z) for z in JSON["hubA"]]
    hB_m = [mpf(z) for z in JSON["hubB"]]
else:
    raise SystemExit("run linearized_central_search.py first")
GRID = F(1, 10 ** 7)


def to_frac(x):
    return F(int(mp.nint(mpf(x) * 10 ** 7)), 10 ** 7)


hA = (to_frac(hA_m[0]), to_frac(hA_m[1]))
hB = (to_frac(hB_m[0]), to_frac(hB_m[1]))
say("=== kernel controls (lead 2c01d868): sign of alpha - beta*sqrt(Q) - target, target = 0 ===")
CONTROLS = [((2, 1, 1), 1), ((1, 2, 1), -1), ((-2, -1, 1), -1), ((-1, -2, 1), 1), ((1, 1, 1), 0),
            ((1, 2, 0), 1), ((0, 2, 0), 0), ((-1, 2, 0), -1)]
ok_ctrl = True
for (aa, bb, qq), expect in CONTROLS:
    got = sign_of(F(aa), F(bb), F(qq), F(0))
    ok_ctrl = ok_ctrl and (got == expect)
    say("  (alpha, beta, Q) = (%3d, %3d, %d): sign = %+d (expected %+d) %s"
        % (aa, bb, qq, got, expect, "OK" if got == expect else "MISMATCH"))
say("all kernel controls pass: %s" % ok_ctrl)
say("")
say("=== EXACT verification (Fractions only, no arcsin branch in the claim) ===")
say("r = %s = %.6f ; rho = %s" % (R, float(R), RHO))
say("rational hubs: A = (%s, %s) ; B = (%s, %s)" % (hA[0], hA[1], hB[0], hB[1]))
say("hub-ball data: [|A|^2 = %s, |B|^2 = %s]" % (fn2(hA), fn2(hB)))
say("  hub-ball slacks (rho - |h|): |A| = %.6f -> %.6f ; |B| = %.6f -> %.6f"
    % (float(msqrt(mpf(fn2(hA).numerator) / fn2(hA).denominator)), RHO - float(msqrt(mpf(fn2(hA).numerator) / fn2(hA).denominator)),
       float(msqrt(mpf(fn2(hB).numerator) / fn2(hB).denominator)), RHO - float(msqrt(mpf(fn2(hB).numerator) / fn2(hB).denominator))))

# --- nine pin constraints, exact ---
say("")
say("nine pin constraints (exact, Fraction+sqrt): r^2 - |h - pin|^2 > 0 ?")
ok_pins = True
for nm, h, pairs in (("A", hA, FAN_A), ("B", hB, FAN_B)):
    for (i, j) in pairs:
        pin = pin_exact(i, j)
        alpha, beta, Q = pin_slack_sq(h, pin)
        s_plus = sign_of(alpha, beta, Q, R * R)       # |h-(m+o)|^2 - r^2
        s_minus = sign_of(alpha, -beta, Q, R * R)     # |h-(m-o)|^2 - r^2
        # the near pin is the nearer of the two radius-r circle centres through the ring pair
        def val(sgn):
            import math
            return float(2 * sgn)
        # compare the two squared distances exactly: alpha - beta*sqrt(Q) vs alpha + beta*sqrt(Q)
        near_minus = (sign_of(alpha, beta, Q, alpha + beta * 0) == -1) if False else None
        # exact comparison: (alpha - beta sqrtQ) < (alpha + beta sqrtQ) iff beta > 0
        # the NEAR pin is the radius-r circle centre closer to the ORIGIN: m-o if m.o > 0 else m+o
        m, perp, D, K = pin
        mdot = m[0] * perp[0] + m[1] * perp[1]        # rational; m.o = mdot*sqrt(K/D)
        if mdot > 0:
            s = sign_of(alpha, -beta, Q, R * R)       # |h-(m-o)|^2 = alpha + beta*sqrt(Q)
            which = "m-o"
        elif mdot < 0:
            s = sign_of(alpha, beta, Q, R * R)        # |h-(m+o)|^2 = alpha - beta*sqrt(Q)
            which = "m+o"
        else:
            s = sign_of(alpha, beta, Q, R * R)
            which = "equal"
        ok_pins = ok_pins and (s < 0)
        say("  hub %s pin(%d,%d): near root %s ; sign(|h-pin|^2 - r^2) = %+d => pin covered: %s"
            % (nm, i, j, which, s, s < 0))
say("all nine pins strictly covered: %s" % ok_pins)

# --- the violated central triangle and its circumcentre ---
p = circumcentre(hA, CEN[C0], hB)
say("")
say("violated central triangle (A, c0=cert5, B): circumcentre p = (%s, %s)" % (p[0], p[1]))
say("|p|^2 = %s ; |p|^2 - 1 = %s  -> p inside the unit disk: %s" % (fn2(p), fn2(p) - 1, fn2(p) < 1))
say("exact checks |p - c_j|^2 - r^2 > 0 for the eleven covering centres:")
allpos = True
COVER_CENTRES = [(j, CEN[j]) for j in range(11) if j not in (HUBA, HUBB)] + [("A", hA), ("B", hB)]
for tag0, cc in COVER_CENTRES:
    val = fn2(fsub(p, cc)) - R * R
    allpos = allpos and (val > 0)
    tag = ("ring %2d" % tag0) if isinstance(tag0, int) else ("hub %s (moved)" % tag0)
    say("  %s: %s  (%s)" % (tag, val, "strictly outside" if val > 0 else "*** NOT outside ***"))
say("ALL ELEVEN strictly outside: %s" % allpos)
say("=> p is a point of the unit disk covered by NONE of the eleven radius-r disks (exact rational signs,")
say("   no arcsin/Delaunay branch used for the claim).")

# --- two-representation comparison (motivating angular form vs certificate-grade direct check) ---
def phi_num(a, b, c):
    ax, ay = mpf(a[0].numerator) / a[0].denominator, mpf(a[1].numerator) / a[1].denominator
    bx, by = mpf(b[0].numerator) / b[0].denominator, mpf(b[1].numerator) / b[1].denominator
    cx, cy = mpf(c[0].numerator) / c[0].denominator, mpf(c[1].numerator) / c[1].denominator
    v1 = (ax - cx, ay - cy)
    v2 = (bx - cx, by - cy)
    n1 = msqrt(v1[0] ** 2 + v1[1] ** 2)
    n2 = msqrt(v2[0] ** 2 + v2[1] ** 2)
    ang = acos((v1[0] * v2[0] + v1[1] * v2[1]) / (n1 * n2))
    ab = msqrt((ax - bx) ** 2 + (ay - by) ** 2)
    return ang - asin(ab / (2 * mpf(R.numerator) / R.denominator))


say("")
say("two-representation comparison (same witness):")
say("  (i) motivating angular form: phi_0 = %+.3e  (<0 would mean R_c > r; only heuristic)"
    % float(phi_num(hA, hB, CEN[C0])))
Rc2 = fn2(fsub(p, hA))
say("  (ii) certificate-grade: |p-A|^2 - r^2 = %s ; |p-C_{c0}|^2 - r^2 = %s ; |p-B|^2 - r^2 = %s"
    % (Rc2 - R * R, fn2(fsub(p, CEN[C0])) - R * R, fn2(fsub(p, hB)) - R * R))
say("       (these three are equal: R_c^2 - r^2, the same quantity the angular form encodes)")
say("       circumradius R_c = %.9f vs r = %.9f  -> R_c > r: %s" % (float(msqrt(mpf(Rc2.numerator) / Rc2.denominator)), float(R), Rc2 > R * R))
json.dump(dict(r=str(R), hubA=[str(hA[0]), str(hA[1])], hubB=[str(hB[0]), str(hB[1])],
               p=[str(p[0]), str(p[1])], p_norm2=str(fn2(p)),
               outside_signs=[str(fn2(fsub(p, cc)) - R * R) for _, cc in COVER_CENTRES],
               pins_strict=bool(ok_pins), all_eleven_outside=bool(allpos),
               Rc2_minus_r2=str(Rc2 - R * R)), io.open(HERE / "exact_missed_point.json", "w"), indent=1)
io.open(HERE / "exact_missed_point.out.txt", "w", encoding="utf-8").write("\n".join(OUT) + "\n")
print()
print("wrote exact_missed_point.out.txt / .json")
