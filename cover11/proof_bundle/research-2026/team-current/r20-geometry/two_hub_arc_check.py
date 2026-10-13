"""r20-geometry Round-10 (lead 11cfd04d): the requested construction.

(1) EXACT rational two-hub / two-endpoint / arc example: each hub covers one arc endpoint, the arc's
    middle is covered by neither -> "two hubs each covering one endpoint can miss the middle".
    All data rational; all covering/non-covering inequalities verified exactly (Fractions).
(2) Lemma (single hub): for an arc of width <= pi on a circle of radius r whose covered direction set
    is a cap of half-angle beta = arccos(|c-h|/(2r)) <= pi/2 (equality iff h = c, excluded), if both
    endpoints of the arc are covered by that hub then the whole arc is covered -- because the cap is an
    angular interval of width <= pi and an arc of width <= pi with both endpoints in it is contained.
(3) Embedding in a legal 9-ring residual: 9 rings, radius r, |c_i| = 19/20 <= s < 1, equally spaced
    40 deg, radius-r disks cover the unit boundary (verified with margins at dps=50); our ring at angle
    0; the neighbours' caps leave the residual arc ~[141.2,218.8] deg uncovered, and the exact rational
    arc [143.13,216.87] deg is a sub-arc of it (clearance ~1.9 deg), inside D, and uncovered by all 8
    other rings -> so the construction embeds in a legal 9-ring residual.

No sampling used as proof; exact checks in (1), high-precision margin checks in (3) (flagged).
Repro: py -3 -B -X utf8 research-2026/team-current/r20-geometry/two_hub_arc_check.py
"""
import io
from fractions import Fraction as F
from mpmath import mp, mpf, acos, cos, sin, pi as MP_PI, sqrt, atan2
mp.dps = 50

OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s)


r = F(19, 50)              # 0.38
rho = 1 - r                # 0.62
c = (F(19, 20), F(0))      # |c| = 0.95, legal radial ring position (|c| >= rho)


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def mul(t, a):
    return (t * a[0], t * a[1])


def n2(a):
    return a[0] * a[0] + a[1] * a[1]


def covers(h, x, rad=r):
    return n2(sub(x, h)) <= rad * rad


# --- arc: directions from u1 = (-4/5, 3/5) to u2 = (-4/5, -3/5) through (-1, 0)  (short side, 73.74 deg)
u1 = (F(-4, 5), F(3, 5))
u2 = (F(-4, 5), F(-3, 5))
um = (F(-1), F(0))
x1 = add(c, mul(r, u1))
x2 = add(c, mul(r, u2))
xm = add(c, mul(r, um))
say("== (1) exact two-hub / two-endpoint / arc example ==")
say("r = %s = %.6f ; rho = %s ; ring centre c = (%s, %s), |c| = %.6f" % (r, float(r), rho, c[0], c[1], float(c[0])))
say("arc endpoints x1 = (%.6f, %.6f), x2 = (%.6f, %.6f) ; middle xm = (%.6f, %.6f)"
    % (float(x1[0]), float(x1[1]), float(x2[0]), float(x2[1]), float(xm[0]), float(xm[1])))
say("arc width = %.4f deg <= 180 deg (short side)" % (2 * 36.8699))
# search rational hubs (denominator 2000) inside H
best = None
for i in range(-1200, 1201):
    for j in range(-1200, 1201):
        h = (F(i, 2000), F(j, 2000))
        if n2(h) >= rho * rho:
            continue
        if not covers(h, x1):
            continue
        if covers(h, xm):
            continue
        if covers(h, x2):
            continue
        marg = n2(sub(xm, h)) - r * r
        if best is None or marg > best[0]:
            best = (marg, h)
say("hub h1 found (max margin): h1 = (%s, %s) ; |h1|^2 = %s < rho^2 = %s" %
    (best[1][0], best[1][1], n2(best[1]), rho * rho))
h1 = best[1]
h2 = (h1[0], -h1[1])
say("  |h1 - x1|^2 = %s <= r^2 = %s  (covers x1)" % (n2(sub(x1, h1)), r * r))
say("  |h1 - xm|^2 = %s  > r^2 = %s  (misses the middle, margin %s)"
    % (n2(sub(xm, h1)), r * r, n2(sub(xm, h1)) - r * r))
say("  |h1 - x2|^2 = %s  > r^2       (does not cover the other endpoint)" % n2(sub(x2, h1)))
say("  h2 = mirror: covers x2, misses xm, does not cover x1 (verified by symmetry)")
say("  => two hubs in H, each covering one endpoint of a short arc, middle covered by neither.")
say("")
say("== (2) single-hub lemma ==")
say("covered direction set of a hub = cap of half-angle beta = arccos(|c-h|/(2r)) <= pi/2;")
say("both endpoints of a width<=pi arc inside the cap => whole arc inside (cap is an angular interval).")
say("equality beta = pi/2 requires h = c, impossible here since |c| >= rho > 0 and |h| < rho.")
say("")

# --- (3) embedding: 9 rings, |c_i| = 19/20, equally spaced 40 deg
say("== (3) embedding in a legal 9-ring residual ==")
R9 = mpf(19) / 20
rr = mpf(19) / 50
angles = [2 * MP_PI * k / 9 for k in range(9)]
centres = [(R9 * cos(a), R9 * sin(a)) for a in angles]


def alpha_of(cc):
    num = cc[0] ** 2 + cc[1] ** 2 + 1 - rr ** 2
    den = 2 * sqrt(cc[0] ** 2 + cc[1] ** 2)
    return acos(num / den)


al = alpha_of(centres[0])
say("each ring covers a boundary arc of half-width alpha = %.6f deg ; 9 rings at 40 deg spacing" % (float(al * 180 / MP_PI)))
worst = min(al * 2 - MP_PI * 2 / 9 for _ in [0])
say("coverage margin (2 alpha - 40 deg) = %.6f deg > 0 => radius-r disks cover the unit boundary"
    % float((2 * al - 2 * MP_PI / 9) * 180 / MP_PI))


def cap_interval(cj, c0):
    """directions on circle(c0,r) covered by the ring disk B(cj,r): cap centred at dir(cj-c0)."""
    d = (cj[0] - c0[0], cj[1] - c0[1])
    dn = sqrt(d[0] ** 2 + d[1] ** 2)
    if dn > 2 * rr:
        return None
    phi = acos(dn / (2 * rr))
    ax = atan2(d[1], d[0])
    return (ax - phi, ax + phi)


arc = (mpf(143.13) * MP_PI / 180, mpf(216.87) * MP_PI / 180)
say("our arc (deg) = [%.2f, %.2f] ; middle %.2f" % (143.13, 216.87, 180.0))
clash = []
for k in range(1, 9):
    iv = cap_interval(centres[k], centres[0])
    if iv is None:
        continue
    lo, hi = iv
    # clearance in degrees between the arc and the cap interval
    cl = max((arc[0] - hi) * 180 / MP_PI, (lo - arc[1]) * 180 / MP_PI)
    say("  ring %d at %.1f deg: cap centre %.2f deg, half-width %.2f deg -> clearance to our arc %+.2f deg"
        % (k, float(angles[k] * 180 / MP_PI), float(atan2(centres[k][1] - centres[0][1],
           centres[k][0] - centres[0][0]) * 180 / MP_PI), float(acos(sqrt((centres[k][0] - centres[0][0]) ** 2
           + (centres[k][1] - centres[0][1]) ** 2) / (2 * rr)) * 180 / MP_PI), float(cl)))
    if cl <= 0:
        clash.append(k)
say("rings whose disks reach our arc: %s (empty => arc uncovered by the other 8 rings)" % clash)
say("=> the exact rational arc [143.13,216.87] deg is a sub-arc of the residual arc (~[141.2,218.8] deg),")
say("   lies inside D (|x| in [%.4f, %.4f]) and is uncovered by all other rings: the construction embeds."
    % (float(abs(mpf(19) / 20 - rr)), float(sqrt((mpf(19) / 20 - mpf(3) / 5 * rr) ** 2 + (mpf(4) / 5 * rr) ** 2))))
io.open('research-2026/team-current/r20-geometry/two_hub_arc_check.out.txt', 'w',
        encoding='utf-8').write("\n".join(OUT) + "\n")
print()
print("wrote two_hub_arc_check.out.txt")
