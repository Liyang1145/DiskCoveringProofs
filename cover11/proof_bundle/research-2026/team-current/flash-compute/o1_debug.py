# -*- coding: utf-8 -*-
"""o1_debug.py -- independent re-derivation of the reported negative margins.

For a given (r, m, t1,t2,t3,o12,gf) print everything: centres, both crossings, |v|,
distances to every third centre, the O1 margin, and the ledger quantities (o, private
parts, sum 2t).  Then a coarse brute-force scan of the m=0 and m=6 domains to see
whether negative margins are really attainable (min over a grid).
Only numeric; used to falsify/confirm the optimiser's readings.
"""
import math


def rho(t, r):
    return math.cos(t) - math.sqrt(max(r * r - math.sin(t) ** 2, 0.0))


def cen(t, psi, r):
    rr = rho(t, r)
    return (rr * math.cos(psi), rr * math.sin(psi))


def both_cross(c1, c2, r):
    dx, dy = c2[0] - c1[0], c2[1] - c1[1]
    D = math.hypot(dx, dy)
    h = math.sqrt(max(r * r - D * D / 4, 0.0))
    mx, my = (c1[0] + c2[0]) / 2, (c1[1] + c2[1]) / 2
    px, py = -dy / D, dx / D
    a = (mx - h * px, my - h * py)
    b = (mx + h * px, my + h * py)
    return a, b


def report(r, m, t1, t2, t3, o12, gf, label=""):
    a = math.asin(r)
    d12 = t1 + t2 - o12
    psi1, psi2 = 0.0, d12
    psi3 = psi2 + t2 + gf + t3
    c1, c2, c3 = cen(t1, psi1, r), cen(t2, psi2, r), cen(t3, psi3, r)
    vA, vB = both_cross(c1, c2, r)
    rA, rB = math.hypot(*vA), math.hypot(*vB)
    v = vA if rA <= rB else vB
    gn = 2 * math.pi - (psi3 - psi1) - t1 - t3
    mu = math.dist(v, c3) - r
    print("  %s r=%.5f m=%d  t=(%.6f,%.6f,%.6f)rad o12=%.6f gf=%.6f" % (label, r, m, t1, t2, t3, o12, gf))
    print("     psi = (%.6f, %.6f, %.6f)  gamma12 = %.6f rad (%.3f deg)" % (psi1, psi2, psi3, d12, math.degrees(d12)))
    print("     |c| = (%.6f, %.6f, %.6f)  rho/cos check: rho(%.4f deg)=%.6f"
          % (math.hypot(*c1), math.hypot(*c2), math.hypot(*c3), math.degrees(t1), rho(t1, r)))
    print("     crossings |v-| = %.9f  |v+| = %.9f  (inner=%s)" % (rA, rB, "v-" if rA <= rB else "v+"))
    print("     |v - c3| = %.9f   margin mu = %+.6e" % (math.dist(v, c3), mu))
    print("     arg(v) = %.3f deg ; arg(c3) = %.3f deg ; |diff| = %.3f deg"
          % (math.degrees(math.atan2(v[1], v[0])), math.degrees(math.atan2(c3[1], c3[0])),
             math.degrees(abs((math.atan2(v[1], v[0]) - math.atan2(c3[1], c3[0]) + math.pi) % (2 * math.pi) - math.pi))))
    print("     near gap gn = %.6f (budget %.6f) ; sum2t = %.9f (2pi = %.9f) ; excess = %.6f"
          % (gn, 12 * a, 2 * (t1 + t2 + t3), 2 * math.pi, 2 * (t1 + t2 + t3) - 2 * math.pi))
    return mu


def scan_m0(r, n=61):
    """brute force: t1,t2,t3 in [0.35a,a], o12 in [0,2min(t1,t2)], gf in [-2min(t2,t3),0] ."""
    a = math.asin(r)
    best = None
    for i in range(n):
        t1 = 0.35 * a + (a - 0.35 * a) * i / (n - 1)
        for j in range(n):
            t2 = 0.35 * a + (a - 0.35 * a) * j / (n - 1)
            for k in range(n):
                t3 = 0.35 * a + (a - 0.35 * a) * k / (n - 1)
                for io in range(11):
                    o12 = 2 * min(t1, t2) * 0.995 * io / 10
                    for ig in range(11):
                        gf = -(2 * min(t2, t3) * 0.995) * ig / 10
                        d12 = t1 + t2 - o12
                        psi3 = d12 + t2 + gf + t3
                        gn = 2 * math.pi - psi3 - t1 - t3
                        if not (0 <= gn <= 12 * a):
                            continue
                        c1, c2, c3 = cen(t1, 0.0, r), cen(t2, d12, r), cen(t3, psi3, r)
                        vA, vB = both_cross(c1, c2, r)
                        v = vA if math.hypot(*vA) <= math.hypot(*vB) else vB
                        mu = math.dist(v, c3) - r
                        if best is None or mu < best[0]:
                            best = (mu, t1, t2, t3, o12, gf, v, c3, c1, c2)
    return best


if __name__ == "__main__":
    r = 0.38
    a = math.asin(r)
    print("=" * 78)
    print("A. the optimiser's m=0 argument, recomputed from scratch")
    print("=" * 78)
    t1, t2, t3 = [math.radians(x) for x in (19.276, 22.334, 20.248)]
    report(r, 0, t1, t2, t3, 0.553635, -0.0, "opt-argmin")
    print()
    print("=" * 78)
    print("B. brute-force scan of the m=0 domain (a = %.6f)" % a)
    print("=" * 78)
    b = scan_m0(r)
    print("  min mu = %+.6e at t=(%.4f,%.4f,%.4f)deg o12=%.6f gf=%.6f" %
          (b[0], *[math.degrees(x) for x in b[1:4]], b[4], b[5]))
    report(r, 0, b[1], b[2], b[3], b[4], b[5], "scan-min")
