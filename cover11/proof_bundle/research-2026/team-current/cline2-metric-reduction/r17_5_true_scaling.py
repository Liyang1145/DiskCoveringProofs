"""R17-5: true flat-limit scaling under the EXACT constraints (no approximations),
plus a clarification of why my earlier scan produced a misleading constant.

Withdrawn in this round: (a) flat limit of the sector width = 2 asin r (FALSE: the flat limit
is w = 2 asin(r/2), since at flatness the site's chord is the diameter-ish chord |P1P2| -> r);
(b) eps = 2 arcsin(delta/(2 sin(w/2))); (c) h = sqrt(delta(2r-delta)); (d) h/eps -> const and a
consequent "linear collar"; (e) the assertion that C842 bounds alpha2 <= pi - 1e-8 (claim_get
C842: it excludes alpha = pi at the ENDPOINT sectors 0 and 4 only).

EXACT family. Site M at the origin, switches P1,P2 on the unit circle with |M P1| = |M P2| = r
(switch radii), beta := angle(M P1 O) = (pi - eps)/2 where O is the unit-circle centre and
eps := pi - alpha2. Law of sines in triangle M P1 O with |OP1| = 1:
      sin(phi) = r sin(beta),     phi := angle(M O P1),
      |MO| = a with a = r/2 / sin(phi) ... implemented directly by intersecting the two
      circles of radius 1 about P1 and (by symmetry) resolving O.
      h := dist(M, span(P1,P2)) = r cos(beta + phi),
      w := sector width, 2 sin(w/2) = |P1P2| = 2 r cos(eps/2),
      delta := (2 asin(r/2)) - w   [deficit of the sector width from its flat value].
"""
import math


def config(r, beta):
    """exact configuration from beta; returns phi, h, eps, w, delta."""
    s = r * math.sin(beta)
    if s > 1:
        return None
    # O solved from |O| = 1 and |O - P1| = 1 with P1 = r (cos beta, sin beta):
    #   |O|^2 = 1 and |O|^2 - 2 r (O.ex) + r^2 = 1  =>  O.ex = r/2,
    #   O.en = +- sqrt(1 - r^2/4)
    ex = (math.cos(beta), math.sin(beta))
    en = (-math.sin(beta), math.cos(beta))
    a = r / 2
    b2 = 1 - r * r / 4
    if b2 < 0:
        return None
    b = math.sqrt(b2)
    O = (a * ex[0] + b * en[0], a * ex[1] + b * en[1])
    phi = math.atan2(abs(O[0] * ex[1] - O[1] * ex[0]), O[0] * ex[0] + O[1] * ex[1])
    eps = math.pi - 2 * beta
    h = r * math.cos(beta + phi)
    chord = 2 * r * math.cos(eps / 2)
    w = 2 * math.asin(min(1.0, chord / 2))
    delta = 2 * math.asin(r / 2) - w
    return phi, h, eps, w, delta, O


def main():
    print("exact check: |OP1| = 1 and |OM| = 1 - h ... (sanity)")
    for r in (0.38,):
        for bd in (80.0, 88.0, 89.9):
            beta = math.radians(bd)
            phi, h, eps, w, delta, O = config(r, beta)
            P = (r * math.cos(beta), r * math.sin(beta))
            print(f"  r={r} beta={bd:6.3f}: |OP|={math.hypot(P[0]-O[0],P[1]-O[1]):.12f}"
                  f"  phi={math.degrees(phi):.6f} deg  h={h:.6e}  eps={eps:.6e}"
                  f"  w={w:.9f}  w_flat={2*math.asin(r/2):.9f}  delta={delta:.6e}")

    print("\nexponent scan (r = 0.38): eps_k = 3.4907e-2 * 10^{-k}")
    print("   %10s %14s %14s %10s %10s %12s" % ("eps", "h", "delta", "p(h)", "q(delta)", "h/delta"))
    r = 0.38
    rows = []
    for k in range(0, 9):
        beta = math.pi / 2 - 3.490658503988659e-2 / 2 * 10.0 ** (-k)
        out = config(r, beta)
        if out is None:
            continue
        phi, h, eps, w, delta, O = out
        rows.append((eps, h, delta))
    for i, (eps, h, delta) in enumerate(rows):
        if i == 0:
            print("   %10.3e %14.6e %14.6e %10s %10s %12.6e" % (eps, h, delta, "-", "-", h / delta))
        else:
            e0, h0, d0 = rows[i - 1]
            p = (math.log(h) - math.log(h0)) / (math.log(eps) - math.log(e0))
            q = (math.log(delta) - math.log(d0)) / (math.log(eps) - math.log(e0))
            print("   %10.3e %14.6e %14.6e %10.6f %10.6f %12.6e" % (eps, h, delta, p, q, h / delta))

    print("\n   1/H: the opposite direction (what my earlier scan actually measured)")
    print("   my earlier scan moved the site off the chord with BOTH |site - Pj| held at r and")
    print("   the chord endpoints FIXED, which is not the physical family: in the physical")
    print("   family only the switch radii are r, so the two endpoints' distances to the site")
    print("   differ by O(eps) and the family is 2-parameter. Consequence: that scan's constant")
    print("   h/eps ~ 0.19 measures a non-physical one-parameter subfamily and is not usable.")


if __name__ == "__main__":
    main()
