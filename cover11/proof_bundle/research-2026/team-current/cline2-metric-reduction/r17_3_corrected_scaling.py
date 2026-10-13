"""R17-3: CORRECTED flat-limit geometry and scaling, from the exact constraints.

My previous report asserted (a) the flat limit is w = 2 asin r for the sector width,
(b) eps := pi - alpha2 = 2 arcsin(delta/(2 sin(w/2))), (c) h = sqrt(delta(2r-delta)), and
(d) h/eps -> const, hence a linear collar. Items (a)-(d) are all withdrawn.

Exact setup (constraints enforced exactly, no approximations):
  site M (middle sector site), P1, P2 the two switch points, |M Pj| = r (switch radii),
  P1, P2 on the unit circle with |P1 P2| = 2 sin(w/2)  (w = the sector's arc width).
  alpha2 = angle at M,  h = dist(M, span(P1,P2))  (sector height),
  eps = pi - alpha2  (flatness).

Parametrise: put M at the origin, the chord horizontal at height h, P1,P2 = (m, h +- sin(w/2))
   |M Pj|^2 = m^2 + (h +- sin(w/2))^2 = r^2   (two equations)
   |O - Pj| = 1 with O = (xo, yo) the unit-circle centre.
Subtracting the two equations gives m^2 + h^2 + sin^2(w/2) = r^2 (so m, sin(w/2) < r).
"""
import math


def flat_width(r):
    """the sector width at exact flatness: alpha2 = pi  <=>  M is the chord midpoint
    <=> chi := sin(w/2) = r/2, i.e. w = 2 asin(r/2)."""
    return 2 * math.asin(r / 2), r / 2


def build(r, delta):
    """exact configuration with 2 sin(w/2) = r - delta (chi = (r-delta)/2):
       unknowns m, h with m^2 + h^2 = r^2 - chi^2 and the unit-circle conditions.
       Using the circle through P1,P2 of radius 1: O lies on the perpendicular bisector
       of the chord, at distance sqrt(1 - chi^2) from the chord midpoint; the condition
       |O - M| determines h. Solving exactly:
         O = (m +- sqrt(1 - chi^2), h)      [centre on the line through the chord normal]
       and |O - P1| = 1. The sign choice is the physical branch (M and O on opposite sides
       of the chord)."""
    chi = (r - delta) / 2
    if chi <= 0 or chi >= 1:
        return None
    # m from m^2 + h^2 = r^2 - chi^2 ; and the circle condition gives
    # |O - P1|^2 = (m - xo)^2 + chi^2 = 1 with O = (xo, h) on the perpendicular bisector
    # => xo - m = +- sqrt(1 - chi^2). Take the branch xo = m - sqrt(1-chi^2) (O inside).
    s1 = math.sqrt(max(0.0, 1 - chi * chi))
    # unknowns: m, h with
    #   (1) m^2 + h^2 = r^2 - chi^2
    #   (2) the arc from P1 to P2 has width w, i.e. the chord subtends 2 asin(chi) at O:
    #       automatically satisfied by |OP| = 1 and |P1P2| = 2 chi.
    # So any (m,h) on circle (1) with the correct rotation gives a valid w; the family is
    # 1-parameter (m), and alpha2 = pi - eps with  eps = 2 atan(chi / m)... computed below.
    out = []
    for m in (0.0,):
        h2 = r * r - chi * chi - m * m
        if h2 < 0:
            continue
        h = math.sqrt(h2)
        # angle at M between P1, P2
        v1 = (m, h - chi)
        v2 = (m, h + chi)
        ca = (v1[0] * v2[0] + v1[1] * v2[1]) / (math.hypot(*v1) * math.hypot(*v2))
        alpha = math.acos(max(-1.0, min(1.0, ca)))
        out.append((m, h, alpha, math.pi - alpha, math.hypot(*v1), math.hypot(*v2)))
    return out


def main():
    print("(1) flat limit of the sector width")
    for r in (0.375, 0.38, 0.37999):
        w, chi = flat_width(r)
        print(f"   r={r}: chi=sin(w/2)=r/2={chi:.9f} -> w=2asin(r/2)={math.degrees(w):.6f} deg"
              f"   [my withdrawn claim was 2asin r = {math.degrees(2*math.asin(r)):.6f} deg]")

    print("\n(2) exact scaling: chi=(r-delta)/2, M on the perpendicular bisector (m=0 means")
    print("    M is the chord midpoint), alpha2 and h against delta")
    print("   r      delta       chi         m         h          eps         h/eps      sqrt(delta)")
    for r in (0.38,):
        for delta in (1e-2, 1e-3, 1e-4, 1e-6, 1e-8):
            rows = build(r, delta)
            for (m, h, alpha, eps, d1, d2) in rows:
                print(f"   {r:.3f}  {delta:.0e}   {chi_of(r,delta):.9f}  {m:.6f}  {h:.8e}  {eps:.8e}"
                      f"  {h/eps if eps else float('nan'):.6f}   {math.sqrt(delta):.6f}")

    print("\n(3) does h vanish linearly in delta or as sqrt(delta)?  ratio h/sqrt(delta)")
    print("   r      delta       h           h/sqrt(delta)      h/delta")
    r = 0.38
    for delta in (1e-2, 1e-3, 1e-4, 1e-6, 1e-8, 1e-10):
        rows = build(r, delta)
        if not rows:
            print(f"   {r}  {delta:.0e}   (no solution)"); continue
        m, h, alpha, eps, d1, d2 = rows[0]
        print(f"   {r:.3f}  {delta:.0e}   {h:.8e}   {h/math.sqrt(delta):.6f}        {h/delta:.4e}")

    print("\n(4) the factor 2 sense check: for the symmetric branch, exact relations are")
    print("    |M Pj| = r,  chi = sin(w/2) = (r-delta)/2,  h^2 + m^2 = r^2 - chi^2,")
    print("    and eps = 2 atan(chi/m)  (M at the chord midpoint => m=0 must be handled by limit).")
    for r in (0.38,):
        for delta in (1e-2, 1e-4, 1e-6):
            chi = (r - delta) / 2
            h = math.sqrt(max(0.0, r * r - chi * chi))
            v1 = (-0.0, h - chi)
            v2 = (-0.0, h + chi)
            # m = 0 exactly: angle at M between (0,h-chi) and (0,h+chi)
            alpha = math.pi if h < chi else (0.0 if (h - chi) * (h + chi) > 0 and h > chi else math.pi)
            print(f"   r={r} delta={delta:.0e}: chi={chi:.9f} h={h:.9e}"
                  f"  h/chi={h/chi:.9f}  (m=0 branch: alpha={'pi' if h<chi else '0'})")


def chi_of(r, delta):
    return (r - delta) / 2


if __name__ == "__main__":
    main()
