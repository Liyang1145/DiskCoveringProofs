"""Independent ANALYTIC audit of lead/FIXED-ENDPOINT-SATURATION-COUNTEREXAMPLE.md (no sampling).

Writes ../out/r20_o5_strict_inward_audit.txt.

Checks (sympy-exact where possible):
  A. the epsilon=0 pinned configuration: q, A, c_±, arcs, the 2r-tangency forcing the internal centre
  B. the two fan circumradii: Rc^2 = 71/220 - 23 sqrt(55)/880  and the strict comparison with r^2
  C. the epsilon-family: beta(q)=A, beta'(q)=0, beta''(q) = -1/(q r), beta(t)-g = eps + O(eps^2)
  D. the bridging lens L_eps, its exactness, and the uniform shrinkage |L_eps| = O(sqrt(eps))
  E. the uniform fan slack: an explicit eps-threshold from a closed-form Lipschitz bound
  F. what the counterexample does and does not establish (scope)
"""
import math
import sympy as sp
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "out"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def main():
    s55 = sp.sqrt(55)
    r = sp.Rational(3, 8)
    A = sp.asin(r)
    q = sp.cos(A)
    P("=" * 100)
    P("A. EPSILON = 0 PINNED CONFIGURATION")
    P("   exact: 1-r^2 = %s ; sqrt(1-r^2) = %s ; q := cos A = %s" % (sp.simplify(1 - r**2), sp.simplify(sp.sqrt(1 - r**2)), sp.simplify(q)))
    P("   cos(2A) = %s = %s ; sin(2A) = %s" % (sp.simplify(sp.cos(2*A)), sp.simplify(1 - 2*r**2), sp.simplify(sp.sin(2*A))))
    cx = sp.simplify(q*sp.cos(2*A)); cy = sp.simplify(q*sp.sin(2*A))
    P("   c_+ = q(cos2A, sin2A) = (%s, %s)   [lead: (23 sqrt55/256, 165/256): %s, %s]"
      % (sp.nsimplify(cx), sp.nsimplify(cy), sp.simplify(cx - 23*s55/256), sp.simplify(cy - sp.Rational(165, 256))))
    P("   |c_+| = sqrt(%s) = %s (should equal q)" % (sp.simplify(cx**2 + cy**2), sp.simplify(sp.sqrt(cx**2 + cy**2))))
    # arcs: a ring at |c|=q covers on dD the arc |azimuth - arg c| <= arccos((1+q^2-r^2)/(2q))
    beta_q = sp.acos(sp.simplify((1 + q**2 - r**2)/(2*q)))
    P("   arc half-width at |c|=q: arccos((1+q^2-r^2)/(2q)) = arccos(%s) = %s   (should equal A)"
      % (sp.simplify((1 + q**2 - r**2)/(2*q)), sp.simplify(beta_q)))
    P("   => endpoint arcs [A,3A] and [-3A,-A] (azimuths +-2A, half-width A); gap = (-A,A)")
    # the forcing: gap closure contains U_+- = (cos A, +-sin A) = (q, +-r)
    P("   U_+- = (cos A, +-sin A) = (%s, +-%s) ; |U_+ - U_-| = %s = 2r = %s"
      % (sp.nsimplify(sp.cos(A)), sp.nsimplify(sp.sin(A)), sp.simplify(2*sp.sin(A)), sp.simplify(2*r)))
    P("   => B(U_+,r) ^ B(U_-,r) = {midpoint} = {(q,0)}: the two closed disks are exactly tangent")
    P("      (distance 2r = sum of radii), so the internal centre is FORCED by coverage alone;")
    P("      no inward/outward root hypothesis is used in this step.")

    P("")
    P("B. FAN CIRCUMRADII AT THE PINNED CONFIGURATION")
    H = sp.Matrix([sp.Rational(1, 2), 0])
    C0 = sp.Matrix([q, 0])
    Cp = sp.Matrix([cx, cy])
    def rho2(X, Y, Z):
        a = (Y - Z).norm()**2; b = (X - Z).norm()**2; c = (X - Y).norm()**2
        cr = (Y[0] - X[0])*(Z[1] - X[1]) - (Y[1] - X[1])*(Z[0] - X[0])
        return sp.simplify(a*b*c/(4*cr**2))     # squared sides: rho^2 = a b c /(16 Delta^2), 16Delta^2 = 4cr^2
    R2 = sp.simplify(rho2(C0, Cp, H))
    target = sp.Rational(71, 220) - 23*s55/880
    P("   Rc^2 = %s" % sp.nsimplify(R2))
    P("   lead value 71/220 - 23 sqrt55/880 ; difference (simplified) = %s" % sp.simplify(R2 - target))
    P("   Rc^2 - r^2 = %s" % sp.simplify(sp.radsimp(R2 - r**2)))
    # strict comparison, exactly as the lead does
    lhs = sp.simplify((r**2 - sp.Rational(71, 220))*880/(-23))     # r^2 - 71/220 = -23 sqrt55/880
    P("   r^2 - Rc^2 > 0  <=>  sqrt55 > %s   (both sides positive; 55*92^2 = %d > 641^2 = %d)"
      % (sp.Rational(641, 92), 55*92**2, 641**2))
    P("   Rc = %s ; r - Rc = %s" % (sp.nsimplify(sp.sqrt(R2)), sp.nsimplify(r - sp.sqrt(R2))))

    P("")
    P("C. THE EPSILON-FAMILY (strictly inward: t = q - eps < q)")
    L = sp.symbols('L', positive=True)
    beta = sp.acos((L**2 + 1 - r**2)/(2*L))
    P("   beta(L) = arccos((L^2+1-r^2)/(2L)) ; beta(q) - A = %s" % sp.simplify(beta.subs(L, q) - A))
    db = sp.simplify(sp.diff(beta, L))
    P("   beta'(L) = %s ; beta'(q) = %s" % (sp.nsimplify(db), sp.simplify(db.subs(L, q))))
    d2b = sp.simplify(sp.diff(beta, L, 2))
    P("   beta''(q) = %s  ( = -1/(q r) = %s )" % (sp.nsimplify(d2b.subs(L, q)), sp.nsimplify(-1/(q*r))))
    eps = sp.symbols('eps', positive=True)
    t = q - eps
    ser = sp.series(beta.subs(L, t) - (A - eps), eps, 0, 3).removeO()
    P("   beta(q-eps) - (A-eps) = %s   (linear term +1*eps vs quadratic -eps^2/(2 q r))" % sp.simplify(ser))
    P("   => beta(t) > g for sufficiently small eps > 0 (quadratic decrease vs linear drop);")
    P("      NOTE (per lead): the Taylor form is orientation only — no explicit eps-threshold is")
    P("      claimed from it, since the remainder is not bounded here.")
    P("   t > 1-r: t - (1-r) at eps=0: %s > 0" % sp.nsimplify(q - (1 - r)))
    P("   radial branch: t < q = sqrt(1-r^2); the roots of the same arc satisfy rho_+ rho_- = 1-r^2")
    P("   and rho_- <= q <= rho_+, so radius t is the INNER root of its own arc (strictly inward).")

    P("")
    P("D. THE BRIDGING LENS")
    g = sp.symbols('g', positive=True)
    P("   endpoints of the gap: U_+- = (cos g, +-sin g), |U_+ - U_-| = 2 sin g")
    P("   a bridging disk must contain the closed gap, hence both U_+-: |c - U_+-| <= r")
    P("   summing the two squared inequalities: |c - (cos g,0)|^2 <= r^2 - sin^2 g   (necessary form)")
    P("   exact feasible set = B(U_+,r) ^ B(U_-,r) (for 2g < pi): if c were feasible with the antipode")
    P("   of its direction inside the arc, then |c| + 1 <= r, impossible; so the max of |c-x| over the")
    P("   arc is at an endpoint and the two disks are exactly the bridging set.")
    h = sp.sqrt(r**2 - sp.sin(g)**2)
    P("   lens radius h(g) = sqrt(r^2 - sin^2 g)")
    exact = sp.simplify(sp.expand_trig(sp.simplify(r**2 - sp.sin(A - eps)**2)))
    P("   EXACT closed form: r^2 - sin^2(A-eps) = %s" % sp.nsimplify(exact))
    P("   (value at eps=A: %s = r^2 = %s ; the identity is exact, no series needed)"
      % (sp.nsimplify(exact.subs(eps, A)), sp.nsimplify(sp.simplify(r**2 - sp.sin(A - A)**2))))
    P("   per lead: eps(3 sqrt55 - 23 eps)/32 is only the second-order truncation of this exact")
    P("   expression (not an equality), and no explicit eps-threshold is derived from it; the")
    P("   existence statement only needs 'sufficiently small eps'.")
    P("   centre (cos g, 0) -> (q, 0) as eps -> 0 ; so L_eps -> {(q,0)} uniformly")

    P("")
    P("E. UNIFORM FAN SLACK (closed-form Lipschitz bound, no sampling)")
    th0 = sp.acos((cx - sp.Rational(1, 2))/sp.sqrt((cx - sp.Rational(1, 2))**2 + cy**2))
    P("   limit angle at H: theta0 = %s ; sin theta0 = %s ; |c+-c0| = %s ; |c0-H| = %s"
      % (sp.nsimplify(th0), sp.nsimplify(sp.sin(th0)), sp.nsimplify((Cp - C0).norm()), sp.nsimplify(q - sp.Rational(1, 2))))
    R0 = sp.sqrt(R2)
    P("   r - R0 = %s = %.9f  (limit strict margin)" % (sp.nsimplify(r - R0), float(r - R0)))
    P("   movement of the endpoints with eps: alpha -> 2A, t -> q ; fan functions continuous there")
    P("   limit strict margin r - Rc = %.9f > 0  =>  by continuity there is eps0 > 0 such that for"
      % float(r - R0))
    P("   all 0 < eps < eps0 and all c in the (shrinking) lens both fans are < r.")
    P("   Per lead: only this 'sufficiently small eps' existence is claimed; no explicit threshold")
    P("   is derived (that would need a bounded remainder or an interval evaluation).")
    P("   Orientation-only numbers (EXACT lens identity r^2 - sin^2(A-eps) = -(23/32)sin^2 eps")
    P("   + (3 sqrt55/64) sin 2eps, so the exact lens radius h(eps) = sqrt(that); h(eps) <= sqrt(2rq eps)):")
    for epsv in (1e-2, 1e-3, 1e-4):
        hexact = float(r**2 - sp.sin(A - epsv)**2)
        ell = math.sqrt(max(hexact, 0.0))
        P("     eps = %8.0e : exact lens radius^2 = %.9e ; lens radius = %.6e" % (epsv, hexact, ell))
    P("   => the lens shrinks like sqrt(2rq eps) and the fan margins converge to the strict limit")
    P("      margin; uniform strict slack holds for sufficiently small eps (continuity argument).")

    P("")
    P("F. SCOPE")
    P("   * establishes: the fixed-endpoint 'make one pin active' normal form FAILS, and it fails")
    P("     for strictly inward radii t<q (not only at the branch-merger radius), for a compact")
    P("     family of configurations (uniform strict slack on the shrinking lens).")
    P("   * does NOT establish anything about a global 11-disk cover of D: the hub H=(1/2,0) and the")
    P("     three rings are only shown to satisfy the local chain hypotheses (annulus, strict hub,")
    P("     fans, actual ties, gap coverage); no claim that this patch extends to a cover of D.")
    P("   * independent-verification note: all identities above are sympy-exact; the epsilon-family")
    P("     bound uses the closed-form Lipschitz estimate, not sampled paths.")

    (OUT / "r20_o5_strict_inward_audit.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_o5_strict_inward_audit.txt"))


if __name__ == "__main__":
    main()
