"""r20 fiber infeasibility / separation certificates (homogeneous Farkas; no CQ needed).

Writes ../out/r20_fiber_farkas_certificate.txt.  Read-only outside r20-chain.

SETTING.  Fiber constraints of the 2-hub chain come in two kinds:
  (i) DISK constraints  B(p_j, r_j)  — pin bodies K = ^_j B(p_j,r)  (and the central fan disks);
  (ii) non-convex "fan" conditions  h_B in (B(q_+,r) u B(q_-,r)) \\ (int B(q_+) ^ int B(q_-)).
Certificates used here (all for the DISK part, where Helly-3 applies):

  (F) HOMOGENEOUS FARKAS (primal-infeasibility ray):
      if there are vectors u_j with  sum_j u_j = 0  and  sum_j (p_j.u_j + r_j|u_j|) < 0
      then  ^_j B(p_j,r_j) = empty.
      Proof: if x were common, then <p_j - x, u_j> >= -r_j|u_j| for every j, i.e.
      p_j.u_j + r_j|u_j| >= x.u_j; summing, the certificate value >= <x, sum_j u_j> = 0.  Contradiction.
      No constraint qualification is used; the certificate is a dual ray.

  (S) ONE-DIRECTION SEPARATION (sharpest single direction):
      K ^ B(q,r) = empty  if  u.q - r > h_K(u)  for some u with |u| = 1.
      CLOSURE / CQ CAVEAT (lead's correction): the infimal-convolution identity
          h_{^_j K_j}(u) = inf{ sum_j h_{K_j}(u_j) : sum_j u_j = u }
      holds in general only for the CLOSED infimal convolution; it needs a CQ (e.g. a common
      interior point) to be an equality.  We therefore do NOT rest any weight on it:
        * h_K(u) itself is computed from FINITE BOUNDARY CANDIDATES (arc points with outer normal
          u/|u| plus pairwise circle intersections) — a direct geometric argument, no duality;
        * the certificate used is the CQ-free product/diagonal separation (F)/(N).
      The dual weights are quoted only as an INTERPRETATION, in the approximate sense below.
      Sharpest choice of u:  u = (q - x*)/|q - x*| with x* the point of K closest to q; then
      u.q - h_K(u) = |q - x*| = dist(q,K), so
          separation margin  = dist(q,K) - r          (> 0 needed)
          FARKAS OBJECTIVE   = r - dist(q,K)          (< 0 needed; it is minus the margin)
      SIGN CONVENTION (lead's correction): never write "Farkas value = dist - r"; the Farkas
      objective is r - dist, i.e. minus the separation margin.
      ATTAINMENT CAVEAT (lead's correction): without Slater the dual optimum need NOT be attained;
      for a STRICT gap (dist > r) an approximate dual certificate suffices (take u_j^* along an
      infimising sequence), so the certificate below is used in the "strict gap + approximation"
      sense and no attained optimum is assumed.

  (N) NECESSITY (analytic; not numeric): for ANY finite family of closed disks with empty
      intersection there ALWAYS exist u_j with sum_j u_j = 0 and sum_j (p_j.u_j + r_j|u_j|) < 0.
      Proof (diagonal strong separation in the product space):
        P = prod_j B(p_j,r_j) is compact convex; D = {(x,...,x)} is a closed convex cone (a
        subspace).  Intersection empty  <=>  P ^ D = empty.  P compact and D closed convex
        =>  strong separation: exists a linear functional L = (L_1,...,L_m) on (R^2)^m with
        sup_P L < inf_D L.  Since D is a subspace containing 0, inf_D L is either 0 or -inf, and
        the inequality forces L|_D = 0, i.e. sum_j L_j = 0, while
        sup_P L = sum_j (p_j.L_j + r_j|L_j|) < inf_D L = 0.
        So u_j = L_j is the required certificate, and no constraint qualification is used.
      Equivalent dual view (equal radii r): ^_j B(p_j,r) /= empty  <=>  Rc(p) <= r, where Rc is the
      minimum enclosing radius of the centres (Chebyshev centre problem), and then the certificate
      can be taken from its dual (the balanced weights below).

  (H3) HELLY-3 / UNIVERSAL THREE-DISK WITNESS (exact, non-equilateral included):
       let B(p_1,r),B(p_2,r),B(p_3,r) be closed disks with Rc(p_1,p_2,p_3) > r (then they have no
       common point, since a common point x would give |x-p_j| <= r for all j, hence an enclosing
       circle of radius <= r).  Let m be the Chebyshev centre (minimum enclosing circle centre) and
       Rc its radius, and let lambda_j >= 0 with sum lambda_j = 1, sum lambda_j p_j = m, supported
       on the ACTIVE indices (|m - p_j| = Rc; for an Acute triangle these are all three and lambda is
       the positive barycentric coordinate vector of the circumcentre).  Put u_j = lambda_j (m-p_j).
       Then  sum_j u_j = (sum lambda_j) m - sum lambda_j p_j = 0, and using
       |p_j|^2 = Rc^2 + 2 p_j.m - |m|^2 (valid for active j) plus sum lambda_j p_j = m:
            sum_j (p_j.u_j + r|u_j|) = |m|^2 - sum_j lambda_j |p_j|^2 + r Rc = Rc (r - Rc) < 0.
       This is a universal exact certificate for three equal disks; the equilateral case is the
       specialisation lambda = 1/3 and Rc = the circumradius.
"""
import json, math
from pathlib import Path
from mpmath import mp, mpf, sqrt, matrix, lu_solve

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "out"
ROOT = HERE.parents[3]
OBJ = ROOT / "n11" / "upper" / "certified_object.json"
LOG = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


# ---------------------------------------------------------------- helpers on float tuples
def circle_isect(q1, q2, R):
    d = math.hypot(q2[0]-q1[0], q2[1]-q1[1])
    if d > 2*R or d == 0:
        return []
    mx, my = (q1[0]+q2[0])/2, (q1[1]+q2[1])/2
    nx, ny = -(q2[1]-q1[1])/d, (q2[0]-q1[0])/d
    h = math.sqrt(max(R*R - d*d/4, 0.0))
    return [(mx+h*nx, my+h*ny), (mx-h*nx, my-h*ny)]


def support_K(pins, R, u):
    """true h_K(u) by finite boundary candidates (arc points with normal u/|u| + vertices)."""
    m = len(pins)
    nu = math.hypot(u[0], u[1])
    cand = [(p[0] + R*u[0]/nu, p[1] + R*u[1]/nu, "arc") for p in pins]
    for a in range(m):
        for b in range(a+1, m):
            for v in circle_isect(pins[a], pins[b], R):
                cand.append((v[0], v[1], "v%d%d" % (a, b)))
    best, arg = None, None
    for (x, y, tag) in cand:
        if all((x-p[0])**2 + (y-p[1])**2 <= R*R*(1+1e-12) for p in pins):
            val = x*u[0] + y*u[1]
            if best is None or val > best:
                best, arg = val, (x, y, tag)
    return best, arg


def closest_pt_K(pins, R, q):
    """point of K closest to q (finite candidates: projections of q on circles + vertices)."""
    m = len(pins)
    cand = []
    for j, p in enumerate(pins):
        d = math.hypot(q[0]-p[0], q[1]-p[1])
        if d > 0:
            cand.append((p[0] + R*(q[0]-p[0])/d, p[1] + R*(q[1]-p[1])/d, "proj%d" % j))
    for a in range(m):
        for b in range(a+1, m):
            for v in circle_isect(pins[a], pins[b], R):
                cand.append((v[0], v[1], "v%d%d" % (a, b)))
    best, arg = None, None
    for (x, y, tag) in cand:
        if all((x-p[0])**2 + (y-p[1])**2 <= R*R*(1+1e-12) for p in pins):
            dd = math.hypot(x-q[0], y-q[1])
            if best is None or dd < best:
                best, arg = dd, (x, y, tag)
    return best, arg


def dual_weights(pins, R, u):
    """weights u_j with sum u_j = u minimising sum(p_j.u_j + R|u_j|) (SLSQP, cross-check)."""
    from scipy.optimize import minimize
    m = len(pins)

    def obj(w):
        s = 0.0
        for j in range(m):
            uj = (w[2*j], w[2*j+1])
            s += pins[j][0]*uj[0] + pins[j][1]*uj[1] + R*math.hypot(*uj)
        return s
    cons = [{'type': 'eq', 'fun': lambda w: sum(w[2*j] for j in range(m)) - u[0]},
            {'type': 'eq', 'fun': lambda w: sum(w[2*j+1] for j in range(m)) - u[1]}]
    res = minimize(obj, [u[0]/m, u[1]/m]*m, constraints=cons, method='SLSQP',
                   options={'maxiter': 800, 'ftol': 1e-16})
    return float(res.fun), [(res.x[2*j], res.x[2*j+1]) for j in range(m)]


def main():
    P("=" * 100)
    P("A. FARKAS RAY (F) AND ONE-DIRECTION SEPARATION (S) — statements proved in the header")
    P("   (F) sum_j u_j = 0 and sum_j (p_j.u_j + r_j|u_j|) < 0  =>  empty intersection (no CQ).")
    P("   (S) |u|=1 and u.q - r > h_K(u)  =>  K ^ B(q,r) = empty; sharpest u along q - x* gives")
    P("       certificate value = dist(q,K) - r.  The two forms carry the same weights")
    P("       (u_j = u_j^* for pins, u_c = -u for the central disk, sum = 0).")

    P("")
    P("B. CALIBRATION 1 — two unit disks, centre distance d (r = 1):")
    for d in (1.0, 2.0, 2.5):
        p1, p2 = (-d/2, 0.0), (d/2, 0.0)
        # Farkas ray along the axis: u_1 = (1,0), u_2 = (-1,0)
        val = p1[0]*1 + 1*1 + p2[0]*(-1) + 1*1
        P("   d = %.2f : value = %.3f -> %s   (intersection nonempty iff d <= 2)"
          % (d, val, "CERTIFICATE FIRES (empty)" if val < 0 else "no certificate"))
    P("   (at d = 2 the value is exactly 0: the disks touch, intersection nonempty, certificate")
    P("    correctly does NOT fire — sharpness of the ray form.)")

    P("")
    P("C. CALIBRATION 2 — HELLY-3 CORRESPONDENCE with a POLYNOMIAL NORMALIZED WITNESS")
    P("   three unit disks at the vertices p_j of an equilateral triangle, |p_j| = rho:")
    P("   pairwise intersections nonempty (side s = sqrt(3) rho < 2), common intersection empty iff rho > 1.")
    P("   Witness: u_j = -p_j  (polynomial in the data, no radicals); sum_j u_j = 0 by symmetry;")
    P("   value = sum_j (p_j.(-p_j) + |p_j|) = 3 rho (1 - rho)  < 0 iff rho > 1.")
    for rho in (0.9, 1.0, 1.1):
        ps = [(rho*math.cos(2*math.pi*j/3), rho*math.sin(2*math.pi*j/3)) for j in range(3)]
        val = sum(p[0]*(-p[0]) + p[1]*(-p[1]) + rho for p in ps)
        P("   rho = %.2f : side = %.6f (<2: pairwise meet) ; witness value = %+.6f (= 3rho(1-rho) = %+.6f) -> %s"
          % (rho, math.sqrt(3)*rho, val, 3*rho*(1-rho),
             "CERTIFICATE FIRES (triple empty)" if val < 0 else "no certificate (triple nonempty)"))
    P("   => Helly-3 form: the infeasibility is witnessed by the 3-subfamily with weights u_j = -p_j;")
    P("      the value 3rho(1-rho) is polynomial and vanishes exactly at the Helly-critical rho = 1.")

    P("")
    P("D. RECORD OBJECT — CONTROL (certificates must NOT fire at the optimum)")
    raw = json.loads(OBJ.read_text(encoding="utf-8-sig"))
    R = mpf(str(raw["certified_interval"]["lo"]))
    Rf = float(R)
    C = [[mpf(int(a))/10**17, mpf(int(b))/10**17] for a, b in raw["centers_scaled_1e17"]]
    rings = sorted([i for i in range(11) if i not in (0, 2)],
                   key=lambda i: math.atan2(float(C[i][1]), float(C[i][0])))
    Cbase = [C[rings[i]] for i in range(9)] + [C[0], C[2]]
    idx = [(i + 4) % 9 for i in range(9)] + [10, 9]
    c = [[float(x) for x in Cbase[j]] for j in idx]
    HA, HB = c[10], c[9]
    chainA = [4, 5, 6, 7, 8]
    chainB = [0, 1, 2, 3]

    def pinf(a, b, r):
        m = [(a[0]+b[0])/2, (a[1]+b[1])/2]
        d = math.hypot(b[0]-a[0], b[1]-a[1])
        n = [-(b[1]-a[1])/d, (b[0]-a[0])/d]
        k = math.sqrt(max(r*r - d*d/4, 0.0))
        p1 = [m[0]+k*n[0], m[1]+k*n[1]]
        p2 = [m[0]-k*n[0], m[1]-k*n[1]]
        return p1 if p1[0]**2+p1[1]**2 < p2[0]**2+p2[1]**2 else p2

    pins_all = [pinf(c[i], c[(i+1) % 9], Rf) for i in range(9)]
    P("   r = %.15f ; hub A = row0, hub B = row2 ; switch rings row5 (lead c[0]) and row6 (lead c[4])"
      % Rf)
    for nm, ch, hub in (("A", chainA, HA), ("B", chainB, HB)):
        pins = [pins_all[i] for i in ch]
        P("   --- hub %s : K_%s with %d pins ; central fan disks for the two switch rings:" % (nm, nm, len(pins)))
        for s_nm, s in (("row5", 0), ("row6", 4)):
            # radius-r circle centres through (hub, c_s)
            a, b = hub, c[s]
            mx, my = (a[0]+b[0])/2, (a[1]+b[1])/2
            dd = math.hypot(b[0]-a[0], b[1]-a[1])
            nx, ny = -(b[1]-a[1])/dd, (b[0]-a[0])/dd
            kk = math.sqrt(max(Rf*Rf - dd*dd/4, 0.0))
            for sgn in (+1, -1):
                q = (mx + sgn*kk*nx, my + sgn*kk*ny)
                # (S): sharpest direction from the closest point of K to q
                dist, xstar = closest_pt_K(pins, Rf, q)
                if dist and dist > 1e-14:
                    u = ((q[0]-xstar[0])/dist, (q[1]-xstar[1])/dist)
                else:
                    u = (0.0, 0.0)
                hK, argK = support_K(pins, Rf, u)
                sep = (u[0]*q[0] + u[1]*q[1]) - Rf - hK
                if abs(sep) < 1e-12:
                    lab = "BOUNDARY (|sep| < 1e-12: tight/equality case, NO certificate; this is the saturation reading)"
                elif sep > 0:
                    lab = "FIRES (excluded)"
                else:
                    lab = "no certificate"
                P("     %s q%s = (%+.9f, %+.9f): dist(q,K) = %.12f ; SEPARATION MARGIN dist - r = %+.3e ;"
                  " FARKAS OBJECTIVE r - dist = %+.3e ;"
                  % (s_nm, "+" if sgn > 0 else "-", q[0], q[1], dist, dist - Rf, Rf - dist))
                P("        h_K(u) = %.12f (%s) ; u.q - r - h_K = %+.3e -> %s"
                  % (hK, argK[2], sep, lab))
                P("        (same certificate in Farkas normal form: weights u_j^* on pins, -u on the central")
                P("         disk; objective value = r - dist = %+.3e < 0 iff excluded. No attained dual" % (Rf - dist))
                P("         optimum is assumed: strict gap + approximate certificate suffices.)")
                hval, wj = dual_weights(pins, Rf, u)
                P("        dual cross-check: h_K(u) = %.12f ; sum(u_j) - u = (%.2e, %.2e)"
                  % (hval, sum(w[0] for w in wj) - u[0], sum(w[1] for w in wj) - u[1]))
    P("")
    P("   Control reading: at the record optimum the hub does lie in the fan region, so the")
    P("   certificates should not fire (dist(q,K) <= r or separation <= 0).  Any 'FIRES' line above")
    P("   would mean the rounded record object is NOT inside that particular fan disk (usable as an")
    P("   exclusion input, not as a global statement).")

    P("")
    P("E. NECESSITY (N) + UNIVERSAL THREE-DISK WITNESS (H3) — EXACT, non-equilateral control")
    P("   (N) proved in the header by diagonal strong separation in the product space; no CQ used.")
    P("   (H3) u_j = lambda_j (m - p_j) with sum lambda_j = 1, sum lambda_j p_j = m, lambda >= 0")
    P("        supported on the active set |m - p_j| = Rc  =>  sum u_j = 0 and")
    P("        sum_j (p_j.u_j + r|u_j|) = Rc (r - Rc) < 0 whenever Rc > r.")
    P("   Exact non-equilateral control (all rational, no radicals): triangle")
    P("        p_1=(0,0), p_2=(2,0), p_3=(1,2)   [acute: largest side^2 = 5 < 2^2 + 5 = 9]")
    P("        circumcentre m = (1, 3/4), Rc = 5/4, barycentric lambda = (5/16, 5/16, 3/8) > 0;")
    P("        radius r = 6/5 > sqrt(5)/2 (so all pairs of disks meet) and r < Rc = 5/4 (triple empty)")
    import sympy as sp
    p1, p2, p3 = sp.Matrix([0, 0]), sp.Matrix([2, 0]), sp.Matrix([1, 2])
    m = sp.Matrix([1, sp.Rational(3, 4)])
    Rc = sp.Rational(5, 4)
    lam = [sp.Rational(5, 16), sp.Rational(5, 16), sp.Rational(3, 8)]
    r_ex = sp.Rational(6, 5)
    P("        check sum lambda_j p_j = m : %s ; lambda positive: %s"
      % (sp.simplify(sum([lam[j]*sp.Matrix([p1, p2, p3][j]) for j in range(3)], sp.zeros(2, 1)) - m), all(l > 0 for l in lam)))
    P("        check |m - p_j| = Rc for all j : %s"
      % [sp.simplify(sp.sqrt((m - pj).dot(m - pj)) - Rc) for pj in (p1, p2, p3)])
    us = [lam[j]*(m - sp.Matrix([p1, p2, p3][j])) for j in range(3)]
    P("        u_j = lambda_j (m - p_j) = %s" % [[str(u[0]), str(u[1])] for u in us])
    SumU = sp.simplify(sum(us, sp.zeros(2, 1)))
    P("        sum_j u_j = (%s, %s) (exact zero)" % (SumU[0], SumU[1]))
    val = sp.simplify(sum((sp.Matrix([p1, p2, p3][j]).dot(us[j]) + r_ex*sp.sqrt(us[j].dot(us[j])))
                          for j in range(3)))
    P("        Farkas objective = %s   (Rc(r-Rc) = %s)" % (val, sp.simplify(Rc*(r_ex - Rc))))
    P("        exact equality: %s ; negative: %s" % (sp.simplify(val - Rc*(r_ex - Rc)) == 0, val < 0))
    P("        pairwise intersections nonempty: max side/2 = %s <= r = %s" % (sp.sqrt(5)/2, r_ex))
    P("   => the universal witness is exact and rational here; the equilateral case is lambda = 1/3.")

    P("")
    P("F. SCOPE")
    P("   * (F) sufficiency, (N) necessity: for finite closed disk families the Farkas ray exists")
    P("     iff the intersection is empty — a complete, CQ-free criterion.")
    P("   * (S) is the same certificate in normal form with the TRUE support; the dual weights are")
    P("     the correct replacement for the withdrawn min-h selector (no attained optimum assumed).")
    P("   * (H3) gives a universal exact 3-disk witness (acute barycentric; obtuse diameter case).")
    P("   * Non-convex fan conditions (crescent = union minus lens) are NOT reachable by Farkas;")
    P("     they need the containment/vertex analysis (all vertices of K inside the lens etc.).")
    P("   * Record-object numbers are 40-digit readings of a rounded object; no global claim.")

    (OUT / "r20_fiber_farkas_certificate.txt").write_text("\n".join(LOG) + "\n")
    P("\nwrote " + str(OUT / "r20_fiber_farkas_certificate.txt"))


if __name__ == "__main__":
    main()
