# C853-RIDGE-DOMAIN.md — exact ridge-feasibility domain (global on the legal chart domain)

Owner: cline2-sharp-fan (own files only; no kernel write, no lead edits).
Instrument: tools/ridge_domain_analysis.py -> out/p34_ridge_domain.txt (mpmath dps=30).
Read: lead/LOCAL-HUB-RIDGE-ELIMINATION.md.  No monotonicity of the objective is used here:
this file answers only the FEASIBILITY question for the ridge point.

Domain used (legal chart domain, C849):  r in [3/8, 19/50],  b1,b2 in (acos(r)/2, acos(r)],
s = sqrt(1-r^2), phi = asin r.  Note acos(r) = pi/2 - phi and the legal-width threshold
bmin = (acos r + asin(sin eta / r) - eta)/2 satisfies bmin >= acos(r)/2, so the legal-width
domain is a SUBSET of this domain.

Ridge point:  delta* = b1 - b2,  H* = 2r sin(b1+b2),  A = b2,  B = b1.

================================================================================
1. THE ONE NECESSARY-AND-SUFFICIENT INEQUALITY
================================================================================
Write c9 for the hub centre.  On the ridge
    c9 = (s - H* cos delta*, -H* sin delta*) = (s - r(sin 2b1 + sin 2b2), r(cos 2b1 - cos 2b2)),
and the C848 hub-norm condition is exactly |c9| <= 1 - r.  Its residual is
    R := H*^2 - 2 s cos(delta*) H* + 2r(1-r) = |c9|^2 - (1-r)^2 = -2 r * Phi,
with the three equivalent forms of Phi (each verified equal to machine zero at dps=30):
   Phi = 2 s sin(b1+b2) cos(b1-b2) - 2 r sin^2(b1+b2) - (1-r)
       = s (sin 2b1 + sin 2b2) - 2 r sin^2(b1+b2) - (1-r)
       = r cos(2b1+2b2) + s (sin 2b1 + sin 2b2) - 1.
    ** RIDGE IS C848-FEASIBLE  <=>  Phi(r,b1,b2) >= 0,
       i.e.  r cos(2b1+2b2) + sqrt(1-r^2) (sin 2b1 + sin 2b2) >= 1. **
This single inequality is sufficient as well as necessary, because every other C848
constraint is automatic at the ridge:
   (F1) both face upper bounds are SATURATED exactly: H* = 2r sin(b1+b2) = 2r sin(2b1-delta*)
        = 2r sin(2b2+delta*), so H* is admissible with zero slack;
   (F2) the separation lower bound H* >= 2r|sin delta*| holds with the exact identity
           H* - 2r|sin delta*| = 4 r cos(max(b1,b2)) sin(min(b1,b2))  > 0
        (verified to machine zero); it can vanish only at min b = 0 or max b = pi/2, both
        excluded because b <= acos(r) = pi/2 - asin r < pi/2 strictly and b > 0;
   (F3) H* <= 2r since sin(b1+b2) <= 1;
   (F4) "Phi >= 0" already implies disc >= 0 (if the quadratic in H had no real root it would
        be positive everywhere and Phi >= 0 would fail), so no separate discriminant check.

================================================================================
2. THE FEASIBLE (b1,b2) SET IS THE WHOLE LEGAL DOMAIN
================================================================================
Relaxation: b1,b2 in (acos(r)/2, acos(r)] forces
   w := sin(b1+b2) in (sin 2phi, 1] = (2rs, 1]      and     cos(b1-b2) >= sqrt((1+r)/2),
(the second because |b1-b2| < acos(r)/2 strictly).  Phi = 2 s cos(b1-b2) w - 2 r w^2 - (1-r)
is concave in w and increasing in cos(b1-b2), so on the relaxed box
   Phi >= min( A , B ),   A = (1+r)( sqrt(2(1-r)) - 1 ),
                          B = (1-r^2)( 4r sqrt((1+r)/2) - 8 r^3 ) - (1-r),
with A from the endpoint w = 1 and B from the endpoint w = 2rs.
On r in [3/8, 19/50] both are strictly positive, with the crude rigorous constants
   A >= 1.375 ( sqrt(1.24) - 1 ) = 0.1561...   (uses 2(1-r) >= 1.24, 1+r >= 1.375)
   B >= 0.8556 * ( 1.5 sqrt(0.6875) - 8 (0.38)^3 ) - 0.625 = 0.0635...  > 0
   (uses 4r >= 1.5 on the left endpoint, sqrt((1+r)/2) >= sqrt(0.6875), r <= 0.38, 1-r^2 >= 0.8556)
    =>  **Phi > 0 everywhere on the legal domain: the ridge is feasible for EVERY
        (r,b1,b2) with r in [3/8,19/50] and bj in (acos(r)/2, acos(r)] — and hence a fortiori
        for every tuple whose legal width fiber is nonempty (bj >= bmin >= acos(r)/2).**
So the answer to "is the ridge always feasible on the legal width bmin?" is YES, uniformly,
with no excluded (b1,b2) region.  Numeric scan of Phi (161x161 grid per r) gives
min Phi = 0.16113, 0.15811, 0.15606 at r = 0.375, 0.378, 0.38, attained at the corner
(acos(r)/2, acos(r)); the rigorous bound min(A,B) >= 0.0635 is cruder but unconditional.

================================================================================
3. OBTUSE ARGUMENTS: INDEPENDENT OF RIDGE FEASIBILITY, AND NOT GLOBAL
================================================================================
At the ridge both sine arguments coincide: 2b1 - delta* = b1+b2 = 2b2 + delta*, so the
"obtuse face arguments" hypothesis of the delta-elimination is  b1 + b2 > pi/2, i.e. the
common argument must lie in (pi/2, pi).  Since b1+b2 ranges over (acos r, 2 acos r] =
(pi/2 - phi, pi - 2 phi], this is NOT automatic: e.g. at r = 0.375, b1 = b2 = 0.59379
(both legal) gives b1+b2 = 1.18759 < pi/2 while Phi = +0.44943, i.e. the ridge is feasible
precisely where the arguments are ACUTE.  Consequences:
  * ridge FEASIBILITY does not need obtuseness (section 2 covers the whole domain);
  * the delta-elimination DOES: the branch orientation "h1 increases, h2 decreases in delta"
    requires 2b1 - delta and 2b2 + delta in (pi/2, pi) throughout the relevant delta range,
    which for the global domain fails on a nonempty region (roughly b1+b2 <= pi/2, e.g. near
    the lower corner b1,b2 ~ acos(r)/2).  On the lead's Q0 box the condition is met
    (arguments in [2.170, 2.182]) but that is a box-specific fact, not a domain-wide one.

================================================================================
4. DEGENERACIES
================================================================================
 D1 (separation) H* = 2r|sin delta*| only if min(b1,b2) = 0 or max(b1,b2) = pi/2: excluded
    (b > 0, b <= acos r < pi/2), so the separation margin is strictly positive on the domain.
 D2 (hub band) Phi = 0, i.e. |c9| = 1 - r, is NOT attained: the numeric minimum is ~0.156
    and the rigorous bound is >= 0.0635; the hub band boundary is never touched on the domain.
 D3 (face saturation) both face upper bounds are attained with EQUALITY at the ridge, so the
    ridge is a boundary (not interior) point of the H-fiber; there is no slack to exploit.
 D4 (r = 1/2) the relaxed bound A vanishes at r = 1/2 (since sqrt(2(1-r)) = 1); on the actual
    range r <= 19/50 < 1/2 it is strictly positive, so the argument is non-vacuous.
 D5 (delta* = 0, b1 = b2) is a legal slice (delta* = 0, Phi > 0), where H* = 2r sin(2b1);
    the ridge degenerates to the symmetric configuration but stays feasible.
 D6 (|b1-b2| -> acos(r)/2) is excluded strictly by the chart domain (both b's live in a
    half-open interval of length acos(r)/2), so cos(b1-b2) > sqrt((1+r)/2) strictly.

STATUS: exact necessary-and-sufficient inequality + exact uniform margin; local-to-domain
scope, no kernel write, no claim registered, no objective-monotonicity assumption used.

