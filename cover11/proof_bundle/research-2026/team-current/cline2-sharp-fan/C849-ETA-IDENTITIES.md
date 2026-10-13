# C849-ETA-IDENTITIES.md — neighbour-centre eta/alpha/L, constants, uniform bounds

Owner: cline2-sharp-fan (own files only). Instrument `tools/c849_identities.py`,
output `out/p32_c849_identities.txt`. No kernel re-audit, no sign-monotonicity re-check.

Setup (C849 chart): s = sqrt(1 - r^2), phi = asin r,
  c = (s - 2 r sin b cos b, -2 r sin^2 b),  P1 = (s, -r) = (cos phi, -sin phi),
  P(w) = clockwise rotation of P1 by w,  so arg P(w) = theta1 - w with theta1 = -phi = -asin r.
  eta(w) := atan2( cross(c,P(w)) , 1 - c.P(w) ).
All statements below are exact (the only numerical content is the calibration at the end).

================================================================================
T1. THE COMPLEX IDENTITY BEHIND eta  (exact)
================================================================================
Write P for P(w), p = c.P, so cross(c,P) = c_x P_y - c_y P_x.  With z = P as a complex
number and conj(c) the conjugate of c,
   conj(c) P = (c.P) + i cross(c,P)      [direct expansion]
   =>  1 - conj(c) P = (1 - p) - i cross(c,P),
   =>  eta = -arg(1 - conj(c) P).
Also (P - c) conj(P) = |P|^2 - c conj(P) = 1 - c conj(P), whose conjugate is 1 - conj(c)P;
hence arg(1 - conj(c)P) = -arg((P-c)conj(P)) = -arg(P-c) + arg(P), and therefore
    **eta(w) = arg(P(w) - c) - arg P(w) = arg(P(w) - c) - (theta1 - w).**
Equivalently, for the fixed point P1:  eta1 := arg(P1 - c) - theta1 = eta(0).

================================================================================
T2. alpha AND L  (exact; the lead's two formulas)
================================================================================
alpha := the oriented angle at c from (P - c) to (P1 - c), i.e. arg(P1 - c) - arg(P - c).
Using T1 twice:
  alpha = arg(P1-c) - arg(P-c) = [eta1 + theta1] - [eta(w) + theta1 - w] = w + eta1 - eta(w).
    => **alpha = w + eta1 - eta(w)**   (and alpha(0) = 0, consistently, since eta(0) = eta1).
L := the angle at P in the triangle (c, P(w), P1).  The chord direction from P(w) to P1 is
perpendicular to the radius at the midpoint argument, hence has argument
  (theta(w) + theta1)/2 + pi/2 = theta(w) + w/2 + pi/2      (using theta1 = theta(w) + w),
and the direction of P -> c is arg(c - P) = arg(P - c) + pi = theta(w) + eta(w) + pi.
  L = [theta(w) + eta(w) + pi] - [theta(w) + w/2 + pi/2] = pi/2 + eta(w) - w/2
    => **L + w/2 = pi/2 + eta(w)**.

================================================================================
T3. THE CONSTANT eta1 (exact evaluation)
================================================================================
c - P1 = (-2 r sin b cos b, -2 r sin^2 b + r) = (-r sin 2b, r cos 2b), hence
  P1 - c = r (sin 2b, -cos 2b)   and   arg(P1 - c) = 2b - pi/2.
(Verified exactly: (P1 - c) - r(sin 2b, -cos 2b) = (0,0).)
With theta1 = -asin r:
    **eta1 = (2b - pi/2) - (-asin r) = 2b + asin r - pi/2.**        [exact]
Sign/range on the chart domain b in (acos(r)/2, acos(r)]: pi/2 < 2b + asin r <= pi - asin r,
so eta1 = 2b + asin r - pi/2 lies in **(0, pi/2 - asin r]**, i.e. eta1 in (0, pi/2 - asin r],
positive and bounded away from pi/2 (strictly < pi/2 because asin r > 0).

================================================================================
T4. UNIFORM |c| BOUND, and THE DENOMINATOR IS UNIFORMLY POSITIVE  (r in [3/8,19/50])
================================================================================
|c|^2 = (s - r sin 2b)^2 + r^2 cos^2 2b   (using -2r sin^2 b = -r + r cos 2b)
      = 1 + r^2 - 2 r (s sin 2b + r cos 2b) = **1 + r^2 - 2 r sin(2b + phi)**     [exact,
      verified symbolically: |c|^2 - (1 + r^2 - 2 r sin(2b + asin r)) = 0]
Domain b in (acos(r)/2, acos(r)]  <=>  2b + phi in (pi/2, pi - phi]  =>  sin(2b+phi) in [r, 1),
hence
    **(1 - r)^2 < |c|^2 <= 1 - r^2 = s^2**,   i.e.   **1 - r < |c| <= s < 1.**
This is the requested uniform bound (equality |c| = s exactly at the inwardness boundary
b = acos r; |c| -> 1-r as b -> acos(r)/2).  In particular |c| < 1, so for every unit P
    1 - c.P >= 1 - |c| >= 1 - s,   and   s = sqrt(1-r^2) <= sqrt(55)/8 on r in [3/8, 19/50]
    (s decreasing in r; min of 1-s at r = 3/8).
EXACT RATIONAL BOUND:  1 - sqrt(55)/8 > 1/14  <=>  13/14 > sqrt(55)/8  <=>  (52/7)^2 > 55
   <=>  2704/49 > 55  <=>  2704 > 2695.   TRUE.
    =>  **1 - c.P > 1/14 > 0 uniformly on the whole chart domain, r in [3/8, 19/50].**
Consequences (all from the same bound):
 (a) eta = atan2(imag, real) with real part 1 - c.P > 0, so eta takes values in
     **(-pi/2, pi/2)** and is a SMOOTH function of w on the whole real line: the atan2 has no
     branch crossing.  Hence alpha(w) = w + eta1 - eta(w) and L(w) + w/2 = pi/2 + eta(w) are
     smooth for ALL w, including w past the flat endpoint, and alpha is automatically the
     UNWRAPPED branch (the physical sector is the restriction alpha in [0, pi]).
 (b) d^2 = |P - c|^2 <= (1 + |c|)^2 <= (1 + s)^2 <= (1 + sqrt(55)/8)^2 = 3.713425... < 4.
 (c) With the previously machine-verified alpha' = (1 - c.P)/d^2 (and here also directly:
     eta' = (|c|^2 - c.P)/d^2, so alpha' = 1 - eta' = (1 - c.P)/d^2), we get
        **alpha' > (1/14)/4 = 1/56 > 0**   uniformly: alpha is strictly increasing in w, so
     alpha = pi happens at exactly one w = w_pi, and for w > w_pi the smooth formula gives
     alpha > pi, i.e. it extends the unphysical widths beyond the flat endpoint.

================================================================================
T5. CALIBRATION (identity confirmation, not proof material)
================================================================================
`tools/c849_identities.py` recomputes, at dps=40, (i) alpha from the raw triangle and
(ii) w + eta1 - eta(w), plus (i) L from the raw triangle and (ii) pi/2 + eta(w) - w/2:
they agree to the printed 10 digits at (r,b,w) = (0.38,1.0,0.3), (0.38,0.7,0.9),
(0.375,1.1,1.4), (0.38,0.6,0.2), (0.38,0.9,1.6).  Two rows need no explanation beyond the
harness: (0.375,1.1,1.4) shows the 2*pi wrap because the harness extracted alpha through
atan2 in (-pi,pi] while the identity gives the unwrapped branch; and at w = 0 the harness's
"L" is 0 because the triangle (c,P1,P1) is degenerate, whereas the identity gives the correct
limit L(0+) = pi/2 + eta1 = 2b + asin r (the tangent-chord limit), which lies in (pi/2, pi).
The exact-equality checks in T3/T4 were done symbolically (sympy difference identically 0),
and 2704 > 2695 is an exact rational comparison.

STATUS: exact identities + exact uniform bounds; no certificate, no claim registered.
