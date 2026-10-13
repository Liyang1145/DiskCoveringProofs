# C853-RIDGE-UNIFORM.md — ridge geometry feasibility is AUTOMATIC (uniform, strict)

Owner: cline2-sharp-fan (own files only; no kernel write).  Instrument
tools/ridge_uniform_proof.py -> out/p35_ridge_uniform.txt (sympy exact + mpmath sanity).
Continues C853-RIDGE-DOMAIN.md; delivers the uniform rational proof the lead asked for.

Data:  T = b1+b2, D = b1-b2, ridge H* = 2r sin T, delta* = D, A = b2, B = b1,
s = sqrt(1-r^2);  domain r in [3/8, 19/50], b1,b2 in (acos(r)/2, acos(r)].

================================================================================
0. THE LEAD'S FORM IS CORRECT, AND IT IS -Phi
================================================================================
  norm/(2r) := ( H*^2 - 2 s cosD H* + 2r(1-r) ) / (2r)
             = 1 - r cos 2T - 2 s sinT cosD
             = (1-r) + 2r sin^2 T - 2 s sinT cosD          [verified identical, exact]
             = -Phi,   Phi = 2s sinT cosD - 2r sin^2 T - (1-r).
So the hub-norm condition is norm <= 0  <=>  Phi >= 0  <=>  |c9| <= 1-r, and in the lead's
variables:
      2 s sinT cosD  >=  1 - r cos 2T  =  1 - r + 2r sin^2 T
      <=>   cosD  >=  f(v) := (1 - r + 2 r v^2)/(2 s v),      v := sinT > 0.

================================================================================
1. PROOF THAT  max_{v in (2rs,1]} f(v) <= sqrt((1+r)/2) <= cosD  FOR ALL r IN [3/8,19/50]
================================================================================
Step 1 (range of v).  T = b1+b2 in (acos r, 2 acos r] = (pi/2 - phi, pi - 2 phi] with
phi = asin r;  sin is increasing on [pi/2-phi, pi/2] and decreasing on [pi/2, pi-2 phi], and
sin(pi/2-phi) = s, sin(pi-2phi) = 2rs with 2rs < s because 2r < 1; hence
      v = sinT in (2rs, 1].
Step 2 (range of cosD).  b1,b2 lie in a half-open interval of length acos(r)/2, so
|D| < acos(r)/2 strictly, and cos is even, so
      cosD >= cos(acos(r)/2) = sqrt((1+r)/2) =: c0.
Step 3 (f is convex).  f(v) = (1-r)/(2sv) + (r/s) v  has  f''(v) = (1-r)/(s v^3) > 0 on v > 0
[verified symbolically], so on the closed interval [2rs, 1] its maximum is at an endpoint:
      sup_{v in (2rs,1]} f(v) <= max( f(2rs), f(1) ).
Step 4 (endpoint v = 1).  f(1) = (1+r)/(2s) and
      f(1) <= c0  <=>  (1+r)/(2s) <= sqrt((1+r)/2)  <=>  1+r <= 2(1-r^2)  <=>  r <= 1/2.
Since r <= 19/50 < 1/2 this is strict, with f(1)/c0 = 1/sqrt(2(1-r)) <= 1/sqrt(1.24)
= 0.898027 < 1.
Step 5 (endpoint v = 2rs).  Here
      f(2rs) = (1 - r + 8 r^3 s^2)/(4 r s^2),   s^2 = 1 - r^2,
so f(2rs) <= c0  <=>  1 - r + 8 r^3 (1-r^2) <= 4 r (1-r^2) sqrt((1+r)/2).
RATIONAL BOUNDS ON r in [3/8, 19/50]:
   L(r) := 1 - r + 8r^3 - 8r^5 is increasing, because L'(r) = -1 + 24r^2 - 40r^4 and
     24r^2 - 40r^4 >= 24(3/8)^2 - 40(19/50)^4 = 2.540946... > 1
   (24r^2 >= 24(3/8)^2 from r >= 3/8;  40r^4 <= 40(19/50)^4 from r <= 19/50);
   hence  L(r) <= L(19/50) = 38890151/39062500 = 0.99558787...
   R(r) := 4 r (1-r^2) sqrt((1+r)/2) >= 4(3/8)(1-(19/50)^2) sqrt(11/16)
                                        = 6417 sqrt(11)/20000 = 1.06413906...
   (r >= 3/8, 1-r^2 >= 1-(19/50)^2 decreasing in r, sqrt((1+r)/2) >= sqrt(11/16)).
   EXACT INTEGER COMPARISON (both sides positive, so squaring is legitimate):
       L(19/50) * 20000 < 6417 sqrt(11)  <=>  777803020000^2 < 6417^2 * 11 * 39062500^2 :
       TRUE   [checked in exact integer arithmetic].
   Hence f(2rs) < c0 with a strict margin of at least 1.06413906 - 0.99558787 = 0.068551.
Step 6 (conclusion).  max(f(2rs), f(1)) <= c0 <= cosD, therefore f(v) <= cosD for every
  admissible v, therefore norm <= 0 (strictly) for every r in [3/8,19/50] and every
  b1,b2 in (acos(r)/2, acos(r)].  Together with the automatic separation bound
      H* - 2r|sin delta*| = 4 r cos(max(b1,b2)) sin(min(b1,b2)) > 0
  the ridge point lies STRICTLY inside the C848 H-fiber, with both face upper bounds
  saturated exactly (H* = h1 = h2).

TRUE SLACK (numeric, mpmath dps=25):  max(f)/c0 = 0.92394954 / 0.92344626 / 0.92248884 /
0.92159622 at r = 0.375/0.376/0.378/0.38, worst endpoint v = 2rs, i.e. about 7.6% slack.
The crude rational route (Step 5) certifies 0.068551 absolute slack, which is enough.

================================================================================
2. CONSEQUENCE FOR THE REDUCTION (what this removes and what it does not)
================================================================================
REMOVED: the ridge hub-norm feasibility condition.  It is now a theorem on the entire legal
domain, uniformly in r, so no ridge-based argument has to carry it as a hypothesis, and no
(b1,b2) exclusion region exists.  Equivalently: the "crude D <= acos r/2 gives cosD >=
sqrt((1+r)/2) ~ 0.83" bound is sufficient; the suspect is confirmed.
NOT REMOVED (these remain box-specific and are objective-side, not geometric):
  (i) the obtuse-argument condition.  At the ridge both sine arguments coincide and equal
      T = b1+b2, so the branch orientation "h1 increasing / h2 decreasing in delta" needs
      T in (pi/2, pi) on the relevant delta-range; this fails on a nonempty part of the
      global domain (T ranges over (pi/2-phi, pi-2phi] and can be < pi/2, e.g. r = 0.375,
      b1 = b2 = 0.5938 gives T = 1.1876 < pi/2 — the ridge is feasible there, so geometry
      and orientation are genuinely independent);
  (ii) the two branch derivative sign certificates.
Equivalence note: the lead's threshold route and my Round-16 endpoint route are the same
inequality — Phi(v=1, cosD=c0) >= 0 <=> c0 >= f(1) and Phi(v=2rs, cosD=c0) >= 0 <=>
c0 >= f(2rs) — the threshold presentation is the cleaner one and gives the better bound
(0.0686 crude vs 0.0635).

STATUS: uniform strict proof, exact rational comparisons, no claim registered, no kernel write.
