# C862b-INTERIOR-CRITICAL.md — can the hub objective have an interior local max?

Owner: cline2-sharp-fan (own files, own drivers).  Exploratory diagnostic, NOT a certificate.
Drivers: tools/interior_critical_probe.py, tools/widthlegal_nd_probe.py, tools/check_p41_points.py
Outputs: out/p41.log, out/p41_interior_critical.{txt,json}, out/p42.log, out/p42_widthlegal_nd.json.
Coefficients: joint_nested_frozen.json.  Domain: r in [0.375,0.38], FULL legal bearings
b_j in (acos(r)/2, acos r], plus the width-legality variant b_j >= bmin(r) where
bmin(r) = (acos r + asin(sin(G/2)/r) - G/2)/2, G = 2pi - 16 asin(19/50) (= 0.61256 at r = 0.375).
Hub points are the lens Omega = 3 disks INTERSECT wedge, i.e. (delta, H) with
-delta in (0,b1), H in the C848 fiber.

================================================================================
0. HESSIAN AND ITS VALIDATION
================================================================================
F = affine + sum_j [a_j theta_j + beta_j L_j^2 + gamma_j L_j],  c_j = |gamma_j|,
    Hess F = 2(beta1+beta2) I - sum_j (c_j/L_j)(I - n_j n_j^T) + sum_j (a_j/L_j^2) M_j,
with n_j = (hub - Q_j)/L_j and M_j the polar-angle Hessian (eigenvalues +-1, eigendirections at
+-45 deg to n_j).  Calibration against finite differences over 40 random legal points:
  worst |analytic - numeric| = 3.85e-4 with the convention (n, n^perp) form [[0,-1/L],[-1/L,0]]
  (i.e. w_j = n_j rotated by -pi/4), versus 7.7e1 with the opposite sign.  So the formula and the
  sign convention match the lead's matrix; the 3.85e-4 is finite-difference error at h = 1e-6.

================================================================================
1. STRUCTURAL PINCH (why ND can only live in a tiny region)
================================================================================
ND at an interior point needs w^T Hess w <= 0 for ALL unit w; testing w = n_1 and w = n_2 (using
n_j^T M_j n_j = 0 and n_1^T M_2 n_1 >= -1) gives the NECESSARY conditions
    c2/L2 + a2/L2^2 >= 2(beta1+beta2) = 2.791753650   =>  L2 <= 0.419177,
    c1/L1 + a1/L1^2 >= 2(beta1+beta2)                 =>  L1 <= 0.421097,
and tr(Hess) = 4(beta1+beta2) - sum c_j/L_j = 5.583507299 - sum c_j/L_j <= 0 gives
sum_j c_j/L_j >= 5.5835.  So ND forces the hub within ~0.42 of BOTH ring centres, i.e. small
d/(2r); equivalently it is a "pinched" configuration, and generic points are far from ND.

================================================================================
2. RESULT — INTERIOR STATIONARY POINTS EXIST BUT ARE MIN/SADDLE; ND POINTS ALSO EXIST
================================================================================
(a) 400 random legal samples (full bearing range): 0 with lambda_max < 0; min lambda_max = 0.2957
    (r=.37582 b1=.73716 b2=.62035 delta=-.02892 H=.62519, sum c/L = 5.80, trace = -0.217);
    lambda_max spans [0.296, 585.4]; min |grad F| over samples = 0.0623.  So random points are
    not ND and not stationary — "no exceptions by inspection" was indeed not enough.
(b) DE minimising lambda_max(Hess) (2 seeds x 80 iters, popsize 12, polish):
      chart-legal corner: lambda_max = -0.6555, lambda_min = -0.6560 at r=.37500 b1=b2=.59320,
        delta=-.00226, H=.58163, L1=.3321 L2=.3303, sum c/L = 6.895, trace = -1.31;
      WIDTH-LEGAL run (b_j >= bmin): lambda_max = -0.466954, lambda_min = -0.466957 at
        r=.37500, b1=.61258, b2=.61257 (= bmin(0.375) = 0.61257), delta=-.00230, H=.60039,
        H strictly interior to its fiber [0.30203, 0.70505], wedge interior.
    => **an interior NEGATIVE-DEFINITE point EXISTS, also inside the width-legal domain.**
       The "global positive-eigenvalue hypothesis" is therefore FALSE (as the lead anticipated);
       its negation is not the explanation for boundary-only maximisation.  The witness is nearly
       explicit — symmetric b1 = b2 = bmin(r), delta ~ 0, r = 3/8, H ~ 0.6004 — so it is a
       realistic target for an interval certificate (that would upgrade this to a theorem; the
       present finding is numeric and kills the hypothesis only, not any maximum claim).
(c) DE minimising |grad F| (2 seeds x 80 iters): interior STATIONARY points exist and are legally
    width-compatible (b1,b2 >= 0.66 > bmin):
      seed 86240: |grad| = 4.1e-9, r=.37958 b1=.90923 b2=.83226 delta=+.01868 H=.69423,
                  eigen = (+0.0565, +1.3560)  =>  local MINIMUM;
      seed 86241: |grad| = 7.9e-11, r=.37615 b1=.91646 b2=.66756 delta=+.16629 H=.50314,
                  eigen = (-2.2704, +2.1860)  =>  SADDLE.
    Both were verified INTERIOR to the lens (H strictly inside the fiber, wedge strictly inside).
    So interior critical points are not rare, but the ones found are not maxima.
(d) No point was found that is BOTH stationary and ND: the ND points have |grad| ~ 0.73, and the
    stationary points have lambda_max > 0.  An interior local max requires exactly that
    combination (grad = 0 AND Hess <= 0), so this diagnostic finds no interior local maximum.

================================================================================
3. WHAT THIS MEANS FOR "BOUNDARY-ONLY FOR ALL BEARINGS"
================================================================================
 * The Laplacian argument (C861/C862) is not the only possible obstruction and cannot be salvaged
   by concavity: ND points exist, so the objective is not concave at every legal point.
 * The viable route is the one the lead named: combine stationarity with the sign structure —
   e.g. minimise |grad F| OVER the ND region (lambda_max <= 0), or minimise
   lambda_max + mu|grad F| for a small mu, and show no stationary point lies in the ND set.  This
   is a 5-parameter search (r,b1,b2,delta,H) whose ND region is pinched by section 1 (L_j <= 0.42
   and sum c/L >= 5.5835), so it is a genuinely small-box obligation, not a global one.
 * Limits, stated plainly: everything here is numeric exploration (400 samples + 4 x (2 seeds x 80)
   DE runs); "no interior maximum found" is not "no interior maximum exists".  The one-sided
   information is the ND existence direction: a certified ND point would rigorously kill the
   positive-eigenvalue hypothesis, and the symmetric witness above is the natural target.

STATUS: diagnostic reported; no claim registered; no certificate implied.


================================================================================
4. CORRECTIONS FROM THE LEAD (applied; see C862c-PINCHED-STATIONARITY.md)
================================================================================
 (i)  The stationarity formula in C862c must include the quadratic gradient:
        grad F = alpha + sum_j 2 beta_j L_j n_j - sum_j c_j n_j + sum_j a_j grad theta_j = 0
      (alpha alone is only the affine part).  The DIAGNOSTICS here were computed by finite
      differences of the full objective, so their |grad| values are unaffected; only the written
      formula was wrong.
 (ii) The mixed entry of the polar-angle Hessian scales as 1/L^2 (times L^2 gives -1); a printed
      "*L = +-1" in the companion note was dimensionally wrong.
 (iii) In the companion note the stationary point with (lambda_min, lambda_max) =
      (-0.0022, +1.4276) is INDEFINITE, not semidefinite; the word was wrong and is withdrawn.
 (iv) The two angle terms have OPPOSITE chirality in the lead's coordinates, so the Hessian used
      in this file (same chirality for both) was that of a neighbouring function; the corrected
      re-run is in C862c.  The DIRECTION of both conclusions (an ND point in the width-legal
      domain exists; the interior stationary points found are not maxima) survives, but the
      numerical eigenvalues in this file are superseded.
 (v)  Interface verified: my Cartesian hub factor equals the code chain's (delta,H) hub part plus
      the absorbed (z3-z1) delta term to 3.7e-16 over 300 points.
