# n12 structure member — durable note (research-2026/n12-global/members/structure/)

Owner: structure member. Scope: k=11 / k=10 exclusion at the fixed radius
U = 0.361102963744508672616920293904, and the coupled hub/ring structure.
All files here are my own; the shared STATUS/claims were not modified.

## 1. Rigorous statements (independent of any candidate)

Notation. D = unit disc; r ≤ U < 1/2; 12 discs of radius r. A disc is
boundary-active if it meets S^1. k = number of boundary-active discs,
m = 12-k hubs (non-active). `FOUNDATIONS.md` (lead) gives k ∈ {9,10,11} and
that every hub has centre norm < 1-r, so hubs never meet S^1; every point of
B(0,1-2r) is farther than r from every boundary-active centre, so the hubs
cover B(0,1-2r).

(S1) PER-RAY HUB END. Parameters: hub centre h, e=|h|, beta = signed angle
measured from the BACKWARD ray w = -h/|h| (beta=0 at the back). The hub covers,
along the ray beta, exactly [0, R(beta)] with
    R(beta) = -e cos beta + sqrt(r^2 - e^2 sin^2 beta) > 0
(it meets every ray since e < r). The ring must reach down to R(beta) on every
ray (closedness of the union of the finitely many closed discs).

(S2) REACH CRITERION. A ring disc of norm t whose centre direction is at
angular distance d from the ray beta reaches down to R(beta) iff
    t sin d <= r  and ( R(beta) sin d > r  or  t <= f(R(beta), d) ),
    f(R,d) = R cos d + sqrt(r^2 - R^2 sin^2 d),
f(R,0)=R+r and f is strictly decreasing in d. If R(beta) <= r the escape
clause R sin d > r is impossible, and then
    t <= f(R(beta),d) <= R(beta)+r,
so the disc reaching down at beta satisfies, with alpha(t) the S^1 arc
half-width,
    alpha <= A(beta) := alpha(min(sqrt(1-r^2), R(beta)+r)).
Moreover  f(R,d) >= 1-r  <=>  d <= dmax(R),  so its centre lies in the arc
[beta - dmax(R(beta)), beta + dmax(R(beta))] (inflate dmax outward to keep it
an upper bound!).

(S3) COUNTING LEMMA. Pick beta_1..beta_M with pairwise disjoint arcs
I_m = [beta_m ± dmax_up(beta_m)] inside {R(beta) <= r}. Then the M serving
discs are DISTINCT, hence
    sum_{i=1..11} alpha_i <= sum_m A(beta_m) + (11-M) asin r .
The 11 arcs on S^1 must cover S^1, so sum alpha_i >= pi; a bound below pi
therefore excludes k=11 at radius r.

(S4) BACK-RAY RIGIDITY (extreme eccentricity). If e = 3r-1 exactly, then
f(r-e, d) <= f(r-e, 0) = 2r-e = 1-r with equality only at d=0, and t>=1-r, so
the disc serving the reach condition at beta=0 must have t = 1-r exactly and
its centre exactly on the backward ray. That disc's S^1 arc is a single point
(alpha(1-r) = 0), so the other ten discs must cover S^1 almost alone.

## 2. Numeric-only statements (NOT lemmas; flagged after lead review)

(N1) CAPACITY/JENSEN screen. Deep discs (|c-h| <= 2r) carry the hub-boundary
circle S(h,r) (arc half-widths B_i, sum B_i >= pi); writing s_i = 2r cos B_i
and t_i <= s_i + e gives alpha_i <= h_e(B_i) = alpha(2r cos B_i + e). If h_e is
concave, Jensen gives sum alpha_i <= n h_e(pi/n) + (11-n) asin r for each
admissible n >= pi/B_max. h_e'' < 0 was CHECKED NUMERICALLY only (-0.37..-0.90
over the e-range); the lead correctly rejects this as a lemma, so N1 is a
screen, not a proof.

(N2) Values of the two screens at r = U (degrees; contradiction needs < 180):
  e:        0      0.01   0.02   0.025  0.03   0.035  0.04   0.05   0.06   0.07   0.075  0.08   3U-1
  capacity max_n: 145.7 156.2 165.4 169.5 173.4 177.0 180.4 186.8 192.5 197.7 200.1 202.3 203.8
  counting min_M: 199.5 209.2 207.6 206.7 205.7 204.6 203.4 190.0 184.9 172.3 166.2 138.8  42.7
So capacity covers e<=0.035, counting covers e>=0.07, and e in [0.04,0.065]
is a genuine gap for the two screens (scripts count_lb.py, bounds2.py,
counting_final.py; logs in this directory).

(N3) FAMILY OPTIMA (numeric, coarse-to-fine; NOT global lower bounds):
uniform 11-ring + centred hub attains R ≈ 0.37303 at t ≈ 0.715 (fine grid
400x1440); hub-eccentric families are worse (≈0.3776 at e≈0.017). The C182
configuration (9 ring + 3 hubs) has R_max ≈ 0.36092 on the same grid.
Scripts kfeas.py, probe11.py.

## 3. Dual / Fourier route and hand-off to the lead kernel

The two necessary circle conditions (ring covers S^1; ring covers
|x-h| = U+eps, eps->0, which the hub misses) give, for every NONNEGATIVE weight
function w on either circle, a row functional = (1/2)*arc integral of w over
that disc's arc. Dual LP (few variables):
    maximise pi*sum_r w_r  s.t.  sum_r w_r A[r,p] <= 1 for all centres p,
and a radius-U k=11 cover implies pi*sum(w) <= 11*sup_p sum_r w_r A[r,p].

With K=1 Fourier rows the nonnegativity condition is a >= sqrt(b^2+c^2) for the
aggregate (a,b,c) per circle, and the folded functional is exactly
    F = wb0*alpha + sin(alpha)(wb1 cos phi + wb2 sin phi)
      + wh0*beta  + sin(beta)(wh1 cos psi + wh2 sin psi).
Files: onehub-dual/onehub_dual_U.py (single point calibration e=0.04),
segment_U.py + segment_U_K1.json (12 e-segments of [0,3U-1]; each segment's
target pi*sum(w)/11 in 1.1244..1.1462, numeric sup over the segment in
1.0021..1.0199 -> numeric margins 0.12..0.14), weights_exact.py +
weights_K1_exact.json (exact rational weights per segment), scan_U.py (controls:
negative control at R=0.3734,e=0 gives bound/11 = 0.9887 < 1, so the instrument
is not vacuously excluding; positive control R=U,e=0 gives 1.146 > 1).

Lead's interval kernel `lead/onehub_interval_certificate.py` (mpmath.iv, exact
rational U and grid) replaces my numpy interval attempt, which was found
unsound in review (reversed argument order in iacos, sign handling in the
products, np.nextafter reliance); its certification labels were withdrawn.
My independent read-only controls on the lead kernel
(`onehub-dual/control_lead_kernel.py`) pass on all 12 segments:
  * aggregate rows rebuilt independently == lead.aggregate (exact Fractions);
  * nonnegativity a^2 >= b^2 + c^2 holds per circle and segment;
  * at degenerate point boxes the kernel's upper bound exceeds an independently
    40-digit pointwise evaluation, slack ≈ 5e-30 (i.e. equality up to rounding);
  * interval width at a point ≈ 1e-29 (no over-widening).
Weight-representation note: the lead kernel rounds row weights to 9 decimals
while weights_K1_exact.json keeps limit_denominator(1e9) rationals; per-weight
difference <= 4.7e-10, irrelevant against the ~0.12 margins, but a single
canonical set should be fixed before the certificate is registered.

## 4. Retractions and corrections (kept deliberately)

(R1) Earlier claim in this session of "exact tiling / rigidity" of the C182
configuration was a NUMERIC observation (arc sum 360.000° at 17-digit input);
the exact-rational input does not by itself prove exact tiling. Downgraded to
numeric. (Arc data: 3 arcs of 36.436356° + 6 of 41.781822°.)
(R2) comb_lb.py's combined bound used B_i <= arccos((t_m-e)/(2r)) from
t_i <= t_m, which is backwards (a smaller t gives a LARGER hub-boundary arc);
that combined bound was withdrawn and is not load-bearing. (Lead's catch.)
(R3) My numpy interval certifier (certify_U2.py / certify_segments.py) is not a
certificate: argument-order and sign errors plus reliance on np.nextafter; the
"EXCLUDES" verdicts printed by those scripts are withdrawn.
(R4) The reach-counting packer originally used a grid lower bound for dmax,
which weakens the disjointness conclusion; counting_final.py inflates dmax
outward instead.

## 5. Status and gaps

* Proved here (elementary, unconditional): S1, S2, S3 (with outward dmax), S4,
  plus the k=11 reduction facts quoted from FOUNDATIONS.
* Not proved here: exclusion of k=11 at r ≤ U for all e, exclusion of k=10 at
  all; the capacity/Jensen screen (N1) and both screens' numbers (N2) are
  numeric only; no claim about optimality or the value of r_D(12).
* The k=11 exclusion at radius U is, at the time of writing, resting on the
  lead's interval kernel for 12 e-segments (my controls pass; independent
  certification still outstanding), combined with the interface
  "enlarge r ≤ U to U, recount k, then inner-root" (lead's FIXED-U document).
* Next executable step (for whoever picks this up): run the lead kernel on the
  whole e-range with one canonical rational weight set, then repeat the same
  instrument for the k=10 branch using the separated-hub reduction.
