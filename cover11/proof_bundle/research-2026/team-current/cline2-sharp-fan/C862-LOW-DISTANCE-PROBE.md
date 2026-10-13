# C862-LOW-DISTANCE-PROBE.md — bounded search over the complement d/(2r) < 1.38

Owner: cline2-sharp-fan (own files, own driver).  Exploratory; sampling is NOT a certificate.
Driver tools/probe_low_distance.py -> out/p40_low_distance.log, out/p40_low_distance_probe.json.

================================================================================
1. LOADER FINDING (matters for reuse)
================================================================================
probe_nested_patch.py reaches its objective through check_arc_chart.py -> check_joint_reduced.py,
and the latter loads **joint_patch_frozen_v2.json** (the OLD coefficients), not
joint_nested_frozen.json.  My driver execs the same chain but overrides the exec'd namespace's z
with the CURRENT joint_nested_frozen.json, and verifies the override bites:
   exec-chain reduced() at a fixed chart point: CURRENT z 27.706996098 vs OLD v2 z 27.761340538
   (override effective: True), and the detail path agrees with the summed objective (<1e-8).
No lead file was modified; probe_*.py was reused as a component only (it is __main__-guarded).

================================================================================
2. RESULT — the low-distance complement is NOT far below the threshold
================================================================================
Two DE runs (seeds 8620/8621, popsize 12, maxiter 80, polish, init sobol, ~5400 evaluations each)
over the chart box r in [.375,.38], q1,q2,qA in (0,1), restricted to **d/(2r) < 1.38** with all
legality filters (H-fiber nonempty, width fibers >= g):
  seed 8620: value 28.104237696621  r=.37999925 b1=.847522 b2=.838669 A=1.538698 delta=-.691176
             H=.521025 w1=.544618 w3=.530720 d/(2r)=1.115135
  seed 8621: value 28.104240583963  r=.37999981 b1=.836817 b2=.847269 A=.145509 delta=+.691307
             H=.521232 w1=.527760 w3=.544230 d/(2r)=1.113042
  **BEST in complement = 28.104240583963**, gap to the threshold 28.107045 = **0.002804416**.
So the answer to the operational question is: the complement is NOT far below the threshold — it
lands within 0.0028 of it, i.e. the low-distance branch is essentially tied with the boundary
region and CANNOT be discarded by a crude bound; it must be carried (or coupled) in whatever the
next certificate does.
Structure of the optima (both seeds): r pinned at the top of the range (.380), b1,b2 ~ .837-.847
(LOW bearings, i.e. outside the C861/C862 high-bearing/high-distance region), delta ~ +-0.691
(so A and B are strongly asymmetric: .145 and 1.539 in the two mirror cases), H at the TOP of its
fiber (H_argmax_is_hi = true) with the fiber nearly degenerate, and the binding constraints are
the corresponding face disk (residual 0 / 2.8e-17) and the hub-norm disk (residual -1.9e-6 /
-3.9e-9); the wedge margins are strictly positive (.1455) and both width margins ~0.48.  The two
seeds found the mirror pair (delta -> -delta with b1 <-> b2), which is the expected symmetry of
the objective's face structure and is a consistency check on the search, not extra information.

================================================================================
3. WHAT I ALSO CHECKED IN THE EXTENSION ITSELF (lead/HUB-BOUNDARY-ASYMMETRIC-EXTENSION.md)
================================================================================
 * the distance bound d >= 2r(sin^2 b1 + sin^2 b2) holds with EQUALITY at b1 = b2 (checked
   numerically; e.g. b1=b2=1.1 gives d/(2r) = 1.5884 vs S+S' = 1.5885), and the clean form
   d/(2r) = sqrt(1 + cos^2 T - 2 cos T cos D) with T=b1+b2, D=b1-b2 reproduces it;
 * the wedge exclusion identity is EXACT: with x0 = 2b_j - acos(r),
   |c_j|^2 - (1-r)^2 = 2r[1 - cos x0], because cos x0 = sin(2b_j + asin r) = 2s sinb_j cosb_j +
   r(cos^2 b_j - sin^2 b_j) (verified symbolically against |c_j|^2 = s^2 + D_j^2 - 2sD_j cos b_j).
   Legal positive width gives b_j > acos(r)/2, so x0 in (0, acos r] subset (0,pi) and the
   difference is strictly positive: the wedge-edge exclusion indeed extends beyond b_j >= 1;
 * the uniform Delta bound: 4(beta1+beta2) - (4/3) max((50/19)c1 + c2, c1 + (50/19)c2)
   = 5.583507299 - 5.5358956 = 0.047611 (using d - u >= (19/50)(2r) and 1/(2r) <= 4/3),
   matching the note's 0.04761102216066.  Correct.

================================================================================
4. LIMITS
================================================================================
 * The search optimises the FIXED-coefficient 7-factor patch objective on the local chart; it is
   not an upper certificate, and "we did not find more" is not a bound (no sampling -> certificate).
 * Only 2 seeds x 80 DE iterations were run, as specified; the near-tie with the threshold is
   robust across both seeds and both mirror branches, but a larger budget could only raise the
   complement value, never lower it, so the conclusion "not far below" is one-sided safe.
 * The optima are boundary points in several constraints at once (face disk and hub norm nearly
   binding, H-fiber collapsing), so any follow-up bound for this branch must handle the
   degenerate-fiber interface, not assume a positive-width interior optimum.

STATUS: exploratory result reported; no claim registered; no certificate implied.
