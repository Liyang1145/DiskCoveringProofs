# cline2-coupled-factors — CORRECTION / RETRACTION (round 4)

## Retracted: "u_k = v_k identically"

**Status: RETRACTED. The claim is false in general. The lead's objection is correct.**

What I asserted (f12/f13/f15): for ring sector k with switches P_{k-1}, P_k, the site c_k
is equidistant from both, hence u_k = |P_{k-1}-c_k|/R and v_k = |P_k-c_k|/R coincide.

Why it fails. The C816 endpoint copies are

    v_k = sigma_k / R      (the switch radius at P_k, i.e. the distance from P_k to its
                            nearest site among c_k, c_{k+1})
    u_k = sigma_{k-1} / R  (the switch radius at P_{k-1}),

so u_k compares TWO DIFFERENT SWITCHES. What the geometry actually gives is the mirror
statement:

    P_k is equidistant from the two SITES c_k and c_{k+1}   (a property of one switch),

NOT

    c_k is equidistant from the two SWITCHES P_{k-1} and P_k  (what I asserted).

The two are different constraints: my "proof" silently used |P-c| = |Q-c| for the two
switches P = P_{k-1}, Q = P_k, which holds only when the two switch radii agree. On the
saved certified candidate they do agree because all nine switches are saturated
(sigma_k = R for every k, 3e-16), so u = v = 1 there — that is a *saturation coincidence*,
not a structural identity. The lead is building a strict-cover tiny perturbation as an
explicit counterexample (certified Lipschitz coverage).

Consequences for my own artefacts (all superseded, do not cite):
* f12_identity.py — the theorem statement and its "perpendicular-bisector" proof: WRONG.
  What is true in that script is only the chart fact: if one *parametrizes* the diagram by
  the switch angles theta and then places c_k at distance r from both P_{k-1}, P_k, then
  u = v holds for every theta (that is a property of that one-parameter construction, in
  which both switch radii are forced equal to r).
* f13_diagonal.py — the "diagonal u = v" and "saturated u = v = 1" restrictions are NOT
  validity-preserving. Their numbers (3.175795871, 3.175773185 for span 4) are
  conditional slices only. Do not use them as bounds.
* f15_argmax.py — the "proved-legal diagonal" column: same defect; only its `full` column
  is meaningful (it reproduces the lead's 3.175702558, as independently verified in
  f3/f4).
* The earlier draft identity S(alpha,1) = R^2 alpha/2 + (w - sin w)/2 was already dropped
  in f14 (the correct diagonal form is R^2(alpha - sin alpha)/2 + (w - sin w)/2); it is
  doubly dead now.

## What survives (independent of the retraction)

1. **Verified assembly** (f3_lead_repro.py, f4_feasible_dual.py): a from-scratch
   reconstruction of lead/q0_closure_dual.py reproduces `sample_upper = 3.175702557547944`
   for span 4 exactly (0.0e+00 difference), with per-factor values
   face total 5.160601204, switch total 0.091959701, ring total 3.538682786,
   const.z = -5.615541133, sum = 3.175702558. The same code reproduces span 3's
   proposer output 3.065792961. This is the calibration the coupled-factor work needs.

2. **Realized angle diagram of the sharp point** (f7c/f8/f16): reconstructed from the
   integer coordinates `centers_scaled_1e17/1e17`, R_cert = .379983853119838733.
   Slot map (slot -> ring site): [4, 9, 10, 3, 5, 7, 1, 8, 6].
   * closure residual  T_k + L_{k+1} + 2 b_k + (w_k + w_{k+1})/2 - pi : max 8.9e-16
   * width sum - 2pi : 0.0 ; endpoint copies max|u-1| = max|v-1| = 3.3e-16 (saturated)
   * switch cap: min (pi/2 - b_k) = 0.520117984
   * exactly 9 faces have circumradius = R_cert; the two hub-hub-ring triangles
     (0,2,5) and (0,2,6) have rho/R-1 = -1.1e-16, -3.3e-16, the other two
     (0,3,10), (0,4,9) are rho/R-1 = -3.03e-3.
   Note the two faces the lead flagged with radii ~.9969665 are NOT present here: this
   object's nine tight faces are all at rho = R exactly, x = 1.000000000.

3. **Headroom at the sharp point** (f9_slack.py, f16_decomp.py): evaluating the lead's
   bound form at this single realization gives
       const.z0 + sum_f (row value) = 3.141837726 = pi + 2.451e-4.
   Since every factor's max dominates its realized value,
       ub(z0) - pi = 0.0341100  =  2.451e-4 (forced dual slack) + 0.0338649 (recoverable).
   So at this point the whole architecture has at most 0.0339 of slack left to reclaim,
   and the lead's best reported value (3.169315) still sits 0.027722 above pi.
   This is the honest budget for any sharper coupling.

4. **First-moment block is a brake, not a strengthening** (f4/f5/f11/f17): opening the
   linear-in-sqrt(x) adjoint rows admits directions along which the bound decreases:
   |L| <= 0.25, 0.5, 1.0, 2.0 give 3.1325, 3.1065, 3.0630, 2.9631 (bounded runs all
   converge), and a uniform offset eps at the fixed feasible z0 gives
   3.175702558 (eps=0), 3.230249371 (eps=.01), 3.599519302 (eps=.05), 4.264100977 (.1),
   i.e. the LP moves *away* from the useful region. Mechanically: a first-moment row
   carries coefficient +-sin A, which within the triangular factor is bounded by 1 while
   the multiplier is free, so the coupled LP is driven by the free multiplier rather than
   by the geometry — structurally different from the squared row, whose coefficient
   x sin^2 A is *exactly* maximized over x in [0,1] and therefore cannot be inflated
   independently of the angle. A first-moment refinement of this dual family is therefore
   not a promising direction; the squared (second-moment) adjoint is the strong one.

5. **The lead's own sector center-norm filter (3.169315) and switch cap (3.17838) are the
   current best reported; both remain above pi.** My diagonal experiments supply no
   evidence against them and no improvement.

## Next step (corrected direction, per lead instruction)

Actual higher-moment matching, staying away from the retracted diagonal:
the exact edge identity is d_e^2/4 = R^2 x_f sin^2 A = R^2 x_g sin^2 B with the SAME
edge length, so the natural next adjoint is the product / mixed row
    (x_f sin A)(x_g sin B) = (d_e/2R)^2,
whose dual coupling condition is  lam_f + lam_g <= 0 with the one-sided multipliers
respected. A bounded LP test on the saved z0 decides whether that direction has any
grip; f20_moment2.py runs exactly that experiment.
