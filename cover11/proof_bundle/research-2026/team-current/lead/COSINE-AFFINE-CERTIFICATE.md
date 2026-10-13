# Whole-arc cosine minorants, exact stress mixing, and scope

For any normalized nonnegative scalar edge weights alpha on the fixed51edge oracle graph, every feasible radius r satisfies r² >= min_free Σalpha_e |Xv−Xw|² = E_alpha(U). With positive weights all free nodes connect to anchors, so the free Laplacian is positive definite. Its exact Schur complement Lambda has zero row sums and offdiagonal entries −w_ij<=0. Therefore E_alpha(U)=Σ_{i<j}w_ij|Ui−Uj|²=Σ2w_ij(1−cos(theta_i−theta_j)). No optimized-alpha linearity is asserted.

For a whole interval [a,b], slope s∈[-1,1], set c_s=min_{z∈[a,b]}(1−cos z−s z). A rigorous lower enclosure of c_s gives a globally valid affine minorant on that interval. Endpoints and BOTH families asin(s)+2kpi and pi−asin(s)+2kpi exhaust possible minima. A short interval is NOT necessarily sin-monotone. Interval overlap tests retain ambiguous roots; extra candidates can only weaken a minimum lower bound. The implementation covers all differences within[-2pi,2pi] by k=-3..3, with guards. Slopes are exact dyadics obtained from numerical proposals; critical trig evaluation is interval.

Take arbitrary rational beta_f>=0,sum beta=1 among exact scalar fields. Define W_ij=Σbeta_f 2w_fij>=0. For each pair choose arbitrary rational gamma_ijs>=0,sum_s gamma=1. Then
V²>=Σ_f beta_f E_f>=Σ_ij W_ij Σ_s gamma_ijs(s(theta_i−theta_j)+c_s).
The last expression is affine in theta and hence in deficit y. On a simplex it is minimized at a vertex. Thus interval evaluation at all9vertices proves a whole-cell bound. Floating LP duals only propose beta/gamma; neither LP feasibility nor LP optimality is a premise. Normalizing the rational proposals exactly preserves all required signs and sums.

## Tested object and gains
`certify_energy_cell.py` constructs exact rational alpha and Schur complements. `certify_cosine_envelope_cell.py` certifies saved adaptive_stellar_pilot node26: V>.38441171006 (formerly squared-range method only .37880740637). `cosine_leaf_pilot.py --full` certifies25 of131 old leaves using45 exact fields. `cosine_tree_pilot.py` extends511cells with longest-y-edge midpoint splitting, replays every old stellar/new midpoint child, and retains617open leaves. No new leaf certified in this extension; no fullP conclusion.

Independent Schur residual and alternative whole-arc Taylor audit is r20-rigidity/cosine_cell_audit.py. Its original draft used c−1e−6 in the Taylor validation but c in vertex evaluation; this mismatch was identified and correction requested. Only the corrected same-intercept chain counts as independent evidence. Lead root enumeration does not use that audit as a mathematical premise.

## Decision diagnostic
`cosine_gap_diagnostic.py` tests3 unresolved cells. Missing stress and relaxation gaps BOTH matter: node69 oldLP .3770459, oldactualenergy .3793920, newly optimized pointoracle .3835886; one new stress only lifts LP to .3771443. Node358 lifts .3796233 to .3803218 after adding stress. Hence do not merely scale longest-edge tree. Next representation: rational pair-partial-sum polytope cells, split the angular difference responsible for concave relaxation loss; certify the final affine bound using rational nonnegative LP duals plus an explicit residual bound on y simplex.
