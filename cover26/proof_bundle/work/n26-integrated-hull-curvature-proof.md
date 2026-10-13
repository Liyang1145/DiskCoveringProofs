# Experimental integrated Taylor curvature lemma

This is not a candidate acceptance interface. All original model and current
source/ownership replay obligations remain necessary. No old frozen geometry
module is modified.

Let r be an exact feasible reference in the original necessary difference
polytope P and Q the actual closed target box. For every x in P intersect Q,
the whole segment y(t)=r+t(x-r), 0<=t<=1, belongs to P by convexity.
On each closed t strip [a,b], the exact coordinate box whose endpoints are
the minimum and maximum of r_k+t(z_k-r_k), for t in {a,b} and
z_k in {Q.lower_k,Q.upper_k}, contains every y(t) on that strip.

Apply the existing exact pair-cosine Hessian minorant to this strip box and
the unchanged necessary difference matrix. Before rational entry rounding,
its matrix H_s is a Loewner minorant of the actual Hessian everywhere on
that strip. The original symmetric entry rounding error has operator norm
less than or equal to 15/10^40.

The closed strips cover [0,1] with shared t endpoints. Their normalized
Taylor weights are

    w_s = integral_[a,b] 2(1-t) dt = 2(b-a) - (b^2-a^2).

These weights are positive rational numbers with exact sum one. Thus the
weighted rounded matrix M=sum_s w_s H_s has the SAME 15/10^40 rounding
operator allowance, not an uncharged collection of rounding losses.

Exact LDL with full rational reconstruction of

    M + diag(eta) - (15/10^40) I > 0

implies

    integral_0^1 (1-t) Hessian E(y(t)) dt >= -diag(eta)/2.

Taylor's integral identity therefore gives the same signed-quadratic
minorant E(x)>=E(r)+grad E(r).(x-r)-sum eta_k(x_k-r_k)^2/2.
It need not bound the Hessian at every segment point by one constant matrix;
late-segment negative curvature is charged with its true smaller Taylor
weight. Floating spectra only propose diagonals; only the fresh exact matrix
test certifies an arithmetic curvature inequality.

To use this for geometry, still require exact reference energy and gradient
intervals, full target-domain signed-quadratic support/dual minimization,
strict same-root energy and radius margins, complete closed coverage and
original LOCAL positive controls, a distinct own-executor frozen verifier,
full original-model/latest-source/history replay, actual publication replay,
complete current admission and independent final rehash. The current
supplemental signed-hull verifier does NOT accept this new mode.
