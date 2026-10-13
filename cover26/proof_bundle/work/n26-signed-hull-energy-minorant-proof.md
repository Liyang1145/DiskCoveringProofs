# Unadmitted signed-curvature hull Taylor lemma

This is an arithmetic extension under development, not a geometry acceptance
or a faster latest-current/source interface. No existing frozen verifier is
modified. Discovery using this lemma pays zero leaves and zero whole roots.

Use the original 92 positive rods, their independently checked grounded
Dirichlet inverse, 16 boundary anchors and 46 free vertices. Let E(theta) be
the original Schur boundary energy. Any actual realization at radius at most
Rstar_upper has E(theta) <= Rstar_upper^2 times the positive weight sum.
This geometry linkage must still be established by the complete original
model and latest-source semantic replay before admission.

Let P be the necessary difference-constraint polytope and Q the target closed
angular box. Choose a rational reference r in P, not necessarily in Q.
For x in P intersect Q, the segment r+t(x-r), 0<=t<=1, stays in P and in
the coordinatewise closed hull of r and Q. Thus the existing exact pairwise
Hessian minorant may be evaluated on this hull intersect P. No Hessian on Q
alone is sufficient if r is outside Q.

For a rational signed diagonal eta, check

    H_rounded + diag(eta) - (15/10^40) I > 0

by exact positive LDL and complete rational reconstruction. The existing
outward pair-cosine bounds and symmetric entry-rounding spectral-error
allowance then imply Hessian E >= -diag(eta) along every such segment.
Taylor's integral remainder gives

    E(x) >= E(r) + grad E(r) dot (x-r)
                     - sum_k eta_k (x_k-r_k)^2 / 2.

Negative eta_k retains positive curvature. It is not a nonnegative
negative-curvature allowance and must not be passed to the old interface.
E(r) is bounded below and each gradient component by exact outward rational
trigonometric intervals. To prevent unbounded denominator growth in squared
stationary-point values, the reference-energy lower endpoint and gradient
lower endpoints are then rounded down to a 10^-80 rational grid, and gradient
upper endpoints rounded up. Exact rational comparisons check each outward
containment and the error less than 10^-80; no rounding loss is omitted.

For each necessary inequality x_j-x_i<=m_ij, choose a nonnegative rational
multiplier mu_ij. With d=x-r, adding

    sum mu_ij * (d_j-d_i - (m_ij-r_j+r_i))

to the Taylor minorant only lowers it on P. The exact constant is
sum mu_ij*(r_j-r_i-m_ij); the exact gradient divergence is negative at i and
positive at j. Minimizing the resulting separable terms over the original
target coordinate intervals, not the larger hull, yields a valid lower bound.

For an interval gradient [g_lo,g_hi] the coordinate term is
min(g_lo*d,g_hi*d)-eta*d^2/2. On d>=0 use g_lo; on d<=0 use g_hi.
If eta>=0, each sign-piece is concave and its minimum is attained at a
piece endpoint. If eta<0, also test the stationary point d=g/eta when it
lies in that sign-piece. Endpoints, zero when included, and these exact
rational stationary points exhaust the minima.

A strictly positive exact energy margin and outward rational radius margin
are necessary for a proposed exclusion. Solver results only suggest
nonnegative multipliers and signed diagonals; every final quantity is
recomputed exactly. Equality never pays.

Before any admission, require arithmetic rejection/positive controls,
complete latest-source/model/ownership reconstruction, retained non-OPEN
history, unchanged original LOCAL allowance, a feasible tiny candidate
positive control, frozen standalone independent acceptance, actual replay,
complete current composition and independent final inventory rehash.
