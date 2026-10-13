# Exact Dirichlet energy exclusion of current candidate angle boxes

Only current, independently reconstructed OPEN leaves can receive these
radius-at-most-Rstar conditional payments. All old source nodes, paid leaves,
closed split boundaries, and unvisited OPEN boxes are preserved unchanged.

The existing accepted positive rod graph has 16 boundary anchors and 46 free
vertices (26 centers and 20 interior face witnesses). Each of its 92 rods has
length at most the cover radius. Its strictly positive rational weights are
copied unchanged from the same-root reference pinning certificate. Therefore
the total rod energy is at most Rstar_upper^2 times the sum of weights.

Write its weighted Laplacian in anchor/free blocks. Positivity of all weights,
and an explicit path from each free vertex to a grounded anchor, imply the
ground block is positive definite: its quadratic form is a positive sum of
squared edge differences and vanishes only at the zero grounded displacement.
The checker verifies every entry of an integer common-denominator inverse
identity. It derives the harmonic extension H and Schur matrix S itself.
All harmonic coefficients are checked nonnegative with row sum one, and S is
checked symmetric with zero row sums and nonpositive off-diagonals.

Completing the square gives, for both Cartesian coordinates independently,

E(a,x) = a^T S a + (x-Ha)^T L_free (x-Ha) >= a^T S a.

An independent exact two-coordinate rational control recomputes this identity
directly. For unit circle anchors, the boundary energy is exactly

2 sum_{i<j} (-S_ij) (1-cos(2*pi*(theta_j-theta_i))).

On a whole closed angle box, each theta is its rational midpoint plus a
deviation of absolute size at most an outward rounded halfwidth. The checker
computes midpoint cosine energy and the *summed* signed sine gradients by
exact rational interval arithmetic, retaining all cancellation. The absolute
second derivative of each pair contribution is at most 8*pi^2*(-S_ij).
Thus a rigorous lower bound subtracts the absolute midpoint gradient times
each halfwidth and the full Taylor remainder
4*pi_upper^2 sum (-S_ij)(halfwidth_i+halfwidth_j)^2.
No convexity of the angular energy is assumed.

A leaf is paid only when this whole-box boundary energy lower bound is
strictly above the same-root upper rod energy. Such a cover is impossible
anywhere in that closed leaf. The known exact candidate tiny box must not be
excluded, and remains in its original LOCAL leaf.

The symbolic inverse generator and numerical exploratory estimates are not
used by the standalone standard-library checker. These payments do not prove
global optimality or alter the original 7/800000 local allowance. They do not
assert emptiness at the larger screening threshold U.
