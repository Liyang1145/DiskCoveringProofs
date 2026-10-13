# Full-type quadratic energy payments with negative curvature

The input is an actually accepted full-canonical-type registry and its matching
published standalone replay. Catalogue vertex bijections, all face images,
the exact same covering root and sharp cap margins are reconstructed.
For every type touched by the overlay, the complete previous force tree and
its closed OPEN boxes are semantically replayed, including an independent
BFS closed partition and independent necessary difference matrix.
Other unchanged complete type proofs remain bound to their actual old replay;
they are not claimed to be rerun.

For a specified full canonical rod graph, every edge has length at most the
cover radius. Strictly positive rational weights may be chosen arbitrarily:
the numerical generator's stationarity and local minimum are not hypotheses.
The entire graph, including every introduced center and face witness, is used.
Its energy is at most radius_upper^2 times the sum of weights.

The grounded Laplacian is positive definite because all weights are positive
and each free vertex has a graph path to a boundary anchor. The checker
verifies every entry of an integer common-denominator inverse identity.
It derives the harmonic extension and symmetric Schur matrix, checks their
row sums and signs, and independently recomputes the two-coordinate identity

E(a,x) = a^T S a + (x-Ha)^T L_free (x-Ha) >= a^T S a.

For unit-circle anchors, boundary energy is
2 sum_{i<j} w_ij (1-cos(2*pi*(theta_j-theta_i))), w_ij=-S_ij>=0.
Its Hessian pair contribution is
8*pi^2*w_ij*cos(2*pi*(theta_j-theta_i))*v_ij*v_ij^T.
The exact cosine minimum is found from endpoints and any half-integer minimum
over the intersection of the closed box and the necessary difference bounds.
Positive cosine minima use pi_lower^2; negative minima use pi_upper^2.
Summing these contributions yields a Loewner Hessian minorant.

To keep rational elimination modest, each symmetric entry is rounded down to
a grid of denominator10^40. The exact entrywise error is below1/grid.
Its symmetric operator norm is at most dimension/grid. The checker verifies
an exact positive LDL decomposition, and every reconstructed entry, of
H_rounded + D - (dimension/grid)*I for the proposed nonnegative diagonal D.
Therefore throughout the convex box/difference domain, Hessian(E)>=-D.
No convexity of E itself is assumed.

An exact rational reference point is required inside every closed box bound
and every necessary difference constraint. Taylor's integral remainder gives

E(theta) >= E(ref)+g(ref) dot delta - sum D_k*delta_k^2/2.

All midpoint/reference trigonometric and gradient intervals are recomputed
with exact rational interval arithmetic. One option subtracts the entire
maximum squared coordinate displacement. A sharper option uses the exact
closed-interval secant inequality, for delta_k in[a_k,b_k],

delta_k^2 <= (a_k+b_k)*delta_k-a_k*b_k.

The corresponding shifted gradient and constant are both charged exactly.
For any exact nonnegative difference multipliers mu_ij, writing
c_k=incoming_mu-outgoing_mu yields a further valid lower support:

g dot delta >= sum mu_ij*(ref_j-ref_i-M_ij)
             +sum min((g_k+c_k interval)*(a_k,b_k)).

The reference is feasible, every multiplier is nonnegative, and every gradient
interval residual is charged. No LP objective or floating eigenvalue is used
as proof. A payment requires this whole-box energy lower bound to be strictly
above the same-root upper rod energy. An exact downward square-root conversion,
checked by both bounding squares, supplies a strict radius margin in the same
units as earlier force payments.

Source trees remain byte-identical. Only actually reconstructed OPEN boxes
are paid in a separate overlay; all untouched or unpayable boxes are retained.
A full type is removed only when every old OPEN is paid and every prior
non-OPEN proof remains bound. Terminal transfers use the complete canonical
spec and all explicit member bijections, never a partial ancestor.
All isomorphic candidate paths are retained.

Independent rational energy identities, exact LDL and secant controls, and a
known feasible rod placement (unit-circle anchors, all free points zero,
radius one) are positive controls. Mutation controls reject changed inverses,
missing rods, nonpositive weights, wrong references, negative curvature
allowances or duals, repeated/unreachable payments, partial specifications,
indefinite LDL claims, and promotion of Rstar-conditional proofs to U.

This certifies only the stated necessary full-type boxes at radius<=Rstar.
Complete n26 enumeration, final unrestricted reduction and global optimality
remain separate unfinished obligations.
