# Exact elimination of real-face radii: fixed-angle Dirichlet existence

This is a circle-pattern Dirichlet theorem in this problem's angle convention, not a new global covering bound. It complements LOG-RADIUS-LAPLACIAN.md and makes the existence condition explicit rather than assuming a nonlinear solver succeeds.

## Data
Finite connected real-face network F, each edge either joins two distinct faces or a face to a fixed boundary anchor. At least one anchor edge; beta_e in(0,pi), c_e=pi−beta_e>0; all prescribed anchor radii a_e>0. For face f set l_f=log R_f and
 h_fg=atan2(exp(l_g)sin beta_e, exp(l_f)−exp(l_g)cos beta_e).
For anchor edges l_g=log a_e. Then h_fg in(0,c_e), h_fg+h_gf=c_e for an internal edge. Seek sum_incident h_fg=pi at each real face (triangular-face equation). Parallel edges, if any, are counted with multiplicity.

For nonempty S subset F let I(S)=sum c_e over edges with both ends in S; B(S)=sum c_e over edges with exactly one face in S (including anchor edges). The necessary and sufficient condition for a positive solution is
 **I(S) < pi |S| < I(S)+B(S), for every nonempty S subset F.**
When it exists the solution is unique, for EVERY assignment of positive anchor radii. The radius caps R_f<=U remain additional constraints, not implied by existence.

## Necessity
Sum the face equations over S. Internal edges contribute exactly c_e, crossing/anchor edges contribute strictly between0 and c_e. B(S)>0 follows connectivity to the boundary. This proves both strict inequalities.

## Sufficiency by coercivity of the convex energy
Let G_f=pi−sum h_fg. Its Jacobian is a weighted Dirichlet graph Laplacian with positive weights w_e=sin(beta_e)/[2(cosh(l_f−l_g)−cos beta_e)], hence symmetric positive definite. On R^F it is the gradient of a C2 strictly convex energy E.

One can choose an internal-edge energy Phi_e(l_f,l_g) with derivatives(-h_fg,-h_gf). It differs by a bounded quantity (constant depending only on beta) from **−c_e min(l_f,l_g)**. To see this, write d=l_f−l_g and Phi=−c_e l_g+phi(d), phi'=-h(d). For d→+infty, h(d)→0 exponentially, so phi tends to a finite constant; for d→−infty, h(d)→c_e exponentially, so phi(d)+c_e d tends to a finite constant. Both remainders are bounded on the remaining compact interval. An anchor-edge energy similarly differs boundedly from −c_e min(l_f,l_anchor); replacing min(l_f,l_anchor) by min(l_f,0) changes it by at most |l_anchor|.

Therefore E(l), up to a uniformly bounded function, equals the positively homogeneous piecewise-linear function
 P(l)=pi sum_f l_f −sum_internal c_e min(l_f,l_g) −sum_anchor c_e min(l_f,0).

Let S_t^+={f:l_f>t}, S_t^-={f:l_f<−t}, t>=0. Decomposing each minimum into positive and negative layers gives the exact identity
 P(l)= integral_0^infty [pi |S_t^+|−I(S_t^+)] dt
      +integral_0^infty [I(S_t^-)+B(S_t^-)−pi |S_t^-|] dt.
Check signs: an internal edge's positive minimum contributes when BOTH endpoints exceed t; its negative minimum contributes minus when AT LEAST ONE endpoint is below−t. An anchor at log0 never contributes a positive minimum and contributes a negative minimum exactly when its real endpoint is below−t.

There are finitely many nonempty subsets, so under the strict cut inequalities their two margins have positive minimum eta. The two layer integrals imply P(l)>=eta(max_f l_f^+ +max_f(-l_f)^+)>=eta||l||infty. Thus E is coercive, attains a minimum in R^F, and G=0 there. Strict convexity gives uniqueness.

## Structural payoff and limits
The positive real radii can be eliminated as a UNIQUE function of beta and positive boundary radii on an explicitly described open polytope of beta. The Jacobian is invertible, hence the solution is analytic locally, and monotone in anchor radii by the comparison principle. This removes nonlinear root multiplicity/existence as a bearing assumption; it does NOT eliminate beta variables, enforce radius caps, or enforce unit-boundary closure.

At a cut equality no finite positive solution exists: connectivity to an anchor makes B(S)>0 and every crossing contribution lies strictly between0 and c_e. Approaching such equalities can force log radius sequences to diverge. Do not use the theorem for beta endpoints0,pi or zero anchor radii without a separate limit analysis. The finite inequalities are exponential in face count; a coherent-angle flow feasibility formulation/min-cut separation can test them, but prior coherent-angle probes found no extra exclusions on their tested graphs. The benefit here is exact parameterization, not a new catalogue pruning claim.

Relation to literature: Bobenko–Springborn (2004) convex Euclidean circle-pattern functionals and coherent angles. This elementary proof is written in our paired-beta convention to avoid silently importing the wrong interior/exterior angle convention.
