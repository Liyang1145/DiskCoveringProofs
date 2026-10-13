# Signed angular curvature gives a simplex vertex certificate

Use an EXACT dual-feasible vector field p on the fixed51 graph, and its anchor loads l_i. Unit: radius V, not energy V². For any anchors, V(U)>=f(theta)=sum_i l_i·(cos theta_i,sin theta_i). Coordinates theta are affine functions of widths; theta0 is fixed. No geometric primal condition enters this bound.

Let a cell be the convex hull of finitely many angle vectors v^j. Let [a_i,b_i] contain its i-th coordinate range, and choose kappa_i>=max_{t∈[a_i,b_i]}(0,−l_i·U(t)). The Hessian of f is diagonal with entry −l_i·U(theta_i), so
h(theta)=f(theta)−(1/2)sum_i kappa_i theta_i²
is concave on the whole containing box, hence on the cell. For theta=sum_j lambda_j v^j,
f(theta)>=sum_j lambda_j f(v^j)−(1/2)sum_i kappa_i Var_lambda(v_i).
Since any distribution on [a_i,b_i] has variance <=(b_i−a_i)²/4 (expand E[(X−a)(b−X)]>=0 and maximize (mean−a)(b−mean)),
min_cell V >= min_j f(v^j)−sum_i kappa_i(b_i−a_i)²/8.
In particular if l_i·U(theta_i)>=0 on every coordinate interval, kappa=0 and the vertex minimum suffices with NO Taylor penalty. Cartesian convexity is not used; it is angular concavity of this fixed support function. Minima of the ORACLE V itself are not claimed to be at vertices.

## Exact domain parametrization
L=2asin(19/50), D=9L−2pi>0. Let y≥0,sum y=1 and set Delta_i=L−D*y_i. Then Delta_i∈[2pi−8L,L] and sumDelta=2pi: all P is this one8-simplex. Fix theta0=0, theta_i=sum_{j<i}Delta_j for i1..8. A simplex cell in y maps affinely to angle space. Bisection at an edge midpoint replaces one endpoint by that midpoint in each of two children; union exactly equals parent, intersection is common facet. Exact dyadic y vertices permit append-only tree verification with no approximate coverage test. L,pi enter only via outward interval evaluation.

## Scope
This supplies a verifiable cell lower bound, not global completion. A bounded pilot may leave cells unresolved; failed lower certificate is not a primal counterexample. C912 is a separate candidate-local patch and will require an explicit containment test with raw/canonical chart mapping before it can close any leaves.
