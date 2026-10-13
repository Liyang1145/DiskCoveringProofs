# Pairwise closed-domain affine minorants

This is a necessary-model arithmetic lemma, not current geometry admission,
unrestricted covering reduction, a complete forest cover or optimality.

For an actually checked positive full134rod Schur kernel, divide its boundary
energy by the positive total rod weight W. The result is
sum c_ij f(theta_j-theta_i), where c_ij>0 and
f(x)=2(1-cos(2*pi*x)). The exact energy cap is rho^2.
Intersect each pair difference with BOTH its entire closed coordinate box
and the exact necessary difference matrix. No feasible difference is removed.

On a closed interval [a,b], f''=8*pi^2*cos(2*pi*x).
The exact trigonometric endpoint/extremum bounds and sign-dependent outward
pi endpoint give a rational H with f''>=H throughout the interval.

For any c in [a,b], outward values f(c)>=v and f'(c) in [g0,g1] give
f(x)>=v+g*(x-c)-epsilon+H*(x-c)^2/2, with
g=(g0+g1)/2 and epsilon=(g1-g0)/2*max(c-a,b-c).
This follows from the integral Taylor remainder; its integration weight is
nonnegative for either direction from c.

If H>=0, dropping the quadratic gives a valid affine minorant.
If H<0, (x-a)(x-b)<=0 implies
(x-c)^2 <= (a+b-2*c)*x+c^2-a*b.
Multiplication by H/2 reverses that inequality, yielding the implemented
affine slope and constant. Shared boundaries and endpoints remain included.
On a wholly concave interval, the chord through outward LOWER endpoint values
is also a valid minorant. A degenerate interval uses its single outward value.

Each of five references gives a WHOLE-interval minorant. ANY nonnegative
exactly normalized convex combination remains a minorant; numerical LP dual
values merely propose its rational mixture.

After summing all positive pair terms, add any rational nonnegative multiples
of theta_j-theta_i-M_ij <=0. This can only lower the affine expression on the
necessary domain. Exactly minimize each remaining linear coordinate term over
its entire closed interval. The resulting rational is a valid energy lower
bound. No numerical objective, primal feasibility, multiplier stationarity
or sampled function comparison is needed for this proof.

The implementation reconstructs all lines and normalizations in exact
arithmetic. Endpoint/midpoint checks are additional arithmetic diagnostics,
not the whole-domain proof. An outward square-root floor and strict comparison
with the SAME rho are both required for strict leaf arithmetic.

Actual latest root25 v3 boxes and independent controls must be bound separately.
Root28 grown-v9 support kernels are universal arithmetic DATA only: no donor
tree, old bounds, ownership or payments are transferred. Existing histories
are unchanged. Any successful leaf still needs a distinct entire latest
source/model/history geometry replay, actual publication and serial current/
independent final before payment. Testing a subset cannot close the whole root.
