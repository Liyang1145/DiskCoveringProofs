# Experimental nonnegative difference-slack products

This new arithmetic mode is not admitted by either running frozen verifier.
It pays zero geometric leaves/roots and cannot substitute for full original
model/current-source/history replay.

For a necessary inequality x_j-x_i<=m_ij and feasible reference r, write
u(x)=m_ij-x_j+x_i=u(r)+a.(x-r), with a=e_i-e_j after eliminating gauge x_0=0.
On the necessary polytope P, u(x)>=0. For any second necessary slack v(x)>=0
and rational multiplier lambda>=0, lambda*u(x)*v(x)>=0.

Let M be the existing exact normalized integrated-Taylor Hessian minorant on
all closed reference-to-target strips. Taylor's remainder is bounded below by
d.M.d/2, with the same charged 15/10^40 symmetric rounding operator error.
Check exact positive LDL/full rational reconstruction of

    M - sum lambda*(a*b^T+b*a^T) + diag(eta) - (15/10^40)I > 0.

Then

    E(x) >= E(r)+grad E(r).d
              +sum lambda*(a.d)*(b.d)-sum eta_k*d_k^2/2.

Expanding the product, and omitting only its nonnegative lambda*u(x)*v(x),
gives the valid lower minorant

    E(r)-sum lambda*u(r)*v(r)
    +[grad E(r)-sum lambda*(v(r)*a+u(r)*b)].d
    -sum eta_k*d_k^2/2.

All reference product constants and reference-linear terms must be charged
exactly. Small but nonzero reference slacks are never replaced by zero.
Reference energy and gradient keep the proved outward 10^-80 rounding;
product arithmetic uses exact rational coefficients.
The signed coordinate minima over the original closed target box then give
an arithmetic energy lower bound, converted to an outward rational radius.

Exact LDL is necessary for an arithmetic certificate. Solver eigenvalues,
optimized multipliers and positivity on a small reference neighborhood do not
establish a whole-root proof. Complete target ownership, closed partitions,
original LOCAL semantics, positive controls, independently frozen geometry
acceptance, actual replay, current admission and independent final rehash are
all still needed. Current mixed verifier supports only its two sealed modes,
not this experimental product mode.
