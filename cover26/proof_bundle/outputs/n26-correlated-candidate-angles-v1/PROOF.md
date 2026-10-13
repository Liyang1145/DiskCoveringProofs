# Exact circle-arc support with a difference-constraint dual

This is a conditional lower-bound continuation for the same labelled, full
candidate rod graph. It does not pay its very broad global prefix [24,40],
does not establish the full catalogue and does not prove global optimality.
No competitor is restricted to D2 symmetry.

Every old non-OPEN node and every closed split remains unchanged. Correlated
leaves are first replaced by OPEN for the previously accepted semantic replayer:
the original U-domain is reconstructed with both closed children and shared
boundaries. Only at a correlated leaf is the independently certified necessary
sharp matrix applied, under the hypothesis that its radius is at most R*.

Write the angles in turns, with theta_0=0. The certified matrix and the closed
box give theta_j-theta_i <= T_ij, where T_ij is the minimum of the matrix entry
and upper_j-lower_i. For any explicitly listed rational mu_ij >= 0, reconstruct
c_i = sum_j mu_ij - sum_j mu_ji exactly. Summing the inequalities proves

    sum_i c_i theta_i >= -sum_ij mu_ij T_ij.

The integer anchor loads g_i are realized by exactly reconstructed edge flows,
with zero interior divergence and the necessary root load. Their outward norm
sum D bounds the true flow-norm sum. Thus radius >= sum_i g_i.(q_i-q_0)/D
whenever the computed numerator is positive.

For midpoint m_i, half-width h_i in turns, and H_i=2*pi_upper*h_i in radians,
exact trigonometric intervals bound f_i(m_i)=g_i.q(m_i) and the turn derivative
d_i=2*pi*g_i.q'(m_i). Taylor's theorem over the entire closed arc gives

    f_i(theta_i) >= f_i(m_i)_lower + c_i(theta_i-m_i)
                     - max(|d_i_lower-c_i|,|d_i_upper-c_i|)*h_i
                     - norm(g_i)_upper*H_i^2/2.

Summing these bounds and the nonnegative difference dual gives the accepted
numerator. The full derivative residual is paid: numerical derivatives, LP
feasibility, and convergence flags are not assumed exact. All dual coefficients,
divergence, endpoint intervals, curvature charges and norm sums are recomputed
with rational arithmetic. Acceptance requires a strict bound above the
certified strict upper endpoint of R*.

With zero dual the formula reduces exactly to the old direct-arc certificate.
At fixed feasible angles, the box difference bounds are exact and every
nonnegative dual cancels exactly, again recovering the direct-arc value.
Positive controls check both reductions and whole-box support on known feasible
regular rings. Rejection controls cover negative or repeated duals, zero flow,
lost old payments, missing closed halves and unreachable nodes.
