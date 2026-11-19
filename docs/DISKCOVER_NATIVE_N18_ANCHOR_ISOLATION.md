<!-- SPDX-License-Identifier: MIT -->
# n=18: exact lower exclusion in the candidate anchor neighborhood

**Scoped result.** For the specific 72-rod active graph of the independently
[verified candidate](DISKCOVER_NATIVE_N18.md), with \(q_0=(1,0)\), all eleven
other anchors on the unit circle and
\[
 \left(\sum_{i=1}^{11}|q_i-q_i^*|^2\right)^{1/2}\le 7/60,
\]
any realization of all rods at length at most \(r_*=\sqrt{t_*}\) has exactly
the candidate's 90 geometric coordinates. Therefore a **strictly smaller**
cover cannot realize that active graph in this anchor neighborhood. The
result places no neighborhood restriction on the centers or on the
16 triple-contact witnesses, only on the anchors. It does not constrain
candidate-graph anchor placements outside this neighborhood or different
surviving topologies.

## Exact positive matrix

Let \(A\) be the \(83\times90\) spatial Jacobian of the 72 squared-length
equations and eleven circle equations at the tight candidate root, and
let \(M\) be half the spatial Hessian of the Lagrangian. Thus an exact
quadratic form of \(M\) is the weighted sum of squared rod displacements
plus the anchor multiplier terms. Set \(P_A\) to projection onto the
22 free anchor coordinates, \(\nu=7/625\), and
\(W=\operatorname{diag}(w_0^2,\ldots,w_{71}^2,\nu^2,\ldots,\nu^2)\).
Use the coefficient choices from the
[pinned written specification](https://github.com/VonEquinox/DiskCoveringSolve/blob/089584973f41e6374ce110f6e5b5ee456df19352/cover18/docs/r18_proof_zh.md).
The checker reconstructs the matrix independently of any supplied
positivity factor and proves
\[
 M+400A^\top WA-(69/50000)P_A\succ0 .
\]

The checker reruns the independent root isolation, then rounds the
coordinates, weights and multipliers to denominator \(Q=10^{15}\).
Their differences from the whole tighter root box are strictly below
\(E=2/Q\), and all 72 weights lie in \((0,1/10)\) while all eleven
multipliers lie in \((-\nu,0)\). Each rod derivative row has at most four
entries, each disturbed by at most \(4E\); each circle derivative row
has at most two entries, disturbed by at most \(2E\). Hence the
Jacobian's operator norm error is at most \(\delta_A=500E\), by its
Frobenius norm. Laplacian row sums give
\(\delta_M=(2\Delta_{\max}+1)E\). The diagonal weight-square error is at
most \(\delta_W=E/4\) since both compared rod weights are below \(1/10\).
The checks on the rounded arrays give
\(\|\bar A\|_2<10,\|\bar W\|_2<1/100\). Expanding the quadratic product
shows the operator norm error is bounded by
\[
 \delta_M+400((20+\delta_A)\delta_A/100+\delta_W(10+\delta_A)^2)<10^{-8}.
\]
Subtract \(10^{-8}I\) from the symmetric rounded matrix, scale by \(Q^4\),
and apply fraction-free Bareiss elimination. All 90 leading principal
determinants are strictly positive, giving the required matrix inequality
by Sylvester and the strict perturbation bound. No floating-point
eigenvalue or proof verdict is accepted.

## Why the matrix excludes smaller radii in this neighborhood

Let \(d\) be the spatial perturbation of any competing realization.
Write \(a^2=d^\top P_A d\) and \(u_i=|d_{q_i}|^2\). For each rod
\(e=uv\), set \(v_e=|d_u-d_v|^2\) and
\(s_e=t_*-|z_u-z_v|^2\ge0\). The exact quadratic expansions give
\(A_ed=-(s_e+v_e)\) and \(A_id=-u_i\) in the rod and circle rows.
Stationarity gives
\[
 \sum_e w_e(s_e+v_e)=\sum_i(-\mu_i)u_i\le\nu a^2,
 \qquad
 d^\top M d=-\sum_e w_es_e\le0.
\]
Nonnegative summands bound the sum of squares by the square of their
sum, so \(d^\top A^\top W A d\le 2\nu^2 a^4\). A nonzero \(d\)
would now imply
\[
 0<d^\top(M+400A^\top WA-(69/50000)P_A)d
 \le a^2(800\nu^2a^2-69/50000)\le0.
\]
The last inequality uses \(a\le7/60\) and the exact strict comparison
\(800\nu^2(7/60)^2<69/50000\). Thus \(d=0\), including when \(a=0\);
it cannot have all rods strictly smaller than their exact candidate
length.

For a future angle-box replay, if every free anchor's normalized
turn parameter differs from the candidate parameter by at most \(11/2000\),
then the whole box is safely inside the certified neighborhood:
the chord is at most \(2\pi\) times the turn difference, and
\(11((44/7)(11/2000))^2<(7/60)^2\).
This is a sufficient criterion and does not by itself identify which
other angle boxes can be discarded.

## Replay

Use the same hash-pinned root18.json linked in the
[attainment documentation](DISKCOVER_NATIVE_N18.md).

    python -B verification/n18/anchor_isolation.py path/to/root18.json --negative-controls

A corrupted first principal pivot is rejected. The
[receipt](../verification/n18/anchor_isolation_receipt.json) binds
the root input and exact positive matrix. Continuous exclusion
outside this local anchor region remains unproved by this checker.
