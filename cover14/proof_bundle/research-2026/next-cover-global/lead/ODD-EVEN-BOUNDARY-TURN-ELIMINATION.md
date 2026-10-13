# Boundary closure without redundant perimeter: odd/even turn elimination

Strict flat coupled system as in C1257, before requiring unit-circle boundary closure. All original/virtual/owner triangles positive; shared edges compatible; site angle ledger makes all14 interior vertices flat. Let L_i>0 be edge lengths of the abstract outer anchor boundary, omega_i its interior angle at vertex A_i, and tau_i=pi−omega_i. Require tau_i>0. Discrete Gauss–Bonnet gives sum tau_i=2pi, independently of the radius scale or unit-circle constraints. Direct proof: sum all triangle angles = pi F; subtract2pi times number of interiorvertices to get sum boundaryangles=(q−2)pi by3F=2E_int+q and Euler. Thus sumtau is an identity in valid strict data, not another constraint to impose.

If the boundary is unitcyclic with successive positive arc angles theta_i in(0,pi), edgei joins A_i to A_(i+1), then
 **theta_(i−1)+theta_i=2tau_i**,
 **L_i=2sin(theta_i/2)**.
Conversely these equations with sumtheta=2pi imply the unitcyclic boundary by C1251; sumtheta=2pi already follows by summing the first equation. No independent perimeter equation is needed once all closure equations and the exact flat ledger hold.

## Odd q (in particular q=11)
The cyclic adjacent-sum matrix is invertible. Explicitly
 theta_i = tau_i−tau_(i−1)+tau_(i−2)−...+tau_(i−q+1),
 with q alternating terms and cyclic indices. Derivation: repeatedly substitute theta_i=2tau_i−theta_(i−1), and use oddq to obtain2theta_i=2alternatingsum. The theta are uniquely determined by SCALE-INVARIANT triangle angles, with sumtheta=2pi. Positivity theta_i>0 and theta_i<pi are necessary; arbitrary positive turns do not automatically ensure them.

Now remove common radius scale: choose positive anchor ratios y_i with product1, solve the Dirichlet real radii (C1261), and compute owneredge ratios ell_i and turns tau_i. Absolute scale t multiplies all radii and all boundaryedge lengths while leaving all angles unchanged. The boundary is unitcyclic iff the calculated theta satisfy(0,pi) and
 **t_i=2sin(theta_i/2)/ell_i is the SAME positive number for all i.**
That number uniquely fixes the scale t. Actual cover radius bound is then t max(all realface radii and all anchor ratios)<=U, plus virtual/owner validity conditions. Thus q11's unitcircle equations can be represented by10 dimensionless equal-ratio constraints; perimeter and scale have both been eliminated. No sampled equality is exact, and beta/anchor ratio domain remains nonconvex.

## Even q (in particular q=10)
The adjacent-sum matrix has a one-dimensional alternating kernel. Solvability requires sum_i(-1)^i tau_i=0. When it holds, theta_i=theta_i^0+(-1)^i z with one free scalar z. The interval0<theta_i<pi bounds z explicitly. For any such z, sumtheta=2pi is automatic. Circle closure then requires equality of the10 scale proposals 2sin(theta_i(z)/2)/ell_i; this is9 scalar equality constraints in z and the scale-free data, plus the turn compatibility. These displayed equations still have TWO geometric dependencies from vector closure of the already developed polygon. Therefore their raw equation counts are NOT ranks. Use the nonparallel-edge elimination below; do not claim generic9 or10 independent constraints from these raw lists.

## Why this matters and what it does not prove
This is an exact representation change, not a new inequality or global exclusion. It removes a redundant perimeter equation and avoids treating global radius scale as a free variable. With Dirichlet elimination it is suitable for a bounded solver/certificate study of surviving q11 topologies: failures from nonpositive alternating theta can be rejected before nonlinear unitcircle matching. Candidateq10 has straight owner vertices alpha=pi; the extension in FLAT-DISK-STRAIGHT-OWNER-EXTENSION applies but numericalrank may be singular there. Do not infer absence of covers from solver failures, and do not discard compact degeneracies in a global lower-bound argument.

## Eliminate two length equations exactly, not by numerical rank
The positive triangle metric with flat interior and convex boundary already develops to a CLOSED convex polygon (degree argument does not require a circle here). Its consecutive edge directions d_i are determined up to rotation by turns tau_i, and sum L_i d_i=0. If theta solves the adjacent-sum equations withsumtheta=2pi, the unitcircle chord model with lengths c_i=2sin(theta_i/2) has the SAME successive directions (after one rotation) and also sum c_i d_i=0.

Choose any TWO nonparallel boundary edge directions d_j,d_k. Impose L_i=t c_i for every other i (where t is a common polygon circumradius; equivalently use inverse scale in the earlier normalization). Subtract the two vector closures:
 (L_j−t c_j)d_j+(L_k−t c_k)d_k=0.
Nonparallelity forces BOTH missing length equations. Thus enforcing q−2 of the q common-scale length equations is exactly enough; of those q−2 equations, one fixes t and only q−3 are scale-free constraints. For q11 this leaves8 scale-free constraints, not10. For evenq10 the extra scalar z and the turncompatibility must also be retained; no rank assertion at boundary branches is made. Convexity ensures that some nonparallel edgepair exists. For a certified parameterbox, choose a fixed pair and prove its determinant bounded away from0; globally use finitely many such charts. This is algebraic elimination using closedpolygon geometry, not sampled-rank promotion.

The missing implication for formal algebraic systems: vectorclosure must come from an ACTUAL developed flatdisk, supplied by positive triangle metrics and angleledger. One cannot remove equations from arbitrary incomplete radius/angle assignments by invoking polygonclosure before realizing their metric. Degenerate systems require a compact-limit bridge or a different chart.
