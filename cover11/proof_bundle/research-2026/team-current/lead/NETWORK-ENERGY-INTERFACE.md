# Squared-distance stress representation: exact interface and calibration

## Object
Use the 31-node/51-edge fixed-switch graph in FIXED-SWITCH-SOC-REDUCTION.md, with nine prescribed anchors U and 22 free nodes (11 sites and 11 face auxiliaries). Let q_e(X,U)=|X_v-X_w|^2. All distances are in unit-disk units.

Define E_alpha(U)=inf_X sum_e alpha_e q_e(X,U), for alpha>=0, sum alpha=1. The infimum is essential. Without it the expression still depends on free coordinates and is not a lower bound independent of X.

## Exact dual identity
V(U)^2 = min_{X,t} {t: q_e(X,U)<=t for all e}.
The constraints are convex quadratic. They have a strictly feasible point (all free nodes zero and t larger than every edge square). The full graph is connected to anchors; bounded t bounds all free nodes along paths, giving primal attainment. Its Lagrangian is
L(X,t,alpha)=(1-sum alpha)t+sum alpha q_e.
The infimum in unrestricted t is finite exactly when sum alpha=1. Convex Slater duality gives
V(U)^2=max_{alpha in simplex} E_alpha(U).
The dual maximum is attained: E is the infimum of continuous linear functions of alpha, hence upper semicontinuous, and the simplex is compact. Each energy minimum also exists by solving weighted least squares; components without anchors contribute zero and allow translation freedom.

Consequences:
- E_alpha is concave, generally NONLINEAR in alpha, not linear.
- It is a nonnegative convex quadratic in Cartesian U: eliminate free coordinates from the weighted graph Laplacian, treating zero-weight components separately.
- Concave maximization does NOT reduce to simplex vertices.
- No interchange of min over angular U and max over alpha follows. A single stress valid on the entire angular domain is sufficient, not necessary.

## Independent exact calibration
For a two-edge path U--x--W with alpha=(a,1-a), completing the square gives
 a|x-U|^2+(1-a)|x-W|^2=|x-aU-(1-a)W|^2+a(1-a)|U-W|^2.
Thus E_a=a(1-a)|U-W|^2. For distinct anchors its maximum is at a=1/2, strictly larger than zero; BOTH simplex vertices give zero. The dual value is |U-W|^2/4, agreeing with the smallest enclosing radius of two points squared.
In our network each single edge has at least one free endpoint, so every simplex vertex likewise gives E=0. Any finite-vertex stress reduction would therefore destroy the desired positive bound.

## Angular derivatives and scope
Writing E=sum_ij Lambda_ij cos(theta_i-theta_j), the correct derivatives are
 g_i=-2 sum_j Lambda_ij sin(theta_i-theta_j),
 H_ij=2 Lambda_ij cos(theta_i-theta_j) (i!=j), H_ii=-sum_{j!=i}H_ij.
A fixed stress can furnish a local sharp lower bound at an interior legal anchor only if g=0 on the rotation quotient. PSD H alone is not sufficient for local minimality if it has additional zero directions.

The exported SLSQP sparse multiplier has nonzero individual tangential anchor loads and a numerically negative H eigenvalue about -0.02016. This tests only that particular numerical stress. It does not test the C897 lift, which enforces cancellation of each tie's tangential load. The positive physical stress is being reconstructed before the decisive fixed-stress test.

Implementation warning: face f does NOT have sites (f,f+1,f+2) modulo11. Every edge must use the explicit incidence map. A graph replacement can produce plausible Laplacians while computing the wrong quantity.
