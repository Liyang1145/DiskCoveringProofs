# Candidate-network global angular convexity mechanism

Status: this file preserves the original analytic mechanism and numeric scout history. Its candidate-root/stress/Hessian premises have since been certified by `root_t_certificate.py`, `root-t-stress-certificate.json`, `EXACT-CANDIDATE-STRESS.md`, and `members/stress-audit/REPORT.md`; the complete k9 synthesis is C986 / `K9-SHARP-THEOREM.md`. The historical 'remaining' list below is not the current task list. No unrestricted12-disk conclusion is claimed here.

Sources: lead/candidate_stress_probe.py; evidence/candidate-stress-probe.json; evidence/stress-hessian-scout.json; ANCHOR-NETWORK-INTERFACE.md.

## Fixed stress network
Keep only the6 observed active face witnesses (3 HRR and3 HHR) and all18 boundary site-anchor edges; omit6 slack HRR and1 slack HHH constraints. This relaxes the complete candidate topology safely. The graph has9 anchors,12 sites and6 witnesses:36 active edge inequalities. At the numeric D3 chart root, the free-node equilibrium matrix has one-dimensional nullspace; normalized stress α has minimum0.01165992192009>0, equilibrium residual1.6e-17. Schur energy E at candidate matches r² to float accuracy and its9-dimensional angular gradient is<1.1e-16.

Let E(θ)=Σ_{i<j}2q_ij(1−cos(θ_i−θ_j)), q_ij≥0 the fixed stress Schur coefficients. Hessian quadratic form is
zᵀH(θ)z=Σ_{i<j}2q_ij cos(θ_i−θ_j)(z_i−z_j)².
For any legal k9 anchor vector, each consecutive gap lies in(0,L], L=2asinU. If the cyclic label distance between i,j is d∈{1,2,3,4}, the shorter-label path has angular sum s∈[0,dL]. Since4L<π, cos(θ_i−θ_j)=cos(s)≥cos(dL). This remains true regardless of which directed lift of θ was used.

Define a constant symmetric matrix M with quadratic form
zᵀMz=Σ_{i<j}2q_ij cos(d(i,j)L)(z_i−z_j)².
Then H(θ)−M is positive semidefinite throughout the ENTIRE legal width simplex, because every coefficient difference is nonnegative. Some cos(dL) are negative; positivity of M must be checked on mixed directions, not inferred from individual blocks.

## Numeric discriminant
For the calibrated positive candidate stress, eigenvalues of M are approximately
[0, .00236615469, .00236615469, .0344575191, .0344575191, .0603240539, .0706144168, .0833348942, .0833348942].
Thus there is a substantial apparent positive gap modulo common rotation. This is much stronger than the initial10009 simplex Hessian samples (min .0025788); those samples are no longer the intended route to proof.

## Consequence if certified
The legal angle domain fixing one anchor is a convex polytope (affine image of the width simplex). If exact candidate stress α≥0 with Σα=1 is available, exact root gives equilibrium and angular stationarity, and an interval/exact LDL certificate proves M positive on1⊥, then E is strictly convex over this full domain, with its minimum at the candidate anchor vector θ*. The exact equilibrium/free minimization and all positive-weight edge equalities give E(θ*)=r_*². Consequently
V_G(θ)²≥E(θ)≥r_*²
for all anchors in the full domain, with no box search and no assumed symmetry on competitors.

To avoid square-root trigonometric constants, one may use any certified rational lower constants c_d≤cos(dL), check the corresponding exact/interval M, and retain the same implication. The d-dependent coefficients can be bounded using U rational and cos(2asinU)=1−2U² plus Chebyshev polynomials: cos(dL)=T_d(1−2U²) is EXACT RATIONAL. Only q depends on the exact algebraic root/stress.

## Remaining bearing obligations
1. Exact isolate D3 chart root and certify covering at it (candidate member).
2. Obtain exact positive stress as rational functions of root coordinates; verify equilibrium INCLUDING angular forces, and normalization. Numerical nullspace is not proof.
3. Interval q and exact rational cosine constants; complete mixed-direction8×8 principal-minor LDL for M. M1=0 and positive principal minor imply positivity modulo rotation.
4. Prove every surviving topology supplies THIS network (nine-topology only gives finite list, not this identification), or exclude every other network by separate lower bounds.
5. Exclude k10/11 globally. The convexity insight does not skip these branches.
