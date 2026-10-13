# Full-coordinate local exclusion epsilon=1/25000

Object: exact C1167 candidate C*, squared contact radius r*^2. Rotational gauge coordinate19=y(X+)=0. All28 coordinates in |C-C*|_infty<=1/25000; labels fixed. No symmetry is imposed on perturbations. Exact stationarity and positive contact weights inherited from LOCAL-SOSC-PROOF.md / C1182.

P(C)=sum over18 positivecontacts [lambda_k(f_k(C)-r*²)+3/2 (f_k(C)-r*²)²]+3/2 C_19².
The kernel certifies positive contact branches, genuine nearest witnesses and 2lambda_k+3delta_k>0 on the entire box. Hence every cover at radius<=r*, in the gauge, satisfies P<=0. At the exactroot P=0 and gradP=0.

New representation: choose a fixed EXACT DYADIC invertible W, proposed from a floating Cholesky inverse. Each affine input coordinate C_i is initialized in interval second-order AD with gradient equal to row_i(W), Hessian0. At every boxpoint this computes derivatives of f(C+Wt) at t=0, so outputs enclose W^T grad f and W^T Hess f W directly. The coordinate value intervals are STILL the original axis-aligned C-box, not a mistakenly rotated box. Variable t is only a derivative direction; it does not describe the interval domain. This keeps chain-rule cancellations inside the expression evaluation. Matrix positivity tests all mixed28 directions.

The final interval matrix M encloses W^T HessP(C) W. With E_ij=max(abs(Mlo_ij−Iij),abs(Mhi_ij−Iij)), saved positive rational v gives EXACT weighted row bound max_i sum_j Eij vj/vi=b<1; display b=0.3743708410423505. For each real matrix M in the intervals, ||M−I||_(v,infty)<=b. All its eigenvalues satisfy |lambda−1|<=b; the actual M is symmetric, hence positive definite. Fraction replay checks the exact bound and exactrankW28. Numerical eigenvectors only PROPOSE v; numerical Cholesky only PROPOSES W; no approximation is trusted for the inequality.

Strict convexity on the convex originalcoordinatebox plus exactstationarity yields P(C)>0 at every C!=C*, contradicting feasibility. Thus no other covering at<=r* exists in this box modulo the stated rotational gauge. This extends C1259 epsilon2e-5 by a factor2, and the original1e-8 box by4000. It is LOCAL only.

Files: local_neighborhood_directional.py, local-neighborhood-directional-4e5.json/log/err; local_perron_fraction_replay.py, local-neighborhood-directional-4e5-fraction-replay.json. Repro (defaults epsilon1/25000,K3):
 py -3 -B research-2026/next-cover-global/lead/local_neighborhood_directional.py
 py -3 -B research-2026/next-cover-global/lead/local_perron_fraction_replay.py
Ensure N14_LOCAL_EPS/K/OUTPUT env overrides are unset first. Matrix replay is independent rational arithmetic on SAVED geometric enclosures, not an independent geometric AD implementation. Underlying AD chain rules and exactKKT remain bearing premises, unchanged.

Consequence for saved cyclicity-repair points: their float-aligned offsets2.947e-5..3.594e-5 are numerically inside this box. This does not certify their membership or that they are covers. It means an exact realization lying in this box cannot improve or equal r* unless it is the exact candidate. No claim that all realizations near a residual-small parameter vector are in the box, and no global classification follows.
