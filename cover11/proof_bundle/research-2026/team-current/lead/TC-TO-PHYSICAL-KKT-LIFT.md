# TC root to full physical first-order KKT: implicit boundary elimination

## Intended structural gain and scope
Avoid a second 56-dimensional root solve and avoid inferring exact stationarity from a tiny SVD singular value. The existing exact symmetric TC KKT equations already give restricted stationarity. Their missing interface is a regular five-constraint boundary chart plus multiplier signs, not approximate rank of an overdetermined angle-space matrix. The analytic lift and its sign obligations are now discharged for the C891 exact root by C897: the odd-cycle chart proves rank, and phase7_interval_cyclic_nu.py encloses all multiplier and conversion signs.

## Physical symmetric dimensions
Reflection across x-axis fixes rings C4 and the two hubs; four ring pairs contribute 8 coordinates, C4 contributes1, hubs2, radius1: total12. Nine boundary-tie branches have five reflection orbits. At the candidate seven active fan faces plus two central faces have five orbits (three paired fan orbits, one self-reflected fan, one central pair). Hence use five representative boundary constraints B_j(x)<=0 and five representative interior constraints F_i(x)<=0 on symmetric variables x∈R12. Two slack faces are excluded locally using their strict margin, not by assumption.

Let the five B_j be smooth physical covering-radius-minus-R branches for actual neighboring boundary ties. Require rank DB=5. Then M={B=0} is seven-dimensional. The explicit TC map Phi(z), z=(a0,a1,a2,a3,y0,y1,R), must be a local chart onto M. Boundary arc tiling and inward roots provide its candidate inverse; the orientation, distinctness, and nonzero radial branch derivatives must be checked. Merely counting dimensions is not enough.

For interior F_i choose smooth constraints that agree with TC res5 after pullback. They need only have positive first-order factors relative to actual radius-minus-R branches at the root. The fan inner-pin residuals are locally equivalent by the C879 product identity, since outer factor is strictly positive; the central waist residual needs its analogous correct-side product check. Do NOT assume equality of radius gradient and pin-distance gradient.

## Exact multiplier lift
Root equations give dR=Σ lambda_i d(F_i∘Phi), lambda_i as defined by repaired12Dsystem. Set mu_i=-lambda_i. Thus w=dR+Σmu_i dF_i annihilates T_xM=ker DB. By rank DB=5, uniquely
w+DB^T nu=0,
nu=-(DB DB^T)^(-1) DB w.
This is an exact consequence at the exact TC root, not a residual-based inference. Formula is written in any Euclidean symmetric coordinates, with the corresponding consistent coordinate metric; solving a nonsingular5column minor is equivalent and may enclose better.

If all mu_i>=0 and nu_j>=0, and the local branch conversion factors are positive, this is a symmetric physical KKT certificate. Strict positivity can be verified on the isolating root box without proving an overdetermined interval linear system has a zero. The root equations furnish exact consistency; interval arithmetic need only enclose the explicit multipliers and branch factors.

## Reflection lift
Extend each representative constraint to the full physical variable space R23 (22 center coordinates and R). Replace it by its orbit average under simultaneous site permutation and geometric reflection; the restriction of the average to Fix(reflection) equals the representative. Divide its multiplier equally among distinct branches in the orbit. The resulting weighted covector is reflection invariant. Its restriction to Fix(reflection) vanishes by the symmetric KKT equation, and it vanishes on the anti-invariant subspace by invariance. Hence it vanishes on all R23.
This is not the false assertion that each individual branch has zero antisymmetric derivative. It is the averaged weighted sum that does. Radius objective and active set are reflection invariant. Rotation invariance supplies its own null direction but is irrelevant to the first-order lift; a rotation slice is necessary only for a strict second-order minimum statement.

## Remaining obligations
1. Construct B_j and verify DB rank5 + Phi local onto B=0. A direct inverse from arc gaps may establish rank without interval determinant expansion.
2. Check five F_i local branch factors, especially central orientation.
3. Evaluate nu and mu intervals at the exact root and prove nonnegative signs.
4. Obligations1–3 are closed in C897 (TC-BOUNDARY-CHART-RANK.md and r20-stress/phase7_interval_cyclic_nu.py). This yields first-order full physical stationarity ONLY. C893 certifies the symmetric2D common-gradient Hessian; antisymmetric2D certification remains. Once both blocks are positive, FINITE-MINIMAX-QUALITATIVE-SUFFICIENCY.md supplies a uniform C² remainder argument for existential local quadratic growth; no numerical third-derivative bound is needed. Global optimum still requires remote configuration exclusion.

## Explicit odd-cycle boundary multipliers (no inverse conditioning)
Use full nine-ring polar radial coordinates at fixed angles and R. Distribute each TC interior multiplier mu=-lambda equally among its two reflected face residuals, or retain it on the self-reflected fan8. Let v_j=Σ_faces mu_face ∂f_face/∂rho_j, where f_face is the GENUINE chord-circle inner-pin residual, not the unit-tie expression continued outside B=0. Set w_j=v_j/a_{j,rho}. Radial stationarity for the full boundary gap constraints g_i is
 nu_{j-1}+nu_j=w_j.
Because there are nine sites its exact solution is
 nu_j=(1/2)Σ_{k=0}^8 (-1)^k w_{j-k mod9}.
Thus no interval solve of a potentially singular overdetermined system is required. The exact root equations, chart regularity, and reflection averaging establish all other components of stationarity; this formula merely computes the UNIQUE lift already proved to exist. Interval evaluation need only prove its entries positive.
At the candidate, calibration by r20-stress/phase6b_nu_explicit.py gives symmetric orbit sums approximately (.043898,.035400,.050868,.048892,.015286), all positive. NOT certified yet.

Physical radius branch weights: if df_i=c_i d(G_i), c_i=4y_i²/Fout_i>0, and dg_j=b_j d(B_j), b_j=a_{j,R}+a_{j+1,R}>0, then weights are mu_i*c_i for face constraints and nu_j*b_j for boundary constraints G_i=gamma_i-R, B_j=t_j-R. Their sum is exactly1 by the R component of stationarity, since gamma_i and t_j depend on centers only. Positivity of mu and nu implies a genuine positive minimax stationary weight vector. A separately observed s=Σmu_i*c_i<1 follows from positive boundary weights and exact normalization; it is not an independent premise if these interfaces are proved.
