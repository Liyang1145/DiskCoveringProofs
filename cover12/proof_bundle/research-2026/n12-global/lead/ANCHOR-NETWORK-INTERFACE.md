# General anchor-network relaxation for k9 triangulated representatives

Status: analytic interface CONDITIONAL on a valid clipped Voronoi dual triangulated disk T with9 boundary sites, m≤3 interior sites, and every chosen triangle having a nearest-point witness in D at distance≤r. This note does not assert that T has already been obtained for every cover; that central topology interface is assigned to members/nine-topology.

## Variables and implication (direction matters)
Let u_0,...,u_8 be the nine cyclic boundary switches; ring site c_i owns arc u_{i-1}..u_i. Let p_f be a point witness for each triangular face f. Define an abstract graph G with vertices:
- nine fixed anchors u_i;
- 9+m free site nodes c_i,h_j;
- one free witness node p_f per triangle.
Connect each u_i to its two incident boundary sites, and each p_f to its three face sites. Put
V_G(u)=inf over all free node positions in R² of max_{edges ab}|z_a-z_b|.
A geometric r-cover with the specified dual supplies feasible positions with every edge length≤r, hence V_G(u)≤r. The free witness variables are NOT constrained to remain inside D, be circumcenters, obey planar incidence, or realize T. Removing those conditions is a safe lower-bound relaxation. Proving V_G(u)≥R_* for every legal anchor u suffices for this topology; V_G(u)≤R does NOT construct a cover.

For k9,m3 there are F=9+2m-2=13 faces, 9+12+13=34 vertices and18+39=57 edge constraints, before coincidences/zero weights. This has25 free point nodes (50 scalar coordinates), rather than only12 center nodes (24 scalar coordinates): witness nodes are added to obtain convexity for fixed anchors.

## Full anchor domain, without symmetry
Every owned arc lies inside its owner's actual arc, so its width Δ_i lies in(0,L], L=2asin U. Their sum is2π. Thus each Δ_i≥2π-8L>0. Put D0=9L-2π>0 and y_i=(L-Δ_i)/D0. Then y_i≥0 and Σy_i=1. Conversely the full closed8-simplex parameterizes precisely these width bounds. Rotate u_0 to(1,0); cumulative sums give all other anchor arguments. Using U rather than r enlarges the domain and removes the radius parameter without replacing centers or changing actual contact geometry.

This is an8D domain even if an ideal candidate is D3-symmetric. Reducing it to a symmetric point requires a global proof, not symmetry averaging: the angular map u(y) is nonlinear, and V_G is convex in anchor Cartesian coordinates, not in y.

## Quadratic stress lower bounds
For any nonnegative edge weights α_e with Σα_e=1 and any placement,
max_e |z_a-z_b|²≥Σ_e α_e|z_a-z_b|².
Minimize the RHS over all free nodes with anchors fixed to obtain E_α(u); then V_G(u)²≥E_α(u). A disconnected all-free weighted component contributes0 and may be dropped. Every anchored free component has positive-definite Dirichlet Laplacian once zero-weight edges are removed, so Schur elimination is legitimate on those components. Never invert a singular free block without this check.

The resulting Schur matrix on anchors is a weighted graph Laplacian: off-diagonals≤0 because eliminating a vertex of incident nonnegative conductances adds effective conductance w_i w_j/(Σw), and row sums stay0. Thus
E_α(u)=Σ_{i<j} q_ij |u_i-u_j|²=Σ_{i<j}2q_ij(1-cos(θ_i-θ_j)), q_ij≥0.
For rational α the elimination and q are exact rational. This supplies finite exact lower bounds on angular boxes or the full simplex. Sampling stresses may propose α but cannot certify the continuum; domain-wide cosine minorants and exact remainder inequalities are needed.

## Remaining obligations
1. Prove exhaustive topology T and its geometric witness interface (active member).
2. Build a complete finite list of nonisomorphic m3 triangle/path fan networks, not only the saved candidate.
3. Exclude unwanted networks or bound their entire anchor simplex.
4. For the surviving network identify the same exact R_* as an attained construction and prove local/global bounds meeting it. Local Hessians alone do not bound remainders or the global simplex.
