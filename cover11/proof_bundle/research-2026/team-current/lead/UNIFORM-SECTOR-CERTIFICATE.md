# One remote angular region excluded

Object: the canonical graph of FIXED-SWITCH-SOC-REDUCTION.md, unit-circle anchors U_i=(cos theta_i,sin theta_i). Fix theta0=0 and allow independently |theta_i-2pi*i/9|<=1/50 for i=1,...,8. The oracle minimizes radius t, NOT squared radius.

Claim: V(U)>39/100 throughout this box. This is stronger than R* on this box since C891 encloses R*<.38. It is not a global bound on P.

## Certificate construction
The SLSQP export is used only to propose 51 oriented vectors. No optimizer optimality, rank, multiplier sign, residual tolerance, or success flag is a proof premise. Round each vector coordinate to a Fraction with denominator10^12. Orient edges from sites toward anchors/auxiliaries. Independently construct the explicit graph with hub9 on edges0..3, hub10 on4..8 and central faces(9,10,0),(9,10,4).

Select a multi-root spanning forest with all9 anchors as roots. Process free nodes in reverse BFS order. If a free node has residual b, correct its parent-edge force by -sign*b, making its divergence EXACTLY zero and adding its residual to its parent. Rational arithmetic proves zero divergence at every one of the22 free nodes. This procedure works for arbitrary input forces and does not rely on residuals being small. The graph reaches every node, checked combinatorially.

Compute S=sum_e sqrt(p_ex²+p_ey²) using interval arithmetic. Choose an exact rational B strictly above the interval upper endpoint; divide every force by B. Recompute balance (exact), and assert sum_e||p_e||<1 (interval). The resulting field is dual feasible. The old export's coordinate-l1 norm is not used.

At each anchor let l_i be the signed force divergence, and decompose l_i·U(theta_i^0+t)=a_i cos t+d_i sin t. For |t|<=h=1/50:
- if a_i>=0: lower bound a_i cos h-|d_i|sin h;
- if a_i<=0: lower bound a_i-|d_i|sin h;
- without a sign: a_i-|a_i|(1-cos h)-|d_i|sin h.
All expressions are computed by outward intervals, and theta0 is fixed, so its term is simply a0. Their sum has lower endpoint >.3905732 and is asserted >39/100. Weak duality proves V(U)>39/100 for EVERY point in the box (and its convex-sector hull).

## Evidence / reproduction
- `py -3 -B research-2026/team-current/lead/certify_uniform_sector.py`
- `uniform_sector_certificate.json` stores exact rational normalized forces, exact graph, normalization, scope and diagnostic interval.
- `uniform_sector_certificate.log` records successful execution.

The kernel's independence is mathematical: exact forest flow balancing and norm/support verification do not share the optimizer's KKT equations. A two-anchor path with opposite forces1/2 gives distance/2 and calibrates orientation/budget (the general dual derivation is already in FIXED-SWITCH-SOC-REDUCTION.md §3). The certificate is invariant to bad multiplier labels in the proposal: it will either pass the final inequalities or not.
