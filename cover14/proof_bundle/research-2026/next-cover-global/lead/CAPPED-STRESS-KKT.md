# Candidate lies on the gap cap: sharp stress must allow constrained stationarity

Method note, analytic conditional theorem, not a certificate for n14.

Let a rooted graph stress have normalized nonnegative weights, energy E(theta) after eliminating free network vertices by Dirichlet minimization. Every covering realization of that graph satisfies E(theta)≤r². For a proposed radius r*, fix L*=2asin(r*) and feasible angular domain P*: theta0=0, cyclic gaps Δ_i∈[0,L*], sumΔ_i=2π. Any cover with r<r* maps into P*, once the cover→graph interface is proved.

Suppose (a) exact graph/root geometry gives E(theta*)=r*², (b) E is convex on the whole P*, and (c) first-order variational inequality gradE(theta*)·(theta−theta*)≥0 for every theta∈P*. Then convexity yields E(theta)≥r*² for all theta∈P*, excluding every cover with r<r*. No assertion gradE(theta*)=0 is necessary when theta* lies on a cap face.

In independent gap coordinates, condition(c) has KKT form gradΔ E = λ1−sum_{i active upper} μ_i e_i+sum_{i active lower} ν_i e_i, with μ_i,ν_i≥0; indeed its dot product with Δ−Δ* is nonnegative. The signs matter: at an upper cap Δ_i*=L*, Δ_i−Δ_i*≤0 and coefficient−μ_i yields a nonnegative contribution. Rotation is quotiented or fixed before testing.

Saved n14 numeric candidate has the two x-axis boundary disks at radius s with s²+r²≈1: their actual boundary arcs have maximal width2asin r, and adjacent covering arcs appear to meet their endpoints. Thus two gap caps are plausibly active. Requiring all anchor torques exactly zero, as in the interior n12 stress, may reject a perfectly useful constrained stress. This is a new branch geometry, not evidence against optimality.

Use of the convenient rational U>r* as the sharp cap enlarges the domain: theta* may then be an interior point even though it lies on the true cap. A nonzero constrained gradient then cannot certify a minimum over the larger domain. Therefore U remains suitable for strict noncandidate exclusions, but the sharp candidate theorem must use L*=2asin(r*) or a radius-dependent inequality with its own proof.

Slack graph faces: at an exact attaining realization with normalized positive edge weights and energy=r*², every weighted edge must be tight. Hence all three incident weights of an interior witness whose radius is strictly belowr* must vanish. Including those slack edges as positive stress to satisfy torques does not yield a sharp certificate. Zero-weight isolated witness vertices should be removed before Schur elimination, rather than declaring singularity a geometric impossibility.

Next executable mathematical test: solve the candidate equilibrium+cap-normal KKT stress cone using14 tight interior witness faces (two slack faces omitted), enforce nonnegative weights and nonnegative cap multipliers, then assess full mixed-direction Hessian bounds. Numeric feasibility is only a proposal; exact stress/root identities and domain-wide curvature remain required.
