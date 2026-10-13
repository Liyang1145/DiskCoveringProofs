# Coherent angle feasibility is EXACTLY the positive-radius domain

Scope: C1261 finite connected fixed-beta face network touching anchors, beta in(0,pi), c=pi-beta. Every real face requires angle sum pi. No radius caps or boundary cyclicity in this theorem.

A coherent angle allocation consists of numbers h_fe>0 for every face-edge incidence, summing to pi at each face, such that h_fe+h_ge=c_e for internal edges and 0<h_fe<c_e for anchor edges.

**Equivalence.** Such an allocation exists iff every nonempty face subset S satisfies I(S)<pi|S|<I(S)+B(S), iff for EVERY positive anchor-radius assignment the unique positive Dirichlet radii exist.
Proof of first-to-cuts: summing face balances cancels interior allocated angles to exactlyI(S). Crossing edges contribute strictly between0 and c_e. Connectivity to an anchor ensures B(S)>0. Cuts-to-radii is C1261. Radii-to-coherent uses h=atan2(Tsinbeta,R-Tcosbeta); h in(0,c), h_fg+h_gf=c. This closes the logical cycle without assuming an arbitrary coherent allocation itself is metrically realized. The actual unique radii can yield DIFFERENT h from the LP witness.

**Finite LP formulation without exponentially many cuts.** At fixed beta maximize a common epsilon subject to h_fe>=epsilon, h_fe+h_ge=c_e, h_fe<=c_e-epsilon on anchor incidences, and sum h=pi. Strict feasibility iff epsilon>0. If beta are also variable, add beta_e>=epsilon, beta_e<=pi-epsilon and the prescribed site-angle ledger; everything is linear in radians. An exact positive rational/pi witness certifies the whole finite cut family indirectly. Conversely, an infeasible LP identifies an obstruction already encoded by some cut, not an additional shared-radius restriction.

For unit-radian rational beta/pi, use scaled variables h/pi and epsilon/pi so all constraints have rational coefficients. A float LP proposal may be repaired/certified by exact linear algebra or interval residual bounds; solver success alone is not a proof.

**Consequence for route selection.** Adding C1261 cut inequalities to a relaxation which ALREADY has the full strictly coherent face-angle ledger cannot improve feasibility merely because they look nonlinear: they describe the same projected beta domain. The genuine new obligations are (i) the radii resulting from a SPECIFIC anchor assignment obey R<=U, and (ii) the developed boundary is unitcyclic with anchor distances<=U. Full face-angle variables can be projected out and recovered via the unique radius map, but their existence alone will never settle these two constraints.

Calibration: q11 retainedgraph58 LP yields a strictlycoherent witness; defaultequalanchors give positive realradii even though boundaryturns fail. Radiuselimination plus oddclosure repaired to a numerical unitcyclic configuration at radius .4275024419938625; independentCartesian development confirms it. A bounded constrainedminimum on that branch reaches .35635598988053274, aboveU. Neither number excludes other branches or makes a global lowerbound. These controls separate positivity, cyclicity and cap exactly as the theorem predicts.
