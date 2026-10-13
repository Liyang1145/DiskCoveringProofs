# Hub-union exposed-boundary capacity: representation for k10 and k9

This is an analytic necessary-condition interface, not a sharp bound or topology assumption. At 1/3<r≤U, project all centers into D and let the m=12-k nonboundary disks have centers h_j with ||h_j||+r<1. Let H=union_j B(h_j,r). Ring disks denote the other k disks. Then ∂H⊂D, with positive distance from ∂D for each fixed configuration. Since every point just outside H but in D is covered by a ring disk, closedness of the finite ring union implies ∂H is covered by ring disks. This is why hub disks cannot simply exempt all their own boundary points in a capacity argument.

If duplicate hub centers occur, remove their duplicates for boundary parameterization only (not from the original twelve-disk count). For each remaining hub define
E_j={θ: x=h_j+r u(θ) lies on ∂H}.
Except for finitely many circle-intersection/tangency points, this equals the angles for which x is strictly outside every OTHER hub disk. Circle boundaries of distinct centers cannot share positive-length arcs. Thus summing angular integrals on E_j counts ∂H once almost everywhere, with total arc length r sum_j |E_j|.

For arbitrary nonnegative continuous weight W_j(θ), and for any nonnegative outer-circle weight W_0, coverage implies
∫_0^{2π} W_0 + Σ_j ∫_{E_j} W_j
 ≤ Σ_{i=1}^k [∫_{S1∩B(c_i,r)} W_0 + Σ_j ∫_{E_j∩{θ:|h_j+r u(θ)-c_i|≤r}} W_j].
All integrals are in local angle, so units are consistent; multiplying hub terms by r would instead use arclength and must also change their weights. Dropping E_j from the single-ring RHS gives a weaker but simpler bound. That relaxation is mathematically valid, unlike dropping the OTHER hub contributions from a single hub-circle demand.

For exactly two DISTINCT hubs distance d:
- if d≥2r, E_1,E_2 each have measure2π (at equality one tangency point is irrelevant);
- if 0<d<2r, the arc of the first circle lying in the second disk has halfwidth b=acos(d/(2r)); so |E_1|=|E_2|=2π-2b.
Thus required total constant-weight hub angular measure is4π-4b, between2π and4π. Its limit as d↓0 is2π, but at d=0 one must merge duplicates, not use two full-circle parameterizations or infer E_j from strict inequalities. Weighted limits depend on opposite exposed semicircles and are not replaced by two identical full circles.

The core lemma supplies a domain restriction: union_j B(h_j,r) covers B(0,1-2r). For m2 at least one ||h_j||≤sqrt((1-r)(3r-1)); this does NOT bound their distance sharply enough by itself. For m3 all possible intersection patterns and a redundant hub must remain allowed. An algebraic circle-intersection decomposition can compute E_j exactly without assuming a hub graph.

Potential structural payoff: optimize/certify ring capacity uniformly over hub domains to eliminate m1 and m2, or derive necessary triangle geometry for m3. Current gap: no uniform dual weights or sharp support inequality has yet been proved. A numerical failure of this relaxation cannot disprove existence of a sharp argument using the unclipped expression.
