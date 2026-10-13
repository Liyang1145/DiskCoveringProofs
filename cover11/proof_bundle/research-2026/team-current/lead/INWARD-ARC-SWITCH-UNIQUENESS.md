# Inward-ring boundary switch uniqueness (analytic)

Scope: 0<r<1, distinct centers a,b with |a|,|b|<=sqrt(1-r²), each disk meets the unit circle in a proper connected arc. For r<=.38 in an n11 cover, C451 supplies nine boundary disks and C464 supplies an inward-root representative; each boundary arc is essential, since eight radius-r disks cover at most16 asin(r)<2pi of boundary. Thus no arc is contained in another. This note addresses the boundary interface of C879, not fan triangulation necessity or the global bound.

## At most one covered equality point
Let m=(a+b)/2, e=(b-a)/d, n=Je, d=|b-a|>0. Equality points on the unit circle lie on x=m+tn, where t solves |m+tn|²=1. Since |m|<1 (distinctness and strict convexity of disk radius<=1), its two roots satisfy t_-<0<t_+. Distance to either site at such a point is d²/4+t².
If both equality points were covered by either site, k²=r²-d²/4 would satisfy k²>=max(t_-²,t_+²). But the average of those squares is 1-|m|²+2(m·n)²>=1-|m|². Consequently |m|²+k²>=1. On the other hand
 |m|²+k²=a·b+r²<1,
since a·b<=|a||b|<=1-r² and equality would force a=b on the limiting radial circle. Contradiction. Thus at most one unit-circle equality point is covered by both disks. This includes double radial roots and arc tangency.

## Existence for intersecting noncontained short arcs
Both arcs have angular length <=2asin(r)<pi (r<=.38). If they meet and neither contains the other, their union has length<2pi, so unwrap on a common interval. Order endpoints l_a<l_b<=u_a<u_b, allowing the single-endpoint intersection. At l_b disk b has distance r and a has distance<=r. At u_a disk a has distance r and b has distance<=r. The continuous squared-distance difference changes sign (or vanishes at the shared endpoint), so an equality point belongs to the common covered arc. The previous argument gives uniqueness.

Therefore the C879 unique covered boundary-switch hypothesis follows for every intersecting pair of noncontained arcs in the canonical inward representative. Adjacent essential arcs in the covering order do intersect (otherwise boundary has a gap); proving the selected fan graph corresponds to these adjacent arcs remains a separate graph interface, not established by this lemma.

## Inner/outer ring-circle intersections
A covered equality point gives d<2r: equality d=2r would force the point to be m, impossible since |m|<1. Set k=sqrt(r²-d²/4)>0. The two RING-circle intersections are m±kn, not the two unit-circle equality points m+t_±n. Exactly one t-root lies in [-k,k]. If it is t_+>0, then t_-<−k< t_+<=k. Thus m−kn is strictly inside D and m+kn is outside intD. The case of t_- is reversed. This proves the complete C879 ring-pair hypothesis, including the strict inner-root and weak outer-root norm conditions. p_in denotes the smaller-norm RING-circle intersection; p_out the larger-norm one. At a boundary arc tangency the common tie equals p_out on ∂D; the OTHER ring-circle intersection is p_in, not p_out.

Hence for any chain of these adjacent arcs, and any strict hub |h|<1−r, ALL fan circumradius constraints are equivalent to membership in the intersection of the closed pin disks and the open strict-hub ball, by C879. No saturation or reflection assumed. This is not yet a proof that every global cover has its central/fan Delaunay graph in that same arc ordering.

Degeneracies: duplicate centers would give duplicate arcs, impossible in nine essential boundary disks. A boundary tangent singleton arc cannot be essential in a finite closed-arc cover: neighboring closed arcs cover its point by limits of the punctured neighborhood. More directly, eight other arcs cannot cover the rest by the same strict total-length bound. Hence all nine arcs have positive length.

Control: the strict a·b+r²<1 uses the inward radial bound. Arbitrary ring centers without that bound are NOT covered by the at-most-one proof.
