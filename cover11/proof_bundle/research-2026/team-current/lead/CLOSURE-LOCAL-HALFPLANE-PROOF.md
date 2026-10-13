# Local halfplane proof of cyclic closure (Round5 repair, no perturbation)

Scope: actual inward-root 9-ring+2-hub cover at radius r<=.38 with established nearest-owned cyclic9 arcs, all sites distinct (duplicate disks contradict indispensability), switches P_i, widths w_i. Need only local sites and Voronoi halfplanes; no global metric gluing sufficiency, no generic trivalence assumed.

Each owned arc lies in actual covered arc of radius-r disk, width<=2asin r<pi. Hence its chord line lies at distance cos(w_i/2)>=s=sqrt(1−r²) from origin. Every inward-root ring site has norm<=s. Therefore every ring site lies in the inward closed halfplane of every chord: n·c<=|c|<=s<=cos(w_i/2) for unit outward chord normal n. This is Cauchy-Schwarz, valid independently of which site owns which arc. The origin is in the switch polygon K since all cyclic gaps<pi; K is intersection of these inward halfplanes. Hubs also lie inK since norm<=1−r<s, but this is not needed for local closure.

All9 widths are strictly positive: w_i>=2pi−16asin(.38)>0, so polygon is strictly convex, angle at each P_i is theta=pi−(w_i+w_(i+1))/2 in(0,pi). Fix P=P_i, a=P_(i−1),b=P_(i+1),c=c_i,d=c_(i+1). The vectors a−P,c−P,d−P,b−P belong to the closed cone at polygon vertexP, aperture theta<pi. Distances |P−c|=|P−d| and c≠d. With n=d−c:
 n·(c−P)=−|d−c|²/2<0,
 n·(d−P)=+|d−c|²/2>0.
Because a belongs to closed Voronoi cell of c, |a−c|<=|a−d|; subtract equality atP to obtain n·(a−P)<=0. Similarly n·(b−P)>=0. A line through vertexP has at most one direction in a cone of aperture<pi; the ray n·v=0 separates c fromd. Since a,b are cone extremes, the four rays occur in order a,c,d,b, allowing coincidences of c with a or d with b but not c with d. Thus
 angle(a−P,c−P)+angle(c−P,d−P)+angle(d−P,b−P)=theta.
These are T_i,2b_i,L_(i+1), respectively, giving
 T_i+2b_i+L_(i+1)+(w_i+w_(i+1))/2=pi.

Degeneracy: other sites equidistant atP do not affect pairwise Voronoi inequalities. Cocircular interior faces do not appear in this proof. Positive width prevents coincident switches. Radius-r disks with center on target boundary are impossible after inward-root (norm<=s<1), so c−P,d−P nonzero. Sector triangles can be collinear at a tangency: interpret their angles as actual ray angles0 orpi, which satisfy the same sum. Since distinct switches give q>0, atan2 may hit axis but not genuine(0,0) for simultaneously vanishing vectors; broad interval angle enclosure covers any relaxed singular corner. No covering-preserving perturbation is invoked.

Important rejected audit artifact: teammate draft AUDIT-CLOSURE.md initially asserted4 Voronoi cells (including both hubs) at each boundary switch, plus tested outside-polygon by DOT not CROSS. Both are false. Lead rejected and sent explicit repair; that report must NOT be used as independent evidence or registered. This local halfplane proof is a distinct precise inference validating the original identity, not the false audit argument.
