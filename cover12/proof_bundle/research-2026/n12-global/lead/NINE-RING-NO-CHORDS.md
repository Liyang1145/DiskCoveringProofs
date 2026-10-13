# k9: nonneighbor boundary disks are disjoint (stronger than n11 locality)

Level: analytic theorem conditional only on the k9 boundary branch and the essential-arc ordering proved in NINE-BOUNDARY-OWNERSHIP.md. No full Delaunay interface needed. All disks have radius0<r≤U=0.361102963744508672616920293904. Their nine actual boundary arcs cover S1. Label these by midpoint circular order.

Every arc is essential (eight arcs cannot cover). Thus no arc contains another; lifted left and right endpoints have identical strict circular order. This follows directly: with midpoint difference δ in an overlap neighborhood, if endpoint orders differ then δ≤|α_i-α_j| and the smaller interval is contained in the larger, impossible. Arcs have length<π/4, so this local interval representation is unambiguous. Essentiality also forbids triple overlap, as already proved in NINE-BOUNDARY-OWNERSHIP.

Suppose two nonneighbor ring disks i,j have a common point p∈R². By the triangle inequality their COMPLETE actual boundary arcs lie in
J=S1∩B(p,2r).
Since2r<1, J is a single closed arc of angular length at most2asin(2r)<π. Cut outside J and lift its arc to an interval. Choose the lifts of A_i,A_j contained in J and order their left endpoints. Every intervening arc in the endpoint order is also wholly contained in J, since both its left and right endpoints lie between the corresponding endpoints of A_i,A_j. Nonneighbor labels in C9 have at least one other label between them in BOTH circular directions, so this lift contains at least THREE complete actual arcs, regardless of which direction the chosen lift takes.

Those ≥3 arcs together cover at most |J|≤2asin(2r); at most6 other arcs have total angular measure≤12asin r. Consequently coverage of S1 would imply
π≤asin(2r)+6asin r.
This is false at every r≤U. Here is a simple rational verification, independent of decimal inverse-trig evaluation:
U<4/11;
sin(41/50)≥41/50−(41/50)^3/6>8/11,
sin(373/1000)≥373/1000−(373/1000)^3/6>4/11.
Both trial angles lie in(0,π/2), and sin is increasing there. Hence
asin(2r)<41/50,
asin r<373/1000,
asin(2r)+6asin r<41/50+6·373/1000=1529/500=3.058<π.
The sine lower bound is the first two alternating Taylor terms on[0,1]; the last bound follows for instance from the perimeter of an inscribed regular hexagon, π>3, which alone is insufficient, so use the inscribed regular dodecagon: π>12sin(π/12)=3(√6−√2)>1529/500. Equivalently the standard elementary π>31/10 suffices. An exact dodecagon check is supplied in the companion rational-controls output rather than assuming π>3.1 without proof.

Therefore all nonneighbor pairs are DISJOINT AS CLOSED DISKS. In particular:
- no three ring disks have a common point (every triple in C9 contains a nonneighbor pair);
- any nearest-site/Delaunay common-point edge between ring sites can only connect adjacent ring labels;
- no all-ring triangle can occur in a refinement whose triangle vertices share an empty-circle center in D of radius≤r;
- no 'ear' ring triangle or ring chord needs a special certificate in k9.

These implications remain true after inner-root replacement, because the resulting representative is still a cover with the same nine actual boundary arcs, and the argument can be reapplied to it. The statement does NOT say arbitrary straight edges between centers are absent: only common-covered-point / nearest-site edges are excluded. It does not yet prove hub adjacency or an embedded straight dual triangulation.

Potential payoff: if a valid clipped Voronoi dual disk with nine boundary and three interior sites is established, every triangle meets the hub set. Planarity then limits the hub-induced graph to a path or triangle (plus possibilities requiring a separate connectivity proof). The dual-disk and connectivity implications are not silently assumed here.
