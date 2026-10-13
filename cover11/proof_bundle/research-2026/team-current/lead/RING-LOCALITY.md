# Ring-intersection locality from essential arcs and capacity

Object: nine congruent radius-r closed disks cover the unit circle, 0<r<=19/50. Their actual arcs I_i are cyclically ordered by their endpoints, individually essential, only cyclic neighbors overlap, and no containment occurs. The last properties follow from the established short-essential-arc lemma; no inward-root or full disk coverage assumption is needed here.

Claim: disks with cyclic index distance 3 or 4 are disjoint in the whole plane. Consequently any three disks with a common point have three consecutive indices.

Proof. Suppose disks i,j contain p. Their entire actual boundary arcs are contained in J=S^1 intersect B(p,2r) by the triangle inequality. This J is one closed arc of length at most 2 asin(2r)<pi (and cannot be empty). Cut the circle at a point outside J and lift to a real interval. Both complete arcs I_i and I_j lie in that interval. Because left and right endpoints of the essential arcs have the same strict cyclic order, every complete arc whose index lies between i,j in this lift has both endpoints between the corresponding endpoints of I_i,I_j. Each such complete arc therefore lies in J. If cyclic index distance(i,j)>=3, both directions around the nine indices have at least four arcs counting endpoints. Thus at least four complete actual arcs lie in J.

Those at least four arcs jointly cover at most 2 asin(2r); at most five remaining arcs jointly cover at most 10 asin r. This contradicts circle coverage, since asin(2r)+5asin r<pi. An exact elementary bound for r<=19/50 is asin(2r)<9/10, asin r<2/5, giving a sum below 29/10<pi (see NO-FOUR-RING-COMMON-POINT.md for rational Taylor verification).

A triple of indices in C_9 whose every pair has cyclic distance at most two is necessarily a consecutive triple (choose a lift with an index at zero and inspect the possible positions -2,-1,1,2). Hence a triple common point must have consecutive labels. In particular, for an intersection v of consecutive disk boundaries i,i+1, any third disk containing v can only be i-1 or i+2. This is a genuine all-other-indices elimination by capacity, not an invalid comparison of rho_j sin(delta_j) across varying radii.

Payoff: O1 (all adjacent inner crossings lie on the actual hole closure) reduces its third-disk nonmembership check to the two flanking disks. It does NOT prove the two remaining inequalities, nor make the whole hole simply connected, nor establish hub adjacency or optimal radius.

Next local domain: for three consecutive inward-root disks use half-widths t1,t2,t3<=a=asin r and angle gaps x,y; require |t1-t2|<x<=t1+t2, |t2-t3|<y<=t2+t3, x+y>t1+t3. Their actual boundary union span is S=t1+x+y+t3. Global nine-arc coverage forces S>=2pi-12a. This is a safe local relaxation containing all legal configurations, not yet asserted sufficient for completion to nine arcs. One sufficient route to O1 is to show their left pair's inner intersection cannot belong to disk 3 throughout this 5D domain (plus r). Reflection handles the other side.

Status: lead analytic proof pending independent endpoint-lift audit. Derived from the same boundary-capacity mechanism as the common-point observation of Fejes Toth; no novelty claim. Does not depend on withdrawn C784.
