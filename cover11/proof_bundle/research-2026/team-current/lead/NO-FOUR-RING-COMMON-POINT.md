# No four boundary disks have a common point, for r<=19/50

Status: analytic exact proof; review pending. Object: nine equal radius-r closed disks collectively cover the boundary of the unit disk, r<=19/50. Centers can be anywhere. Hubs and full disk coverage are NOT needed. Claim: the intersection of any four of the nine disks is empty (in the whole plane, not only D).

Suppose p belongs to four disks. Each of those four disks is contained in B(p,2r), by the triangle inequality. A disk of radius s<1 covers an arc of the unit circle of angular measure at most 2 asin(s). This follows by minimizing (1+d²-s²)/(2d) over the center distance d>0, whose minimum is sqrt(1-s²). At d=0 there is no boundary intersection. Tangencies and disjoint disks cover angular measure zero.

Consequently the boundary covered by the four disks together has angular measure at most 2 asin(2r). Each of the remaining five disks covers at most 2 asin(r). Subadditivity of angular measure gives the necessary inequality

    pi <= asin(2r)+5 asin(r).

But asin(19/50)<2/5 and asin(19/25)<9/10. Both are exact rational Taylor consequences: for 0<x<1, sin x >= x-x³/6, so sin(2/5)>=146/375>19/50 and sin(9/10)>=1557/2000>19/25. Sine is increasing on [0,pi/2], containing both arguments. Hence the right side is strictly below 9/10+5(2/5)=29/10<3<pi, contradiction.

Payoff: under C451, no full Voronoi vertex lying in D and satisfying coverage can have four ring sites among its nearest centers: its common distance is <=r, which would give a forbidden common point. In particular a degree>=4 ring-only Voronoi vertex is excluded. This does not exclude three ring disks meeting, or triple ring Voronoi vertices. It does not prove trivalence, hub adjacency, or optimal radius.

Independent negative-domain control: the proof depends on nine total boundary disks; replacing five remaining disks by six loses this coarse strict inequality and is not covered. The radius threshold is a sufficient range, not claimed sharp. This is an elementary specialization of the common-point boundary-capacity observation in Fejes Toth 2005 p364 (locally extracted in fejes-text.txt L200 onward), not a novelty claim.
