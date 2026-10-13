# Five-ring intersection star excluded; at most one refined ring-only ear

Object: nine radius-r boundary disks cover S(0,1), 0<r<=R=19/50. Their center radii are >=1-r>=31/50; inward-root replacement is not required.

## Star capacity lemma

If a ring disk B(c,r) intersects each of four other ring disks, all actual boundary arcs of these five disks lie in S(0,1) intersect B(c,3R). For an outer point x in any neighboring disk centered d, |x-c|<=|x-d|+|d-c|<=r+2r<=3R; its own arc is contained too.

Put rho=|c|>=31/50 and L=3R=57/50. The intersection of B(c,L) with S(0,1) is never the full circle: rho+1>=81/50>L. When nonempty its halfwidth is

 b(rho)=acos((1+rho^2-L^2)/(2rho)).

Since L>1, the acos argument has derivative (rho^2+L^2-1)/(2rho^2)>0, so b decreases with rho. Hence

 b(rho)<=b(31/50)=acos(53/775)<151/100.

The last strict bound is certified by the alternating cosine Taylor polynomial of degree 8: cos(151/100)<=1-x^2/2!+x^4/4!-x^6/6!+x^8/8!<53/775, an exact rational comparison. Also A=asin(R)<39/100, since sin(39/100)>=x-x^3/6>19/50.

The five arcs in this one window and the other four ring arcs therefore yield

 pi <= b(31/50)+4A <151/100+4*39/100=307/100<pi,

contradiction (the final pi>3.07 is elementary, e.g. pi>3.1). Thus NO ring disk intersects four other ring disks. Each ring disk has at most three ring neighbors, including the two cyclic neighbors which necessarily intersect.

## Global consequence for refined ears

By the independently established topology reduction, any refined ring-only face is an ear {i-1,i,i+1}. TWO-TRIPLE-CAPACITY.md already excludes two disjoint-label ears. If two remaining ears share a corner ring, that ring intersects the other four rings, excluded by the star lemma. Ears cannot share an edge or adjacent skipped labels. Hence every triangulated refinement has q<=1. In particular all q=2,3,4 classes are excluded and the refined hub degree sum K=13-q belongs to {12,13}.

Equivalent graph reading: ring intersection graph is a subgraph of C9 plus a matching of skip-one chords (every ring already has its two cyclic neighbors). Under hub adjacency planarity, multiple skip-one dual chords would cut either label-disjoint ears (two-triple capacity) or a shared-corner star. Therefore the refined dual has at most one ring chord.

Scope: proved analytic finite geometric exclusion at r<=.38, conditional on the established topological reduction only for the q conclusion. The star capacity lemma itself needs neither hubs, locality, arc essentiality, nor general position, just nine boundary disks covering the circle. It does not yet exclude q=1 or establish the sharp radius in q=0.
