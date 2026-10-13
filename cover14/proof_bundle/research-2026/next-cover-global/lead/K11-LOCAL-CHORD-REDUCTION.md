# k11 essential-arc branch: only short chords and disjoint ears

## Domain and reason for this note
n14 arbitrary-center unit-disk cover0<r≤U<1/3. C1142 leavesk10/k11. This note addressesk11, not via the incorrect85graph no-chord catalogue. Let the11 actual active S1 arcs be nonempty; choose a cardinality-minimal subcover ofS1. Nine disks cannot coverS1, so that subcover has10 or11 arcs. If it has10, the ten chosen disks satisfy the proved k10 disk-nonintersection theorem, but the remaining11th active disk is not automatically an inactive hub. That branch is retained as a separate gap.

If minimum size is11, every actual arc is essential, nondegenerate, and none contains another. Endpoint and midpoint orders agree; label arcs cyclically0..10.

## Theorem1: cyclic-distance≥3 disks are disjoint (essential11 branch)
Suppose disksi,j sharep. Their actual boundary arcs both lie in J=S1∩B(p,2r), an arc of length≤2asin(2r)<π. The other arcs have length≤2asinr. Endpoint order forces each intervening arc betweeni,j in the lift insideJ to lie wholly inJ. If cyclic distance betweeni,j is≥3, both directions have at least2 intervening labels, soJ contains≥4 complete arcs. The remaining≤7 arcs cover at most14asinr. Thus
π≤asin(2r)+7asinr<.73+7*.34=3.11<π,
contradiction. Constants are rationally established in `../members/structure/nochord_n14_constants.py`; no numeric inverse-trig premise.

Consequently any common-point pair of ring disks has cyclic distance≤2; any common-point subset ofring labels is contained in3 consecutive labels (a clique ofC11 squared). In particular no four ring disks have a common point, and any ring-only3site Voronoi vertex uses consecutive labels.

## Boundary ownership and dual interface
Apply same-arc inner-root normalization. Essentiality and the direct bisector proof of `BOUNDARY-OWNERSHIP-PROOF.md` still prove that each site owns a connected nondegenerate S1 arc. The k10 exclusion of3-site boundary switches needs replacement here: a boundary triple of consecutive ring sites would make the middle ownership arc have zero length, because the three connected ownership intervals meet at one point; three nondegenerate closed intervals with disjoint interiors on a circle cannot all share an endpoint. Every essential arc has a private open interval of ownership, so this is impossible. Thus boundary switches still involve exactly2owners, their bisector is transverse, and the curved dual collar construction works withN=11. Three-ring common points are allowed in the interior.

Merge hubs (there are exactly3 distinct byC1142). Interior Voronoi stars may have≤3ring sites. A star with a hub is fanned from thathub; one without hubs has exactly3ring sites and already is a triangle of3consecutive labels. All triangle witnesses have distance≤r. Curved dual embedding and the ring-cycle outerboundary do not use no-chord until imposing which ring-ring edges occur; same collar proof applies here.

Every dual ring chord joins cyclic distance2labels. It cuts off exactlyone intervening outer ringvertex, sayi, with ends i−1,i+1. The region on thatside has3boundaryvertices. Could hubs lie inside this little triangle? All11 actual arcs are essential. The middle celli has no facets crossing the chord. Nevertheless purely combinatorial geometry allows interior hubs in this triangular region! Thus distance2 chord DOES NOT by itself force the face(i−1,i,i+1) to be an empty ear. The tempting step 'distance2 chord ⇒ emptyear' is NOT proved. It would require excluding hubs in that side by the core/hub geometry or tracking hub counts on both sides. Do not use ear-removal enumeration without that condition.

## Valid combinatorial consequence without empty-ear assumption
The ring chords form a noncrossing subset of diagonals(i−1,i+1) of an11gon. Two consecutive middle labels would give crossing diagonals, so the middle-label set is independent inC11 and has size≤5. A chord cuts off a topological3-gon, but its interior may contain hub nodes. The3 hubs distribute among the regions cut by these≤5chords. This is a finite low-complexity family with total3hubs, not the old85graph no-chord list. Ring-only faces, when present, are true ears; ring-only nonfacial3cycles may enclose hubs.

## Stronger bisector observation (separate, potentially useful)
For any two distinct normalized centers with norms≤s=√(1−r²), bisector distance d=|norm_i²−norm_j²|/(2|ci−cj|) is STRICTLY<s: equal norms gived=0; otherwise d≤(norm_i+norm_j)/2<s since at least one norm<s. Hence two circle crossings are separated by>2asinr, strictly longer than any actual arc. Each pairwise winner set on an actual arc is an interval or empty, even without essentiality. Intersecting gives connected nearest-ownership arcs, possibly empty/zero-length for nonessential disks. Positive-length owners number≥10 by arc capacity and≤11. Degenerate zero-length ties require separate handling; do not claim the full regular collar for that branch without it.

## Proof level and missing implication
Theorem1 is a rigorous analytic elimination of all distant ring intersections in essential11 branch. Minimal-subcover split10/11 is global fork11. This does not prove metric infeasibility ofeither branch, nor eliminate hubs inside3-gon pockets. Next action: use3hub core triangle to constrain pocket hub allocations, or derive support/coverage bounds. A graph-only enumeration must keep hub-populated pockets.
