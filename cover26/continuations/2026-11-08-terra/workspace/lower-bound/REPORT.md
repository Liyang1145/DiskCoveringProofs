# n=26: unconditional lower bounds and necessary families

## Scope and status

This note proves an unconditional numerical bound for arbitrary centers, and proves necessary restrictions for a putative strict improvement over any specified radius U. It does **not** prove the n=26 optimum or the exhaustiveness of any graph catalogue. All disks are closed, centers may be arbitrary, repeated, or degenerate; no symmetry or genericity is assumed in the original covering.

## A strict numerical bound

Let r be the radius of any 26-disk covering. Then

    r > sqrt((1 + 2527/11000000)/26) > 0.19613866.

Proof. If r>1/5 the claim is immediate. Assume 0<r≤1/5. A disk meeting the unit circle covers an arc of half-angle at most asin(r)<1/4: the first inequality follows by minimizing (1+d²-r²)/(2d) over center distances d>0, and the second from sin(1/4)>1/5. Empty or singleton arcs have half-angle zero. The arcs cover the unit circle, so their half-angles sum to at least π>3.05. If at most three have half-angle ≥1/10, their sum is less than 3/4+23/10=3.05. Hence at least four have half-angle ≥1/10.

For such a disk, put the midpoint of its boundary arc at (1,0), and its center at (d,0). Since its covered arc contains angles ±1/10, the quadratic distance inequality gives

    d ≥ cos(1/10) − sqrt(r² − sin²(1/10)).

Its protrusion beyond the tangent line x=1 is h=r+d−1. With sqrt(r²−z)≤r−z/(2r), sin²(1/10)>99/10000, 1−cos(1/10)≤1/200 and r≤1/5, we get h>79/4000>19/1000. The disk contains a rectangle outside the unit disk of area h²/2: choose x in [1,1+h/2] and |y|≤h/2. Indeed h≤2r, so its corners lie inside the disk. Thus each of the four disks loses area strictly greater than (19/1000)²/2 outside the unit disk. Therefore, using subadditivity,

    π ≤ sum area(D ∩ disk_i) < 26πr² − 722/1000000.

As π<22/7, this yields the displayed bound. The inequalities use elementary Taylor estimates and 3.05<π<22/7. No disjointness of those four disks is claimed or needed: the losses are subtracted from the sum of individual intersection areas.

## A small-cover lower bound

For every integer k≥7,

    r_D(k) ≥ sin(π/(k−1)).

For contradiction suppose s is strictly smaller. A disk covers at most 2 asin(s) of the unit circle, so covering it requires at least k disks. Consequently all k disks meet the circle. Since s<sin(π/6)=1/2, every such center has norm at least 1−s>s, so none of these disks contains the origin. This contradicts coverage. The conclusion also holds for fewer than k disks by padding with repeated disks.

## Actual boundary-intersecting disk count: necessary ranges

Let a putative cover by at most 26 radius-r disks satisfy r<U<1/2. Define B as the number of disks that actually meet the unit circle and I as the number that do not. This includes redundant disks and is **not** the count of Voronoi boundary-owning cells. The boundary arcs of these B disks cover the unit circle and each has length at most 2 asin r. Therefore

    B ≥ ceil(π/asin r).

Every disk that meets the circle has center norm at least 1−r, so it misses the open disk of radius 1−2r around the origin. The I remaining disks cover that open disk and, by closedness and finiteness, its closure. Scaling gives

    I ≥ k+1 whenever r/(1−2r) < sin(π/(k−1)), k≥7.

Consequently B≤26−I. If U≤sin(π/7)/(1+2 sin(π/7)) = 0.23230072488870077..., then I≥9 and B≤17. If U≤sin(π/13), then B≥14; hence B∈{14,15,16,17} under both inequalities. If U≤sin(π/14), the stronger B≥15 applies. All equalities at U are allowed because r<U.

For the inherited certified U=1/(√6+√3)=0.23914631..., the k=7 inequality gives I≥8, while U<sin(π/13) gives B≥14. Thus 14≤B≤18 and I≥8 for the actual boundary-intersecting disks. Because a boundary-intersecting disk may own no boundary point, these numbers alone do not establish the same upper bound for a Voronoi-dual boundary count. Relating the two requires a separately proved minimality and connected-boundary reduction; it is unpaid here.

The independent area condition gives I r²≥(1−2r)² by restricting the I disks to the inner disk.

## Precise remaining obligations

1. Establish a certified candidate upper bound U, including a finite cover certificate, and verify U against the above thresholds by rational or interval arithmetic. If U exceeds the k=8 threshold, do not use I≥9.
2. Independently verify the connected-boundary and general-position reduction including Voronoi cells without boundary arcs, both types of private point, and the triangulated dual with no hidden general-position hypothesis on the original cover. Record every interface needed by the graph generator.
3. Enumerate all permitted planar triangulated disk types at each B and I≤26−B with a completeness proof; padding from m<26 requires a separately proved extension that preserves every imposed necessary constraint. No catalogue or enumeration is claimed here.
4. Supply rigorous infeasibility certificates covering every enumerated type at radius below the candidate, or prove a stronger common analytic inequality. A local stationary point, finite samples, and an optimization solver's failure are not global certificates.
5. Verify the candidate's exact radius and its cover, and connect it to the global lower-bound proof. The present 0.19613866 bound is far from a sharp proof.

## Independent replay

Run `python verify_bound.py` with a standard Python 3 interpreter. The script checks all rational inequalities in the numerical proof using exact fractions and reports the exact squared-radius bound; trigonometric facts are supported by alternating Taylor estimates explicitly checked in the script. Its displayed decimal is informational, not part of the certificate.

## Stronger unconditional bound by two nested boundaries

In fact, without any Voronoi construction, for all 26-disk covers,

    r_D(26) ≥ sin(π/9)/(1+2 sin(π/9)) > 0.203091.

The middle quantity is approximately 0.20309498890063094. Let t denote that quantity, and assume r<t. Elementary estimates give t<0.204<sin(π/15), so at least 16 of the disks must meet the unit circle: otherwise their total circular arc length would be at most 15·2 asin(r)<2π. Every disk that meets the unit circle has center norm at least 1−r and thus misses every point with norm <1−2r. The remaining at most 10 disks consequently cover the open disk of radius 1−2r and, because their union is closed, also its closure. Scaling would give a 10-disk unit-disk cover of radius r/(1−2r)<sin(π/9), contradicting the independently proved k=10 case of the small-cover lemma. This argument counts all disks meeting the boundary, including redundant disks, and requires no genericity or assumptions about their centers.

`verify_bound.py` checks by exact rational Taylor estimates that sin(π/9)>34201/100000 and sin(π/15)>207/1000, and that the first lower bound implies the displayed decimal bound. It also checks sin(π/9)<343/1000, sufficient to deduce t<0.204. For the estimates, 333/106<π<22/7 and the alternating Taylor error bounds apply on the interval in question.
