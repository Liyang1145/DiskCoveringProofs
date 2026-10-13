# Full hub Voronoi cells must share a positive-length edge

Status: new analytic reduction pending independent review, conditional on the existing C450 fixed-R dual certificate. Scope: any eleven-disk covering of the unit disk with r<=R=19/50, in an inward-root 9-ring + 2-strict-hub representative. No general-position or zero-overlap assumption.

Input: V1,V2 are the full hub Voronoi cells. Each is a compact convex polygon, has its hub strictly in its interior, and is contained in that hub's radius-r disk (VORONOI-BOUNDARY-REDUCTION.md). The core U=B_open(0,a), a=1-2r>0, lies outside every ring disk: |c_i|>=1-r implies |x-c_i|>r for |x|<a. Therefore U subset V1 union V2 (N1), as well as the union of the two hub disks.

Suppose V1,V2 do not share an edge of positive length. Since they are convex and have disjoint interiors, their intersection has at most one point. Then the connected open disk U cannot meet both interiors: choose a path in U avoiding the possible intersection point, or use that U minus one point is connected and the two disjoint relatively closed pieces would disconnect it. Hence U is contained in one cell, say V1. Taking closure gives B(0,a) subset V1 subset B(h1,r), so e=|h1| satisfies e+a<=r, i.e. e<=3r-1<=7/50. (If r<1/3, this itself is impossible.)

## Radial facet lemma

Every positive-length facet of V1 is then a bisector with a ring site; the other hub can at most impose a redundant point contact. For a unit direction u, let h1+t u, t>0, be the first exit of the ray from V1. Compactness and V1 subset B(h1,r) imply t<=r. At that boundary point at least one genuine facet constraint from a ring site c is active, including when the ray meets a vertex. The bisector equality is

    |c-h1|^2 = 2t u dot(c-h1).

Consequently, at radius R>=r,

    |h1+R u-c|^2-R^2
       = |c-h1|^2-2R u dot(c-h1)
       = |c-h1|^2(1-R/t) <= 0.

Thus the nine ring disks, enlarged to radius R but with unchanged centers, cover the entire circle S(h1,R). They also cover S(0,1), because they already did so at radius r. All nine centers meet S(0,1) after enlargement. This conclusion does not require q>r circles or any limiting-hole argument.

## Contradiction from the existing fixed-radius dual

C450's finite dual is stronger than its original covering formulation: for each e in [0,7/50], its saved nonnegative angular weights W0,W1 satisfy, for every single radius-R disk meeting S(0,1),

    Q(c;e) < B(e)/10,  B(e)=pi(a_00+a_10)>0,

where Q is half its weighted arc coverage on S(0,1) and S(h1,R). Both inward/outward radial roots are included in the certificate, and rotation puts h1=(e,0). This is exactly M10-038-EXCLUSION.md §§3–4, independent of how the inner circle was produced. Covering both circles with nine such disks would require sum_i Q(c_i;e)>=B(e), whereas sum_i Q(c_i;e)<9B(e)/10. Contradiction.

Conclusion: V1 intersect V2 is a positive-length Voronoi edge. It is contained in int D. Degenerate vertices of degree>3 elsewhere are allowed; the conclusion does not assert trivalence or exclude skip-one ring chords.

Evidence dependencies: C450 fixed-R weights and two certified arithmetic kernels, particularly the actual per-disk capacity inequality, not merely the theorem title. Source research-2026/solo-20260922/M10-038-EXCLUSION.md §§3–4; certificate manifest DUAL-MANIFEST.json. Other inputs: N1 / hub-cell compactness and radius containment; C451 / C464 representative reduction.

Structural payoff: eliminates the entire hub-nonadjacent class without requiring ring-only triangle exclusion or a general-position perturbation. In a trivalent representative d=1 and K=k1+k2, q=13-K; finite topology reduction still needs separate care. No new radius lower bound or global-optimality conclusion is claimed.
