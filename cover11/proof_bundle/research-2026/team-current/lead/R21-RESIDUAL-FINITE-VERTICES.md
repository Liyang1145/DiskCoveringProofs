# Split residual finite vertices — historical assembly, not new structural gain

Historical audit found C456 already gives moving-line finite convexification, C458 gives the full weak-normal closure criterion (even unequal radii), and C466 gives a STRONGER annulus bound for inward roots. Therefore C877 is an explicit assembly/generalization in presentation, not a new research advance for the target n11 class. C878 was retracted as duplicate registration of C458, NOT disproved. R21 derivations remain useful independent representations/controls. Use original claims in downstream dependencies. Fixed-ring auxiliary two-center at R=.38 is already C462 with exact bracket (.37996450,.37996454]; do not redo it.

Prerequisites: definitions K=closure_D{x: all |x-ci|>r}, H and split K± from R20-RESIDUAL-TWO-CENTER.md. Assume finitely many DISTINCT ring centers, each |ci|<=s<1, and their radius-r closed disks cover unit boundary. No symmetry or exact contact assumption. Equal coincident disks can first be deduplicated; genuine n11 reduced centers are distinct.

## Annulus lemma
For any unit e choose i with |e-ci|<=r. For t in [s,1], f(t)=|te-ci|² has derivative 2(t-e.ci)>=2(t-s)>=0. Thus f(t)<=f(1)<=r² and the whole annulus s<=|x|<=1 is ring-covered. Consequently K subset B(0,s), strictly away from target boundary. For n11 inward-root configurations s=sqrt(1-r²)<1, so assumptions hold.

## Vertex set
Fix a line L={n.x=t}. For one side S=K intersect {n.x<=t}, let V consist of:
(A) all pairwise ring-circle intersection points in S;
(B) all intersections of L with a ring circle that belong to K.
This is finite (at most 2*C(9,2)+2*9=90 pre-filter points for n11). Equality/inequality tests alone do NOT decide K membership at singular circle configurations: must use closure of strictly uncovered cells. The same construction applies to the other side.

Claim: if S nonempty then V nonempty, and for every h in R²,
  max_{x in S}|x-h|² = max_{v in V}|v-h|².
Hence constrained one-center problems on S are exactly finite-point problems on V; in particular a disk contains S iff it contains V, and S subset convex hull V. This does NOT say two disks containing all unsplit residual vertices cover the residual: the dividing line adds new vertices B.

## Proof by exclusion of nonvertex maxima
A maximum exists by compactness. Suppose x is not in V. Since K is away from target boundary, only ring circles and L can constrain local directions.
1. x not on any circle and not on L: because x in K, all circle distances strictly >r; an open neighborhood lies in K and S. The strictly convex squared-distance function cannot have a local maximum in an open set.
2. x on L but no circle: an interval along L through x lies in S. Restriction of squared distance has second derivative 2, so no local maximum.
3. x on exactly one distinct ring circle and not L: all other inequalities are strict nearby. Locally K is the exterior of that circle (including the circle), and side constraint is inactive. Let x=c+r u. Restrict to circle x(theta)=c+r(cos theta,sin theta). Squared distance = |c-h|²+r²+2r(c-h).u.
At a local circle maximum, either c=h (constant) or u=(c-h)/|c-h|. In both cases the outward radial derivative equals 2(x-h).u=2r or 2(r+|c-h|)>0. Moving outward is locally admissible, contradicting maximality. If circle restriction is not locally maximal, already an admissible tangential improvement exists.
Every remaining case lies on at least two circles, or on a circle and L; hence lies in V. Tangencies/multiple circles are retained, never discarded. This covers all cases, proving claim.

## Structural gain and missing implication
For fixed ring centers,r,L the ENTIRE residual continuum has been eliminated from each hub optimization. Inner optimum has at most 3 witnesses by R20 convex dual. The remaining variables are ring centers,r and L; V changes at explicit circle-arrangement and line events. No sharp global covering inequality follows without controlling those outer variables. This is an exact representation, not a proof n11 optimal or of rho2=R for the saved candidate.

Independent check to perform: explicit circular-hole example with three disks, compare maxima computed from circle vertices against dense residual samples; finite sampling only calibrates implementation, analytic proof above carries continuum assertion. Degenerate K membership must be tested separately (equilateral isolated equality trap).
