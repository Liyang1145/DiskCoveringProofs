# Conditional central-fiber elimination, not joint convexity

## Object and quantifiers
Fix radius r>0, rho=1-r>0, ring data, chain-pin sets P_A,P_B, and two distinct switching ring centers c0,c4. Assume the legal-chain hypotheses of C879, so a strict hub for each chain means membership in K_X=B_open(0,rho) intersect all closed B(p,r), p in P_X. This note concerns the two central circumradius constraints; no symmetry or saturation is imposed. Domain of a: K_A, 0<|a-ci|<2r for i=0,4.

For each a and i define the two radius-r circle centers through a,ci:
 q_i^±=(a+ci)/2 ± sqrt(r²-|ci-a|²/4) J(ci-a)/|ci-a|.
Choose one as q_i, the other as q'_i. Require the following exact condition over the a-domain under consideration:
 (E) for all a in that domain and every b in K_B, |b-q'_i(a)|>r, for i=0,4.
It suffices to prove this on any rigorously enclosing localization region for K_B, uniformly over a. This is an inequality obligation, not implied by numerical candidate values.

## Exact fiber theorem
Under(E), b in K_B satisfies both central circumradius inequalities iff
 b belongs to K_B intersect B_closed(q0(a),r) intersect B_closed(q4(a),r).
Proof: let y be height of b over chord a,ci. The polynomial identity
 4 y²(Rc²-r²)=(|b-q_i|²-r²)(|b-q'_i|²-r²)
with positive second factor gives the result for nondegenerate triangles. Degenerate b cannot belong to the displayed disk intersection: on the chord line both factors coincide, so membership in the near disk contradicts strict positivity of the far factor. Conversely the original circumradius predicate already excludes degeneracies. Thus no unmentioned collinearity stratum enters this equivalence.

The branch choices may vary over different a-pieces, but must be specified and verified on each. In particular q_i(a) is NOT fixed when a moves. The joint(a,b) region is NOT thereby convex and is NOT an intersection of balls in R4.

## Eliminate b by finite planar Helly
For each fixed a, the fiber is an intersection of finitely many convex sets in R2, one open ball and the rest closed equal-radius disks. Finite Helly applies without closedness or Slater assumptions: it is nonempty iff all subfamilies of at most3 members intersect.
If m=|P_B|>=1 and the old chain K_B is known nonempty, only subfamilies containing a new central disk need checking. It suffices to list triples from the full family (smaller subsets extend to triples). For m=4 there are25 new triples:
 * one central +two old chain disks: 2*C(4,2)=12;
 * two central +one old chain disk:4;
 * open norm ball +one central+one chain disk:8;
 * open norm ball +two central:1.
For a triple of equal-radius closed disks with centers u,v,w, common intersection exists iff MEC(u,v,w)<=r. This includes obtuse and collinear triples; a circumradius-alone condition would be false.
For the open norm ball and two closed disks, let S=B(u,r) intersect B(v,r). If S is empty the triple is empty; otherwise it is nonempty iff min_{b in S}|b|<rho (STRICT). Compute the min by 0 if feasible, feasible single-circle nearest points, and feasible circle-intersection points, with coincident circles deduplicated. This uses compactness of S, not of the open-ball intersection.
Thus central coupling eliminates the two b coordinates exactly on every certified(E) region, leaving finitely many scalar inequalities in a and ring data. The remaining two-dimensional a problem is not automatically convex or solved.

## Certificate status
Analytic conditional reduction proved above. Member central_crescent_interval.py currently under repair: float-converted rational weights, endpoint handling and sqrt branch checks were identified; its earlier claimed delta bounds are NOT accepted as interval certificates. No global domain coverage or global optimum follows from this note alone.
