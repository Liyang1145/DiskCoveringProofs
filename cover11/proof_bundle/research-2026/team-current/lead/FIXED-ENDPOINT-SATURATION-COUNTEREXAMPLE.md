# Fixed-endpoint internal-ring saturation fails, even near strict inward rings

## Proposition being tested
Fix radius r, a strict interior hub H, and two inward-root boundary ring centers c−,c+. Move the sole internal ring center c while preserving coverage of their intervening unit-circle gap and requiring both fan circumradii<=r. Is there always a feasible replacement c with at least one fan circumradius=r?
Answer: NO. This is a local normal-form counterexample, not a disproof of the global11disk optimum. It rules out a proposed elimination of arbitrary internal ring slack while holding hub and neighboring rings fixed.

## Exact endpoint counterexample
Take r=3/8, A=asin(3/8), q=cos A=sqrt(55)/8. Set
 H=(1/2,0), c=(q,0),
 c±=q(cos(2A),±sin(2A))=(23sqrt(55)/256,±165/256).
All three ring centers are at the canonical inward/outward branch-merger radius q=sqrt(1-r²)<1. Their unit-boundary arcs have maximal possible halfwidth A. The two endpoint arcs are [−3A,−A] and [A,3A]. Their intervening open gap is (−A,A).
Any radius-r disk preserving that gap coverage must, by closedness, contain U±=(cos A,±sin A)=(q,±r). These points have distance2r. The ONLY possible disk center at distance<=r from both is their midpoint (q,0). Thus the internal center is forced by boundary coverage alone, even without imposing inward-root restrictions.

H is strict: |H|=1/2<1-r=5/8. Both fans are nondegenerate and their common circumradius squared is exactly
 Rc²=71/220−23sqrt(55)/880.
It is strictly less than r²=9/64: equivalently sqrt(55)>641/92, whose square is valid since both sides are positive and 55*92²=465520>641²=410881. Thus both fans are strictly slack. Adjacent boundary arcs actually meet at U± and the covered tie hypothesis of C879 holds. No movement of the internal center is feasible, let alone movement to a tight fan.

## Not merely an isolated radial degeneracy
There is also an open-parameter family with ALL THREE ring radii strictly below q and with the same obstruction.
For small epsilon>0, set t=q−epsilon and beta(t)=acos((t²+1−r²)/(2t)). Define
 g=A−epsilon, alpha=beta(t)+g,
 c±(epsilon)=t(cos alpha,±sin alpha),
 c0(epsilon)=(t,0), H unchanged.
The endpoint gap is exactly (−g,g). Since beta(q)=A and beta'(q)=0, beta(q−epsilon)=A+O(epsilon²)>A−epsilon=g for sufficiently small positive epsilon. Therefore c0(epsilon) covers that gap, and all three radial coordinates equal t<q, strictly on the inward branch. They remain >1-r. The two fan radii at c0(epsilon) remain strictly below r by continuity, and neighboring arcs overlap, so actual covered ties persist.

Any possible replacement c bridging the gap must belong to the compact lens
 L_epsilon=B((cos g,sin g),r) ∩ B((cos g,−sin g),r).
Adding its two squared-distance inequalities yields
 |c−(cos g,0)|² <= r²−sin²g.
Hence every c∈L_epsilon tends UNIFORMLY to (q,0) as epsilon→0+, not only the selected c0. The endpoint centers also converge to c± above. The fan area determinants at the limit are nonzero, so both circumradius functions are continuous on a whole neighborhood. The strict limit slack then implies: for all sufficiently small epsilon>0 and ALL c∈L_epsilon, both fan circumradii remain <r. Consequently NO gap-preserving replacement can make either fan tight, even if its radial branch restriction is dropped. Feasibility is nonempty because c0(epsilon) is admissible.

This compact-uniform argument proves existence of strict-inward counterexamples without pretending sampled paths certify a continuum. It establishes a method limit: one must also vary hub/endpoints, or retain slack parameters. It gives no conclusion about whether such a patch can be part of a global11disk cover at the optimum.
