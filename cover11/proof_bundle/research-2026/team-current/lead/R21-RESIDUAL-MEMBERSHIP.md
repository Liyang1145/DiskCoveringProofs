> Historical duplicate: C458 already proves this criterion, more generally for unequal positive radii. C878 retracted for duplicate registration, not mathematical error. This file is an independent derivation/control only.

# Exact residual membership at interior circle-arrangement points

Scope: finitely many radius-r disks, r>0; x strictly inside unit target D. Let U={y in D: |y-ci|>r for all i}, K=closure_D U. This resolves the degeneracy interface left explicit in C877; not a sharp radius bound.

If some |x-ci|<r, x is not in K. If every distance>r, x is in U. Otherwise let I={i: |x-ci|=r} and vi=x-ci (nonzero).

**Exact criterion:** assuming all distances>=r,
 x in K iff there is a nonzero direction d with vi.d>=0 for every i in I.

Sufficiency: x+epsilon d remains in D for small epsilon because |x|<1. For active disks,
 |x+epsilon d-ci|²-r²=2epsilon vi.d+epsilon²|d|²>0.
Inactive strict inequalities persist by continuity. Thus x+epsilon d in U for arbitrarily small positive epsilon. Weak dot products suffice even for opposite normals/tangent disks: the positive quadratic term is essential.
Necessity: take yk in U approaching x, yk!=x, normalize dk=(yk-x)/|yk-x| and pass to a convergent subsequence dk->d with |d|=1. Strict distances give 2vi.dk+|yk-x|>0, hence vi.d>=0 in the limit.

Equivalent planar test: active normals lie in some CLOSED semicircle; equivalently x is not in the (ordinary two-dimensional) interior of conv{ci:i in I}. This includes every configuration with <=2 active distinct disks, including external tangency. For >=3 active centers that surround x strictly, the weak-feasible point is isolated from the strict uncovered set and must be removed. Relative interior must NOT replace ordinary 2D interior (opposite two normals permit perpendicular escape).

C877 annulus lemma guarantees true K lies strictly inside D. In its finite enumeration, points with |x|>=1 can be discarded: K subset B(0,s), s<1. Points inside D use this exact criterion, so the K-membership issue is finite algebraic geometry, not an uncomputed topological oracle. For a split S=K intersect halfplane the membership criterion concerns K alone; a boundary point need NOT be approached from within the same halfplane, since S is defined by intersection AFTER closure.

Control cases: one active disk -> escape outward; two opposite disks -> escape perpendicular with epsilon² clearance; three equilateral active centers around x -> no escape and local punctured neighborhood covered. These distinguish strict and weak linear tests and full versus relative interior.
