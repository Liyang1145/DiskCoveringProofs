# Ring-only quadratic hub-distance certificate (no constraint qualification)

## Object and role
Let K_A=intersection_i closed B(p_i,r_i), K_B=intersection_j closed B(q_j,s_j), subsets of R². In the C879 chain application each p/q is an inner ring intersection, corresponding radius r; optionally append center0 radius1-r to each family. These are closed relaxations of STRICT-hub feasible sets. No symmetry, saturation, nonempty interior, or normal-cone equality is assumed. Empty sets already exclude the configuration. The conclusions below are necessary for any feasible pair a in K_A,b in K_B.

## Quadratic elimination
Choose arbitrary nonnegative real multipliers alpha_i,beta_j. Put
A=sum alpha, B=sum beta, P=sum alpha_i p_i, Q=sum beta_j q_j,
T=sum alpha_i(|p_i|²-r_i²)+sum beta_j(|q_j|²-s_j²),
Delta=A+B+AB.
Assume A+B>0, hence Delta>0. Then every feasible pair satisfies

|a-b|² >= L := T - ((1+B)|P|²+2P·Q+(1+A)|Q|²)/Delta.       (1)

Proof: on a feasible pair,
Lagr(a,b)=|a-b|²+sum alpha_i(|a-p_i|²-r_i²)+sum beta_j(|b-q_j|²-s_j²) <= |a-b|².
The quadratic matrix for each Cartesian coordinate is
M=[[1+A,-1],[-1,1+B]], with positive principal entry and determinant Delta>0.
Thus inf over unconstrained a,b is T-[P,Q]^T M^{-1}[P,Q], equal to (1).
No KKT necessity, Slater, optimizer existence, or exchange of inf/sup was used. The bound survives tangent-disk singleton domains and redundant constraints. It may be negative or weak; it is never a false exclusion when evaluated rigorously.

## Central coupling interface
In q0(6,7), let D=|c0-c4| be the RING endpoint separation, d=|a-b| HUB separation. The two central triangle constraints give d<=2r and, if D>=2r, d²<=4rD-D² (lead/R20-CENTRAL-SPAN-NECESSITY.md).
Therefore
D>=2r and L>4rD-D²   imply NO full cover with these rings.          (2)
For D<2r use only L>4r². If D>4r, central span is impossible outright. Domain of the central triangles and opposite sides is as stated in the span lemma; this is not a sufficient cover test.

This is ring-only: choose rational multipliers, compute P,Q,T and Delta from ring pins and r. No optimization variables a,b remain. For moving-ring interval boxes, a lower enclosure of L and an upper enclosure of 4rD-D² suffice. Do not use a feasible primal pair as a lower bound. Since Delta>0 one may cross-multiply after checking its sign, avoiding denominator wrapping. Strict > is needed for exclusion; equality does not decide feasibility.

## Controls and method limit
1. Two disjoint equal unit disks with centers0 and(3,0): alpha=beta=1 gives Delta=3,P=0,Q=(3,0),T=7,L=1, exactly their squared distance. Minimizers a=(1,0),b=(2,0) satisfy both active constraints.
2. Coincident unit disks centers0: alpha=beta=1 gives L=-2, while true distance²=0. A negative lower bound is legal, not a disproof.
3. K_A=B((-1,0),1) intersect B((1,0),1)={0}, K_B=B((0,3),1). With equal alpha=t>0 and beta=2, L=16-36(1+2t)/(2+6t), tending to4 from below. True distance²=4. Finite multipliers need not attain the sharp bound at this non-Slater singleton. Gradient-normal-cone equality cannot be assumed: K_A's active gradients span only the x-axis while its normal cone is the full plane.

These exact rational controls are in check_hub_distance_dual.py/json. This certificate family is a necessary coarse filter and central span is slack at the current sharp candidate, so (2) alone is not expected to prove the exact optimum. Its structural role is rigorous elimination of four hub coordinates without false CQ assumptions, potentially for remote ring regions.
