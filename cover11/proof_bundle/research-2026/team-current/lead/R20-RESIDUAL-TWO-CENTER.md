# Residual two-center representation (lead analytic derivation; sharp bound still open)

Scope: fixed physical ring centers c0,...,c8, unit closed target disk D, radius 0<r<1. Let H=B(0,1-r) be allowed closed hub-center region (interior hubs of original covers lie strictly inside H; closed H is a valid relaxation and any solution still covers D). No symmetry or equal-angle assumption.

## 1. Correct residual object
U={x in D: |x-ci|>r for EVERY ring i}, K=closure_D(U). U can be relatively open at boundary. K is compact, possibly empty. The ring disks plus closed hub disks cover D iff the hub disks cover K: necessity follows by continuity from U; sufficiency because every point outside U is already ring-covered.
IMPORTANT: K is NOT automatically {x in D: |x-ci|>=r for all i}. The latter can contain isolated equality components absent from closure(U). Adding these imposes false necessary constraints. Any implementation must retain closures of genuinely uncovered cells, not blindly change > to >=.

## 2. Eliminate two hub positions into a separating line
For a unit normal n and offset t let K-=K intersect {n.x<=t}, K+=K intersect {n.x>=t}. For a nonempty compact S define
  M_H(S)=min_{h in H} max_{x in S}|x-h|^2.
Set M_H(empty)=0.
Then existence of two hubs in H covering K is equivalent to existence of n,t with both M_H(K-), M_H(K+) <= r^2.
Proof: given distinct hubs a,b, their nearest-center bisector is n=(b-a)/|b-a|, t=(|b|^2-|a|^2)/(2|b-a|). A point on the a side covered by either hub is covered by a. Tied points covered by one are covered by both. If a=b any line works. Conversely two one-center solutions cover the two closed pieces. For nonempty K choose t in [-1,1] wlog; empty sides allowed. No assumption that a proposed line equals the bisector of the reconstructed centers is needed for sufficiency.

Each inner problem is a strongly convex minimization: max_x |x-h|^2=|h|^2+max_x(|x|^2-2h.x), hence a unique minimizer on convex H. This eliminates four hub coordinates into two line parameters plus two canonical inner solutions; it does not eliminate ring coordinates or r.

## 3. Exact three-point witness representation of each inner problem
For a probability measure mu supported on S, write m=E_mu x and v=E_mu |x|^2. Convex-concave minimax on compact H and probability measures gives
  M_H(S)=max_mu [v-|m|^2+dist(m,H)^2]
         =max_mu [v-|m|^2+(max(|m|-(1-r),0))^2].
Derivation: min_h E|x-h|^2=v-|m|^2+min_h|h-m|^2; optimizer is projection_H(m). Swapping min and max is valid because the integrand is convex continuous in h and affine continuous in mu.
A maximizing measure may be chosen on at most THREE points. At minimizer h*, active farthest points A satisfy 0 in 2(h*-conv A)+N_H(h*). Thus some m in conv A has h*=projection_H(m). Caratheodory in R2 expresses m using <=3 active points. Since all active points satisfy |x-h*|^2=M, their second moment v=M-|h*|^2+2h*.m is preserved by this substitution. The resulting measure attains M.
Equivalently, feasibility H intersect (intersection_{x in S} B(x,r)) is certified/obstructed by planar convexity. An infeasible family has a finite Helly witness of <=3 sets counting H if present; hence <=3 point-disks suffice (possibly only2 plus H). Compactness of H justifies extraction from an infinite family. This is a different inference auditing the same finite-witness reduction.

## 4. What this does and does NOT give
Exact nested geometric formulation: for fixed rings and r, search n,t so both convex inner optima <=r^2. The circle union residual is global geometry, not independent face factor relaxation. Three active residual witnesses define each inner hub; active types may change.
Missing main implication: prove that EVERY legal ring placement at r<rstar and EVERY split n,t has at least one inner value>r^2. Finite witnesses vary with ring placements and split. Nothing here certifies this universal statement or candidate uniqueness. A numerical inner solve would only diagnose active regimes.

Next bounded experiment: construct candidate residual cells correctly; calibrate the two-center value and active points against the saved candidate. Then test whether a small family of witness types persists or whether this representation merely moves the complexity. Do not launch high-dimensional subdivision until that decision.
