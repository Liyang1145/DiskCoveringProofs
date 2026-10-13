# Ring-only inequalities and quantitative hub localization

Depends on C879 (whole-chain hub convexification); all centers/lengths physical. This specializes elementary variance to the chain pins and eliminates hub location in useful necessary inequalities. No global sharp bound is asserted.

For a chain choose any nonnegative weights lambda_i summing1 on its inner pair-intersection pins p_i. Define
 b=sum lambda_i p_i,
 V=sum_{i<j}lambda_i lambda_j |p_i-p_j|².
Then for every h,
 sum lambda_i|h-p_i|²=V+|h-b|².
Therefore a feasible chain hub MUST satisfy V<=r² and
 |h-b|<=sqrt(r²-V).
This is exact even if h is not the unconstrained minimum-enclosing-circle center. Weights may be fixed rational numbers, or any explicitly defined nonnegative functions of the ring variables; no smoothness is needed. It holds for arbitrary positive/flat-free chain geometry covered by C879, not only a local candidate.

If V=r² then h=b is forced, without assuming saturation of all faces. If V<r², this gives a quantitative localization, not an equality assertion. For two chains, choose weights independently, giving bA,bB and epsA,epsB. Then
 |hA-hB| >= max(0,|bA-bB|-epsA-epsB).
Combined with R20-CENTRAL-SPAN-NECESSITY.md, when D=|c0-c4|>=2r a purely ring-only necessary condition is
 max(0,|bA-bB|-sqrt(r²-VA)-sqrt(r²-VB))² <= 4rD-D².
If VA>r² or VB>r² already exclude the ring configuration. No claim this last central-span relaxation is sharp.

## Triple exact branch
For three noncollinear pins p,q,s with all three angles strictly acute, the one-center minimum squared radius is
 rho²=|p-q|²|q-s|²|s-p|² / [4 cross(q-p,s-p)²].
Thus they can be covered by one unconstrained radius-r disk iff
 |p-q|²|q-s|²|s-p|² <=4r² cross(q-p,s-p)².
Acuteness is the three inequalities (q-p).(s-p)>0 etc. At right/obtuse or collinear cases the longest-side diameter condition is the correct branch; never apply circumradius criterion to an obtuse triple without qualification. The constrained hub norm and other pins still need checking for sufficiency for the CHAIN.

## Candidate calibration / mechanism
check_r20_chain_variance.py uses the saved rational ring coordinates and float r=.3799838531198388. Five-edge fan (hub10 of q0 mapping) has active pin indices4,6,8. Candidate barycentric weights are approximately (.45997773056,.08004453927,.45997773016), all positive. V-r²≈-1.94e-16; pins form an acute triple. This is NUMERIC evidence that equality of one ring-only triple constraint pins this hub at the candidate. It is not an exact sharp equality, as the input is the rational upper-cover object, not an isolated exact optimal solution.

Rational weights (459977731,80044539,459977730)/10^9 give an everywhere-valid necessary inequality V<=r², regardless of their candidate tightness; their exact tightness is neither expected nor used. The variance identity is algebraic; numeric checks are calibration only.

Main unresolved implication: show every legal nine-ring boundary configuration below exact candidate radius violates a chain feasibility inequality or the remaining central coupling. This remains a continuum problem. The present gain is replacing nine triangle-radius constraints by two convex hub domains plus explicit ring-only obstructions and localization; no fixed finite target subset is being substituted for the original disk.
