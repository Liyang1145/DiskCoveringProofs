# Lead inference audit of finite-reduction v2 and exact checker

Object: nonempty finite labelled C⊂D, duplicates allowed; R(C)=max_D min_i|x-c_i|. Sources read in full: members/finite-reduction/PROOF-finite-reduction.md v2; QE-interface.md v2; py/exact_checker.py. Main theorem is mathematically accepted after these checks; numerical battery is not used as its proof.

## Independent inference reconstruction
On the boundary, a maximum either has two distinct nearest sites (thus a pair bisector-circle point), or a unique nonzero nearest site (smooth tangential maximum is the antipode), or an origin nearest site (value1 and global upper1; a boundary of its closed plateau ties with a nonzero site, or all sites are0 and (1,0) works). Interior maxima require0 in the 2D interior of the convex hull of vectors x-c_i over nearest sites: otherwise a separating/support vector increases every active squared distance by a nonnegative linear term plus a strictly positive quadratic term, while the finite inactive margin persists. Three affinely independent active sites then give a circumcenter inside D. Thus the finite list is complete, including zero/duplicate/collinear cases, without sampling or a Voronoi general-position premise.

Distinct centers in D have midpoint strictly inside D, so their bisector crosses S1 twice. This guarantees positive pair radical s=4|c_j-c_i|²-(|c_j|²-|c_i|²)². All circumcenters must be filtered by |x|≤1; omitting the filter is still sufficient for a positive coverage test but destroys equivalence and explains huge historical exterior-candidate values.

## Algebra checks
B: antipode x=-c_i/√s leads to a+b√s≤0 with a=2 c_i·c_j, b=1+|c_j|²-r².
C: n=c_j-c_i,N=|n|²,H=|c_j|²-|c_i|², x=(Hn±√(4N-H²)n⊥)/(2N). Multiplying distance²-r² by N gives N(1+|c_k|²-r²)-H n·c_k∓√(4N-H²)n⊥·c_k.
D: v=(H u2_y-J u1_y,J u1_x-H u2_x),Δ=det(u1,u2), x=v/(2Δ); denominator-cleared membership |v|²≤4Δ² and coverage |v-2Δc_m|²≤4Δ²r² are correct for either sign of Δ.
For s>0, a+b√s≤0 is decided exactly by signs and comparison a² versus b²s. Code cases exhaust b=0; a≤0,b<0; a>0,b>0; a≤0,b>0; a>0,b<0. Equality handling is correct.

## Instrument safety requests before replay/registration
The original exact checker silently continued on s≤0 and did not enforce C⊂D. This cannot occur on its checked C182 input, so it does not invalidate that reported evaluation, but must fail loudly for a reusable theorem interface. Requested explicit nonempty/C⊂D/r≥0 or rho≥0 checks, assertion on s≤0 for distinct centers, and nonzero failure exit on caught C182 errors. No increased bisection budget requested. Code will be rerun after these changes; this note is not an assertion that a run has already occurred.

## Scope
The finite theorem eliminates the continuum x∈D in FIXED-configuration coverage and gives a quantifier-free polynomial/radical-sign predicate. It does not eliminate the existential24-dimensional center search or prove that a symmetric candidate is optimal. ≤365 candidates is an upper bound, not a guaranteed cardinality. 299 grouped checks include pairs with two branches. The fixed point is essential only to guarantee the all-zero-center case.

## Completed replay milestone
Member applied requested instrument guards/error exits and reran11 controls plus8 domain checks. Lead separately ran `criterion(load_c182(),U)` after patch: A/B/C/D all true,184 retained interior circumcenters. Output `evidence/exact-sign-lead-replay.json`. This is an exact Fraction sign calculation, not an interval enclosing zero. C932 registers the analytic theorem; C934 registers the revised same-object upper bound and supersedes historical C182.
