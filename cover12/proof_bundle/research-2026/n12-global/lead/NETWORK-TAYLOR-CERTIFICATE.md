# Global network exclusion with weak negative curvature

Analytic theorem, first exact-rational-grid instance at triangle block2+3+4. No claim that this exhausts competing topologies.

Let fixed rational normalized nonnegative edge stresses define Schur energy E(θ). As in GLOBAL-STRESS-CONVEXITY.md, on the full legal9-gap simplex H_E(θ)≥M, where M has edge coefficients2q_ij T_d(1−2U²), d=cyclic ring-anchor distance. If a rational κ≥0 satisfies M+κI≥0 on all9 dimensions, then for any legal reference θ0 and any legal θ,
E(θ)≥E(θ0)+∇E(θ0)·(θ−θ0)−κ||θ−θ0||²/2.
The line segment stays within the convex legal angle domain; integrate second derivative with weight1−t. The linear term attains its minimum at a simplex vertex; the squared norm, being convex, attains its maximum at a vertex (or is bounded by the maximum of vertex values). Thus evaluating only9 vertices proves a global lower bound, not sampling.

Use exact simplex coordinates y≥0,sum y=1 and θ_i=iL−D sum_{j<i}y_j, L=2asinU,D=9L−2π. Round any numerical proposal to EXACT positive rational stresses and an EXACT rational simplex reference, then verify from scratch. Numerical optimization success is not a premise.

## First instance
Graph: triangle hub blocks2,3,4, all13 witness faces. Proposed by network_minimax.py (numeric). Certificate: network_interval_certificate.py 234 1/50; output evidence/network-certified-234.json. It proves25 Dirichlet elimination pivots>0 and9 mixed curvature pivots>0 for M+(1/50)I. The Taylor lower energy exceeds U² by an exact rational amount displayed≈0.0002926037875967. Therefore no radius≤U cover whose reduced graph has this type exists, PROVIDED the geometric cover→this witness network interface and graph indexing are verified. The matrix claim itself is full-domain, not local around the reference.

## Arithmetic
Every interval primitive rounds out to rational grid10^-45; π uses Machin16atan(1/5)−4atan(1/239) with alternating-series rational bounds; L bracket uses rigorous sin Taylor signs at rational endpoints. Trigonometric evaluation uses recurrence for Taylor terms (division only by degree products), bounded derivative remainder and exact outward arithmetic. Earlier prototype divided large powers by huge factorial intervals: grid-rounded reciprocal error made widths explode; it failed the final assertion and gave no certificate. Recurrence repaired this conditioning issue, not mathematical proposition.

## Numerical design limits
Simple alternating max stress/min angles oscillated even at known3+3+3 calibration. Changed representation to nested stress maximization. Numeric scout helper originally printed eig[1] as 'nonrotation min', which is wrong if M has multiple negative eigenvalues; no certified conclusion uses this field. Exact certificates check the FULL matrix M+κI by LDL, so all negative eigendirections are accounted for. Sharp candidate M is checked via a principal minor with exact M1=0, separately.
