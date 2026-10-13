# Full eight-dimensional fixed-oracle lower bound

## Statement and scope
Use exactly the canonical51edge graph in FIXED-SWITCH-SOC-REDUCTION.md: ring sites0..8,hubs9,10,faces (9,k,k+1),k0..3; (10,k,k+1 mod9),k4..8; (9,10,0),(9,10,4). Let L=2asin(19/50),D=9L-2pi and y range over the CLOSED simplex y>=0,sum y=1. Anchors theta_i=iL-D sum_{j<i}y_j. Then V(U(y))>=R*, the exact C891 candidate radius. This is global over this P, NOT yet an unconditional claim about every11disk cover.

## Scalar certificate principle
For any normalized nonnegative edge weights alpha and any oracle feasible radius t, sum alpha_e |Xv-Xw|²<=t². Minimizing all22free coordinates gives E_alpha(U)<=t². Thus V²>=E_alpha. Our371 archived weights are strictly positive rationals. Graph paths connect each free vertex to an anchor, so the Dirichlet free block is positive definite: its quadratic form is sum positive weights times squared differences and vanishes only for the all-zero free assignment. Exact Schur elimination yields M; M1=0 and symmetric, offdiagonal Mij<=0. Setting wij=-Mij gives E_alpha=sum_{i<j}2wij(1-cos(theta_i-theta_j)). Every archived alpha and every wij rederived in replay_all_fields.py, not trusted from provenance. 371/371 exact matches.

## Whole-cell lower bounds
For fixed rational slope s in [-1,1], minimize 1-cos z-sz over the entire interval of z. Endpoints and both critical families asin(s)+2kpi and pi-asin(s)+2kpi are enumerated with outward interval evaluation. k=-3..3 covers every stored arc in (-2pi,2pi). Each resulting affine minorant is valid on the WHOLE cell; no curvature, local tangent, or sampling premise.
Rational nonnegative normalized mixtures beta of fields and gamma of minorants give an affine lower f0+c.y. For rational DBM inequalities Ay<=b, any rational lambda>=0 implies f0+c.y>=f0-lambda.b+min_i(c+A^Tlambda)_i on the simplex. All residuals retained. Stored decimal intercepts and bounds are not trusted in replay: slopes, beta,gamma,lambda re-evaluated against exact cell and interval trig.

## Domain coverage and local leaves
DBM entry[p][q] bounds t_q-t_p, t_i=sum_{j<i}y_j. Root constraints are exactly the closed simplex. Exact rational Floyd closure only adds implied constraints. Every split replaces one interval by its two midpoint halves, retaining both; thus union of children equals parent including their shared boundary. replay_closed_dbm.py checks the root, all2505 splits, exact child DBMs, unique reachability of every node, and no open leaf.
2386 leaves certify V greater than a rational threshold at least T=3799838531198387090485182/10^25>R*. 120 remaining leaves certify containment in rawtheta8-pinned local balls (12 C919 and108 C920). Direct chart formula h_k=(i-6)L-D(t_i-t6)-(theta_i*-theta6*), i=(k-2) mod9,k0..7. C891 angles recomputed from exact dyadic root box. Sum interval h_k² bounds actual Euclidean q². C919/C920 give V²>=R*²+q²/100000. No reflected or central/corner patch is used by the final tree. In replay earlier patch may be replaced by any presently certified containing patch; recorded final tree uses only directC919/C920.
Therefore each point in P lies in a leaf with V>=R*. This settles the full-P oracle obligation.

## Artifacts and reproducibility
- cosine_dbm_local920.json, sha256 6706b42690a1d99d8f49523ff0d7d82fbc688fd64a18b228512acec139aef987 (2505split,2506certified,0open;371fields).
- py -3 -B research-2026/team-current/lead/replay_closed_dbm.py: closed_dbm_replay.json/log; all2386 energy bounds +120 patches replayed, all2505splits.
- py -3 -B research-2026/team-current/lead/replay_all_fields.py: all_fields_replay.json/log;371 exact Schur checks.
- C919 anisotropic_stress_ball_certificate.json; C920 relative_stress_ball_certificate.json and RELATIVE-STRESS-BASIS.md.

## Remaining implication to human goal
Need the complete arbitrary-cover -> canonicalq0(6,7) reduction, including9+2, connected boundary ownership, hub adjacency, locality, refined dual, all other q/degree classes. Existing registered exclusions require source audit, not assumption. C892 supplies attainment at R*. This note proves neither class exhaustion nor that arbitrary oracle solutions cover the disk. No goal completion from this restricted-graph theorem alone.
