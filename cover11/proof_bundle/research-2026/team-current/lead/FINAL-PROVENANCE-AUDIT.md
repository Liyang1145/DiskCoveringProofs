# Final provenance audit after q1/C450 replay

## Completed arithmetic obligations

1. `replay_q1_final.py` ran all q1(5,7) shared-factor representatives starts 0,1,2,3. Return codes are 0 and exact interval totals are respectively 3.135371803575..., 3.116719830521..., 3.090706951898..., 3.089277744076..., each below the independent pi lower bound. The per-factor outputs include all 11 faces, 9 switches, 9 ring factors and retained subdivision upper bounds. Start 7 is controlled by `check_compatible_fraction.py`, independently represented by Fraction/Taylor support. The same run also reran the degree-3 and degree-4 Fraction controls. Manifest: `q1_final_replay.json`; logs `certify_shared_factors_{0,1,2,3}_3_final.log`.

2. The q1 class reconstruction gives (5,7) representatives {0,1,2,3,7}; reflection orbits are {0,6},{1,5},{2,4},{3},{7}. Balanced (6,6) representatives {0,2} under reflection+hub exchange. This is a finite class enumeration, not a substitute for the topology embedding.

3. C450 fixed-point kernel B replay passed all 36 contiguous e intervals, including [0,.004], [.004,.0071], [.0071,.008], and 31 intervals of width .004 through [.136,.140]. Both archived kernels cover e=[0,7/50], each with 198152 boxes, and `audit_dual_manifest.py` verifies exact endpoint contiguity, identical rational weights, and nonnegative Fourier densities. Logs: `C450_fixed_final_replay.log`, `C450_fixed_low_final_replay.log`; manifest `solo-20260922/DUAL-MANIFEST.json`. This validates finite replay provenance, not independent mathematical review.

## Mathematical interface now reconciled

The formerly pending arbitrary-cover bridge is proved in `UNRESTRICTED-PROOF-ASSEMBLY.md` §§1–6 and the corrected `r20-geometry/FINAL-TOPOLOGY-ATTACK.md`, inspected by lead. The cellulation alone does not imply hub adjacency/locality/trivalence: the hub-edge capacity argument, locality window inequality, selected-Delaunay-polygon incidence proof, witnessed refinement and empty-ear count supply these separately. Genuine consecutive polygon edges yield positive facets; artificial diagonals yield only common witnesses. Path-vertex counts give m1+m2=11-q, hence degree sum13-q. Metric graph orbits and full normalized domains were reconciled against each certificate. A member verdict is not substituted for these arguments.

C921 retains GLOBAL[P] scope. The proved full bridge maps every putative r<R* cover to that P with V(U)<=r. C922 compares its exact energy threshold with the SAME C891 root; C892 supplies exact attainment. Therefore the assembled contradiction R*<=V(U)<=r<R* now proves the unrestricted equality. Main theorem: `N11-GLOBAL-OPTIMALITY-THEOREM.md`.

The C919/C920 kernels were strengthened with all45-edge and all9-anchor upper assertions, avoiding any reliance on ordering overlapping intervals in Python max. Both fresh replays return0 with unchanged rational bounds/radii: `anisotropic_component_final_replay.log`, `relative_component_final_replay.log`. Full-vs-half hub separation notation in the chart proof was clarified; the underlying res5 formula was unchanged. These are explicit interface hardening/notation corrections, not a new numeric premise.

No identified mathematical gap remains for the stated n11 equality. Global uniqueness, n14, proof-assistant formalization and external publication are not asserted.
