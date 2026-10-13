# Rounds7–8 milestone

Original target unchanged: unconditional sharp n11 global optimality (or n14), cap999. n11 bound remains C825 r>3/8 and C249 upper .379983853119838689722261606136093214308718957. Sharp theorem OPEN.

## Structural gain (analytic, C835–C838)
1. Positive29triangle metric disk is sufficient for actual covering: flat development, canonical cyclic boundary, degree1; individual triangle coverage and circular-cap dot-product proof. No missing planar-realization constraint in simultaneous positive metric model.
2. Odd9boundary inversion determines widths from turns; common9chord scale ratios eliminateR.
3. Strict-allowanceR>r plus inward-root replacement preserves STRICT boundary coverage by exact sign identity. Forces all29triangles positive. Thus positive-model infimum equals global optimum, even for original degenerate covers. Does not approximate arbitrary formal singular assignments.
4. Intrinsic/canonical boundary vector closure removes two adjacent chord-ratio equalities.62intrinsic variables,40rows; 6rather than8circle ratios. Saved candidate rank40 numeric,3local solutions all9ratios agree2.2e-15, radius.37998385311984 and18of20radii active. No local or global optimality certificate.

Proofs: METRIC-GLUING-SUFFICIENCY.md; ODD-BOUNDARY-SCALE-ELIMINATION.md; POSITIVE-METRIC-INFIMUM.md; SIX-INDEPENDENT-CIRCLE-EQUATIONS.md.
Controls: check_metric_gluing.py (exact incidence V20E48F29/links +21numeric geometries), check_gluing_kernels.py (exact strict-root and barycentric identities), check_odd_scale.py (exact odd matrix inverse+numeric scale), q0_scale_free_shape.py (3bounded local runs). All settled.

## Completed diagnostics (NOT certificates)
Resource DP with hub angles:25side grid/180bins original dual3.1628935681, theta dual3.1567087786.1440bins3.1623824650 and3.1561776501. Controls3-state brute DP and actual candidate. Weak improvement.
All21shared-side joint11face+9switch factor, independent9sectors:350LPiterations finite-grid best3.1538092121 (LP3.1537907218), still>pi. t=0 switch branch currently onlyb=0,y-grid, omitsy=0,b>0; scope RESTRICTED finite diagnostic, no full degeneracy coverage. Full domain needs unionbranches. No further grid escalation selected.

## Rejected member audit claims
Fan report repeatedly wrong circumradius, false boundary degeneration, reversed1−cos estimate, false positive degree7penalty (regular star exactly0); subsequent correction still falsely says wrong formula coincides whenisosceles. NONE bearing. Lead FAN-DEFICIT-COORDINATES.md and exact sine-law completion control authoritative.
Metric report initially invented alternating site/switch boundary; actual boundary only9switch points. Corrections inventE47 (actual48), demand small inner-root displacement (not needed, sign exactly scales by positive root), confuse circle ratios with existing coordinate-cycle identities. Those corrections rejected; independent validation not claimed. Lead analytic proofs stand on stated exact premises and separate algebra/topology checks.

## Next obligation
Exploit homogeneous side matching to eliminate19of20local scales analytically (dual face adjacency connected with cycle rank2), then circle-shape constraints. Aim global shape lower bound, not repeat local candidate convergence. Must retain both dual-cycle compatibility equations and all max-radius inequalities; no saturationWLOG. Need check whether dimensional reduction helps certified compact-domain bounding or analytic shape inequality.
