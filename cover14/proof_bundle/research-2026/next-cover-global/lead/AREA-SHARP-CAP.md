# Sharp boundary-cap budget; additional13 graph exclusions

Forq∈{10,11}, anglesθ_i∈[0,L] withΣθ_i=2π, letg(θ)=θ−sinθ and L=2asinU. The exact directed constants certify9L<2π<10L. The convex functionΣg on this compact polytope attains its maximum at a vertex. Any vertex has at most one coordinate strictly between0andL (otherwise move mass between two such coordinates). Thus a maximizing vertex has nine coordinatesL, oneR=2π−9L∈(0,L), and any remaining coordinate0. Consequently

    Σ(θ_i−sinθ_i)/2 ≤ Csharp=π−(9sinL+sinR)/2.

This strengthens the old chord-line bound by more than .00669374. It is already a fixed-U statement: forr≤U all actualownedangles satisfyθ_i≤L(U), so no separate monotonicity derivative is needed for this sharpercap. Outward-clip limit uses continuity first, exactly as AREA-CATALOGUE-LIMIT.md; limit angles meet the fixed-U constraints. The same supporting planes are otherwise unchanged.

`area_sharp_cap.py` evaluates the newcap and all2042 stored upperbounds in directedintervals. It excludes13 additional systems, with no optimizer rerun. Independent exact Fraction endpointTaylor evaluation ofsinR and replay of the13 newlyexcluded planes passes.

Totals now454 excluded,1588 retained:
- q10/m3:38 excluded,30 retained;
- q10/m4:154 excluded,778 retained;
- q11/m3:262 excluded,780 retained.

This supplements C1199: remaining **808 q10 +780 q11 =1588**. All previous441 exclusions remain valid; the13 additions are explicit in `area-sharp-cap.json`, independently replayed in `area-sharp-cap-fraction-replay.json`.

The separate valid viewing-angle capacity Σmin(α_i,L)≥2π (`BOUNDARY-VIEW-ANGLE.md`) was tested on the21 savedretainedq10 planes whose optimum proposals violated it. `area_perimeter_probe.py`/`area-perimeter-probe.json`: none obtained a negative bound in that bounded experiment. This is inconclusive for thosegraphs, not a disproof of the angle inequality nor of the covering target. Do not increase precision or grids merely to repeat this test; stronger metric coupling is needed.

No sharp global radius bound follows; all1588 retained systems remain necessary candidates, not proven realizations.
