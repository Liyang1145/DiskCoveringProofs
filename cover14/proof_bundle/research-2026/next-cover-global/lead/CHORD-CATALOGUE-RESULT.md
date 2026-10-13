# Asymmetric chord coupling: additional458 exclusions (independent exact replay complete)

Uses the valid unequal-endpoint envelope in BOUNDARY-CHORD-ENVELOPE.md. The fixed-U safearea angle representation inherits Σα_i≥(2π−qA)/k. The exactsupportingplane bound adds nonnegative multiplier μ to all boundaryangle slopes and subtracts μK; its validity does not depend on optimizer convergence.

Bounded onepass through C1203's1588 retainedsystems, with A=.334,k=.124, gave457 additional strictnegative intervalbounds:
- q10/m3:29 of30;
- q10/m4:392 of778;
- q11/m3:36 of780.

`area_chord_catalogue.py`, `area-chord-catalogue.jsonl`, `area-chord-catalogue-metadata.json`; all proposals complete in onepass. Independent Fraction replay ALL457 bounds completed: area-chord-catalogue-fraction-replay.json.

A focused analytic refinement closes the sole remaining q10/m3 index62: rational A=.333272257, k=.123099267, tangentpointα0=2.420575 satisfy the three envelope inequalities, strictly checked in directedintervals. `area_chord_tighten.py`, `area-chord-tighten.json` gives uppermargin<−.00909878. Independent Fraction constants+plane replay `area_chord_fraction_replay.py --tight` completed successfully, area-chord-tighten-fraction-replay.json.

With both independent replays complete, the resulting necessaryclasslist has **1130=386q10/m4+744q11/m3**, with the entire q10/m3 family eliminated. This is a structural removal of the fewer-effective-sites case, not a proof ofglobaloptimality. Remaining graphsystems maystill contain nonrealizable relaxations.

Calibration: actualcandidategraph notexcluded (`area-chord-candidate-control.json`); its actual Σα≈25.553>K10. Member analytic interface audit `members/root-cc2/chord-envelope-audit/AUDIT.md` corroborates convexcornermax and concavef; its mpmathconstantchecks are numeric, notindependentinterval certification. Ignore member's extraneous assertion that ANYvalidaffineupperbound must have slope≥f'(α0): an arbitrarilyhighintercept can clearly allow slope0. This warning is notused inanyproof.
