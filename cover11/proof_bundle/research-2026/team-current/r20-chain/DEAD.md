# r20-chain DEAD / invalidated (this session)

Every entry: what is dead, the root cause, and the independent control.

## D-CHAIN-9 — C880 F1 "single-arc critical phases = endpoints ∪ {arg(H−C)}" — DEAD (sign error)
* Root cause: on the arc, `|x(s)−H|² = R²+|C−H|²−2R|C−H|cos(s−arg(H−C))`; the **maximum** sits at
  `s = arg(H−C)+π = arg(C−H)` (the anti-pole), the **minimum** at `arg(H−C)`. C880 (and
  `tools/identities2.py:maxdist_arc_exact`) appended only the minimum phase, so the containment test
  accepts non-covered arcs.
* Control (independent): C=(2,0), H=(1,0), R=1, arc centre 0, halfwidth 0.5: corrected criterion and
  8001-point sampling both give 2.0, the code's phase gives 1.9378 (endpoints) while `arg(H−C)=π` is
  not even in the arc. Same 4000-case harness: code 2003/4000 violations, corrected 0/4000. The
  stored evidence `out/identities2.txt:4` itself reports 2003 — contradicting C880's "0/4000".
* Replacement: critical set = endpoints ∪ {arg(C−H), arg(H−C)}; for a max check `arg(C−H)`.

## D-CHAIN-10 — C881 F2 "triangle covered ⟺ ρ ≤ r" — DEAD (necessity false)
* Root cause: for an obtuse triangle the circumcentre lies **outside** the triangle, so `ρ > r` gives
  no uncovered witness inside `T`; the true threshold is the 3-centre covering radius `c(T) < ρ`.
* Control (independent): `T = conv{(−1,0),(1,0),(0,0.1)}`, `ρ = 5.0500`; at `r = 0.51` the three
  vertex disks cover `T` (max of `min_k|x−v_k|` = 0.5050, grid + refinement, analytic candidate
  `(1+ε²)/2`). So "ρ ≤ r ⟺ covered" is false; it is true for non-obtuse triangles.
* Replacement: for non-obtuse faces use `ρ ≤ r` both ways (the two central faces of the record object
  are acute); for general faces use `c(T)` or keep only the sufficient direction.

## D-CHAIN-11 — C882 F3(iii) "exactly one closed disk" — DEAD (boundary-intersection failure)
* Root cause: the correct criterion is the **product** identity (lead Lemma 2)
  `4y²(ρ²−r²) = (|h−p_in|²−r²)(|h−p_out|²−r²)`; "exactly one" is the strict-product subclass and
  fails whenever `h` sits on one circle and inside the other disk.
* Control (independent): `h = m+(r−k)n` (non-collinear) has `|h−p_in| = r`,
  `|h−p_out| = |r−2k| < r` (both closed disks contain h) yet `ρ = r` by direct circumradius
  computation; three explicit random witnesses in `out/audit_c880_889.txt` P3(a). Also: the excluded
  set is collinearity with `c_i,c_j` (not the perpendicular bisector), and the parenthetical "on the
  line both hold or both fail ⟹ ρ>r" is wrong in the lens region.
* Replacement: non-collinear `ρ ≤ r ⟺ product ≤ 0`; plus domain hypothesis (`|p_out| ≥ 1`,
  `|h| < 1−r`) ⟹ `ρ ≤ r ⟺ |h−p_in| ≤ r`.

## D-CHAIN-12 — C884(b) "hub A has 1 active pin / hub B 3, rigid case not realised" — DEAD
* Root cause: chain assignment and active counts mis-read (the old node order's "hub A chain
  {4,9,10,3}" is a truncation of hub A's actual 5-edge chain) and the (shift,swap) mapping mis-read
  as a label bug.
* Control (independent): the Delaunay matching is **unique** (shift,swap)=(4,1) hence `c[10]` = row 0
  = hub A; hub A has **3** active pins with all-positive barycentric weights and `V = r²−3.6e−17`
  (rigid case realised); hub B has **4** active pins spanning 170.0° < 180° (non-rigid).
  `out/audit_lead_q0_map.txt`, `out/r20_5chain_elimination.txt §C`.

## D-CHAIN-13 — C885's "cap/width type mixing" root cause — DEAD (the inequality is valid)
* Root cause of the error: `s_i = arccos(d_i/(2r))` is legitimately both the hub-covered half-arc on
  `Λ_i` and the per-edge turn bound; by the law of sines
  `ρ = |c_ic_{i+1}|/(2 sinθ_i) ≤ r ⟺ |s_i−s_{i+1}| ≤ θ_i ≤ s_i+s_{i+1}`, so `cap-sum ≥ turn-sum` is
  a correct necessary condition. The tool itself stated this FACT (`tools/cluster_criterion.py:10`).
* Control (independent): `out/r20_transfer_map.txt` P1/P2 (0/3020 map mismatches; all-tight and
  `|s_i−s_{i+1}|` constructions both give `ρ = r` in 6000/6000), and the record cross-check
  (tight edges = active pins, cap−θ = 0 or 1.391e−2).
* What stays dead: the file family `out/corner_capacity.txt`, `out/cluster_criterion.txt`,
  `out/decisive_experiment.txt`, `out/final_bounded_experiment.*` (no exclusion power; inf/skip and
  "corner form" wiring bugs; the `+1e9` line means "no split evaluable"). L1–L4 remain false.

## D-CHAIN-14 — C887/C888/C889 "exposed rim arc extent = 2 s_i (resp. π−2 arccos)" — DEAD
* Root cause: conflating the **hub-covered** arc of `Λ_i` (length `2s_i`, endpoints at angular offset
  `±s_i` from `arg(H−c_i)`) with the **exposed** rim arc, whose endpoints are the neighbouring ring
  circles' intersections (the pins) and whose length is fixed by the ring geometry.
* Control (independent): at the record object `extent = 2 s_i` only for rings 7,1,8 (hub B interior);
  rings 4,9,10,3,5,6 differ by 5e−3 … 2.5e−1 (`out/arc_account.txt` hw vs `out/clean_measurement.txt`
  s_H), and 18/18 exposed-arc endpoints match pins; independent 4e5-point-per-rim sampling agrees
  with the analytic extents to ≤9.5e−6. C889's formula additionally contradicts its own data
  (ring 7: π−2(0.433) = 2.2756 vs 0.865997) and its "two independent sources agree" is false (they
  agree only on rings 7,1,8).

## D-CHAIN-15 — C886's *retraction reason* ("label swap": hw = arccos(|H−c_i|/(2R))) — DEAD
* Root cause: the asserted identity is false (hw vs arccos agree only on rings 7,1,8), so it cannot
  explain anything; the `|p_out| = 1` reading it was meant to refute is correct.
* Control (independent): 60-digit reading on the nine edges: `|p_out|−1 = +2.62e−17 … +8.11e−17`;
  `|p_out|−(R+|hub|) > 0.10`. Only the count was wrong ("8" should be 9 edges).
  `out/r20_5chain_elimination.txt §F`. Recorded as a review event on C886.

## Method notes (transferable)
* **A criterion must not reject a certified legal object.** Run it on the certified configuration
  first; a positive "exclusion" there is a bug, not a discovery. (Three of the dead files above
  fail exactly this test.)
* **Type discipline:** every scalar in a chain argument must be labelled MAX-type (containment
  threshold, an upper bound on what a disk can cover) or MIN-type (a width the cover must span).
  Sums and inequalities may never mix the two. *(Amended 2026-09-25: `s_i = arccos(d_i/(2r))` carries
  both a MAX reading (hub-covered arc) and a legitimate turn bound — the per-edge inequality
  `θ_i ≤ s_i+s_{i+1}` is valid; label each use, do not condemn the quantity.)*
* **Sampling cannot certify a geometric identity.** Both failures this session (L1, L2) were
  statements that "held" in my sampling because the sampling was conditioned on the wrong thing.
  Use an explicit critical-point set and verify it by an independent representation. *(Amended: the
  critical set itself must be derived, not guessed — the F1 phase sign is exactly this failure, and
  it survived 4000 "passing" samples only because the harness mis-armed the check.)*
* **Do not trust a hand-derived closed form without an exact numeric check of that same form.**
  I produced two wrong forms of the cross term in `|p_out|^2` in a row (writing `2k|m·n|` as a
  function of `|m|,k` instead of evaluating `m·n` directly); only the direct dot-product evaluation
  matched the code. The final verified forms are in the report as (F5'); the intermediate wrong
  guesses are recorded here so they are not re-derived.
* **Read the index mapping out of the code, never out of the labels.** The (shift,swap) selection in
  the lead's q0 scripts is decided by a Delaunay match; guessing "which hub is `c[10]`" produced two
  opposite errors in one session (C884's readings and AUDIT-A-B's "label bug"). Print coordinates
  next to every label.

## D-CHAIN-1 — L1 "arc covered iff origin-pole covered" — DEAD (analytic counterexample)
* Root cause: the critical points of `x -> |x-H|` on a circle `Cc(C,R)` are the arc endpoints and
  the phases of `H-C`; I used the critical point of `|x|` (the origin-pole), which is irrelevant
  unless `H = 0`.
* Control (independent, by the lead): `R = 1`, `C = (2,0)`, `H = (1,0)`. The origin-pole `(1,0)`
  is in `B(H,1)` but the point `(2,1)` of the same circle is at distance `sqrt2 > 1` from `H`.
  A single explicit counterexample kills the statement; no sampling can certify it.
* Correct replacement: F1 in `SCOPED-REPORT-L1-L4.md` (endpoints ∪ phases of `H-C`), verified.

## D-CHAIN-2 — L1' "(a-R)(b-R) = 1-R^2" — DEAD (meaningless identity)
* I never derived it; the numeric check in `tools/chain_verify.py` did not even use the intended
  quantities (it printed `L-R` and `L+R` products). Discarded rather than repaired.

## D-CHAIN-3 — L2 "exposed rim endpoints of the two circles coincide" — DEAD (unproven)
* I only ever checked by sampling; there is no proof. Any use of an "angular endpoint coincidence"
  between two different circles is withdrawn.
* Correct replacement: the exposed rim arc of `Lambda_i` is computed exactly as
  `disk_interval(Lambda_i) minus the union of the partner-cover arcs`, extent `2 s_i`
  (`tools/arcs.py`), verified against 1.6M-point sampling to 1e-9.

## D-CHAIN-4 — L3 "theta >= s_i + s_{i+1} - pi/2 via Helly" — DEAD (invalid inference)
* Root cause: three disks with pairwise intersections need not have a common point; my "Helly"
  step was a non sequitur. There is no triple-disks argument in the workspace.
* Correct replacement: do not bound the turn; use the exact pair condition F3
  (`rho(c_i,c_j,h) <= R`) or the exact arc containment F1. Both are necessary AND sufficient.

## D-CHAIN-5 — L4 "chain sum telescopes to `m*pi/2 + (s_k - s_l)`" — DEAD (artefact of D-CHAIN-4)
* Root cause: summing the invalid L3 inequalities. The exact turn decomposition at the candidate is
  `theta = s_i + s_{i+1} - pi/2 + (alpha_i + alpha_{j})` with `alpha` the arc corrections; this is
  a measurement, not a derived inequality, and it carries no bound on the chain.
* Superseded by: F3 per edge + F4 for the rigidity question.

## D-CHAIN-6 — the "cap >= width" exclusion criterion family — DEAD (wrong side of the inequality)
* Files: `out/corner_capacity.txt`, `out/cluster_criterion.txt`, `out/decisive_experiment.txt`,
  `out/final_bounded_experiment.txt` (+ `.json`, `.log`).
* Root cause: `s_H(c) = arccos(|H-c|/(2R))` is a MAX-type containment threshold (it bounds the
  angle a hub disk can *cover*), while the chain imposes MIN-type width conditions (the hub must
  *span* an angular interval). Adding caps and comparing with a width mixes the two types.
  Symptom: the "best-split slack" reached `+18.6` at `R = 0.39`, impossible for a width-like
  quantity (widths are at most `2pi`).
* Control: the candidate itself is a legal cover and the criterion marks it VIOLATED at `R = 0.38`;
  a criterion that rejects a certified legal configuration is wrong by construction.
* None of those files may be cited. `tools/gap_arc.py` and `tools/true_arcs.py` are superseded by
  `tools/arcs.py`.

## D-CHAIN-7 — the "outer exclusion" convexification route — DEAD **as I stated it** (corrected)
* My statement: `|p_out| >= 1` for every legal consecutive pair, hence the chain domain is
  `⋂(B(p_k^in,R) \ B(p_k^out,R))` and is **not convex**.
* Corrected status after AUDIT A (`AUDIT-A-B.md`): the counterexample pair
  (`|c_i|=0.629029817`, `|c_j|=0.646623077`, `d=0.738073386`, `|m+kn|=|m-kn|=0.4298/0.6108 < 1`)
  **violates the interface hypothesis** of `lead/R20-CHAIN-HUB-CONVEXIFICATION.md`: the two disks'
  covered unit-circle arcs are disjoint (spans `0.2076` and `0.3479`, intersection length 0), so
  there is no common covered equal-distance point `U`; consequently `A^2+t_+^2 = 2.4465 > r^2` and
  `t_+ = 1.5200 > k = 0.0906`, i.e. the lead's Lemma-1 inequality `t_+ <= k` fails for this pair.
  **The pair is outside the domain of the convexification.** My "nonconvex" conclusion must be
  withdrawn as a statement about that domain; what remains valid is only:
  *for an arbitrary annulus pair the interface hypothesis is not automatic, and when it fails
  `|p_out| < 1` is possible.*
* Not dead, and now supported: the convexification on its own domain. On the realised chain of the
  certified object every edge has `|H - p_in| = r` exactly while `|H - p_out| >= 0.543 >> r`, and
  the interface hypothesis holds (unique covered tie), so the convex hub-set conclusion applies.
* Control for the correction: the hypothesis table in `AUDIT-A-B.md` §A (six hypotheses tested
  against the same pair with printed values).

## D-CHAIN-8 — two label/mapping errors (mine), both localised
* **My C886 text** ("`|p_out| = 1` for all eight adjacent pairs") confuses two objects:
  `arc_account.py` prints the exposed arc `(centre, halfwidth)` whose `halfwidth` equals
  `arccos(|H-c_i|/(2R))` (a distance-derived quantity), while `|p_out|` is a property of the pair.
  C886 must be read only as: for all eight adjacent pairs the exposed-arc maxima equal `R` and
  `|p_in| ∈ [0.396, 0.623]`. The `|p_out| = 1` statement is about the pins of the candidate and
  needs re-derivation before use.
* **My "H_B is outside the pin triangle" reading** was computed in my own ring order; in the lead's
  order the same conclusion holds but for a different reason (see AUDIT-A-B §B): hub A's active
  pins are `{1,3,8}` and `H_A` **is** inside their triangle (λ = the lead's weights, permuted);
  hub B's active pins are `{4,5,6,7}` and `H_B` is outside *their* hull. The earlier `[1.1195,...]`
  triple is `H_B`'s barycentrics in the triangle `{4,5,6}`, not `{4,6,8}`.
* Method note: a "label" mistake here silently changes which mathematical statement is being
  checked; every calibration must print its hub coordinates next to the weights.

## Method notes (transferable)
* **A criterion must not reject a certified legal object.** Run it on the certified configuration
  first; a positive "exclusion" there is a bug, not a discovery. (Three of the dead files above
  fail exactly this test.)
* **Type discipline:** every scalar in a chain argument must be labelled MAX-type (containment
  threshold, an upper bound on what a disk can cover) or MIN-type (a width the cover must span).
  Sums and inequalities may never mix the two.
* **Sampling cannot certify a geometric identity.** Both failures this session (L1, L2) were
  statements that "held" in my sampling because the sampling was conditioned on the wrong thing.
  Use an explicit critical-point set and verify it by an independent representation.
* **Do not trust a hand-derived closed form without an exact numeric check of that same form.**
  I produced two wrong forms of the cross term in `|p_out|^2` in a row (writing `2k|m·n|` as a
  function of `|m|,k` instead of evaluating `m·n` directly); only the direct dot-product evaluation
  matched the code. The final verified forms are in the report as (F5'); the intermediate wrong
  guesses are recorded here so they are not re-derived.

## D-CHAIN-16 — §5.10 route claims are WRONG and are withdrawn item by item (lead audit)
* **Direction error.** I wrote that maximising `Σ_int s_i` "pushes the rings away from the hub". Wrong:
  `s = arccos(|H−c|/(2r))` is **decreasing** in `|H−c|` (arccos is decreasing), so maximising `s`
  pulls rings **toward** the hub. Any optimisation statement built on the reversed direction is void.
  (The corrected single-ring analysis is in §5.11 / `out/r20_single_ring_phase_exact.txt`.)
* **Monotonicity + compactness do NOT give tightness.** "At the extremum every `|H−p_j| = r`" was
  asserted, not proved: no argument shows the maximum of `Σ_int s_i` must push every pin onto the hub
  circle; and even if an extremum were tight, that says nothing about *deforming* an arbitrary
  admissible configuration to it — I conflated extremality with deformability.
* **No convexity available.** The ring domain (annulus) is not convex and the pin map is not convex,
  so "the interior maximum is a convex problem, hence boundary-attained" is unsupported. Withdrawn.
* **`Θ ≤ cap` pointwise does not give `Θ_max = cap_max`.** The transfer cap bounds each admissible
  configuration's turn span; it does not identify the maximiser, nor does it certify that the cap is
  attained. Withdrawn as an optimisation statement (it remains a valid per-configuration bound).
* **Eliminating H is illegal when the objective depends on H.** `K ≠ ∅` removes `H` from the
  *feasibility* statement only; `s_i` and `Θ` are functions of `H`, so one may not drop `H` and then
  evaluate them. Any DP whose cost is `H`-dependent must carry `H` (or optimise over `H ∈ K`) —
  otherwise the value function is not well defined.
* **D-CHAIN-16b — the "legal chain" counterexample attack mis-states the interface.** The 3-ring
  example (hub `(0.149,0)`, `r = 0.38`, `|c| = 0.70`, azimuths `−60°,0°,+60°`) satisfies only the
  *pin–hub* condition (both pins within `r` of the hub); it is **not** a C879/chain-interface legal
  configuration (its arcs are disjoint, `32.05°` each with `27.95°` gaps), so calling it "legal" was
  wrong. What it really shows is only that the *pin–hub* condition alone does not force contiguity of
  the covered arcs — the endpoint-span identity needs the cover/contiguity hypothesis, which was
  never in doubt for a cover. Do not cite it as a chain counterexample.
* **Method note.** Both errors above have the same shape: an *inequality* or a *definition* was
  silently upgraded into an *optimisation identity* ("the extremum is tight", "the cap is attained").
  Before any optimisation claim: name the objective, its exact domain (convex or not), the attained
  configuration, and the direction of every monotone quantity involved.

## D-CHAIN-17 — bearing check on a float64 FD artifact (mine, 2026-09-25c/d)
* I verified the rank/margin claims by **loading the rigidity side's saved float64 differenced matrix**
  (`r20_J60.npy` / `r20_JA_analytic.npy`) and computing its SVD/τ there.  That matrix carries a
  finite-difference noise floor of order `1e-9`, so I reproduced the artifact instead of the geometry:
  the "rank 18 / kernel 3 / no exact positive relation / σ18 = 2.4e−9 / vacuous bound" package was all
  noise.  With the **exact-formula jet** (dps = 50, no differencing) the same object gives
  `σ18 ≈ 6e−17` (a kernel direction), exact kernel dim 5 = 2 Sym + 3 Anti (rotation slice: kernel 4,
  rank 17, `T_perp` 17-dim), and `τ = min_{λ∈Δ}‖J^Tλ‖ = 1.8e−59` with all 18 components positive —
  i.e. the exact positive-weight relation holds and the original (C1) lemma **is** applicable.
  Refuted/extended by `cline2-r23-rigidity` (exact jet) — accepted.
* **Rule**: a bearing check must use exact-formula/interval data, never a saved float64 *differenced*
  matrix; a singular value at the FD-noise scale is treated as zero until the exact jet says otherwise.
  Corollary: "independent verification" of a claim with the *same noisy artifact* is not independent.
* Retained from the episode (still valid): the lemma's algebra and the `μ = w_min·σ/2` form; the
  sqrt-corrected interface `σ ≥ 1/√(‖G_S^{-1}‖_F)`; the factor-2 `ρ`-refinement in the approximate
  variant (now only a surrogate).

## D-CHAIN-18 — over-reach: "strict" from an npy + ordinary inverse (mine, 2026-09-25e)
* I reported the Gram-sqrt cross-check on `r20_J_exact_18x22.npy` as a **"strict μ_lower = 2.81e-4"**.
  Wrong: a float `.npy` midpoint plus ordinary matrix inversion is **not** an interval computation, so
  nothing there may be called strict/certified.  Correct status: **numeric proposal** (consistent with the
  rigidity side's interval enclosure `σ17 >= 2.242496e-3`, `μ >= 1.109440e-5`, which stays the bearing object).
* Edge-count slip: the active edge set is **18 + 9*3 = 45** (the 6 slack-face edges carry alpha = 0), not 17;
  I had conflated the jet's rank 17 with the edge count.
* Also recorded: an **exact rational determinant of the float J** only proves a statement about the float J,
  not about the actual symbolic J — that class of "exactness on a float artifact" is not bearing either
  (same family as D-CHAIN-17).
* Rule: interval/rounding claims require interval inputs; a float copy may be used for a *numeric proposal*
  or an independent cross-check only, and must be labelled as such.

## D-CHAIN-19 — synthetic face indexing `(f+j)%11` was WRONG (lead's catch) + stray-file incident
* The 11 face site-lists are NONCONSECUTIVE: face edges must come from the exported `incidence_map`
  (`(kind, site, q)`: 'endpoint' -> switch q, else aux q).  `tools/r20_schur_stress_energy.py` now
  REFUSES to synthesise an incidence (guard); canonical runner is `tools/run_export_schur.py`.
  Conventions unified: `alpha = 2*r*lambda` (51, norm form); `H_ij = 2*Lam_ij*cos(theta_i-theta_j)`
  (`i != j`), `H_ii = -sum_{j!=i}H_ij`.
* Hygiene incident (mine): a failed `cd` in a stale shell made an `Add-Content -Path DEAD.md` write a
  stray `research-2026/team-current/DEAD.md` OUTSIDE my scope.  Detected and **deleted** in the same
  session; no other file touched.  Rule: never use a relative output path right after a `cd` whose
  success was not verified; check `Test-Path` and clean up immediately.

## D-CHAIN-20 — canonical radial stress corroboration (numeric proposal only)
* Inputs: `lead/radial_network_check.json` (alpha51, Lambda, H, eigenvalues) and
  `r20-alternative/socp_anchor_export.json` (`incidence_map`, `U`, `r_solution`).
* Independent path (my own graph built from `incidence_map`, NOT their tool): alpha has **45** entries
  > 1e-10, min `0.0029344412881088322`, sum `1.0`; `E(U*) = 0.14438772863179944` vs `r^2 =
  0.144387728631799` (diff `+4.44e-16`); `||Lambda - Lambda_lead||_inf = 0.0`, `||H - H_lead||_inf =
  6.9e-18`; eigenvalues `[-9.283644682e-3, -4.9e-18, 8.122024201e-3, 3.140899314e-2, 3.450130144e-2,
  5.514577275e-2, 5.876288426e-2, 7.899330407e-2, 8.291571520e-2]` — reproducing the lead's numbers
  exactly, including the single negative eigenvalue `-0.00928364468` on a non-rotation direction.
* Reading: with a *canonical* stress (all 45 weights positive, balance `2.7e-10`, angular gradient
  `5.4e-11`) the frozen-stress quadratic route is still a numeric **saddle**.  This is a numeric
  proposal about that stress family — NOT a disproof of the n=11 optimum and NOT a statement about all
  admissible stresses (float multipliers, non-interval inputs).
* Pending (budget): the bounded diagnostic — evaluate the TRUE optimised `V` along the negative-energy
  eigenvector at `eps = +-1e-4, +-1e-3` (respecting `P`), 4 solves plus a candidate recalibration, all
  recorded as **primal upper readings**, never as a strict certificate.  If `V` rises, the next step is
  an improved-alpha continuum route (stress envelope), not more pointwise sampling.

## D-CHAIN-21 — RETRACTED verdict: "path-only screen cannot fire" (my formula was wrong)
* **Withdrawn (lead's correction, 2026-09-25h)**: I wrote the `m`-edge path bound as
  `V ≥ |U_a−U_b|/(2√m)` with `E = |Δ|²/(4m)`.  Wrong.  Uniform `α = 1/m` plus the triangle inequality
  gives `Σ|x_v−x_w| ≥ |Δ|` ⟹ `Σ|x_v−x_w|² ≥ |Δ|²/m` ⟹ **`E = |Δ|²/m²`, `V ≥ |Δ|/m`**; for `m = 2`
  that is `|Δ|/2 = 0.3713` (mine was 0.2625).  Hence the verdict "path-only screen never fires" is
  **retracted**, and the path family is **unjudged, not dead** (one wrong instance never judges a
  family).  The old path-only columns in `out/r20_short_gap_screen.txt` are void.
* Corrected all-pair shortest-path table (BFS on the explicit incidence) is in
  `GLOBAL-SHORT-GAP-SCREEN.md` §2: every adjacent anchor pair has `m = 2` (bound `|chord|/2`),
  non-adjacent pairs `m = 4`; at the candidate the max bound is `0.378543` (< 0.38) and at a gap at the
  cap it is exactly `0.38` — borderline, so nothing here kills the path route.
* **Also withdrawn as unproved (mine)**: (i) "`Φ = max_α E_α` convex/homogeneous ⟹ minimum at a
  vertex" (`Φ = V²` is degree 2, `V` degree 1; convexity does not place a minimum at a vertex);
  (ii) "force form gives Lipschitz ≤ 1/2" (no norm specified, no proof).
* **Still valid**: the full-dual ascent readings (they evaluate the Schur complement directly, not via
  the path formula) — `√(max_α E_α) ∈ [0.389041206, 0.404198897]` on 27 structured extremal cases of
  `{Δ_i ≤ 0.2}` — recorded as numeric/structured-case only, not a region-wide proof.
* Scope note: the fixed-stress negative curvature (D-CHAIN-20) says nothing about the oracle `V`; `H`
  PSD ≠ local sharp remains in force.  Process rule accepted: assigned scope only, no expansion, no
  intervalisation before calibration.
