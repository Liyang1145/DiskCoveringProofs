# r20-chain STATUS (rev 2026-09-25b, after the C880–C889 audit)

**Read `BRIEF-2026-09-25-AUDIT-AND-CHAIN-TRANSFER.md` for the full account and all raw readings.**
Everything below is evidence-only; the claim store edits of this session are retractions
(C880/C881/C882/C884/C885/C887/C888/C889) plus one review event (C886). No new claims.

## Scope (never narrowed, never assumed away)
q0(6,7) two-hub class: unit closed disk `D`, `n = 11` congruent disks of radius `r`,
9 essential ring centres with `1-r <= |c_i| <= 1`, hubs strictly inside `B(0,1-r)`; the 9 ring
edges are served by two hubs as contiguous chains. **No symmetry, equal-angle or saturation premise.**

## Index mapping (resolved by code, not by label guessing) — RESOLVED
`lead/q0_exact_closure_radius.py` selects `(shift,swap)` by `Delaunay(c) ==
q0_graphs.json[2].faces`; the match is **unique: (4,1)**, hence `c[10] = object row 0 = hub A`,
`c[9] = row 2 = hub B`. The lead's `h = c[10]` **is** hub A (no label bug); AUDIT-A-B.md's "label
bug" attribution is withdrawn. Lead edge `(i,i+1)` = object edge `(rings[i+4], rings[i+5])`,
`rings = [4,9,10,3,5,7,1,8,6]`. Evidence: `out/audit_lead_q0_map.txt`, `tools/audit_lead_q0_map.py`.
Recomputed lead pins `[4,6,8]` = (−0.378668736514,−0.115955861337), (−0.000574102353,−0.529412040784),
(0.378416356737,−0.116776858375), all at distance `r` from `c[10]` (≤2.8e−16); weights
`(0.459977730563, 0.080044539274, 0.459977730163)` reproduce hub A to 6.8e−18; `V-r² = −3.63e−17`
(60-digit).

## VALID (this session)
* **F1′ single-arc extremum (corrected)**: max of `|x−H|` on an arc is attained at an endpoint or at
  the phase `arg(C−H)` (anti-pole); `arg(H−C)` is the **minimum**. Corrected test 0/4000 vs 8001-point
  sampling (the old criterion had 2003/4000). `out/audit_c880_889.txt` (P1).
* **F2′ triangle/circumradius (corrected)**: identity `Σλ_k|x−v_k|² = ρ²−|x−O|²` holds;
  "covered by the 3 vertex disks ⟺ ρ ≤ r" holds only for **non-obtuse** triangles (obtuse
  counterexample: ρ=5.05 covered at r=0.51). `out/audit_c880_889.txt` (P2).
* **F3′ two-root product criterion (corrected)**: non-collinear h: `ρ ≤ r ⟺
  (|h−p_in|²−r²)(|h−p_out|²−r²) ≤ 0`; with `|p_out| ≥ 1` and `|h| < 1−r` this is `⟺ |h−p_in| ≤ r`.
  "Exactly one closed disk" fails at circle-boundary intersections (explicit h = m+(r−k)n).
  0/20000 product-vs-ρ mismatches. `out/audit_c880_889.txt` (P3).
* **F1″(arcs)**: exposed rim arcs are bounded by the neighbouring ring circles at the **pins**
  (18/18 endpoints match, 4e5-point-per-rim sampling control ≤9.5e−6); the hub-covered arc of `Λ_i`
  has extent `2 s_i`, and `extent = 2s_i` for the exposed arc only when they coincide (rings 7,1,8).
  `out/audit_c880_889.txt` (P4).
* **C879 calibration (corrected)**: hub A (row 0) = the 3-active-pin rigid instance (weights all
  positive, `V=r²−3.6e−17`); hub B (row 2) = 4 active pins in an arc of 170.0° (<180°),
  `H_B ∉ conv`, non-rigid. `out/audit_lead_q0_map.txt`, `out/r20_5chain_elimination.txt §C`.
* **Outer roots (C886 reading confirmed)**: all **nine** edges have `|p_out|−1 = +2.6e−17…+8.1e−17`
  (60-digit) and `|p_out|−(R+|hub|) > 0.10`; the interface hypothesis holds with equality.
  `out/r20_5chain_elimination.txt §F`.
* **Elimination identity / deviation bound**: `Σλ_k|h−p_k|² = |h−h_λ|² + V(λ)`,
  `K = ⋂_λ B(h_λ,√(r²−V(λ)))`, `diam K ≤ 2√(r²−Vmax)`, `K=∅` if `Vmax>r²`; chain-level uses below.
  0 violations in the containment/separation/empty/diameter tests. `out/r20_5chain_elimination.txt §A`.
* **5-chain reading (hub A) — NUMERIC, not certified**: 3 of 5 pins active (`|H_A−p_k|−r ≤ 1.7e−16`),
  `λ>0`; idealised case (`V=r²` exactly) ⇒ hub = circumcentre of the active pin triangle; at the
  rounded record `V(λ*)−r² = −3.63e−17` (60-digit) so the content is the conditional numeric bound
  `|h−h_λ*| ≤ 6.03e−9` (not "hub forced", not a certified `diam ≤ 1.21e−8`). The 4-chain (hub B) is a
  lens of diameter `0.066124` (= the bound, attained). `out/r20_5chain_elimination.txt §C`.
* **Central coupling**: switch rings = rows 5,6; each switch-ring exposed arc has one end tight for
  each hub; the two central faces `(h_A,h_B,row5/6)` are acute with `ρ = R` (tight, ≤1.7e−16).
  Ring-determined hub pair: `h_A` = circumcentre of the 3 active pins (matches record 1.3e−16);
  `h_B` = solution of the two central `ρ=R` equations (matches record 5.4e−15).
  `out/r20_5chain_elimination.txt §D/§E`.
* **Per-edge transfer map (exact; scope per lead)**: hypotheses `d_i ∈ (0,2r)` strict, `θ_i ∈ (0,π)`
  (non-collinear, `ρ` defined); then `ρ ≤ r ⟺ |s_i−s_{i+1}| ≤ θ_i ≤ s_i+s_{i+1}` with the **upper**
  endpoint always non-degenerate and tight, the **lower** endpoint tight only when `> 0` (if
  `s_i = s_{i+1}` it is `θ_i = 0`, collinear, `ρ` undefined). 0/3020 mismatches; all-tight and
  `|s_i−s_{i+1}|` constructions give `ρ=r` in 6000/6000. Closed-cycle corollary (all spokes ≤2r):
  `Σ s_i ≥ π`. Record cross-check: tight edges = active pins. `out/r20_transfer_map.txt` (P1–P3).
  The all-tight construction is an **abstract-fan** statement; it does not by itself prove tightness
  of the extremum over legal unit-`D` ring chains (annulus bounds `s_i` by
  `arccos((1−r−|H|)/(2r))`).
* **Fixed-endpoint local variation (OUT OF C464 DOMAIN — cannot be a normal form)**: with endpoints
  fixed the total boundary span is an **identity**; the earlier tested family used `|c_L| = |c_R| = 1 >
  L* = sqrt(1−r²)` and the old "annulus `[1−r,1]`" as the domain, so its affirmative answer (a
  straight-segment deformation to exactly one active pin, `sup_F max(ρ1,ρ2) = r` for
  `α ∈ {22°,…,44°}`) applies **outside** the C464 inward-root domain and is not a global normal form.
  `out/r20_fixed_endpoint_variation.txt`. Canonical-domain answer = §5.6 (negative).
* **O5 CLOSED NEGATIVE — audited counterexample (canonical domain, strict inward included)**:
  `r = 3/8`, `A = asin r`, `q = cos A = sqrt(55)/8 = L*`, `H = (1/2,0)`, `c = (q,0)`,
  `c_± = q(cos2A, ±sin2A)`. The gap is `(−A,A)`, its closure contains `U_± = (cos A, ±sin A)` with
  `|U_+ − U_-| = 2r` exactly ⟹ `B(U_+,r) ∩ B(U_-,r) = {(q,0)}`: the internal centre is **forced by
  coverage alone** (branch-free), both fans strictly slack (`Rc² = 71/220 − 23√55/880` exactly,
  `r − Rc = 0.015980763`). Strict-inward family `t = q−ε`, `g = A−ε`, endpoints at `±(β(t)+g)`:
  `β(t) > g` for sufficiently small `ε` (second-order decrease; **no explicit threshold claimed** —
  the lead's correction: the Taylor remainder is unbounded, and `ε(3√55−23ε)/32` is only a truncated
  series; the exact closed form is `r² − sin²(A−ε) = −(23/32)sin²ε + (3√55/64)sin2ε`), the bridging
  set `L_ε` shrinks to `(q,0)` uniformly, and continuity of both fan circumradii from the strict limit
  margin gives uniform strict slack for sufficiently small `ε`.
  `out/r20_o5_strict_inward_audit.txt`, `tools/r20_o5_strict_inward_audit.py` (sympy-exact audit).
  Consequence: the fixed-endpoint saturation normal form fails; the ledger must carry slack
  parameters or vary the hub/endpoints. Local normal-form failure only — no statement about a global
  11-disk cover.
* **Endpoint shape derivative under central-preserving hub variation (lead task; CORRECTED)**: family =
  `h_A` fixed, one switch ring moved by `t·d`, `h_B(t)` on the branch of **both central faces tight**
  (re-solved hub B matches the record to `1.8e−16`). Base: `M_A := r² − Vmax(A-chain) = +3.5e−17`
  (**numerically** zero on the rounded object — not a proof of exact zero), `M_B = +1.093e−3`,
  rotation slacks `0.027818` (A) and `2.8e−15` (B). Local derivatives at `t = 0`: radial-outward on a
  switch ring decreases **both** margins at rate `≈0.23`; tangential directions have one margin up and
  the other down. **No zero-tolerance and no finite-allowance statement** (first derivative + unbounded
  remainder cannot bound an excursion). **The rotation slack ledger is NOT monotone** (slackB ≈ 0
  identity-like; derivatives O(1)–O(10) with direction-dependent signs) — not to be repackaged.
  Candidate for the global argument: the pair `(M_A, M_B)`, whose active boundary direction is
  radial-outward. `out/r20_endpoint_shape_derivative.txt`, `tools/r20_endpoint_shape_derivative.py`.
* **WITHDRAWN — min-h "support selector"**: for `K = ⋂_j B(p_j,r)`, `h_K(u) ≠ min_j(p_j·u + r|u|)` in
  general (only `≤`). Calibration (lead): two unit disks at `(±1/2,0)`, `u` vertical: `min = 1` but
  `h_K = √3/2`. Correct: **dual/infimal convolution** `h_K(u) = inf{Σ_j(p_j·u_j + r|u_j|) : Σu_j = u}`
  (Slater) and **finite boundary candidates** (arc points with normal `u/|u|` ∪ pairwise circle
  intersections, no CQ) — both give `√3/2` with **split** dual weights; correct shape derivative
  `∂h_K/∂p_j = u_j^*` (FD-verified on the calibration). Record bodies: `K_B`, `u=(0,1)`: true
  `0.339101` vs min-h `0.685613`. `out/r20_dual_support.txt`, `tools/r20_dual_support.py`.
* **Fiber infeasibility / separation certificates (valid; signs fixed per lead)**: **(F)** if
  `Σ_j u_j = 0` and `Σ_j(p_j·u_j + r_j|u_j|) < 0` then `⋂_j B(p_j,r_j) = ∅` — exact one-line proof,
  **no CQ** (dual ray for primal infeasibility); sharp: two unit disks at distance `d` give `2 − d`
  (0 exactly at tangency). **(N) Necessity (analytic)**: for ANY finite family of closed disks with
  empty intersection such `u_j` always exist — diagonal strong separation in the product space
  (`P = ∏B_j` compact convex, `D` = diagonal subspace; `P ∩ D = ∅` ⟹ `Λ|_D = 0` i.e. `ΣΛ_j = 0` and
  `sup_P Λ = Σ(p_j·Λ_j + r_j|Λ_j|) < 0`); equal radii: `⋂B(p_j,r) ≠ ∅ ⟺ Rc(p) ≤ r`. Criterion is
  complete (ray ⟺ empty), no CQ. **(S)** `|u| = 1`, `u·q − r > h_K(u)` ⟹ `K ∩ B(q,r) = ∅`; sharpest
  `u = (q−x*)/|q−x*|` ⟹ **separation margin `dist − r`** (>0) and **Farkas objective `r − dist`** (<0)
  — never "Farkas = dist − r"; no attained dual optimum assumed (strict gap ⟹ approximate certificate).
  **(H3)** universal exact 3-disk witness `u_j = λ_j(m − p_j)` (`λ ≥ 0`, `Σλ_j = 1`, `Σλ_j p_j = m`,
  active `|m−p_j| = Rc`; acute ⟹ `λ` = positive barycentrics of the circumcentre), exact value
  `Rc(r − Rc) < 0` when `Rc > r`. **Exact non-equilateral rational control**: `p = (0,0),(2,0),(1,2)`,
  `m = (1,3/4)`, `Rc = 5/4`, `λ = (5/16,5/16,3/8)`, `r = 6/5` (all pairs meet, triple empty):
  `Σu_j = (0,0)` exact, objective `= −1/16 = Rc(r−Rc)` exactly (sympy). Control at the record object:
  hub A `dist(q,K_A) = r` to 1e−16 for all four central fan disks (all four central faces saturated;
  margin/objective `~1e−16` = boundary), hub B one disk tight, others `0.377102 < r`; nothing fires.
  **Limit**: crescent/fan (non-convex) part not Farkas-reachable — needs vertex/containment analysis.
  `out/r20_fiber_farkas_certificate.txt`, `tools/r20_fiber_farkas_certificate.py`.
* **Closure/CQ caveat (lead's correction)**: the infimal-convolution identity
  `h_{⋂K_j} = inf{Σ h_{K_j} : Σu_j = u}` holds only for the **closed** inf-convolution; without a CQ
  it is not an equality. No weight is rested on it: `h_K` is computed from **finite boundary
  candidates** (direct geometry, no duality) and the certificate comes from the **CQ-free
  product/diagonal separation** (F)/(N).
* **Independent MEC/active-set audit of the central triples (r20-geometry file read, not modified)**:
  exact criterion for equal-radius disks (unique MEC centre `m`, MEC radius `Rc`):
  `⋂B(p_j,r) = ∅ ⟺ Rc > r`; `= {m} ⟺ Rc = r`; interior `⟺ Rc < r`; `m` optimal ⟺
  `0 ∈ conv{(m−p_j)/|m−p_j| : active}` (max gap ≤ 180°), which equals the singleton test **only under
  saturation**; the circumcircle is the MEC only in the **acute** branch (else diameter). All 35
  triples of `{central0, central4, 5 fan pins}` audited: geometry's four flagged triples are the only
  ones with `Rc − r` numerically zero (`−6.09e−17, −4.58e−17, −4.31e−17, −2.73e−17`, circumcircle
  branch) and for each the MEC centre coincides with hub B to ~1e−16. For
  `(central0, central4, pin(9,10))`: `Rc − r = −4.31e−17`, active = all three, positive barycentric
  `λ = (0.321374, 0.321374, 0.357253)`, `|m − hub B| = 8.5e−17`, cyclic gaps `(112.47°, 123.77°,
  123.77°)` ⟹ **max gap 123.77°, not 189°** (the 189° figure belongs to geometry's other fan-A/4-pin
  gap list — their own correction note says so); objective `Rc(r−Rc) = +1.6e−17` = 0 to rounding ⟹ no
  infeasibility. All readings **numerical** (`|Rc − r| ~ 1e−17` is not exact equality).
  `out/r20_central_triple_mec_audit.txt`, `tools/r20_central_triple_mec_audit.py`.
* **MEC uniqueness justification corrected (lead)**: `max_j|x−p_j|` is NOT strictly convex (a single
  norm is linear along rays); use `max_j|x−p_j|² = |x|² + max_j(|p_j|²−2p_j·x)` — strongly convex plus
  a max of affine = strictly convex, unique minimiser, equivalent to the unsquared problem.
* **Chain extent as an optimal-control problem (lead task)**: hub eliminated by the running-region
  state.  Domain `1−r ≤ |c| ≤ L*`; pin `p_i = inner root(c_i,c_{i+1})`; **state `(c_i, K_i)`** with
  `K_i = ⋂_{j≤i}B(p_j,r)` (so `MEC(p_1..p_i) ≤ r` ⟺ `K_i ≠ ∅`, ring-only, no hub variable);
  **transition** `K_{i+1} = K_i ∩ B(p_{i+1},r)`; DP exact by the principle of optimality and **all
  slack branches covered** because `K` is carried as a region (never a point/equality) — the lead's
  FIXED-ENDPOINT-SATURATION state (pinned ring, both fans slack) is admissible; no tightness normal
  form assumed.  Extents: **(E1)** covered-arc measure — under contiguity the interior rings cancel
  exactly (`span = (az_last+β_last) − (az_first−β_first)`; record 227.733°); **(E2)** turn span
  `Θ(H) ≤ s_1+s_{m+1}+2Σ_int s_i` (record `Θ = 3.818062137`, cap `3.845880194`, slack `2.782e−2`),
  so the DP reduces to maximising `Σ_int s_i` s.t. `K ≠ ∅`; prefix-MEC walk
  `−3.800e−1, −2.394e−1, −9.985e−2, −1.759e−2, −4.580e−17` (last = tight circumcircle triple).
  **ROUTE RETRACTED (lead audit) — see DEAD.md D-CHAIN-16/16b.** Withdrawn item by item:
  (i) `s = arccos(|H−c|/(2r))` is **decreasing** in `|H−c|` ⟹ maximising `Σ_int s_i` pulls rings
  **toward** the hub (my "away" was backwards); (ii) monotonicity + compactness do **not** give
  tightness, and extremality ≠ deformability; (iii) the annulus and the pin map are **not convex** —
  no "convex problem" claim; (iv) `Θ ≤ cap` pointwise does **not** give `Θ_max = cap_max`;
  (v) `K ≠ ∅` eliminates `H` from *feasibility* only — an `H`-dependent objective may not drop `H`;
  (vi) the 3-ring "legal chain" example satisfies only the pin–hub condition (arcs disjoint), **not**
  the C879/chain interface ⟹ withdrawn as stated.  What remains is only the *definitional* framework
  (domain / pin map / running `K` / transition) plus raw record readings.
  `out/r20_chain_extent_oc.txt`, `tools/r20_chain_extent_oc.py` (route withdrawn).
* **Fixed-H single-ring exact phase optimisation (new, §5.11)**: for fixed hub `H`, fixed inward radius
  `rho = |c|`, gap endpoints `v_1 ≤ v_2`, with `a := β(rho) = arccos((1+rho²−r²)/(2rho))`:
  (P1) covering the gap ⟺ covering its endpoints (antipode outside the gap since `rho ≥ 1−r`);
  (P2) **admissible phase interval** `Φ = [v_2 − a, v_1 + a]`, nonempty ⟺ `v_2 − v_1 ≤ 2a`;
  (P3) `|H−c(φ)|² = |H|² + rho² − 2rho|H|cos(φ−ψ_H)` (min at `ψ_H`, max at `ψ_H+π`);
  (P4) since `s` decreases in `d`: `s_max` at the **closest phase** (projection of `ψ_H` onto `Φ`),
  `s_min` at an **endpoint phase** (or `ψ_H+π` if inside) — all closed-form;
  (P5) two gaps ⟹ intersection of the two intervals (empty / single phase / interval), listed exactly.
  Calibrations: O5 config (`r = 3/8`, `H = (1/2,0)`, `rho = √55/8`) gives `a = A` exactly and
  `Φ = {0}` (the pinning reproduced exactly); record `rho = 0.700870` (`β = 0.280822`): gap `0.4 rad`
  ⟹ `Φ = [−0.080822, 0.080822]`, `s_max = 0.383073159272` at `−0.080822`, `s_min = 0.288862878919` at
  `+0.080822`; two-gap: overlapping → interval, touching → single phase `[−0.319222, −0.319178]`,
  far-apart → empty.  `out/r20_single_ring_phase_exact.txt`, `tools/r20_single_ring_phase_exact.py`.
* **Single-chain span bound + slack judgement (span route PAUSED as non-sharp)**: (T1) φ-free per-ring
  upper bound `s_i ≤ arccos(||H|−rho_i|/(2r))`; (T3) `Θ ≤ s_1^max+s_{m+1}^max+2Σ_int s_i^max` (upper
  bound only, not attainable); (T4) `Σ_all 2β(rho_i) ≥ 2π`.  At the saved candidate: (T3) bound
  `6.003071810957` vs actual `Θ = 3.818062137086` ⟹ slack `+2.185` (**does not vanish**); (T4) global
  slack `+4.43e−16`, chain-union slack `+4.44e−16` (**vanishes**; arcs tile = the closure dual's
  existing total-width slack).  Conclusion: span-bound route **not worth continuing** as a dual-active
  constraint.  `out/r20_chain_span_bound.txt`, `tools/r20_chain_span_bound.py`.
* **Gradient-margin lemma + σ interface (accepted as analytic; object check corrected twice)**:
  with 18 active gradient rows on the rotation slice, exact kernel 4, `rank 17`, `T_perp` 17-dim, and
  the **exact** positive-weight relation (C897: `Σw_i g_i = 0`, `w ≥ w_min > 0`, `Σw = 1`):
  `max_i ⟨g_i,t⟩ ≥ μ‖t‖` with **`μ = w_min·σ/2`** (no LP, no CQ).  Interface (sqrt corrected per lead):
  `σ = √λ_min(G) = 1/√(‖G^{-1}‖_2) ≥ 1/√(‖G^{-1}‖_F)`; via a 17×17 Gram minor
  `σ ≥ 1/√(‖G_{S,S}^{-1}‖_F)`, `μ ≥ w_min/(2√(‖G_{S,S}^{-1}‖_F))`.  r23-rigidity's square-minor
  interval route gives `σ17 ≥ 1/‖M^{-1}‖_F ≥ 2.242496e−3` (pivot guards) and candidate interval
  `μ ≥ 1.109440e−5`.  **Artifact withdrawn (see DEAD D-CHAIN-17)**: my intermediate "rank 18 / kernel 3 /
  no exact relation / vacuous bound / v18 soft direction" package came from the **float64 FD matrices**
  (`r20_J60.npy`), whose noise floor is ~1e-9; the exact jet (`r20_physical_kkt_kernel.py`, dps 50)
  gives `σ18 ≈ 6e−17` (kernel), kernel 5 = 2 Sym + 3 Anti, and `τ = min_λ‖J^Tλ‖ = 1.8e−59` with all
  components positive ⟹ (C1) **is** applicable; (C2) is only its numerical surrogate (with the
  factor-2 `ρ` refinement).  `out/r20_gradient_margin_bound.txt`,
  `out/r20_gradient_margin_rank_check.txt` (the latter's rank-18 reading is the artifact — do not cite).
  **Over-reach withdrawn (DEAD D-CHAIN-18)**: the Gram-sqrt cross-check on the float npy
  (`1/√(‖G_S^{-1}‖_F) = 5.674473e−2`, ratio 0.9713) is a **numeric proposal only** — npy + ordinary
  inverse is **not** interval, so no "strict μ_lower" may be claimed; the bearing object stays
  r23-rigidity's interval enclosure.  Also: **active edges = 18 + 9×3 = 45** (6 slack-face edges have
  α = 0), not 17 (that was the jet's rank); and an exact rational determinant of the *float* J proves
  only a statement about that float J, not about the symbolic J.
* **Network quadratic stress / Schur energy (lead task; mechanism derived, numeric check awaiting the α export)**:
  graph nodes 31 = 9 switches `U_i` + 11 sites + 11 aux; edges 51 = 18 endpoint + 33 face (active 45).
  (D1) any primal feasible ⟹ `Σα_e|X_v−X_w|² ≤ r²` (trivial, Σα = 1); (D2) the content is
  `E(U) = min_{free}Σα|·|² = ΣΛ_{ij}⟨U_i,U_j⟩` with `Λ = L_bb − L_bf L_ff⁺ L_fb` (pseudoinverse;
  never invert the full block; zero-α edges handled per connected positive component), Λ a weighted
  boundary Laplacian with off-diagonal ≤ 0; (D3) candidate force balance ⟹ free sites harmonic ⟹
  `E(U*) = R*²`; (D4) `min_{8角}E(U) ≥ R*²` ⟹ main (r ≥ R*), candidate = equality; (D5) angular
  Hessian `d_i d_j E = Λ_{ij}cos(θ_i−θ_j)` (i≠j), `d_i²E = −Σ_{j≠i}…` ⟹ signed Laplacian, far pairs
  `cos < 0` ⟹ block positivity insufficient ⟹ PSD mod rotation must be decided numerically.
  `tools/r20_schur_stress_energy.py` (ready; waits for alternative's 51-α + C, Z, U export,
  looks in `r20-chain/in/switch_alpha.json`), output `out/r20_schur_stress_energy.txt`.
  Verdict rule: negative eigenvalue on the rotation quotient ⟹ frozen-stress bound not globally sharp,
  only the route fails (report, no more sampling).
* **Fixed-switch SOCP audit (interface received from r23-gluing; audit NOT yet executed)**: 9 fixed
  `U_i ∈ ∂D` (8 angles mod rotation); inner variables = 9 ring + 2 hub centres (22) + 11 free aux
  `z_f` (22) + scalar `r`; constraints 18 = `|c_i−U_i| ≤ r` and `|c_i−U_{i−1}| ≤ r`, and 33 = `|c−z_f| ≤ r`
  for the 11 faces × 3 sites (a **free** aux point per face, NOT a circumcentre — the circumcentre form
  is non-convex); no variable elimination, inner convex problem + outer 8-angle parameterisation;
  primal `min r`, any real q0 cover induces a feasible point via the face vertices ⟹
  `SOCP_min(U) ≤ r_cover`; tie-derivative identity (symbol-verified by gluing):
  `∇_c ρ = A·u`, `A = ⟨U−c',t⟩/⟨c'−c,t⟩`, `∇_{c'}ρ = B·u'`, `B = ⟨U−c,t⟩/⟨c−c',t⟩`, `A+B = −1`
  ⟹ weights `(−A,−B)` positive convex combination, **½/½ only in the symmetric special case**
  (asymmetric instances: 0.2060/0.3074/0.4156/0.4487/0.5203/0.5703).  Candidate readings: 9 switches all
  tight, 11 faces all acute, 9/11 tight (7 fan + 2 central, matching C897), slack fans `(5,6,9)`,`(7,8,9)`
  (`Rc = 0.378831172`), chord bound `max|U_{i+1}−U_i|/2 = 0.378542769`.  My planned audit: recompute
  18+33 slacks/active sets with my finite-candidate machinery, check the reduction's injectivity/
  relaxation, verify the tie-derivative weights independently, and flag which steps bear weight.
* **Stress-envelope alignment (2026-09-25g, with r23-stress; no action assigned to chain)**: my 9×9
  Cartesian Schur angular Hessian for the **single** `α_radial` (contains the rotation kernel and the
  negative `−9.28e−3`) is **not in conflict** with the envelope route: `H_0` positive definiteness is
  required only on `K := ker(G^T) ∩ rot^⊥` (lead's `dual_envelope_check.json`: G nonzero singular values
  `[.7451,.5786,.3646,.10391]`, `dim K = 4`, projected eigenvalues `[.00742708,.01752846,.04230869,
  .07123306]` all positive), the negative direction lying outside `K` and being handled by switching `α`
  inside the family.  Recorded: **`H_0|_K ≻ 0` is a content-bearing assumption, not automatic**.
  Also recorded from r23-stress's v2: their earlier "no third-order term" claim is **withdrawn** — the
  quadratic form `F_α` is quadratic only in **Cartesian** `U`; in the angular graph `H_j` carries
  `2(∂²U/∂θ²)S_{α_j}U*` plus an explicit `O(|δ|³)` remainder (cos/sin global derivative bounds), so the
  angular inequality must carry that cubic remainder explicitly.  Chain does not supply `A*`/divergence
  bases (not on this side) and does not re-instantiate the envelope unless the lead assigns it.
* **GLOBAL SHORT-GAP SCREEN (lead assignment; my path-formula verdict RETRACTED 2026-09-25h)**:
  `GLOBAL-SHORT-GAP-SCREEN.md` + `tools/r20_short_gap_screen.py` → `out/r20_short_gap_screen.txt`.
  Object: `V(U)² = max_{α∈Δ₅₁} E_α(U)` (Slater dual); every feasible α gives a lower bound.
  **Correction**: the `m`-edge path bound is `V ≥ |Δ|/m` (uniform α + triangle inequality; `E = |Δ|²/m²`),
  not `|Δ|/(2√m)` — hence my earlier "path-only cannot fire" verdict is **withdrawn** and the path family
  is **unjudged, not dead**.  Corrected all-pair shortest-path table (BFS on the explicit incidence):
  adjacent pairs `m = 2` (bound `|chord|/2`), non-adjacent `m = 4`; at the candidate max = `0.378543`
  (< 0.38), at a cap gap exactly `0.38` (borderline).  Also withdrawn as unproved: "convex/homogeneous ⟹
  min at vertex" (`Φ = V²` is degree 2) and "force Lipschitz ≤ 1/2".
  Still valid (independent of the path formula): the **full-dual ascent** readings
  `√(max_α E_α) ∈ [0.389041206, 0.404198897]` on 27 structured extremal cases of `{Δ_i ≤ 0.2}`
  (`L = 0.779593`, `m = 0.046445`) — numeric, structured-case only, margins `0.009–0.024`.  The
  fixed-stress negative curvature says **nothing** about the oracle `V`; no fixed stress is used.
  Process: assigned scope only; no experiment expansion; no intervalisation before calibration.

## INVALID — do not cite
* L1 "arc covered iff origin-pole covered"; L1' "(a-R)(b-R) = 1-R²"; L2 "exposed rim endpoints of the
  two circles coincide"; L3 "Helly gives θ ≥ s_i+s_{i+1}−π/2"; L4 "chain sum telescopes to
  mπ/2+(s_k−s_l)" — all as before (C885 retraction keeps these; only its "cap/width type mixing"
  root cause is corrected: `θ_i ≤ s_i+s_{i+1}` is a valid inequality).
* `out/corner_capacity.txt`, `out/cluster_criterion.txt`, `out/decisive_experiment.txt`,
  `out/final_bounded_experiment.*` and `tools/gap_arc.py`, `tools/true_arcs.py` — still non-citable
  (implementation/wiring + criterion weakness; cluster_criterion's `+1e9` line means "no split
  evaluable", not "candidate violated").
* **Any use of `out/r20_fixed_endpoint_variation.txt`'s affirmative deformation as a normal form** —
  its domain `|c| = 1` is outside the C464 inward-root domain.
* C880 (F1 phase sign), C881 (F2 "necessary and sufficient"), C882 (iii) ("exactly one closed disk"),
  C884 (b) (active counts + "rigid case does not occur"), C887/C888/C889 (exposed-arc = 2s_i /
  π−2arccos) — **retracted this session**; replacements in `BRIEF-...md §1` and in the claim store.
* C886's *retraction reason* (label swap via hw = arccos(|H−c_i|/(2R))) — refuted; the `|p_out| = 1`
  reading stands (nine edges, not eight).

## Open
* **O1** Interval/proof-grade certification of the §3/§5 equalities (`V−r²`, `ρ−R`, `|H−pin|−r` are
  ~1e−16): currently 60-digit numeric.
* **O2** Glue the ring-determined hub pair (circumcentre + 2 central equations) into the global
  bound: is the reduction "rings ⟹ hubs" a *counting* statement (e.g. a 2π rotation-number
  inequality `Σ s_i ≥ π` per fully-served cycle) or only a local certificate?
* **O3** Coverage-type functionals do not extremise at pin equality (2-ring family, §5);
  in the canonical domain the interior ridge disappears (β increasing up to `L*`), so the extremum
  sits on `|c| = L*` — decide whether the global argument can be carried by the turn/rotation-number
  functional.
* **O4** `Vmax > r² ⟹ chain infeasible` as an exclusion criterion: quantify over legal ring data
  (needs the domain hypothesis or the product branch).
* **O5** **CLOSED (negative)** per §5.6: the fixed-endpoint saturation normal form fails, even
  strictly inward, on a compact family. Remaining sub-question: the *whole-cover* version (hub and
  endpoints also allowed to move) is untouched — does a valid normal form exist there?

## Repro
```
cd research-2026/team-current/r20-chain/tools
py -3 audit_lead_q0_map.py ; py -3 audit_c880_889.py ;
py -3 r20_5chain_elimination.py ; py -3 r20_transfer_map.py ;
py -3 r20_fixed_endpoint_variation.py ; py -3 r20_canonical_tight_boundary.py ;
py -3 r20_o5_strict_inward_audit.py
```
