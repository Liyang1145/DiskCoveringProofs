# CENTRAL-SCREEN-INDEPENDENT-AUDIT — independent read-only audit of the r20-alternative central-crescent interval screen

**Auditor**: r20-gluing lane (cline2-r23-gluing), sole writer of this directory. **No claim registered.**
**Audited object (frozen v3, re-pinned)**:
```
research-2026/team-current/r20-alternative/central_crescent_interval.py
    sha256 dcffaf1798728b570db141d3674a56c8fe643e8029314f6bbf028c03f4d27d60
research-2026/team-current/r20-alternative/central_crescent_interval.json
    sha256 22a78b344c8eccbd5be10e41b5dc54a8ada39ff0d6142a961b2f8563c683c96d
(re-pin history: 13de5bca…/c7852191… then e7095bba…/fe9ced31… are superseded by the sha above;
 the cited cross-check kernel central_crescent_audit2.py was NOT audited here)
```

**FROZEN PIN (audit final).** This audit is final for the sha pair above and the lead target box
`δ = 1/1000, ω = 1/10000` (exact rationals; the δ = 0 baseline included). My kernel and its output
are `r20-gluing/r23_central_screen_audit.py` / `.json` (the JSON records the pinned sha values).
Procedure if the audited file re-freezes: re-pin the new sha, re-run the kernel unchanged, and append
a one-row diff to the Calibration table — no other part of this audit depends on the file revision.
**Calibration row for the re-pin `dcffaf17…/22a78b34…`**: my kernel re-run gives *bit-identical*
readings at the same boxes (nominal `G = 0.154158981851 / 0.154158982454`, `ε_B ≤ 0.033062071`;
`δ=1/1000, ω=1/10000`: `G = 0.0245686655428 / 0.0245401216821`, `ε_B ≤ 0.067372319`,
`ε_A ≤ 0.061717335`) and the audited JSON's declared values are unchanged; the new records
(`delta_interval_str` = the float-valued δ, `radicand_branch_semantics` including the corrected
`k = 0` wording, `domain_declared`) are consistent with the findings below. Note the re-pinned box
uses `δ = float(1/1000) = 1/1000 + 2.08e-20` (recorded as an interval), i.e. it *contains* the exact
rational box, so the exact-rational statement follows both directly (my run) and by containment.


**Scope**: the five items assigned by the lead — (1) box endpoints truly degenerate, (2) sqrt legal
domains, (3) rational weights, (4) C879 inner-pin branch, (5) distal exclusion condition — plus the
declared bearing claims C-1…C-6, at the round conservative box **δ = 1/1000 (ring half-width),
ω = 1/10000 (r half-width)**, exact rationals, with the δ = 0 baseline.
**This is a per-box screen audit only**: no global coverage, no lower bound, no statement that the
box covers any exact root (r₀ is the saved rational upper object UB*).

## Method (fully independent; no shared helpers, no mpmath)

`r20-gluing/r23_central_screen_audit.py` → `r23_central_screen_audit.json`
(own exact-rational interval arithmetic with integer square-root bounds
`√(p/q) ∈ [isqrt(pq·S²)/(qS), (isqrt(pq·S²)+1)/(qS)]`, S = 10²⁰).

* **Variance identity** (my own re-derivation): for weights `λ_j ≥ 0, Σλ_j = 1` and any `b` in every
  disk `B(p_j, r)`: `|b − b₀|² = Σλ_j|b−p_j|² − V ≤ r² − V` with `b₀ = Σλ_j p_j`,
  `V = Σ_{j<k} λ_jλ_k |p_j−p_k|²`; hence `ε = √(r²−V)` bounds `|b − b₀|`.
* **Triangle inequality** for the distal test: `|hub − q_far| ≥ |q_far − b_B| − ε_B`, so the distal
  disk is excluded from the localisation ball whenever `|b_B − q_far| > ε_B + r`.
* **Orientation-preserving branch** decided by the sign of `det(u, b_B − A)` over the whole
  A-region (never by comparing distances — an earlier attempt of mine did that and produced a
  spurious UNDECIDED; the audited file's convention is the correct one).
* **Independent cross-check of the central faces** with my own circumcentre computation (Cohen
  formula).
* Separate symbolic check of the C879 algebra (SymPy, my own transcription).

## Item-by-item result

| # | item | independent reading | verdict |
|---|---|---|---|
| 1 | box endpoints degenerate | v3 records scalar endpoints only (`near_disk_centre_rect_str` = nested **pairs of scalars**, `G_*_dyadic_exact` = exact dyadic tuples); my box built from exact Fractions; **pass** — note the earlier (superseded) JSON stored one end as a space-joined *interval* string, which v3 fixed | **pass** |
| 2 | sqrt legal domains | 9 pin radicands `r²−d²/4` all certified **> 0** on the box; central radicand `r²−|AC|²/4` ∈ [−0.002686, +0.012114] and localisation `r²−V_B` ∈ [−0.002376, +0.004539] **straddle 0** ⇒ only the per-tuple branch semantics ("infeasible, or exclusion holds with the clamped upper-end radius") is sound; v3 now records exactly this (`radicand_branch_semantics`) | **pass (as a branch statement)** |
| 3 | rational weights | `WL`/`WB` are exact Fractions, sum = 1, non-negative; I used the same rationals in my own arithmetic; no float conversion in my evaluation | **pass** |
| 4 | C879 inner-pin branch | all 9 pins decidable over the box (unique `|p|<1`, else smaller norm); the unit-circle root satisfies `|p_out| − 1 ∈ [+2.2e−17, +4.7e−17]` at the **saved 1e17-scaled rationals** (it is exactly 1 only in the *exact chart*, not for the saved data — correcting an earlier claim of mine that came from a 12-digit display); so `|p_out| > 1` and the load-bearing hypothesis is the strict hub norm `|hub| < 1−r`; box-level: `|b_A|+ε_A ≤ 0.2138`, `|b_B|+ε_B ≤ 0.3759` < `1−r ≥ 0.619916` | **pass** |
| 5 | distal exclusion `G = lb|b_B−q_far| − ε_B^hi − r^hi > 0` | δ=1/1000, ω=1/10000: **G(face 0) = 0.0245686655427838664**, **G(face 4) = 0.0245401216821034308** (both > 0); nominal point: **G = 0.15415900198** | **pass** |

### Calibration: my numbers vs the audited file's declared numbers

| quantity | audited file (v3) | my independent value | agreement |
|---|---|---|---|
| `ε_B` upper, δ=1e-3, ω=1e-4 | 0.0673723188561722724 | 0.067372319 | 12 digits |
| `ε_A` upper, same box | 0.0617173352708297179 | 0.061717335 | 12 digits |
| `G(face 0)` lower, same box | 0.0245686655427838664 | 0.0245686655428 | 12 digits |
| `G(face 4)` lower, same box | 0.0245401216821034308 | 0.0245401216821 | 12 digits |
| branch labels | face 0 `+`, face 4 `−` | face 0 `+`, face 4 `−` | identical |
| `K_A` rectangle | [[−0.0063485534, 0.0060920146], [−0.21372204, −0.14530949]] | same to 8 digits | identical |
| `ε_B` nominal | 0.0330620706687240751 | 0.0330620706687 | 12 digits |
| `b_B` nominal | (0.0003318744, 0.3060393571) (C896) | (0.000331874427033, 0.306039357081) | 12 digits |
| distal margin nominal | 0.154159 (C896) | 0.15415900198 / 0.154159001667 | identical |
| `ε_A` nominal | 6.134e−9 | 5.905e−9 | both ≈ 6e−9; see caveat (b) |
| screen disk radii | 0.455743200142484761 / 0.455695702498030708 | `r^hi + qrad = 0.45574320014248475` (face 0) | identical |

### Checks of the declared bearing claims

* **C-1 (crescent interface, corrected direction)** — I re-derived symbolically: with the chord on
  the x-axis, `A = (−A,0)`, `C = (A,0)`, `q = (0,k)`, `q' = (0,−k)`, `k = √(r²−A²)`:
  `g_q − g_{q'} = −4·y·k`, so on the q-side half-plane (`y > 0`) `g_q ≤ g_{q'}` and
  `B(q',r) ∩ H_q ⊆ B(q,r)` — exactly the corrected direction recorded after C894's retraction.
* **C-2 (product identity / single-disk equivalence)** — my own SymPy transcription:
  `4y²(ρ² − r²) − (|h−q|²−r²)(|h−q'|²−r²) ≡ 0`; with `|q'| ≥ 1` and `|h| < 1−r` one has
  `|h−q'| > r`, hence `ρ ≤ r ⟺ |h−q| ≤ r`. The algebraic basis is confirmed independently.
* **C-3/C-4** — `G > 0` at δ = 1/1000, ω ∈ {0, 1e-4}: independently certified (table above).
* **C-5** — the `K_A`/`K_B` rectangles and the near-disk centre rectangle + radius reproduce
  (`screen_disk_radius = r^hi + qrad` recomputed).
* **C-6 (discriminating control)** — replacing `b_B` by the distal centre makes the bound negative
  (my box reading: `G_control = −ε_B^hi − r^hi = −0.4475` at δ=1e-3, ω=1e-4); the positive reading is
  therefore not vacuous.

### Guards and branch decisions in the independent kernel (requested confirmations)

The audited file's `float(D_FIX)`/`float(W_FIX)` caliber issue (its lines 415/416) does not affect
this audit: my kernel ran **both** the exact rational box (`δ = 1/1000`, `ω = 1/10000` as
Fractions) and the float-labelled box (`float(1/1000) = 1/1000 + 2.08e-20`, `float(1/10000)`);
**both certify with identical readings**, and the float box *contains* the rational box, so the
exact-rational statement follows both directly and by containment.

* **Norm-division positivity (fail-loud).** Every division by a norm is done with `idiv`, which
  raises if the divisor interval contains 0. Recorded bounds at δ=1e-3, ω=1e-4:
  * pin pairs: `min_i d² ≥ 0.201615511838 > 0` (list: 0.27814, 0.43141, 0.43141, 0.27813, 0.20162,
    0.30489, 0.35371, 0.30489, 0.20162);
  * central faces: `|c_i − A|² ≥ 0.5293974414` (face 0) and `≥ 0.5294825098` (face 4).
  No assertion fired; a zero-containing divisor would have aborted the run rather than clamping.
* **Branch selection (orientation-preserving).** `sref = det(u, b_B − A)` over the whole sound
  A-rectangle: face 0 `sref ∈ [0.3051249688, 0.3696932408] > 0` (branch `+`); face 4
  `sref ∈ [−0.3697528328, −0.3051863085] < 0` (branch `−`). Both are strictly signed, so the
  far/near assignment is decided, not guessed.
* **`k = 0` and the crossing radicand (corrected argument).** In this box
  `k = √(r² − |AC|²/4) ∈ [0, 0.1100653218]` (face 0) and `[0, 0.109968668]` (face 4):
  **`k = 0` is attained inside the box**, so the certificate is a *per-tuple branch* statement —
  but the exclusion of the `k = 0` tuples does **not** come from `ρ ≥ r` (that would not contradict
  `ρ ≤ r`), and it is **not** a "domain violation ⇒ vacuously true" argument. The correct reason:
  * at `k = 0` one has `|AC| = 2r` and the two circle centres coincide, `q_near = q_far = m`
    (midpoint of `AC`), so the C-1 crescent degenerates;
  * the product identity then reads `4y²(ρ² − r²) = (|b − m|² − r²)²`; for a **non-collinear** tuple
    the central-face constraint `ρ ≤ r` forces `(|b − m|² − r²)² ≤ 0`, i.e. `|b − m| = r` exactly
    (the hub lies *on* the radius-`r` circle about `m`);
  * the certified distal exclusion is **strict**: `G > 0` with `q_far = m` gives
    `|hub − m| ≥ |b_B − m| − ε_B > r` for every hub in the localisation ball;
  ⇒ the two requirements contradict each other, and the `k = 0` tuples are excluded **by the strict
  `G`** (not by a non-strict radius comparison). For the remaining tuples (`|AC| < 2r`, `k > 0`) the
  clamped `k ∈ [0, hi]` is used and `G > 0`.
  **Collinear tuples** (`A, b, C` collinear) have no circumradius at all; C900 handles them by taking
  the **non-collinear necessary domain of the full cover graph** as the working domain, so no
  statement here is globalised by declaring the complement vacuous. The audited file's
  `radicand_branch_semantics` should adopt the same wording (excluded by strict `G`; domain restricted
  to non-collinear `0 < |AC| ≤ 2r`).

### Central-face activity (cross-check, not needed for the screen)

With the saved hub points and ring centres, my own circumcentre computation gives
`ρ(h_A,h_B,c_0) = ρ(h_A,h_B,c_4) = r` exactly (to the data's exactness), and additionally the six
chain triples `(c0,c8,h_A)`, `(c4,c5,h_A)`, `(c1,c2,h_B)`, `(c2,c3,h_B)`, `(c3,c4,h_B)`, `(c6,c7,h_A)`
also have circumradius exactly `r`.

## Caveats / findings (none blocks the audited claims)

1. **δ is passed to the screen as `float(1/1000)`** (the file keeps `F(1,1000)` only as a
   label/record). `float(1/1000) − 1/1000 = +2.0817e-20`, i.e. the computed box is *wider* than the
   rational box; my run at the exact rational box gives bit-identical reading, and the wider-box run
   also certifies, so the conclusion transports — but the record should state which δ produced the
   endpoints (float endpoint or exact rational), as requested by the lead.
2. **`ε_A` at the nominal point is at the rounding floor**: `r² − V_A ≈ 3.5e-17`, so `ε_A` is
   `√(r²−V_A)` and moves by ~4 % for a 1e-17 change in `r²` (my 5.905e-9 vs the file's 6.134e-9 —
   same quantity, different r² rounding). At the box, `ε_A ≤ 0.0617` and the *bbox* intersection, not
   the variance bound, carries the localisation. Both readings are ≪ the margins, so nothing is at risk.
3. **Docstring/version label**: the file's docstring still reads "v2 (lead code review applied)"
   while the report's `kind` says "interval certificate v3". Cosmetic, but the pin should be the sha.
4. The file's self-disclosed earlier **unsound sqrt** in its own cross-check kernel v1 is consistent
   with what I see in the current code (clamped lower end `[√max(lo,0), √hi]`); my audit does not
   depend on that kernel.
5. I did **not** execute the audited file, and I do not certify its `mpmath.iv` internals; the audit
   is of the mathematical quantities, recomputed independently.

## Verdict

At the round conservative box **δ = 1/1000, ω = 1/10000** the central-crescent screen's five audited
items all pass by independent computation, with the distal exclusion certified as
`G ≥ 0.0245686655427838664` (face 0) and `G ≥ 0.0245401216821034308` (face 4) — in exact agreement
with the audited file's declared values, and with a discriminating negative control. The `k = 0`
tuples, present in the box, are excluded **by the strict `G` contradiction** (Guards section), not by
a non-strict radius comparison and not by a domain-vacuity shortcut; collinear tuples are handled by
the non-collinear necessary domain of the cover graph, per C900. The scope stays the single ring box;
nothing here is a global or optimality statement.

**Repro**: `py -3 -B -X utf8 research-2026/team-current/r20-gluing/r23_central_screen_audit.py`
(writes `r23_central_screen_audit.json`).
