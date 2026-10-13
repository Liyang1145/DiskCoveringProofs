# Q10-LOCAL-CELL-INTERFACE (v3, second repair) — q10 production anchors ↔ the C1324 literal cell

Member `dirichlet-cut-audit-cc2`. Artifacts: `q10_local_cell_interface.py` (import-safe), the
certificate `q10-local-cell-interface.json` (schema `member-q10-local-cell-interface/v3`), this note.
No lead file written; batch not run. **Not bearing C1324** — a membership/cut tool for the q10 side.
The first repair (DEAD.md line 65) and the second round of lead-reported defects are both recorded.

## 1. Second-round defects (lead inspection) and their fixes

| defect | fix | evidence |
|---|---|---|
| `cumulative_literal_arcs` cached on `tuple(sigma)` = the KEYS 0..9 for a dict, identical for every map, and ignoring `A` — the four-map comparison was not independent | cache **removed**; `psi` recomputed from `(A, sigma)` on every call | the four maps now genuinely differ in `sigma` (`[2,1,0,9,8,7,6,5,4,3]`, `[7,8,9,0,1,…]`, `[7,6,5,…,8]`, `[2,3,4,…,1]`) yet still give the same `psi`; that agreement is now a *structural* fact — the reference arc pattern is palindromic (`0.66716, 0.56549, 0.67627, 0.56549, 0.66716` in both directions) — not a caching artifact |
| `forward_arc_iv` silently clamped `hi = min(ch[1], .999)` — unsound | clamping deleted; **assert** `0 <= (chord/2)_lo <= (chord/2)_hi < 1`, raise otherwise | all ten adjacent chords pass the assertion |
| literal cyclic branch not certified, and "the arc-sum interval contains 2π, therefore the sum is exactly 2π" is false in general | `certify_literal_cycle` now uses **discrete winding**: anchors are unit vectors by C1167's algebraic construction (not by any residual interval); positive adjacent cross products make every turn a **minor counterclockwise arc in (0,π)**, so the total turn along the closed cycle is `2πk` for an integer winding number `k`; every arc is > 0, hence `k ≥ 1`; the computed interval is asserted to lie inside `(π, 3π)`, which forces `k = 1`, and only then is the sum the exact single turn `2π`. `arc_sum_contains_2pi` is kept as a **consistency check only** | `cross_positive = True`, `cross_min = 0.535833912699049…`, `arc_sum ≈ 6.283185307179586 ∈ (π, 3π)`, `winding_number_pinned = 1`, `cycle_valid = True` |
| `cell_test` did not check the cycle, and an empty vertex set would have passed vacuously | `cell_test` now (i) **refuses an empty vertex set**, (ii) asserts `sigma` is a permutation of the anchors, (iii) asserts the literal cycle is certified | guards are in the source and exercised by the run |
| `graph_maps` scanned every catalogue index | restricted to **index 879** explicitly, raising if that run is absent | still returns the four exact isomorphisms |
| `cell_cuts` picked the wrong interval ends and mislabelled the inner rule | two families with correct outward directions: **`outer_necessary`** takes the interval extremes (`jL - psi_hi - eps` down, `jL - psi_lo + eps` up; satisfied by every configuration of the true cell) and **`inner_sufficient`** the reversed pair (satisfying it puts a configuration inside the cell for every `psi` in its interval). The inner family is explicitly marked **not** a global feasibility cut: violating it does not make a configuration infeasible | anchor 2: outer `[0.119897593923224396, 0.119899593923224398]`, inner `[0.119897593923224396, 0.119899593923224385]`, the families separated by 2.09e-18 (the `psi` interval width) |
| certificate held floats | **bearing** fields are exact rationals rounded outward to 30 decimals, printed as `p/10^30`; `cell_test`'s per-vertex/per-anchor margins are internal float diagnostics, not the bearing statement | `root_worst_abs_delta_exact`, `synthetic_worst_abs_delta_exact`, `prefix_cuts`, `psi` intervals and `reference_angle_deviation_upper` are `p/10^30` strings; the pass booleans are exact |
| synthetic vertices' domain membership assumed | construction capped by `floor(Q*L_lo/(2pi_hi))/Q` and every vertex **checked**: certified lower end of each `d_m` ≥ 0 and `sum d = (10, 0, -1)` exactly | `all_vertices_d_nonneg_certified = True`, `sum_is_exactly_10L_minus_2pi = True`, `delta = 1e-12`, `cap = 0.10763298…`, min certified slack `3.499e-9` |

Kept from the first repair: true interval `(px,py)` enclosure (rigorous interval arithmetic on the
dyadic root box, no midpoint/pad; unit-circle residual interval `±9.55e-19`); owner-pair
correspondence (verified bijective, identical to `lead/q10_anchor_domain_diagnostic.py` for all four
maps); one unwrapped branch shared by all vertices; `phi_j = j*L − sum_{m<j} d_m`; no `atan` anywhere
(arcs from chords via `2 arcsin(chord/2)`, incremental powers, geometric tail; Machin π as an interval
of width 4.8e-58; `L` interval width 1.07e-96).

## 2. Independent checks and calibrations (current run)

* **Reference angles.** The unwrapped `psi` reproduces the lead's independently produced production
  reference angles `[0, 0.66716223, 1.23265734, 1.90893531, 2.47443042, π, 3.80875489, 4.37425,
  5.05052796, 5.61602307]` with certified deviation upper bound `4.9403478660135036928e-9`.
* **Root rejected.** The root node of `q10-polytope-partition-879.json` (the q10 domain, 10 real
  vertices) fails for every map: `root_worst_abs_delta_exact = 0.470478642345997…` rad ≫ 1e-6, so the
  literal cell is a thin slab inside the root.
* **Synthetic accepting cell.** Ten module-exact vertices (`d_m = L − q_m·2pi`, `q_m` floored at
  denominator 1e9 and capped, `q_9 := 1 − Σ_{m<9} q_m`, then `±1e-12` along simplex directions) are
  **accepted**: `synthetic_worst_abs_delta_exact = 3.433832940954266e-8` ≤ 1e-6; by affinity this
  certifies the whole cell, not just its vertices — the maximum of a max-of-two-affine-functions over a
  convex polytope is attained at a vertex.
* The cuts are the linear prefix-sum conditions `sum_{m<j} d_m ∈ [jL − psi_j ∓ eps]` in the two
  labelled families, usable alongside the C1331 fan-lens cuts (orthogonal directions).

## 3. API, scope, gaps

```python
literal_geometry(), literal_owners(), graph_maps()
sigma        = anchor_correspondence(phi, owners)          # bijection via owner pairs, asserted
psi, tot     = cumulative_literal_arcs(A, sigma)           # one unwrapped branch, no cache
res          = cell_test(vertex_set, sigma, A, eps=1e-6)   # pass/fail + per-vertex, per-anchor margins
cuts         = cell_cuts(sigma, A)                         # outer_necessary / inner_sufficient
verts, qm, dom = synthetic_accepting_cell(A, sigma)        # calibration with certified domain checks
certify_literal_cycle(A)                                   # cross-product and full-turn certificate
```
Scope: one literal cell, a caller-supplied convex deficit polytope, A_0 gauge, reflection as the
order-reversing identification. No other anchor region, no global statement. Not done here (the
caller's step): running `cell_test` over the partition's open nodes — the JSON lists which node ids
carry vertex sets.
