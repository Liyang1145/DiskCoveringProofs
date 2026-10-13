# GLOBAL SHORT-GAP SCREEN (r20-chain) — CORRECTED; path family NOT judged dead

Evidence: `tools/r20_short_gap_screen.py` → `out/r20_short_gap_screen.txt`.
Read: `lead/FIXED-SWITCH-SOC-REDUCTION.md`, `lead/NETWORK-ENERGY-INTERFACE.md`.

## 0. Retraction of my own earlier claims (lead's corrections, 2026-09-25h)

* **Wrong path formula (mine).** I wrote `V ≥ |U_a−U_b|/(2√m)` and `E = |Δ|²/(4m)`.  Correct: with
  uniform `α = 1/m` on an `m`-edge path the triangle inequality gives `Σ_e|x_v−x_w| ≥ |Δ|`, hence
  `Σ_e|x_v−x_w|² ≥ |Δ|²/m` and therefore **`E_α = |Δ|²/m²`, `V ≥ |Δ|/m`**.  For `m = 2` this is
  `|Δ|/2 = 0.3713` at chord `0.7426` (my wrong value was `0.2625`).
* **Consequently "path-only screen never fires" is WITHDRAWN** — it rested on that formula, and one
  wrong instance never judged the whole path family.  **No evidence, no death**: the path family is
  *unjudged*, not dead.
* **Withdrawn unproved remarks (mine).** (i) "`Φ = max_α E_α` convex/positively homogeneous ⟹ minimum
  at a vertex" — void: `Φ = V²` is **degree 2** (`V` is degree 1) and convexity does not put a minimum
  at a vertex.  (ii) "force form gives Lipschitz ≤ 1/2" — void until a norm is specified and the bound
  proved.
* Scope rule accepted: **only assigned scope**; no experiment expansion, no intervalisation before the
  machinery is calibrated.

## 1. Object and exact dual (quoted from the lead's interface)

Nine unit anchors `U_0..U_8` cyclically, gaps `Δ_i ∈ [m, L]`, `ΣΔ_i = 2π`,
`L = 2asin(19/50) = 0.779593`, `m = 2π − 8L = 0.046445`.  Oracle `V(U) = min t` over the 31-node /
51-edge fixed-switch graph; by Slater duality `V(U)² = max_{α∈Δ₅₁} E_α(U)`,
`E_α(U) = Σ_{ij} Λ_{ij}(α)⟨U_i,U_j⟩` (Schur complement of the α-weighted graph Laplacian).  `E_α` is
concave in `α`; every feasible `α` gives a lower bound.

## 2. All-anchor-pair shortest graph paths (assigned fix) with the corrected bound `|chord|/m`

`m_{ij}` by BFS on the explicit incidence graph (`incidence_map` of
`r20-alternative/socp_anchor_export.json`); bound `|chord(U_i,U_j)|/m_{ij}` at the candidate anchors:

| pair | m | chord | bound |
|---|---|---|---|
| U0,U8 / U3,U4 | 2 | 0.554291 | 0.277145 |
| U4,U5 / U7,U8 | 2 | 0.668564 | 0.334282 |
| U5,U6 / U6,U7 | 2 | 0.726975 | 0.363487 |
| U0,U1 / U2,U3 | 2 | 0.747432 | 0.373716 |
| U1,U2 | 2 | **0.757086** | **0.378543** |
| all other pairs | 4 | ≤ 1.232282 | ≤ 0.308071 |

Every **adjacent** anchor pair has `m = 2` (path through their common site) so its bound is
`|chord|/2`; non-adjacent pairs have `m = 4`.  Max over all pairs at the candidate: **0.378543**,
consistent with the reported chord bound `0.378542769`.  At a gap at the cap, `chord(L) = 0.76` and
the `m = 2` bound is exactly **0.38** — the path family is *borderline*, not dead.

## 3. Full-dual readings (independent of the retracted path formula)

The ascent evaluates the Schur complement directly (Danskin gradient `∂E/∂α_e = |X*_v−X*_w|²`), so it
does not use the path formula.  On 27 structured extremal cases of `{Δ_i ≤ 0.2}` (3 shapes × 9 cyclic
shifts) it gave `√(max_α E_α) ∈ [0.389041206, 0.404198897] > 0.38`.  (The path-only columns printed in
that same log used the old wrong formula and are void.)

**Scope**: float arithmetic, numeric proposal only; structured cases, not a region-wide proof; margin
`0.009 – 0.024`.  No rigorous region-wide statement is attempted here.

## 4. Status of the instructed items

* `V > 0.38` whenever some `Δ_i ≤ 0.2`: **open** (readings above are encouraging; numeric and
  structured-case only);
* counterexample direction: **not found**;
* the fixed-stress negative curvature says **nothing** about the oracle `V` (as instructed).

## Repro

```
cd research-2026/team-current
py -3 r20-chain/tools/r20_short_gap_screen.py     # -> r20-chain/out/r20_short_gap_screen.txt
```
