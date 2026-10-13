# PAIRED-GAP NECESSITY (r20-chain) — two-edge bound, threshold cap, and why the 3-anchor closed form is unavailable

Assigned analytic obligation (no sampling, no global scan).  Control (bounded, one script):
`tools/r20_paired_gap_control.py` → `out/paired_gap_necessity_control.txt`.
Only this file and that script are written; **STATUS/DEAD untouched** (as instructed).

## 1. The correct two-edge bound (calibration)

For an adjacent anchor pair `(U_{i−1}, U_i)` the middle site `c_i` is adjacent to exactly those two
anchors (verified on the explicit exported incidence: **every site sees exactly 2 anchors**, 18
endpoint edges).  With uniform `α = 1/2` on the two edges,

> `E_α = |U_{i−1} − U_i|²/4 = sin²(Δ_i/2)`,  hence  **`V ≥ sin(Δ_i/2)`**.

Candidate gaps and bounds (`R* = 0.3799838531198385`, `L = 2asin(19/50) = 0.779592593`):

| i | Δ_i | sin(Δ_i/2) |
|---|---|---|
| 0 / 2 | 0.766024 | 0.373716 |
| 1 | 0.776443 | 0.378543 |
| 3 / 8 | 0.561644 | 0.277145 |
| 4 / 7 | 0.681686 | 0.334282 |
| 5 / 6 | 0.744017 | 0.363487 |

`max_i sin(Δ_i/2) = 0.378543 < R* = 0.379984`: **the two-edge inequality is weak at the candidate**
(reported as such; the family is not declared dead for other bounds).

## 2. Threshold necessity (the usable consequence)

Since `V ≥ max_i sin(Δ_i/2)`,

> `V(U) < R*` **implies** `Δ_i < 2asin(R*)` **for every i**.

Numbers: `2asin(R*) = 0.779557680 < L = 0.779592593`, i.e. the threshold supplies a **tighter
necessary cap** with shrink `L − 2asin(R*) = 3.49e−5`.  With the certified root interval's upper
bound `R_hi` (C891) the cap becomes `L' = 2asin(R_hi)`; supply `R_hi` to instantiate (the exported
`R_star` already gives the value above).  Consistency at the candidate: its maximum gap `0.776443`
lies **below** the cap, exactly as the necessity demands.

Consequence for the domain: any configuration with some `Δ_i ≥ 2asin(R_hi)` can support only covers
with `r ≥ R_hi`, so **the boundary layer of `P` is excluded** and the remaining region is the polytope
with the smaller cap `L'` (a strict shrink of the search domain, not a proof of the main inequality).

## 3. Why the paired/3-anchor **closed form** is NOT available here (calibration of the premise)

* Every site is adjacent to exactly **two** anchors; no free node (site or auxiliary) is adjacent to
  **three** anchors — verified on the explicit incidence: `three_anchor_nodes = []`.
* Therefore this graph contains **no Steiner/Y node**.  The closed-form "minimal enclosing disk"
  bound `V ≥ MEC(U_i,U_j,U_k)` — which for three anchors on the unit circle with all gaps `< π` would
  give the huge value `1`, and with a gap `≥ π` the half-chord — is **not an available inequality
  here**; it would require a free node joined to the three anchors, which the fixed-switch graph does
  not have.  Any 3-anchor bound must go through aux-mediated sub-networks and be **computed**, not
  quoted in closed form.
* The paired-gap route in *path* form is also weak: the 4-edge path through two sites gives
  `V ≥ sin((Δ_i+Δ_{i+1})/2)/2`, which is **below** the best single two-edge bound in all nine pairs
  (e.g. pair (0,1): `0.348510 < 0.378543`).  So the path form of the paired route cannot exceed `R*`
  either; only a genuine multi-terminal (shared-budget) sub-network could.

## 4. Status and honest reading

* Two-edge inequality: **valid**, closed form `sin(Δ_i/2)`, but numerically **weak** at the candidate
  (`0.378543 < R*`).
* Threshold necessity: **valid**, gives the tighter cap `L' = 2asin(R_hi)` (shrink `3.5e−5` at the
  exported `R_star`); it shrinks the domain, it does not prove `V ≥ R*` there.
* Paired-gap **closed form**: **not available** (no Steiner node); the paired route in path form is
  weaker than the singles.  Whether an aux-mediated multi-terminal sub-network exceeds `R*` jointly
  for two adjacent (or opposite) large gaps is **open** — it must be computed, and is not claimed here.
* No family is declared dead; no interval claims; float arithmetic throughout.

## Repro

```
cd research-2026/team-current
py -3 r20-chain/tools/r20_paired_gap_control.py   # -> r20-chain/out/paired_gap_necessity_control.txt
```
