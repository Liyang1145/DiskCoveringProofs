# THREE-TERMINAL CONTRACTION (r20-chain) — path contraction + weighted 1-center, calibrated

Assigned structural obligation.  Control (one bounded numeric run, no grid, no global scan):
`tools/r20_three_terminal_contraction.py` → `out/three_terminal_contraction.txt`.
STATUS/DEAD untouched; no subagents.

## 1. The mechanism (analytic, necessary bound)

In the 51-edge fixed-switch graph take three anchors `U_i,U_j,U_k` and one common **free** node `Z`
(site or auxiliary), with shortest path edge-counts `m_i,m_j,m_k`.  Every edge has length `≤ V(U)`,
so along each path the triangle inequality gives `|U_t − Z| ≤ m_t·V`.  Therefore

> `V(U) ≥ W(U_i,U_j,U_k; m_i,m_j,m_k) := min_Z max_t |U_t − Z| / m_t`

(the multiplicatively **weighted 1-center** of the three anchors).  This is a **path contraction**:
it needs only *paths* to a common free node, so the earlier "no free node is adjacent to three
anchors ⇒ no Steiner/Y" observation does **not** kill it (that remark concerns the *closed-form*
unweighted MEC bound only).

## 2. Chosen shared-hub fan tree and its path lengths

Best tree found by the bounded enumeration over (common free node, anchor triple) — 1092 admissible
combinations, a finite combinatorial search, not a grid:

* **common node `Z` = node 27** (an auxiliary), **anchors `(U_3, U_6, U_8)`**, **`m = (4, 2, 2)`**.
  Concretely the contraction uses: `U_6 → c_6 → (its fan aux) = Z` (m = 2), `U_8 → c_8 → Z` (m = 2),
  and `U_3` reaching `Z` along a length-4 route through the shared hub/aux structure.
* Runner-ups: `(Z=25, U_0,U_4,U_6, m=(4,2,2))` with the same value; `(Z=23, U_2,U_4,U_8, m=(2,2,4))`,
  `(Z=20, U_1,U_4,U_8, m=(2,4,2))`, `(Z=21, U_0,U_2,U_4, m=(2,2,4))`, `(Z=22, U_1,U_3,U_8, m=(2,2,4))`.

## 3. Calibration (candidate and uniform) and the honest comparison

| configuration | best three-terminal `W` | best single two-edge bound | `W` vs single pair | `W` vs `R* = 0.379984` |
|---|---|---|---|---|
| candidate (gaps max `0.776443`) | **0.358264434** | 0.378543 | **weaker** (`≤`) | below |
| uniform gaps `Δ = 2π/9` | **0.357974173** | 0.342020 (`sin(π/9)`) | **stronger** (`>`) | below |

Reading:
* On the **candidate**, the three-terminal contraction is **not stronger** than the best single
  two-edge bound (`0.358264 < 0.378543`), and it does not reach `R*`.
* Under **uniform gaps** it *is* stronger than the single two-edge bound (`0.357974 > 0.342020`) but
  still below `R*`.
* Structural reason: the trees with two short legs (`m = 2`) force the third anchor to `m = 4`, and
  the weighted 1-center pays for the long leg; the symmetric shared-hub fan trees (`m = (3,3,3)`,
  reaching the hub node) give only `MEC/3 ≈ 0.23` — weaker still.

## 4. Status

* The inequality `V ≥ W` is **necessary and analytic** (path contraction + weighted 1-center); the
  control only *instantiates* it.
* It is **valid but not decisive** on the tested configurations: it does not exceed `R*`, and at the
  candidate it is weaker than the best pair.  Nothing here declares any family dead.
* Numbers are float (numeric proposal, no interval claims).  No two-edge *cap* numerics were added;
  this is the assigned structural run only.

## Repro

```
cd research-2026/team-current
py -3 r20-chain/tools/r20_three_terminal_contraction.py   # -> r20-chain/out/three_terminal_contraction.txt
```
