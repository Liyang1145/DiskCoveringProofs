# DBM-DUAL-AUDIT — independent analytic audit of the DBM cells, exact midpoint coverage, and the cosine LP dual bound

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. **No new claim, no sub-agent.** Objects
read directly: `lead/cosine_polytope.py`, `lead/certify_cosine_polytope.py`, `lead/cosine_dbm_pilot.py`.
Status line taken as given: 255 cells / 61 certified / 134 open, **not global**; the 2047 extension is
the running instrument. Scope of this audit: the **mechanism** (region algebra + certificate signs),
not the completeness of the current tree.

## 1. The DBM region and its closure — sound and equivalence-preserving

Setting: `t_i = Σ_{k<i} y_k` (`i = 0..9`), `t_0 = 0`, `t_9 = Σ_{k=0}^{8} y_k`, `y ≥ 0`, `Σy = 1`; so
`t_j − t_i = Σ_{i≤k<j} y_k`, `0 ≤ t_0 ≤ … ≤ t_9 = 1`. `db[i][j]` upper-bounds `t_j − t_i`.

**Initial DBM is sound.** (i) monotonicity: for `i < j` one has `t_j − t_i ≥ 0`, i.e. the *upper*
bound on `t_i − t_j` is `0` ⇒ `db[j][i] = 0` (source line 11 comment; the `db[9][0] = −1` convention on
line 13 is the `(i,j) = (0,9)` instance of the same rule made exact); (ii) `t_j − t_i ≤ 1` for all
pairs (since `0 ≤ t ≤ 1`) ⇒ `db[i][j] = 1`; (iii) the `t_9` boundary: `t_9 − t_0 = 1`, so the pair
`(0,9)` carries the **equality pair** `db[0][9] = 1`, `db[9][0] = −1` — the pilot asserts exactly
`rt[0][9] == 1 and rt[9][0] == -1` (line 21), so the boundary is pinned, not dropped. Every `y`-simplex
point satisfies all of them ⇒ sound.

**Closure.** `db[i][j] ← min(db[i][j], db[i][k]+db[k][j])` (line 20) adds only *implied* bounds
(`t_j − t_i = (t_k − t_i) + (t_j − t_k) ≤ db[i][k] + db[k][j]`). Hence the closure is **sound in both
directions**: it never removes a point of the parent region, and every added bound is valid, so the
closed DBM represents the *same* region as the input. This equivalence (not merely soundness) is what
the coverage argument below needs, and it matches the pilot's own note (line 44: "closure
equivalent"). Negative cycles: a closed DBM with `db[i][i] < 0` is **exactly** empty
(`t_i − t_i ≤ db[i][i] < 0`), which is the detection at line 21 returning `None`.

## 2. Midpoint branching covers, and never loses a child

Pair `(i,j)`, `l := −db[j][i]`, `u := db[i][j]` (so the region's bounds on `s := t_j − t_i` are
`l ≤ s ≤ u`). Because the DBM is closed, the **projection property** holds: the projection of the
region onto `(t_i,t_j)` is exactly `[l,u]`; hence `l < u` (asserted line 25) implies both
`s = l` and `s = u` are attained, and the midpoint children `s ≤ m` and `s ≥ m` (`m = (l+u)/2`,
lines 26–27, implemented as `db[i][j] := m` resp. `db[j][i] := −m` followed by closure) are both
non-empty. **Coverage**: every point of the parent satisfies `s ≤ m` or `s ≥ m`; by §1 each child's
region equals the parent's region intersected with that half-space (closure changes nothing), so
```
child_upper ∪ child_lower = parent    exactly,
child_upper ∩ child_lower = {s = m}   (a boundary set, not a lost region).
```
Two obligations follow for the ledger, both present in the sources: every split must record **both**
children (lines 39–48; the replay at line 48 re-derives `mid` from the parent's own DBM and asserts
`len(children) == 2`), and the pair choice must avoid **degenerate** pairs `l = u` (in particular
`(0,9)`, where `l = u = 1`), else `l < u` fails — the assert at line 25 is the guard, and the pilot's
255 processed cells are consistent with it.

## 3. The LP dual bound: signs check out

For the closed cell, `A y ≤ b` collects the 90 rows (45 pairs × upper/lower): row `(i,j)` is the
0/1-indicator `1_{i ≤ k < j}` (line 33 of `cosine_polytope.py`) with bound `db[i][j]`, and its negation
with bound `db[j][i]`. For any `λ ≥ 0` and any `y` in the simplex with `Ay ≤ b`:
```
f0 + c·y  =  f0 + c·y + ⟨λ, Ay − b⟩ − ⟨λ, Ay − b⟩
          ≥  f0 + c·y + ⟨λ, Ay − b⟩            (since Ay − b ≤ 0, λ ≥ 0 ⇒ the added term is ≤ 0)
          =  f0 − ⟨λ,b⟩ + ⟨c + Aᵀλ, y⟩
          ≥  f0 − λ·b + min_i (c + Aᵀλ)_i       (y in the standard simplex ⇒ min over its vertices)
```
which is exactly the header identity of `certify_cosine_polytope.py` (line 2) and the evaluation order
at lines 26/28. **Signs are correct at every step**, and the interval evaluation is in the sound
direction for a *lower* bound: it takes `lo(f0 − Σλ·b)` and `min_i lo(c + Aᵀλ)_i` — lowers of both
terms (the min of interval lowers lower-bounds the min of the true values). Note the `b` vector
contains negative entries (e.g. `db[j][i] = 0` or `−1`), so `−Σλ·b` can be positive; no sign
normalisation is needed because the formula is linear in `b`.

## 4. Checks, calibrations, and residual notes

* **Source-consistency checks I ran by inspection**: the indicator row `1_{i ≤ k < j}` matches
  `t_j − t_i = Σ_{i≤k<j}y_k`; the lower child's DBM entry `−m` encodes `t_j − t_i ≥ m`; the root
  assertion `rt[0][9] == 1, rt[9][0] == −1` pins the `t_9` boundary; the certificate header matches §3.
* **Small exact calibrations (no exhaustive sampling)**: (a) negative cycle — take `db[0][1] = a`,
  `db[1][0] = −b` with `a < b`; the closure produces `db[0][0] ≤ a − b < 0`, so the cell is exactly
  empty and must be recorded as such (an empty child is still a recorded child). (b) known central
  simplex — the uniform point `y = (1/9,…,1/9)` gives `t_i = i/9`, which satisfies every initial row
  (monotonicity `(j−i)/9 ≥ 0`, upper `≤ 1`, and the `t_9` equality), so it lies in the root cell; the
  certificate must satisfy `LB ≤ f(uniform)`, and more generally `LB ≤ min` over any sampled points —
  sampling can *falsify* a wrong certificate, never prove one.
* **Residual notes (no defect claimed)**: (i) `l < u` must be guaranteed by the pair rule, not only by
  the assert (otherwise a degenerate pair yields no progress); the `(0,9)` pair is degenerate by
  construction. (ii) The empty-child case (`db is None`) must be recorded as an empty cell rather than
  dropped — "no lost child" then means "no lost *record*", which the split schema already enforces by
  storing `children` as a pair. (iii) This audit certifies the region algebra and the certificate's
  sign chain only; the current tree is 61 certified / 134 open, **not global**.
