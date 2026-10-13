# FULL-P DBM tree: independent structural audit (r20-rigidity)

Objects: `lead/replay_closed_dbm.py`, `lead/FULL-P-ORACLE-THEOREM.md`, tree file
`lead/cosine_dbm_local920.json`. Instrument: `full_p_tree_audit.py` (read-only, exact Fractions, no
LP, no solver, no lead helper import). Local constants are **not** re-audited here; this is about the
tree's coverage and the closed-leaf reading interface.

## Readings (all recomputed, exact)

| item | reading |
|---|---|
| tree size | 5011 nodes, 371 fields |
| root cell | stored root `db` equals `rootdbm()`; the table is already closed (re-closure is a no-op); explicit simplex points satisfy every row and `t_9 - t_0 = 1` |
| root widths | every pair except the pinned `(0,9)` has width `db[i][j] + db[j][i] = 1`; the pinned pair has `db[0][9] = 1`, `db[9][0] = -1`, i.e. width 0 = `t_9 - t_0` pinned to 1. (My first log line printed "widths all 1: False" because the check did not exempt that pin; the pin itself is the correct root structure, not a defect.) |
| traversal | split 2505, patch-leaves 120, energy-leaves 2386, **0 open**; `seen == set(range(len(nodes)))`; every split regenerates its midpoint and both children exactly through `branches()`, and children are visited exactly once |
| dichotomy | for each split, the two children are the parent plus one half-space each (`t_j - t_i <= mid` vs `>= mid`), so their union covers the parent and their intersection is the hyperplane; tested on sampled feasible points of parent cells (2 points here) — the *analytic* dichotomy, not the sampling, is the coverage argument |

The counts reproduce the lead's 2505 / 2386 / 120 / 0 exactly.

## Closed-leaf reading interface (what makes the replay sound)

1. **beta prefix vs extended fields.** `replay` reads `beta` from the stored certificate, requires
   `len(beta) <= len(fields)`, `min(beta) >= 0`, `sum(beta) == 1`, and for every one of the 36 pairs
   re-derives `W = sum_t beta_t * 2 * w_k^{(t)}` over the **first `len(beta)`** fields and asserts
   `W == rec['weight']`. The weight identity is the guard that makes the prefix reading safe: if the
   library extension had reordered the fields, `W` would not match the stored weight and the assertion
   would fire. Verified for all 2386 energy leaves (assertion passes everywhere).
2. **Whole-arc critical points, both families.** For each leaf the replay **recomputes** the arc from
   the current cell's DBM, `a = lo((i-j)L + D(-db[j][i]))`, `b = hi((i-j)L + D db[i][j])`, and calls
   `certify_cosine_envelope_cell.intercept(a, b, s)`, whose candidate set is the endpoints plus the two
   families `asin(s) + 2k pi` and `pi - asin(s) + 2k pi` (via `atan2(s, sqrt(1-s^2))`), with the
   coverage guard `a > -2pi`, `b < 2pi` asserted inside. Both families are present, and the returned
   intercept is `min(lo(...))` of the candidates, i.e. a valid lower bound of the true arc minimum.
3. **Float proposals and decimal bounds are not load-bearing.** The stored `slope` strings are read as
   exact rationals (`F(z['slope'])`, the binary64 value itself), `gamma` is re-normalised in exact
   rationals, and the stored `arc` and `intercept_lower` fields are **not used at all**: `a`, `b` come
   from the DBM and `v` comes from `ci(a, b, s)`. The LP's numbers therefore act only as a proposal;
   soundness is re-established per leaf. `|s| <= 1` is asserted inside `intercept` before the square
   root. The `lambda` vector and the residual dual are likewise re-derived, with
   `len(lam) == len(A)` and `min(lam) >= 0`, and the bound is an outward interval expression.
4. **Is `rootdbm` really the closed simplex?** Yes: the table `db[p][q] = t_q - t_p` bounds with
   `db[i][j] = 1 (j>i)`, `0 (j<=i)`, `db[9][0] = -1` describe `t_0 <= t_1 <= ... <= t_9` with
   `t_9 - t_0 = 1`, which after `y_k = t_{k+1} - t_k` is exactly the 8-simplex; Floyd-Warshall is a
   no-op on it; explicit simplex points satisfy every row. The conclusion per leaf is
   `V > target` with `target >= 3799838531198387090485182/10^25` asserted, so the assembled statement
   is comparable with the C891 enclosure of `R*`.

## Limits

Local constants (minorants, Schur weights, targets) are taken as given here; they were audited
separately. The dichotomy/coverage argument is analytic (children = parent plus one half-space); my
sampled control is only a sanity check on 2 points per cell. The audit is read-only and adds no claim.
The lead's counts and the `all_fields_replay371` Schur replay are consistent with what I recomputed.

## Reproduction

`py -3 -B -X utf8 full_p_tree_audit.py` -> `full_p_tree_audit.json/.log`.
