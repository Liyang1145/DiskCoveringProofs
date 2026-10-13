# Reflected-DBM patch: independent audit (r20-rigidity)

Object: the newly added reflected-DBM branch of `lead/cosine_dbm_pilot.py` (lines 39-53):
`subset_bounds` on cyclic blocks, applied to the reflection `rho(y)_j = y_{(2-j) mod 9}`, with the
thresholds `C919-reflected-DBM` (`rq2 <= (191/25000)^2`) and `C920-reflected-DBM`
(`rq2 <= (729/50000)^2`). Control: `reflected_dbm_control.py` (exact Fractions).
Scope: this patch only; the C920 radius itself is not re-audited (certified via
`certify_relative_stress_ball.py`), nor is the old root.

## What the patch has to compute, and what it computes

Under the reflection the canonical prefix differences become
`t'_i - t'_6 = sum_{j in J_i} y'_j` with `J_i = {(2-j) mod 9 : j in [min(i,6), max(i,6))}`, and
`sum_{j in J_i} y'_j = t_{hi} - t_{lo}` of the **original** `y` (the reflection of a contiguous block
is a cyclic block). The code needs the enclosure of `t'_i - t'_6` — the same orientation as the direct
patch, where `tt = [-db[i][6], db[6][i]]` correctly encloses `t_i - t_6` (a point I got wrong once and
retracted; this audit re-checks the orientation by explicit point controls, not by inspection).

`subset_bounds(inds)` returns, for a contiguous `inds = [a, b-1]`, the pair `(-db[b][a], db[a][b])`,
which is exactly the enclosure of `t_b - t_a = sum y[a:b]` under the convention
"`db[p][q]` upper-bounds `t_q - t_p`"; for a wrapping (cyclic) block it uses the complement and
`(1 - db[ca][cb], 1 + db[cb][ca])`, correct because `sum_{comp} y = t_cb - t_ca` and `sum_all y = 1`.
The `if i < 6: l, u = -u, -l` flip is the correct transition from a bound on `sum_{[i,6)} y'` to
`t'_i - t'_6 = -sum_{[i,6)} y'`. Non-contiguous complements would trip the built-in `assert`.

## Controls actually run (exact Fractions)

Explicit rational simplex point `y` (min entry `1/15`, `sum = 1`), its prefix `t`, the explicitly
reflected `y'` and its prefix `t'` (`t'_6 = 313/504`, `t'_9 = 1`):

1. **Non-singleton DBM containing the point.** The root DBM (width `db[i][j] + db[j][i] = 1` in every
   difference) is verified to contain the chosen point: `-db[i][j] <= t_i - t_j <= db[j][i]` for all
   `i, j`. (The reflection is what makes a *non-singleton* DBM relevant: the test must work on
   intervals, not on a point.)
2. **Containment of the true reflected prefix difference.** For all 8 loop indices
   `i = (k-2) mod 9`, the code's interval (built exactly as in the patch, with `-D` flipping the
   endpoints only inside `h`) contains the true `t'_i - t'_6`: e.g. `i=0`: `[-1, 0]` contains
   `-313/504`; `i=7`: `[0, 1]` contains `1/7`. **True for all 8.**
3. **Same after real splits.** Splitting the DBM at `(0,5)` and `(2,7)` (midpoint `1/2`, closure
   reapplied) keeps containment. **True in both cases.**
4. **Cyclic-block sum identity.** `sum_{j in J_i} y'_j == t_{hi} - t_{lo}` (original `y`) for all 8
   indices. **True** — this is the step that makes the reflection invisible to `subset_bounds`.
5. **`rq2` containment.** With a dummy rational `roots[]` reference the true reflected squared norm
   `111834657709979/12985932960000` lies inside the interval `[417247/61250, 626547/61250]` computed
   from the code's `tt`. **True.**

## Verdict and limits

No error found: the reflected-DBM branch is oriented and bracketed correctly on this control. Not
audited here: the analytic relation between the C920 radius and this patch (the lead states C920 is
certified separately), the global/tree consequences, and any claim. The audit is a control, not a
certification of the patch for all DBMs; the deterministic content is the orientation and the
cyclic-block identity, both of which are structural.

## Reproduction

`py -3 -B -X utf8 reflected_dbm_control.py` -> `reflected_dbm_control.json/.log`. No claim added.
