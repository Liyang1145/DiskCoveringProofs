# Direct-DBM patch: independent audit (r20-rigidity) — CORRECTED

Object: `lead/cosine_dbm_pilot.py`, `root_angles()` (lines 7-15) and the direct-DBM branch of
`known_patch()` (lines 26-37). Independent control: `direct_dbm_control.py` (exact Fractions).
Scope: this patch test only; not the DBM dual pipeline, not the tree; no claim.

## RETRACTED FINDING (my error, withdrawn)

An earlier version of this file asserted that line 32,
`tt = [lo(I(-db[i][6])), hi(I(db[6][i]))]`, was a transposed interval. **That assertion was wrong.**
It enclosed the quantity `t_6 - t_i`, but the canonical difference the code needs is
`theta_i - theta_6 = (i-6)L - D(t_i - t_6)`, i.e. it needs `t_i - t_6` — and with the convention
"`db[p][q]` upper-bounds `t_q - t_p`" (confirmed by `db[9][0] = -1`, `t_0 = 0`, `t_9 = 1`):

```
   db[i][6] >= t_6 - t_i   =>   t_i - t_6 >= -db[i][6]
   db[6][i] >= t_i - t_6   =>   t_i - t_6 <=  db[6][i]
```

so `tt` is exactly the right enclosure. It is also consistent with the sibling uses on line 18
(`lower[j] = -db[j+1][j]`, `upper[j] = db[j][j+1]`), which I had (correctly) accepted. My earlier table
labelled `[1/2, 1]` as "correct `t_3 - t_6`", when it is in fact the range of `t_6 - t_3`; for
`i = 3 < 6` one has `t_3 <= t_6`, hence `t_3 - t_6 <= 0`. **No code error exists**; the audit error was
mine, and it must not be escalated into a code defect.

## Containment controls actually run (replacing the withdrawn claim)

`py -3 -B -X utf8 direct_dbm_control.py`:

* explicit rational `y` (sum 1, all entries positive) with prefix `t_0..t_9`, `t_9 = 1`;
* **singleton case** `db[p][q] = t_q - t_p` exactly: for all 8 loop indices `i = (k-2) mod 9` the code
  interval `[-db[i][6], db[6][i]]` contains the true `t_i - t_6` — **True**;
* **after splits** on the pairs `(6,3)`, `(0,5)`, `(2,7)` (both children, closure applied):
  containment still holds for all 8 indices — **True** in all six cases;
* **q2 containment**: with a dummy rational `roots[]` reference, the true sum of squared canonical
  perturbations equals `111266769757919/12985932960000`, and the interval computed from the code's
  `tt` (the `-D` coefficient flips the endpoints) brackets it — **True**.

So the direct-DBM angle-norm envelope is oriented correctly, and the thresholds
`q2 <= (431/10^6)^2` (C915-direct-DBM) and `q2 <= (3/2000)^2` (C918-direct-DBM) are fed by a valid
interval as far as this control reaches.

## Other items checked (verified correct)

* **Exact dyadic root.** `root_angles()` uses `F(float.fromhex(...))` on `radius_hex`/`center_hex` of
  `repaired_tc_krawczyk.json`: exact for binary64 hex, no decimal round trip; the box is point `+ [-r, r]`
  with `r` taken at its upper endpoint.
* **Chart recurrence.** `a = [z0,z1,z2,z3, pi-2(z0+..+z3), z3,z2,z1,z0]`; forward pass
  `th[k] = th[k-1]+a[k-1]+a[k]` and backward pass `th[k] = th[k+1]-a[k]-a[k+1]` are exact inverses;
  `raw[k] = th[k]+a[k]` are the site angles.
* **Re-indexing / wrap.** `ROOT_ANGLES[0] = 0`; the rest are `raw[(i+2) mod 9] - raw[2]` with `+2 pi`
  added exactly for `i >= 7`, i.e. exactly for the two indices whose source wrapped below 2; correct
  unwrapping under counterclockwise ordering, consistent with `theta_i = iL - D t_i`.
* **Patch thresholds.** Corner thresholds `1-t` are `3/5` for `j in {0,1,2,5,6}`, `13/20` for
  `j in {4,7}`, `3/4` otherwise — reproducing the recorded C914 corner `t` values (2/5, 7/20, 1/4).
  C913 (`min(lower) >= 31/450`) and C916 (direct and `(2-i) mod 9` reflected indexing) are oriented
  consistently with the same convention.

## Reproduction

`py -3 -B -X utf8 direct_dbm_control.py` -> `direct_dbm_control.json/.log`. No claim added.
