# R16 corrected cap-residual identity + asymmetric Cartesian controls

Own scope; current coefficients (`lead/joint_nested_frozen.json` sha256 `5671967c…21fb`).
**No interval run was performed after the correction.**  This file replaces the filter used
in `R16-INTERVAL-DISJUNCTION-RUN.md`, which is now marked invalid.

## 1. The corrected identity

Sum-to-product with `u = 2b2 + δ`, `v = 2b1 − δ`:

```
      sin(u) - sin(v) = 2 cos((u+v)/2) sin((u-v)/2)
     (u+v)/2 = b1 + b2 ,     (u-v)/2 = b2 - b1 + δ
=>    sin(2b2+δ) - sin(2b1-δ) = 2 cos(b1+b2) sin(b2 - b1 + δ)
```

hence

```
R2 = cap2 - H = 2r[sin(2b2+δ) - sin(2b1-δ)] = 4 r cos(b1+b2) sin(b2 - b1 + δ)
```

**My earlier `2 cos(b1+b2) sin(2δ)` was wrong.** Independent checks:

* `max |LHS − RHS|` over 2000 random `(b1,b2,δ)` draws at 40 dps = **`6.888e-41`**;
* the sine factor vanishes **iff `δ = b1 − b2`**, i.e. exactly at the ridge (C855) — the old
  form would have zeroed it at `δ = 0`, which is not the ridge;
* at the ridge the two cap arguments coincide identically:
  `2b1 − δ = b1 + b2 = 2b2 + δ`, so the hub sits on both cap surfaces simultaneously.

Because `R2` and `N` both contain `H = 2r sin(2b1 − δ)`, **the legality filter depends on
`b1` and `b2`, not on `(r, δ)` alone.**  The old reduction ("legality is `δ ≤ 0` plus the norm
circle") is false and is withdrawn.

## 2. The code's actual filter (literal, from `lead/interval_hub_saturated.py`)

On a branch with hub height `H`, `s = sqrt(1−r²)`:

```
accept  iff   H > s-(1-r),   H < 2r,
              H <= 2r sin(2b1-delta),      R1 >= 0
              H <= 2r sin(2b2+delta),      R2 >= 0
              H^2 - 2 s cos(delta) H + 2r(1-r) <= 0     N >= 0
```

## 3. Three ASYMMETRIC controls (`b1 ≠ b2`), surfaces active

At `δ = b1 − b2` both cap arguments equal `b1 + b2`, so taking `H = 2r sin(b1+b2)` puts the
hub exactly on both cap surfaces (`R1 = R2 = 0`) — the ridge configuration.  Sites at
`φ1 = δ + b1`, `φ2 = δ − b2`; the Cartesian quantities `|hub|` and `|hub − φ_i| − r` are
recomputed independently from those angles.

| # | r | b1 | b2 | δ = b1−b2 | H | R1 | R2 | N | \|hub−c1\|−r | \|hub−c2\|−r | \|hub\| | filter | Cartesian | agree |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 0.375 | 1.1000 | 1.0500 | +0.0500 | 0.627674 | 0 | 0 | +0.299560 | +0.533049 | +0.502126 | 0.627674 | feasible | feasible | **yes** |
| 1 | 0.377 | 1.0500 | 1.1500 | −0.1000 | 0.609606 | 0 | 0 | +0.282247 | +0.497628 | +0.557659 | 0.609606 | feasible | feasible | **yes** |
| 2 | 0.379 | 1.1600 | 1.0200 | +0.1400 | 0.621639 | 0 | 0 | +0.282115 | +0.564369 | +0.478756 | 0.621639 | feasible | feasible | **yes** |

All three are asymmetric (`|b1 − b2|` = 0.05, 0.10, 0.14); the hub is inside the unit disk
and outside both radius-`r` disks, and the filter and the original Cartesian conditions agree
on all three.  The identity `R2 − R1 = 4r cos(b1+b2) sin(b2−b1+δ)` is `0 = 0` at these
configurations, consistent with the ridge.

## 4. Honest limits of the controls

* The three controls exercise the **ridge** configuration, where `R1 = R2 = 0`.  Because the
  two cap arguments coincide there, they do **not** independently separate `R1` from `R2`;
  the separation is tested instead by the identity check in section 1 (2000 random draws).
* A perturbation sweep that varies `H` at fixed `(b1, b2, δ)` is **not** a valid comparison:
  moving `H` off the tangency radius changes the site distances, so the Cartesian point at
  radius `H` along the direction `δ` is a different geometric configuration.  I therefore do
  not report such a sweep as a control (an earlier version of this check did, incorrectly).
* **What remains missing** for a fully independent filter verification: a control where
  `b1 ≠ b2`, the hub is **off** both cap surfaces, and the filter's two cap residuals are
  compared against `2 ×` the corresponding disk-distance margins.  Establishing the exact
  factor relating `R_i` to `|hub − c_i| − r` (which requires the chart's distance identity)
  is the natural next obligation; I have not verified it.

## 5. Status

* Corrected identity: **established** (verified to `1e-41`, ridge property exact).
* Invalidated: the whole legal census and all interval counts in
  `R16-INTERVAL-DISJUNCTION-RUN.md` (`r16rr_factored.py`, `r16qq_deltafirst2.py`,
  `r16pp_deltafirst.py`, `r16oo_paired.py`, `r16nn_run.py`, `r16ll_boundary.py`,
  `r16jj_disjunction.py`); that file now carries an INVALID banner.
* **No 10× refinement was launched and no further interval run was attempted**, per the lead's
  STOP.  Awaiting sizing.

Files: `r16ss_identity_fix.py` (identity), `r16vv_final_record.py` (identity + invalidation),
`r16ww_controls.py` (`out/r16ww_controls.json`, the three controls).
