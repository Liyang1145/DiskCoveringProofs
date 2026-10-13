# C845 retraction archived + narrow-angle finding verified (read-only)

## 0. FINAL: latest loose end archived as unreproduced (per lead)

The `dl/el`-block loose end is **withdrawn**; no claim depends on it. Lead's evidence file
`lead/ring1_direct_control.json` is authoritative: `value = 1.4459409612312664`,
`dl_index = 96`, `el_index = 97`, point `[0.04940796322855881, 0.9999980926513672,
0.8869800567626953]`, scope "direct original factor formula, correct 94 base".

One arithmetic note, recorded only so the numbers are auditable — **not** a claim, and I am not
reopening indexes. Using the frozen row and exactly those indices
(`dl = z[96] = -0.055549338`, `el = z[97] = -2.390899561`, `i = 1`, `mu = z[1]`, `d = z[34]`,
`e = z[35]`, `hl = z[113]`, `hr = z[114]`, `C = z[71]`):

```
fixed part (all terms but -dl*u - el*v)  = -0.625857006
-dl*u - el*v  at u=0.9999980926513672, v=0.8869800567626953 = +2.176229460
recomputed total = +1.550372454        control value = +1.445940961        difference = +0.104431
```
The gap is confined to the `el·v` term (every other term agrees term-by-term): the control total
corresponds to `-dl*u - el*v = +2.071797968`, i.e. an effective `el ≈ -2.27375` versus the frozen
`z[97] = -2.390899561`. Either the control was evaluated against a slightly different `z[97]` or
scale, or my `el` bookkeeping differs; I could not resolve it from the artifacts. Recorded, then
closed.

## 1. C845 — archived as instructed

`C845-RETRACTION-ARCHIVE.md`. Lead's retraction stands on all three points; my own checks now
reproduce the lead's numbers exactly:

* With `hl = z[113]`, `hr = z[114]` (`i = 2`): `corner(75/76) = −2.7089256392436964`,
  `corner(1) = −2.7089256392438172` — bit-for-bit the lead's values. The corner is *flat in t*
  because the `−6·t` term `−(z[98]+z[99])·t` is linear with a large slope offset by `w(t)` growth;
  my `−1.5522` came from mixing z-blocks and is not reproducible. **Withdrawn.**
* Scope: factor 22 is explicitly conditional on `α = π`, so the unrestricted-`α` comparison I made
  is irrelevant to the intended proposition. **Withdrawn.**
* Derivative bound: correct partial `w_α = R·uv·sinα/(√q·den)`; my check of the lead's inequality
  by dense admissible scan gives `max = 0.37939 < L = 0.41082`. My `1.177` came from using
  `R²·uv·sinα/q`. **Withdrawn.**

## 2. The real failure (lead) — independently reproduced

`debug_middle_inward.py` (newest revision, 01:05) stores `bestpoint =
[0.04940796322855881, 0.9999980926513672, 0.8869800567626953]` for factor 21 — i.e. the
narrow-angle region the lead flagged (`α ≈ 0.0494`, `u ≈ 1`, `v ≈ 0.887`), with
`upper = 1.4459559456546291`. The bound was produced by `certify_middle_inward.py` at 00:57
(identical upper/lower, digest `17a0225e…`), and re-running the newer `debug_middle_inward.py`
reproduced the same numbers.

## 3. One loose end worth a single check by the lead

The stored ring-1 bound depends on which z-block the frozen certificate uses for the **linear**
slack coefficients `dl, el`:

| map for `dl, el` | ring-1 value at the debug bestpoint (0.049408, 0.999998, 0.886980) |
|---|---|
| `z[94+2i], z[95+2i]` (current `certify_q0_closure.py` line 78 literal) | **+1.6227** vs stored upper **1.4459** → above the stored bound |
| `z[73+2i], z[74+2i]` (marker-derived map from the earlier revision) | +1.1676 → below the stored bound |

If the frozen proposal reads the `z[94+…]` block (which the current kernel literal and
`check_middle_sector_symbolic.py` line 23 both assume), then the ring-1 bound is also below an
attained value and the narrow-angle gap is a *bound* problem, not only a tightness problem.
If it reads `z[73+…]`, the lead's reading (interval `1.44594` above the true max `1.38490`) is
consistent and the issue is tightness plus the assembly failing at `3.8096 > π`.

I cannot settle this from the artifacts alone because `certify_q0_closure.py` was edited at
21:20:34 (before the 00:57 run) and the frozen row was consumed by the script's truncate+replace
path, so two different `dl/el` blocks are plausible. **Not opening a claim on it** — flagging for
the lead's one-line decision.

## 4. Status of my artifacts

* Retracted/not citable as findings: `MIDDLE-INWARD-AUDIT.md`, `C845-*`, `ring2_bound_vs_sup.py`,
  `corner_soundness_quant.py`, `middle_inward_audit.py`, `assemble_middle.py`,
  `clip_binding_test2.py`, `clip_admissible_scan.py`, `clip_window_test.py`.
* Sound and re-usable as *checks*: `bounds_selfconsistency.py` (all 26 written bounds satisfy
  `upper ≥ lower_probe`), `post_retraction_recheck.py`, `narrow_angle_check.py`,
  `ring1_gap_check.py`.
