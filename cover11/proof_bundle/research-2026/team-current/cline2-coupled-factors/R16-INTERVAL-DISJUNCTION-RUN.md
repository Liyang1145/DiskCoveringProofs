> ## ⛔ INVALID — DO NOT USE ANY RESULT IN THIS FILE
>
> The lead found a factorisation error in the feasibility filter this run was built on.
> I had used
> ```
> R2 = 2r[sin(2b2+delta) - sin(2b1-delta)] = 2 cos(b1+b2) sin(2 delta)     # WRONG
> ```
> The sum-to-product identity gives
> ```
> sin(2b2+delta) - sin(2b1-delta) = 2 cos(b1+b2) sin(b2-b1+delta)
> ```
> so `R2 = 4 r cos(b1+b2) sin(b2-b1+delta)` — the sine factor is `sin(δ + b2 − b1)`, which
> vanishes exactly at the ridge `δ = b1 − b2` (C855), **not** at `δ = 0`.
>
> Consequences: the "legality reduces to `δ ≤ 0` plus the norm circle" reduction is false;
> the claim that `Nc` depends on `(r, δ)` alone is false (it depends on `b1, b2` through
> `H`); and therefore **the entire legal census and every certification count below is
> invalid**, including "2926 certified by `G' ≠ 0`", "44 by `G'' > 0`", "9983 fully-legal
> boxes" and the "obstacle family".  The factored-residual step that made boxes look legal
> was an artefact of the wrong sine factor.
>
> Corrected record: `R16-CORRECTED-FILTER.md`.  Invalidated as legality censuses:
> `r16rr_factored.py`, `r16qq_deltafirst2.py`, `r16pp_deltafirst.py`, `r16oo_paired.py`,
> `r16nn_run.py`, `r16ll_boundary.py`, `r16jj_disjunction.py`.
>
> **No interval result, no theorem, and no legal census from this file is usable.**

# R16 interval certificate attempt — legal face arcs, disjunction `G' ≠ 0 OR G'' > 0` *(INVALID below this line)*

Own scope; current frozen coefficients (`lead/joint_nested_frozen.json` sha256 `5671967c…21fb`);
exact 9-decimal coefficient literals; **bounded run, 20000 box evaluations**; live boxes
returned and **no theorem claimed**.

## 0. Calibration done BEFORE the run (as required)

| route | status |
|---|---|
| **Cartesian curvature identity** | verified: with `theta = pi/2 − 2A` (face 1) and `theta = 2B − pi/2` (face 2) we get `dtheta/ddelta = 2` **exactly**, `\|x_theta'\| = r` **exactly**, `x_theta'' ⊥ x_theta'` with equal modulus. Hence `x' = 2x_theta'`, `x'' = 4x_theta''` and `F'' = 4[x_theta'ᵀ Hess F x_theta' + grad F · x_theta'']` is the *same* object as `d²V/dδ²`. |
| **multi-step FD of V** | agrees at 5 legal points across `h = 1e-2, 1e-3, 1e-4` (e.g. `0.42416287769 / 0.42425376872 / 0.42425467756` at `(0.375, 1.05, 1.05, 0)`, tending to the analytic `0.4242546867`). |
| **analytic assembly** | `r16gg_corrected.py`/`r16rr_factored.py` second derivative validated this way (this is the assembly in which I fixed the earlier `phi2'`→`phi2''` bug). |

So the first and second derivatives used by the interval code are calibrated before use.

## 1. Correct feasibility filters (a real simplification)

On the **face-1 arc** `H = 2r sin(2b1−delta)` identically, so the three filters collapse:

```
R1 = cap1 - H = 0                                   (exactly)
R2 = cap2 - H = 2r[sin(2b2+delta) - sin(2b1-delta)] = 4r cos(b1+b2) sin(2 delta)
Nc = -(H^2 - 2 s cos(delta) H + 2r(1-r))            (norm circle; must be >= 0)
```

with `s = sqrt(1−r²)`, `delta ∈ [−b2, b1]`.  Since `b1, b2 ∈ [1, 1.187]` we have
`cos(b1+b2) < 0`, so `R2 >= 0 ⟺ sin(2 delta) <= 0 ⟺ delta <= 0` on this box.  The face-2
arc is the mirror image (`b1 ↔ b2`, `delta → −delta`).  **The only nontrivial boundary of
the legal set is the norm circle**, and it depends on `(r, delta)` alone (through `H`).

This also removes a spurious interval width: computing `R1` as a difference of two
separately-evaluated sines inflates it to `±0.045`, which is exactly why the first four
runs saw **zero** fully-legal boxes.  With the factored/symbolic forms the run immediately
sees thousands.

## 2. The bounded run (20000 box evaluations, 19 s)

`r16rr_factored.py`, budget 20000, base grid 3×3×3×12 per face:

```
processed 20000 in 18.4s; queue 13222
  certified by G' != 0 : 2926
  certified by G'' > 0 :  44
  illegal              : 1391
  fully-legal boxes    : 9983   (unresolved 7013)
  partially-legal      : 8626
```

Of the 8626 partially-legal boxes, `G' > 0` is already **certain** on 6509 and `G' < 0` on
1965 (only 152 straddle); `G'' > 0` is certain on 61.  So most of the partial population is
certifiable by `G' ≠ 0` as soon as the legality boundary is resolved inside the box.

## 3. The actual gap (live boxes, reported as required)

The unresolved fully-legal boxes all sit in one family:

```
face 1  r ≈ 0.375–0.379   b1 ∈ [1.000000, 1.015533]   b2 ∈ [1.000000, 1.031067]
        delta ≈ [-0.4943, -0.4614]   (delta-width ≈ 0.033)
        G'  ∈ [-0.0005, +0.3458]      <-- straddles 0
        G'' ∈ [-2.6857, -0.6734]      <-- strictly NEGATIVE, so the G'' branch is unusable
```

Representative boxes:

| face | r | b1 | b2 | delta | `G'` interval | `G''` interval |
|---|---|---|---|---|---|---|
| 1 | 0.377083–0.377500 | 1.000000–1.015533 | 1.000000–1.031067 | −0.49433…−0.46138 | [−0.000536, +0.345765] | [−2.685665, −0.673399] |
| 1 | 0.375000–0.375417 | 1.000000–1.015533 | 1.000000–1.031067 | −0.49433…−0.46138 | [−0.003757, +0.341532] | [−2.674248, −0.670701] |

**Exact obstacle.** On this family `G''` is strictly negative over the whole box, so only the
`G' ≠ 0` disjunct can close it, and closing it requires isolating the zero of `G'` inside the
box. The variation of `G'` across the box is dominated by the `(b1, b2)` width
(`|∂G'/∂b1| ≈ 0.5` from the numbers in the table), not by `delta`, so the `delta-width` is
**not** what blocks the certification here: the boxes need to be split in `b1` and `b2`
(each 0.0155 and 0.031 wide, contributing ≈ 0.008 and ≈ 0.008 to the enclosure) until the
enclosure of `G'` no longer contains 0, i.e. the boxes must resolve the `G' = 0` curve in
the `(r, b1, b2, delta)` space to width ≈ `|G'|/0.5`.

Two more obstacles visible in the same run:

* **Norm-boundary boxes.** The tightest partial boxes have
  `Nc ∈ [−0.000483, +0.048967]` with `G' ∈ [−0.4696, −0.2509]` (e.g. face 2,
  `r = 0.375000–0.375833`, `delta = −0.725022…−0.692066`).  Their `G'` is already
  sign-definite, so they close as soon as `Nc`'s sign is resolved — a `delta`-only split.
* **Straddling partials.** 152 of 8626 have `G'` straddling 0 *and* a legality boundary
  inside; these need both refinements.

## 4. What is established and what is missing

**Established (this run):**
* the disjunction is certifiable by this method: 2970 boxes certified outright by interval
  enclosures, of which **44 by `G'' > 0`** and 2926 by `G' ≠ 0`;
* the legal set's only nontrivial boundary is the norm circle and the cap residuals are
  exactly `0` and `4r cos(b1+b2) sin(2δ)` (this is what made certification possible at all);
* a concrete, located obstacle family (section 3) with `G'' < 0` where `G'` must be split.

**Not established:** the disjunction is **not** proved — 20000 box evaluations leave 7013
fully-legal unresolved boxes (plus 8626 partially-legal).  So there is **no** theorem here
and the stationary-maximum exclusion is **not** closed.

**What would close it (next obligation, for the lead to size):** on the obstacle family the
required refinement is in `(b1, b2)` (each box must shrink by roughly a factor 10 in those
coordinates) plus a `delta`-only split for the norm-boundary partials. That is a bounded
multiple of the present run — but the explicit obligation said at most 20000 evaluations, so
I stopped and report the live boxes instead of extending the budget unilaterally.

## 5. Files

`r16ii_calibrate.py` (calibration), `r16jj_disjunction.py`, `r16ll_boundary.py`,
`r16nn_run.py`, `r16oo_paired.py`, `r16pp_deltafirst.py`, `r16qq_deltafirst2.py` (the four
attempts whose diagnoses led to the factored form),
`r16rr_factored.py` (the run above), `r16mm_volume.py` (legal-set volume probe),
`r16kk_legalcheck.py` (boundary diagnosis).  Live boxes: `out/r16rr_live.json`,
`out/r16qq_live.json`, `out/r16pp_live.json`, `out/r16oo_live.json`, `out/r16jj_live.json`.
