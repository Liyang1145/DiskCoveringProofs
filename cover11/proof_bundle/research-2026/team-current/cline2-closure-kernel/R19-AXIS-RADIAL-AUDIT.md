# R19 — NONBEARING / WITHDRAWN

**Status: this report carries no result. Do not cite it for the hub radial lemma or the
3D reduction.** Both versions of R19 were wrong on the angle Hessian, and the equations below
are withdrawn:

* `d²θ2/dρ² = 0` (first version) — **withdrawn**;
* `d²θ2/dρ² = 2α2/L2²`, `Hess θ` 2-homogeneous, operator norm `2/L2²` (second version) —
  **withdrawn**.

The lead's exact control is the authority for the correct identities:
`lead/check_hub_radial_kernel.py` (symbolic `H_θ² = I/L⁴`; radial quadratic form vanishes) and
`lead/hub_radial_kernel_control.json` (Cartesian-vs-axis gradient and Hessian interface
controls, `A = (d/2)n`). I am not restating those formulas here.

Also withdrawn: my statement `|y ± d/2| = L1, L2`. The identities are
`L_j² = x² + (y ∓ d/2)²` and the **constraints** are `|y ∓ d/2| ≤ L_j ≤ 0.76`, hence
`|y| + d/2 ≤ 0.76` and `|y| ≤ 0.535` for `d ≥ 0.45`.

## What in this file is still usable (bookkeeping only, not new mathematics)

* the list of locations where my R19 text was wrong (kept as a trace);
* the observation that the proof-vs-code distinction must be kept explicit, and that
  `probe_axis_radial.py` (1495 evals / 0 live) and `axis_no_contraction_control.json`
  (1851 evals / 0 live) are budget diagnostics of a root-*retention* contractor, not existence
  or uniqueness proofs, and not evidence that surviving maxima were classified.

## Ledger

No claim of mine asserted the withdrawn equations: C833/C834 are the q0(5,8) closure-kernel
claims, C866 was already retracted as a duplicate review of C863. Nothing needs retracting in
the ledger; this note is the record.

---

# R19 (corrected) — hub separation axis: radial lemma + 3D reduction

**This file supersedes the first version of R19.** Five substantive errors in that version are
corrected below; the lead's corrections are all verified. Read-only, analytic, no grids/scans.
Sources: `HUB-SEPARATION-AXIS.md`, `hub_axis_stationary.py`, `probe_axis_radial.py`,
`HUB-ALL-BEARING-BOUNDARY-REDUCTION.md`, `axis_no_contraction_control.json`.

## Corrections to my earlier text

| # | My earlier claim | Correct statement |
|---|---|---|
| 1 | `d²θ2/dρ² = 0` along the ray from Q1 **[WITHDRAWN — see header]**; radial Hessian **equals** `2β1 + [2β2 − c2/L2 − a2/L2²]` | `d²θ2/dρ² = 2α2/L2² ≠ 0` in general (α2 = angle at Q2 from its outward radial); the expression is a **lower bound** (the angular Hessian contributes `+a2·2α2/L2²` and the `−c2 L2` term is not radially isotropic). Equality only when α2 = 0. |
| 2 | `A·X = (d/2)y` | Frame maps Q1 → (0,+d/2), Q2 → (0,−d/2); **`A·X = (d/2)·x`** (verified: A = (d/2)n and `|A| = d/2` to 1e-15; Q1, Q2 both have x = 0). The linear term enters `F_x`, not `F_y`. |
| 3 | reachable `|y| ≤ √(1−r²) ≈ 0.925` | From `|y ± d/2| = L1, L2 ≤ 0.76` and `d ≥ 0.45`: `|y| + d/2 ≤ 0.76` ⇒ **`|y| ≤ 0.535`**. My 0.925 came from a weaker constraint set and does not imply 0.535; the lead's bound is right. |
| 4 | the radial lemma forces `L1,L2 < 0.43` for **every** stationary point | it forces it for **local maxima** only. Stationary minima/saddles with `Lj > 0.43` exist (the lead's numeric minima). The cut is a max-only necessary condition. |
| 5 | boundary conclusion needs C862 for high `d` | it can bypass C862: the radial lemma gives `d ≤ L1+L2 < 0.86`, so the high-distance case is out automatically. C862 is not required for this step. |

## What stands from the corrected analysis

**Radial lemma (verified analytically).** Along the unit radial from Q1, writing
`t = e_r·e`, `w = e_r·n`:

```
d²/dρ² |X−Q2|² = 2 ,   d²/dρ² |X−Q2| = (1−t²)/L2 = w²/L2 ,   d²/dρ² θ2 = 2α2/L2²
d²/dρ² |X−Q1| = 0 ,    d²/dρ² θ1 = 0   (source at the ray origin)
Hess θ2 operator norm: **[my 2/L2² statement WITHDRAWN — see header]**
```

so the radial second derivative is **at least**

```
2(β1+β2) − c2/L2 − a2/L2²
```

(the `a2`-term is bounded by `+a2·2/L2²`; the `−c2 L2` term is not radially isotropic, which is
why this is a one-sided bound). Numeric confirmation at ρ = 0.30 and 0.43 on a generic ray:
`d²F/dρ² = +2.4737 / +2.5348` versus lower bound `+1.9738 / +2.0301`. Directed evaluation at
`L = 0.43` with the frozen constants
(β1 = +0.701924084, β2 = +0.693952741, c1 = +1.145102454, c2 = +1.138494697,
a1 = +0.012841585, a2 = +0.013306528):

```
face2: 2.791753650 − 2.647662087 − 0.071966079 = +0.072125484
face1 (mirror):                                   +0.059273173
```

both positive (≈14% margin), so at a local maximum **both** `L1, L2 < 0.43` — the radial
direction is to the *other* source than the distance in the bound, exactly as the proof states.
Supporting and independently checked: `Wj = 2βj − cj/Lj < 0` on `L ≤ 0.76`
(−0.102865587, −0.110113857), so the sign premise used elsewhere is a checked inequality.

**3D reduction (universal).** `A = (d/2)n` exactly; `X = M + x n + y e` with Q1, Q2 at
`(0, ±d/2)`. With `u1 = y − d/2`, `u2 = y + d/2`, `L_j² = x² + u_j²`:

```
A·X = (d/2)x  (linear part)
F_x = d/2 + (W1+W2)x + a1 u1/L1² − a2 u2/L2²
F_y = W1 u1 + W2 u2 − a1 x/L1² + a2 x/L2²
F_yy = 2(β1+β2) − x²(c1/L1³ + c2/L2³) + 2x(a1 u1/L1⁴ − a2 u2/L2⁴)
```

term-for-term identical to `hub_axis_stationary.direct` / `.equations`. `b1,b2` enter only
through `d` and the frame. **Chirality `σ1 = −1, σ2 = +1` verified**: face-1's centre bearing is
`atan2(−r cos2b1, r sin2b1) = 2b1 − π/2`, so the angle from the hub to Q1 measured from the
outward radial is `−atan2(u1,x)`, giving `∂θ1/∂x = +u1/q1`, `∂θ1/∂u1 = −x/q1` (matches
`+a1 u1/q1`, `−a1 x/q1`); face 2 is the mirror. `Q1 = M + (d/2)e` exactly, so `u1 = q1 = 0` at
Q1: Q1 is the pole of the chart.

**Domain.** `|x| ≤ 2r ≤ 0.75998 ≤ .76`; `|y| ≤ .76 − d/2 ≤ .535` (correction 3);
`d > .45` from `bj ≥ acos(r)/2`. Box is a superset. Note the `d`-upper bound `1.049` is
unnecessary once the radial lemma is in play (`d < 0.86`, correction 5) — it is only a work
parameter, and the filter that implements the lemma is `q1,q2 ∈ [.005², .43²]`.

**Pole exclusion.** `2βj·.76 < cj`; the radial part of source `j`'s gradient is at most `cj`;
projected onto the angular direction at source `j` the own term is `a_j/Lj` while all other terms
are bounded by `d/2 + c_k + a_k/L_k ≤ 1.049/2 + c_k + a_k/.445`; directed checks make `a_j/.005`
strictly larger. So no zero gradient for `Lj ≤ .005`. Uses `Lj, Lk ≤ .76` from feasibility.

## Where the certificate currently stands (proof vs code)

* **Proof-level (analytic):** the identity `A = (d/2)n`; the exact `(d,x,y)` decomposition and the
  two gradient equations; the radial lower bound and its positivity at `L = .43`; `Wj < 0` on
  `L ≤ .76`; the pole margin; `d < .86` at a local maximum.
* **Code-level (not proof):** `probe_axis_radial.py` — 1495 evaluations, 0 live boxes — plus the
  lead's `axis_no_contraction_control.json` (1851 evaluations, 0 live). The Krawczyk contractor is
  a root-*retention* device: it excludes roots by empty intersection and asserts no existence or
  uniqueness; "0 live" means the enumeration emptied, not that the surviving maxima were
  classified. The retained logic is the ordinary second-order necessary conditions (a gradient
  component excluding 0 rejects stationarity; a strictly positive Hessian diagonal/trace rejects
  local maximality), and the no-contraction control confirms the contraction is not doing the work.
* **Not proved (still open):** low-bearing arcs `b1+b2 < π/2` (the ridge-side inequality sign
  reverses; at `π/2` the two face circles coincide) — the proof document states this explicitly,
  and C863/C869/C870 must not be promoted to `bj ≥ acos(r)/2`.

## Main risks (unchanged in substance)

1. **Radial index** — equations use `u_j = y ∓ d/2` while pole terms carry `L_j`; since `u1 = 0`
   exactly at Q1, a transposition of `u` and `x` is invisible on-axis.
2. **Chirality** — a reflected assignment flips both `a_j` terms while leaving the Laplacian and
   the radial bound unchanged, so it would survive both passing tests.
3. **Max-only scope** — every use of the `0.43` cut must carry the "local maximum" quantifier;
   rewriting it as "every stationary point" is false (correction 4).

## Repro

```
cd research-2026/team-current/cline2-closure-kernel
py -3 r20_corrections.py    # all five corrections, pointwise
```
