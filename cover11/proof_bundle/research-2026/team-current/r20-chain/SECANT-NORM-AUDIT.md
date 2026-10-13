# SECANT-NORM-AUDIT — independent algebraic review of `lead/dbm_norm_secant.py`

Scope: review only (no modification of `lead/`, no new certificate, no extra computation beyond the two
requested controls).  This replaces the retracted `DBM-LOCAL-NORM.md` route: the correct device is a
**component secant majorant + rational LP Lagrangian bound**, which is what the lead's script does.

## 1. The core identity (verified)

For `l ≤ h ≤ u`:

> `h² ≤ (l + u) h − l u`,   with **equality exactly at `h = l` and `h = u`**

Proof: `(h − l)(h − u) ≤ 0` ⟺ `h² − (l+u)h + lu ≤ 0`.  The right-hand side is **affine** in `h` — this
is why it can be summed into a linear functional, and why no convex-conjugate step is needed.

Controls (as requested):

| interval | inequality on all sampled `h` | equality at both endpoints | max slack (secant gap) |
|---|---|---|---|
| `[0,1]` | holds | yes | `0.25` at `h = 1/2` |
| `[−1,1]` (non-singleton) | holds | yes | `1.0` at `h = 0` |
| `[−2,1]` (signed) | holds | yes | `2.25` at `h = −1/2` |
| `[0.0076,0.0077]` (the regime of interest) | holds | yes | `2.5e−9` |

## 2. Line-by-line audit of the script

* **L9–L10 (quantity and its enclosure).** `hh = constant − D·tt` with
  `constant = (i−6)L − (ROOT_ANGLES[i] − ROOT_ANGLES[6])` and
  `tt = [lo(I(−db[i][6])), hi(I(db[6][i]))]`.  So `hh` encloses the perturbation of the angular
  difference between anchor `i` and anchor `6`, using **both** directed DBM entries.  The interval is
  built with outward (lower, upper) endpoints, which is the direction the secant step needs: the
  identity is applied to the *enclosed* `h`, so a wider enclosure is conservative (larger `u − l`,
  hence a weaker but still valid majorant).
* **L14 (exact rationalisation).** `l, u` are recovered from the `mpf` bit pattern as exact rationals
  (`(±1)·mantissa·2^exp`), so the subsequent `l·u`, `l+u` are exact rational operations, not floats.
* **L15–L16 (aggregation with the signed coefficient, the lead's "`i − 6`" point).** The majorant
  `Σ_i h_i² ≤ Σ_i [s_i h_i − l_i u_i]` requires, for each `i`, the *gradient* of `h_i` with respect to
  the eight pinned coordinates.  The code accumulates `c[j] += σ_i·s_i·D` on `j ∈ [min(i,6), max(i,6))`
  with `σ_i = −1` if `i > 6` and `+1` otherwise.  **This is correct**: with `Δ_j` the gap variables,
  `a_i − a_6 = Σ_{j ∈ [min(i,6), max(i,6))} (∓Δ_j)`, i.e. `+Σ_{j=i}^{5}Δ_j` for `i < 6` and
  `−Σ_{j=6}^{i−1}Δ_j` for `i > 6`; the sign and the half-open range in the code reproduce exactly this
  pattern (verified for `i = 0,3,7,8`: sign `+` with `[0,6)`/`[3,6)`, sign `−` with `[6,7)`/`[6,8)`).
  Because all `s_i = l_i + u_i` and the DBM rows enter with `λ ≥ 0`, the aggregation is monotone in the
  right direction (upper bound), and no sign flip is introduced.
* **L15 (`f0`).** `f0 += I(s)·constant − I(l·u)` is the constant part of `Σ_i [s_i h_i − l_i u_i]`,
  matching §1 with `h_i = constant_i + (∇h_i)·x`.
* **L17–L18 (LP proposal and rationalisation).** The LP maximises the **midpoint** functional over
  `{A y ≤ b, Σy = 1, y ≥ 0}`; `λ` is read from the inequality marginals, sign-flipped
  (`max(0, −x)`), then rounded to a rational with denominator `10¹²`.  **Non-bearing**: the numbers from
  this step are only a *proposal* for `λ`; validity does not depend on the LP being solved exactly.
* **L19 (the actual bound; this is the step that must be, and is, correct).** For any `λ ≥ 0` and any
  feasible `x`: `cᵀx = (c − Aᵀλ)ᵀx + λᵀAx ≤ max_k (c − Aᵀλ)_k + λᵀb`, where the inner maximum uses only
  `Σx = 1, x ≥ 0`.  The code computes `res = c − Σλ_j A_j` and then
  `ub = hi(f0 + Σλ_j b_j + max_k hi(res_k))`, taking **upper** endpoints throughout (`hi(res_k)`,
  `hi(...)`), which is the correct direction.  So the reported `ub` is a valid upper bound for the
  affine majorant, hence for `‖x‖²`, **for the `λ` actually used** — the float LP only influences
  tightness, not truth.  This is precisely the step my earlier retracted note got wrong (it maximised a
  convex quadratic over all of `R^9`); here the inner maximum is over the **simplex**, where a linear
  functional attains its maximum at a vertex — the requested finite-vertex device.
* **L20 (certificate threshold).** `certified_C919 = (ub ≤ (191/25000)²)`; `191/25000 = 0.00764`, i.e.
  the check is `ub ≤ ρ²` with `ρ = 0.00764`, consistent with the pinned-ball radius quoted by the lead.

## 3. Verdict and residual caveats

* **Algebra: correct.**  Secant identity §1; signed coefficient/range matching `a_i − a_6` for `i ≠ 6`;
  outward interval directions at L10/L19; exact rationalisation of `l,u`; valid rational-Lagrangian
  bound with the residual maximum over the simplex; certificate threshold matching `ρ = 0.00764`.
* **Non-bearing inputs (as requested to check):** the midpoint LP solution and the rounded `λ` are
  proposals only; the final inequality is re-evaluated with interval arithmetic for that `λ`.
* **Caveats worth stating explicitly (not errors):**
  (i) the construction presumes `h_i` is **affine** in the eight pinned coordinates; if the DBM's `h_i`
  were not affine, L15–L16 would not assemble a valid majorant — this is a modelling hypothesis to keep
  visible;
  (ii) if any `hh` interval were unbounded, the exact rationalisation at L14 has no rational endpoints to
  convert; the code implicitly assumes bounded `lo/hi`;
  (iii) `linprog` marginal sign conventions are the usual `≤`-row ones (`λ = max(0, −marginal)`); the
  `max(0, ·)` clamp is safe because the residual term in L19 repairs any resulting dual infeasibility;
  (iv) tightness is not claimed: a large residual `max_k res_k` weakens `ub` even though it stays valid.
* This audit adds no certificate of its own and asserts nothing about the 118 cells' numerical values.
