# COSINE-ENVELOPE-LP — affine minorant library for `g(z)=1−cos z` and a valid affine lower bound

Analytic note (no numerics, no global claim, no subagents).  Written to replace the coarse barycentric
range² penalty: instead of scaling grids, bound the exact scalar energy
`E_α(θ) = Σ_{i<j} 2 w_ij (1 − cos(θ_i − θ_j))`, `w_ij ≥ 0`, from below by a finite library of affine
minorants of `g`.

## 0. ERRATUM (lead's review, 2026-09-25i) — three manuscript errors, corrected in place

1. **"At most one interior critical point" is WRONG.**  A short interval (`length < D`, `2D < π/2`) does
   **not** make `sin` monotone: an interval straddling `π/2` carries **two** interior roots of
   `sin z = s` for `s` close to `1` (e.g. `z = π/2 ± δ`, `sin = cos δ`).  The critical set must
   enumerate **both families** `z = asin(s) + 2kπ` and `z = π − asin(s) + 2kπ` **plus** the two
   endpoints — i.e. **at most 4 candidates**, not 3.  §2 rewritten.
2. **A local line cannot be extended.**  "Convex-side tangent + concave-side secant" is not
   automatically a minorant on the whole interval: **only the global per-slope infimum over `[a,b]`**
   defines a valid intercept.  §3 rewritten accordingly.
3. **The data are not rational.**  `c(s)` contains `asin` (transcendental in general, **not**
   algebraic), and `L = 2asin(19/50)`, `D` involve `π`; so the coefficients are **not rational
   functions** of rational parameters.  The operative certification is **interval lower bounds on the
   intercepts + exact `beta`/`gamma` combinations evaluated at the 9 vertices of the simplex**, with
   **no LP-optimality premise**; the implemented instance is `lead/certify_cosine_envelope_cell.py`
   (complete two-family root enumeration, same positive weights, rational `beta`/`gamma` repair), which
   certifies node 26 with `V > 0.38441171` against the old penalty's `0.3788`.  §6 rewritten.

## 1. The minorant family

`g(z) = 1 − cos z`, `g'(z) = sin z`, `g''(z) = cos z`.  For every slope `s ∈ R` define

> `φ_s(z) := s z + c(s)`,   `c(s) := min_{z ∈ [a,b]} ( g(z) − s z )`.

By construction `φ_s ≤ g` on `[a,b]`, hence for any finite slope set `S` the maximum
`φ_S := max_{s∈S} φ_s ≤ g` is again a minorant (and convex, as a max of affine functions).

## 2. Exact evaluation of the intercept `c(s)` (corrected: both root families)

`h(z) = g(z) − s z` attains its minimum at an interior critical point (`h' = sin z − s = 0`) or at an
endpoint.  Define

> `Z_s := { z ∈ [a,b] : z = asin(s) + 2kπ  or  z = π − asin(s) + 2kπ,  k ∈ Z }`

(the **two** families; empty when `|s| > 1`, in which case the minimum is at an endpoint).  Then

> `c(s) = min{ g(a) − s a,  g(b) − s b,  min_{z ∈ Z_s} ( 1 − cos z − s z ) }`.

Each family is `2π`-periodic, so an interval of length `< 2π` meets each family at most once; hence
`c(s)` is the minimum of **at most 4 explicit candidates** (two interior critical points + two
endpoints).  Both families must be enumerated: an interval straddling `π/2` really can carry two
interior roots.

## 3. Regimes of `[a,b]` (corrected: only the global infimum is a minorant)

* **Convex regime** (`cos ≥ 0` on `[a,b]`): `g'' ≥ 0`, so `g` is convex and every tangent is a global
  minorant; for the tangent slope, `c(s)` is attained at an interior critical point.
* **Concave regime** (`cos ≤ 0` on `[a,b]`): `g` is concave, so the chord is a minorant, and it is
  exactly `φ_{s_c}` with `s_c = (g(b) − g(a))/(b − a)`: `g − s_c z` is concave, so its minimum on
  `[a,b]` lies at an endpoint, giving the chord intercept.
* **Mixed regime** (`[a,b]` straddles `π/2` or `3π/2`): the correct statement is **not** "glue a local
  tangent to a local secant".  A line tangent to `g` on the convex side is a minorant on that side
  only; on the whole interval it is a minorant **iff** its intercept equals the global infimum
  `c(s) = min_{[a,b]}(g − s z)`, which §2 computes via the two families.  Likewise a chord taken on a
  sub-interval becomes a minorant on `[a,b]` only after the same global re-computation.  So the library
  `{φ_s}` is defined globally per slope and that one definition covers all three regimes; every local
  construction must be re-verified against `c(s)`.

## 4. The affine relaxation and its validity direction

Per pair introduce `t_ij` with the rows

> `t_ij ≥ s (θ_i − θ_j) + c(s)`  for every `s ∈ S` and every pair `(i,j)`   (i.e. `t_ij ≥ φ_S(θ_i−θ_j)`).

Since `w_ij ≥ 0`, the objective `Σ_{i<j} 2 w_ij t_ij` is monotone increasing in `t`; choosing
`t_ij := φ_S(θ_i−θ_j)` at any admissible θ is feasible and yields

> `Σ_{i<j} 2 w_ij t_ij = Σ 2 w_ij φ_S(θ_i−θ_j) ≤ Σ 2 w_ij g(θ_i−θ_j) = E_α(θ)`.

Hence **any** computed minimum of this affine relaxation is a valid lower bound on `min_θ E_α(θ)`, for
every library `S`.  The inequality itself needs no optimality premise.

## 5. Several fields share one `t`

For weight vectors `w^{(k)} ≥ 0` the same `t` serves all fields, because the library belongs to the
common `g`: at any θ, `t_ij := φ_S(θ_i−θ_j)` is feasible and gives `Σ 2 w^{(k)} t ≤ E_{w^{(k)}}(θ)` for
each `k`, hence also for the maximum over `k`.  All weights are nonnegative, so the epigraph direction
is the same for every field — no sense reversal, no per-field copy of `t`.

## 6. Certification route (corrected: interval lower bounds + 9-vertex evaluation)

The intercepts contain `asin` and the domain data contain `π`, so nothing here is a rational function
of rational parameters.  The operative route:

* compute **interval lower bounds** for each `c(s_k)` from the complete two-family enumeration of §2
  (at most 4 candidates per slope, each evaluated on a rational interval enclosure of its critical
  point) together with the exact endpoint values;
* combine them with **exact `beta`/`gamma` rational repairs** evaluated at the **9 vertices of the
  simplex**, as implemented in `lead/certify_cosine_envelope_cell.py` (same positive weights, no
  LP-optimality premise) — node 26 certified with `V > 0.38441171` where the old penalty gave `0.3788`.

Honest scope: this note derives the library, the corrected candidate enumeration and the validity
direction only; it makes no numeric or global claim and does not depend on grid refinement — which is
exactly the intended replacement of the coarse barycentric range² penalty.
