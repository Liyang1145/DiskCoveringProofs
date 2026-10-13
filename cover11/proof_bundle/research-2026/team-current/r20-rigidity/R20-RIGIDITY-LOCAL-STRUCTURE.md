# r20-rigidity continuation (2026-09-25): local rigidity, mixed tangent cones, error bound

Author: cline2 DS v4.1f (continuation of the interrupted `cline2-r20-rigidity`).
Write scope: this directory only. **No claim registered, no lead file touched, no delegation.**
Everything below is labelled `numeric` (finite-difference/hessian based) or `proved` where the
argument is elementary and independent of numerics. Caliber: unit closed disk `D`, equal disks of
radius `r`, centre coordinates in units of the radius of `D`, angles in radians, exact rational
centre data (integers / 10^17 or / 10^60 as stored).

> Interface note (lead 2026-09-25, `lead/R21-NO-FIXED-FINITE-SHARP-WITNESS.md`): a **fixed finite
> witness set** can be covered more cheaply after a rotation (avoiding finitely many circle-equality
> angles), so no sharp *centre-space* lower bound may be derived from a frozen list of critical
> points. Every `gamma` in this report is recomputed as the max over the **configuration-determined**
> critical set (all triple circumcentres inside `D` whose three sites are the nearest ones, all
> bisector-boundary points whose two sites are the nearest ones) at each configuration actually
> visited. The moving-witness obligation is *not* discharged here; see §7.

---

## AUDIT DOWNGRADE (2026-09-25, after the lead's review) — raw readings kept, labels corrected

1. **`X60` is *not* an "exact stationary root".** The 18 active values have spread `7.78e-61` while
   the coordinates are `1e-60` rationals: this is **stationarity at the grid scale only**. No exact
   algebraic object is identified.
2. **No rank claim.** `sigma_min(J18) = 1.7e-51` is a finite-difference floor, and a small singular
   value is not rank deficiency. "rank 17 / `dim ker = 5`" are numeric readings, not proved facts;
   the implicit-function-theorem reading of the kernel would require the exact rank.
3. **"No local uniqueness" is withdrawn.** A first-order kernel direction can be a strict
   second-order minimum; the correct statement is **first-order non-rigidity only** (the
   linearisation has a 5-dimensional kernel numerically; this neither gives a positive-dimensional
   solution set nor contradicts a locally unique minimiser).
4. **"Local optimum — true" is withdrawn** and replaced by the corrected conditional form. The
   `max_i`-based cone-restricted Hessian positivity is not sufficient (explicit counterexample in
   `R20-MINIMAX-SUFFICIENT-THEOREM.md` §0), but the **weighted** form — `v^T M_lambda v >= c||v||^2`
   on `K mod rotation` with a stationary multiplier `lambda` — **does hold** at `X60`
   (`Q^T M_u Q` eigenvalues `0.1649, 0.2217, 0.2550, 0.2813`, numeric), and the corrected split-proof
   theorem then gives `gamma(x) - gamma* >= 0.0206·dist(x,O)^2`. **Remaining gap: `C_3`** (and
   exactness of (H1)/`Lambda`); the positive radius is `~9e-7`.
5. **All "certificate" numbers are numeric (finite-difference Hessians), never "proved".** The
   direction coverage of the min-max is complete *given* the Hessians; the Hessians themselves are
   not certified.
6. **Gap accounting corrected:** the gap to the target **`3/8`** is `R_stru - 3/8 = 4.98385e-3`.
   The figure `8.99e-5` is only the *certification* gap `R_stru - 0.3798939830` (numeric lower
   bound); the proved lower bound `0.3709` gives `3/8 - 0.3709 = 4.1e-3`. The earlier text quoted
   `9.0e-5` as if it were *the* gap.

---
## 0. Objects and naming (saved per instruction)

| object | file | meaning |
|---|---|---|
| `x*` | `n11/upper/certified_object.json` (22 ints / 1e17) | saved certified **upper** object, radius `C529 = 0.37998385311983870904851817957342985381159790…` |
| `X60` | `research-2026/session2/n11alg/cert_sym60.json` (22 ints / 1e60) | registered mirror-symmetric object; its registered `RD_interval` lo is `R_stru = 0.3799838531198386897222616061360932143087189561…` |
| `X_f` | `n11/kkt2/frozen.json` | 17-digit truncation of the same symmetric configuration |

**Saved facts (as required):**

1. **Candidate active-set status: 18/20, not fully saturated.** At the saved object the critical
   set has 20 points, of which exactly **18 attain the covering radius** (`9` triple Voronoi
   vertices + `9` boundary bisector points); the two remaining ones are the Voronoi vertices
   `(0,3,10)` and `(0,4,9)` (in x*-labels) at `gamma* - 1.1526819e-3`. Equivalently: of the 20
   metric local radii of the angle-only model (11 site-face circumradii + 9 switch radii),
   **18 saturate and 2 carry slack `1.1527e-3`** (`r20_calibration.json` §C, recomputed here at
   120 dps). The same 18/20 pattern holds at `X60` (`r20_mixed_tangent.log` B1).
2. **C249's upper bound is NOT the exact `rstar`.** The registered `T_cert =
   0.379983853119838689722261606136093214308718957` (`C249`, revised `C830`) is a *certified
   interval endpoint for the 1e-60 witness object* `cert_sym60.json`. My independent 120-dps
   evaluation of that object's covering radius gives `0.379983853119838689722261606136093214308718956`,
   i.e. `T_cert - gamma(X60) ≈ +8.5e-46 > 0`: the bound is 45 correct digits, not the exact real
   number. It must not be quoted as `= rstar`. Likewise `C529 - R_stru = +1.9326257e-17`
   (`= 1.9330e-17` as registered) — the saved 1e-17 object is a *legal but non-optimal* upper
   object.

---

## 1. Decidable proposition 1 — the two registered objects are the same configuration up to rotation

**Numeric (80–120 dps, exact rational inputs).** There is a rotation `R(θ)`, `θ = 271.337645738°`,
with
```
max_i min_j |x*_i - R(θ) X60_j| = 1.7712707e-9 ,
```
and the induced correspondence is `X60(i) -> x*(j)`: `[2,0,7,1,8,6,4,9,10,3,5]`. Per-site residuals:
`3.5e-10, 3.8e-11, 2.5e-10, 1.7e-10, 2.8e-10, 3.6e-10, 4.9e-10, 1.75e-9, 1.78e-9, 5.2e-10, 3.8e-10`.
The two objects have **identical radius multisets** (`0.1494285, 0.27297747, 0.70087005×2,
0.76179827×2, 0.82085326×2, 0.85881094×2, 0.89252173`), so they are the same "shape".

Consequence: the local analysis of the ideal object `X60` is directly relevant to the saved
object — the saved candidate is a `~1.8e-9` perturbation of the symmetric one, and its radius is
`1.9326e-17` worse.

Repro: `py -3 -B -X utf8 r20_rigidity_decisions.py` (Q1), `r20_target_objects.py` (§A/A2).

## 2. Decidable proposition 2 — `x*` is NOT a local minimum; the descent is towards `X60`

Numerically exact statements at 120 dps (exact rational `x*`, configuration-determined critical set):

* The 18 tight values at `x*` are **not** equal: they lie in `[gamma*-7.8624e-17, gamma*]`
  (spread `7.86e-17`); the argmax is the boundary bisector point `V2b(1,7)`.
* The first-order model is therefore the **max of affine functions with offsets**
  `gamma(x*+d) - gamma(x*) = max_i[-δ_i + ∇f_i·d] + O(|d|²)`, `δ_i ∈ [0, 7.86e-17]` — *not* a max
  of homogeneous linear functions.
* Along the unit direction `d̂` towards the rotated `X60` (`|x*(θ*) - x*| = 2.696e-9`) the
  directional derivatives of the 18 tight functions are computed twice (direct central difference
  in `t`, and the 22-coordinate finite-difference Jacobian `J18`), agreeing to `1e-34`:
  ```
  max_i ∇f_i·d̂ = +2.2006e-8   (V3(1,2,7))        min_i ∇f_i·d̂ = -8.8640e-9   (V3(0,9,10))
  ∇f_{V2b(1,7)}·d̂ = -7.1743e-9                   (the argmax function)
  ```
* The **argmax function's gradient norm** at `x*` is `0.7073` (all 18 gradient norms lie in
  `[0.5795, 0.7282]`), so a one-sided descent can in principle run at up to `~0.7` per unit
  distance — but the *affine-max model itself* caps the achievable gain: the model's minimum is
  attained after the offsets `δ_i` are consumed, i.e. within `O(1e-17)` of `x*`. The verified
  total gain towards the ideal object is `1.9326e-17`, the same scale as the offsets.
* The measured `gamma` along the segment is exactly the affine-max model:
  `gamma(x* + t·d(unit)) - gamma* = -1.9326e-17·t` (linear to 5 digits over `t ∈ [1e-3, 1]`,
  endpoints `-1.933e-20 … -1.9326e-17`), i.e. the descent runs at slope `7.17e-9` per unit
  distance — the slope of the **argmax function alone** — and stops when the offsets are consumed,
  at the ideal object.

**Correction of the interrupted analysis (audit finding).** The interrupted work reported
`tau = min_{simplex} ||J^T λ|| ≈ 3.7e-9` and concluded "any admissible first-order decrease is
`≤ 3.7e-9` per unit distance". That conclusion is **wrong for the covering radius**: `tau` bounds
only the *simultaneous* decrease of all 18 tight functions, which is not what a descent needs when
the 18 values differ by up to `7.9e-17`. The admissible first-order decrease of `gamma` at `x*` is
`7.17e-9` per unit distance (a factor `1.9` deeper than `tau`), limited in **depth** (not rate) by
the offsets `δ_i`. Verified both by the direct segment evaluation and by the identity
`max_i[-δ_i + s·∇f_i·d̂] = -1.9326e-17` at `s = |x* - X60|`. The `sigma_min(J18) = 2.411015e-9`
observation itself is confirmed (structural, stable at 40/60/80/120 dps).

Repro: `r20_rigidity_decisions.py` (Q3, Q5), `r20_direction_audit.py` (A1–A4),
`r20_nearnull.py` (interrupted, numbers confirmed).

## 3. Reading at the ideal object `X60` (grid-scale stationarity; see the downgrade banner)

At `X60` (120 dps, exact 1e-60 rationals):

| quantity | value |
|---|---|
| `gamma(X60)` | `0.379983853119838689722261606136093214308718956` (matches registered `RD_interval` lo to `9.7e-81`) |
| critical set | 20 points, 18 tight, **spread of the 18 values `7.78e-61`** — grid-scale stationarity of the pinned system, *not* an exact root |
| mirror symmetry | axis `-1.399778325045969308682966…°`, pairing `[0,1,4,3,2,10,9,8,7,6,5]`, mismatch `8.8e-61`, active set invariant |
| `J18` spectrum | `1.09666, 0.94851, …, 0.05841990826, 1.7e-51` (finite-difference floor) |
| rank / kernel | *numeric*: `sigma_min = 1.7e-51` (FD floor) — **no rank claim**; `dim ker = 5` numerically; rotation generator in `ker` to `3.1e-51` (`|J·rot|`, consistent with the exact rotation covariance) |
| kernel symmetry split | `dim(ker ∩ Sym) = 2`, `dim(ker ∩ Anti) = 3` (the rotation is one of the antisymmetric ones) |
| ranks on the invariant subspaces | `rank(J18|Sym) = 9/11`, `rank(J18|Anti) = 8/11` (9+8 = 17) |
| Danskin multiplier | `u > 0`, `min u_i = 9.8947e-3`, `‖J^T u‖_inf = 2.2e-52` ⇒ `0 ∈ ri conv{∇f_i}` |

**Distinguishing the three notions (the user's request):**

* **Local unique root** — **withdrawn**: only *first-order non-rigidity* is supported (the linearisation has a 5-dimensional kernel numerically); a first-order kernel direction may be a strict second-order minimum, so this is *not* a statement about uniqueness of the minimiser. Raw reading: the pinned system has a 5-dimensional local
  solution manifold (4 after removing the rotation), and the symmetry-reduced system on the fixed
  mirror locus still has a 2-dimensional solution set (`rank(J18|Sym) = 9 < 10`). Neither the
  18-pinned system nor its fixed-axis symmetric restriction isolates the candidate.
* **Local optimum** — **conditional on `C_3` and on exact (H1)/(H3‡)**: the `max_i`-form certificate is insufficient (counterexample), but the **weighted** K-restricted form holds numerically at `X60` (`Q^T M_u Q` eigenvalues `0.1649…0.2813`) and yields quadratic growth with the explicit split proof (`R20-MINIMAX-SUFFICIENT-THEOREM.md` §2-§3). What is established numerically: every
  first-order flat direction has strictly positive second-order growth, and every non-flat
  direction has strictly positive first-order growth (`0 ∈ ri conv ∇f_i`).
* **Far-region separation** — **open / not addressed** (§7). Nothing here excludes a distant
  configuration with a smaller radius, and per the lead's rotation obstruction no frozen finite
  witness set can do it.

## 4. Mixed tangent cones — min-max over directions (numeric Hessians; not a certified proof)

The correct second-order object over the whole flat space is
```
c_k = min_{||v||=1, v ∈ ker(J18)/rotation} max_i v^T H_i v
    = max_{λ ∈ simplex} λ_min( Q^T (Σ_i λ_i H_i) Q )        [concave in λ]
```
with `Q` an orthonormal basis of the 4-dimensional space `ker(J18) ⊖ ℝ·rotation`. The min-max
the min-max equality is an exact linear-algebra fact, so the second expression covers *all directions at once* given the Hessian values (numeric)
(every face of the tangent cone included) — no spherical sampling is used.

Result at `X60` (Hessians by central differences at 120 dps, `h = 1e-16`; Richardson check
`|H(h)-H(2h)| ≤ 4e-31` on spot entries, `0` in float64 resolution on all entries):

| object | value |
|---|---|
| `c_k` (all flat directions, dim 4) | **`0.25550766818243037826`** (float64 SDP `0.2555076680`; 16 restarts) |
| adopted input, 1e-9 safety margin (numeric) | `c₀ = 0.255507667182` |
| `ker ∩ Sym` (dim 2) | `0.3219144793097054` |
| `(ker ∩ Anti)/rotation` (dim 2) | `0.3035345292922964` |
| certificate `λ*` | sum `= 1.00000000000000000000`, all entries `≥ 0`; 8 entries above `1e-6` |
| error budget | FD truncation `≤ 4e-31`, float64 storage `≤ 1e-16`, 120-dps arithmetic `≤ 1e-110`, simplex optimisation `≤ 1e-15` |

So for **every** unit `v` in the flat space, `max_i v^T H_i v ≥ 0.2555`, and the quadratic growth
of the covering radius along flat directions is at least `0.1277·|d|²`.

Transverse first-order rate (complete, by enumerating the `C(18,17) = 18` vertices of the polar
polyhedron `{v ⊥ ker J18 : ∇f_i·v ≤ 1}`):
```
mu = min_{||v||=1, v ⊥ ker J18} max_i ∇f_i·v = 0.0014325394910901321
```
(18 feasible vertices; the maximiser of `||v||` is determined by all constraints except
`V3(0,2,10)`). `mu > 0` is the quantitative form of `0 ∈ ri conv{∇f_i}` off the flat space.

**Correction of the interrupted second-order numbers.** The interrupted work sampled the sphere in
the 3-dimensional quotient `ker J/rotation` and reported `min max_i v^T H_i v = 0.32` ("quadratic
growth ≥ 0.16"). That number came from a *sampled* subset of directions and only from the
antisymmetric part of the kernel. The complete computation gives `0.2555` over the full 4-dimensional
flat space (`0.3219` on the symmetric part, `0.3035` on the antisymmetric part); the sampled value
was thus off by 25 % *and* the direction set was incomplete. Sampling is not used as evidence here.

Repro: `py -3 -B -X utf8 r20_second_order_certificate.py` → `r20_second_order_certificate.json`,
log `r20_second_order_certificate.log`; `r20_mixed_tangent.py` (partial record B1–B5).

## 5. Objective-deficit → distance error bound (corrected: weighted split proof)

Ingredients at `X60` (all numeric):

* **transverse (first order):** `gamma(X60+d) - gamma(X60) ≥ mu·|d_⊥| - M|d|² - O(|d|³)` with
  `mu = 1.4325e-3`, `M = Q_2 = 2.2858`, `d_⊥ = P_{K^⊥}d` (Lemmas 1-2 + Prop. 3 of
  `R20-MINIMAX-SUFFICIENT-THEOREM.md`);
* **weighted (second order, the load-bearing object):** `H̄ = Σ u_i H_i` (Danskin multiplier) is
  positive **on the critical cone modulo the rotation**, `Q^T H̄ Q` eigenvalues
  `[0.1649, 0.2217, 0.2550, 0.2813]`, `c = 0.1649`. The whole-space spectrum
  `[-3.28e-2, -1.32e-2, 3e-17, 9.7e-3, …, 8.96e-1]` has two negative eigenvalues, but that is **not**
  the object the theorem uses (positivity on all of `rot^⊥` is not required);
* **max-based reading on the same flat space:** `0.2555` (numeric, `≥` the weighted value, as it
  must be).

Split proof (`d = v + w`, `v ∈ K`, `w ⊥ K`; the rotation orbit is handled by a local slice):
with `A = 4M/mu = 6382`, `L = 2||H̄|| = 1.792`,

```
gamma(x) - gamma*  >=  min(mu A/2, c/8) · dist(x, orbit)^2  =  0.0206 · dist(x, orbit)^2 ,
for  dist(x, orbit) <= min(9.0e-7, (mu A/2 - M)/C_3) .
```

So the local minimum is strict **modulo the rotation orbit** and the deficit controls the *square*
of the distance to that orbit — **conditional on the third-order remainder bound `C_3`** (and on
exactness of (H1)/`Λ`). A diagnostic estimate of the remainder scale (`max |f_i - Taylor₂|/t³` over
200 random directions at `t = 1e-3`) is `≈ 1.68`; it is a diagnostic, not a bound. The earlier
figure `c ≈ 5.1e-4` (from a cruder case analysis) is superseded by `c = 0.1649`.
## 6. What the certificate does and does not cover

**Does:** all first-order flat directions (exhaustively, via the dual min-max over the simplex);
all faces of the normal cone at `X60` (because `0 ∈ ri conv ∇f_i`, off-flat directions grow
linearly, and the flat directions are exactly `ker J18`); the values are exact to ~1e-13 with the
documented error budget; the critical set is recomputed at every configuration, so no fixed finite
witness set is used.

**Does not:** (i) the Hessians themselves are finite-difference values, so the certificate is
*numeric* — the interval-arithmetic route was attempted and deliberately **not** reported (the
interval LDL of `A(λ)-c₀I` was sabotaged by a zero-width-interval construction and by an
unnormalised `λ` from the SLSQP stage; both defects are documented in the log trail, and the clean
route used instead is the concave dual evaluated at an explicitly normalised `λ*`); (ii) the cubic
remainder bound and hence `ρ`; (iii) any global statement; (iv) the moving-witness obligation
(§7).

## 7. Far-region separation (open) and the interface with the lead's rotation obstruction

For the *global* target `r_D(11) ≥ R_stru` one needs the converse direction: exclude every
configuration with `gamma < R_stru`. The local analysis at `X60` cannot do this, and — per
`lead/R21-NO-FIXED-FINITE-SHARP-WITNESS.md` — neither can any argument that freezes a finite set
of witness points and carries it along a motion; the witnesses must move with the configuration
(or the full `R_D` derivative structure must be used). Current quantitative state:
`r_D(11) ≥ 0.3709` (proved), `≥ 0.3798939830` (numeric), `≤ T_cert = R_stru + 8.5e-46`; the gap is
`R_stru - 3/8 = 4.98385e-3` to the target `3/8`, and `R_stru - 0.3798939830 = 8.99e-5` only as the certification gap. The distance–deficit bound of §5 is the natural local half of a two-region argument
(near `X60`: nothing improves; far: needs the moving-witness machinery); it does **not** by itself
produce a lower bound.

## 8. File map / repro

```
r20_target_objects.py            -> r20_target_objects.json/.log    object comparison, moduli
r20_rigidity_decisions.py        -> r20_rigidity_decisions.json      alignment, J18 at x*/X60, Gordan, minors
r20_direction_audit.py           -> r20_direction_audit.json         the affine-max model, audit of the descent cone
r20_mixed_tangent.py             -> r20_mixed_tangent_part1.json     B1-B5 (partial record; B6 superseded)
r20_second_order_certificate.py  -> r20_second_order_certificate.json (+ r20_hess_cache.npz)  DEFINITIVE C0-C9
r20_error_bound.py               -> r20_error_bound.json             Danskin-average Hessian, remainder diagnostic
```
Run order: `r20_second_order_certificate.py` (caches Hessians; `R20_FORCE=1` to rebuild),
then `r20_error_bound.py`, then the audit scripts.

## 9. Robustness of the critical set (why the segment statements are stable)

Every one of the 20 critical points at `x*` has a **separation margin** (next non-member site
distance minus nearest distance) of at least `0.1630` (the two smallest: `V3(0,3,5)`, `V3(0,4,6)`;
the largest is `4.75e-1`). Since all perturbations used in this report are `≤ 2.7e-9`, the
"really nearest" flags of the critical set cannot change along any motion used here, so the max over
the configuration-determined critical set equals the max over the same 20 smooth functions
throughout — this is what makes the linear segment law `gamma(x*+t·d̂) = gamma* - 1.9326e-17·t`
a statement about the true covering radius and not about a frozen list of points.