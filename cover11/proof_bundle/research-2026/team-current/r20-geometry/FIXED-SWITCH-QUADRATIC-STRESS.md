# Fixed-switch quadratic stress: Hessian lower matrix and a conditional criterion (lead 5c3cb5cb)

Author: r20-geometry (sole writer; no subagents; **no claim registered**). Bounded: **one analytic route**,
independent of the chain-mechanical Schur. Inputs read: `lead/FIXED-SWITCH-SOC-REDUCTION.md`.
Evidence: `fixed_switch_stress_bounds.py/.out.txt` (elementary bounds + 60-dps diagnostics).

## 1. Setup and the sign dichotomy (no general convexity claimed)

Cyclic unit anchors `U_0..U_8` (the fixed switches), arcs `Δ_i ≥ 0` between consecutive anchors,
`Σ Δ_i = 2π`, box `m ≤ Δ_i ≤ L` with `L = 2 asin(r) ≤ 2 asin(0.38)`. For the network form

> `E(U) = Σ_{i~j} c_ij |U_i − U_j|²,  c_ij ≥ 0`, `|U_i − U_j|² = 4 sin²(s_ij/2) = 2 − 2 cos(s_ij)`,

the span `s_ij` is a **sum of consecutive arcs**: `s_ij = Δ_i + … + Δ_{j−1}` (cyclic; by the 9-cycle and
`cos(2π − s) = cos s` we take `k_ij ≤ 4` steps). On the arc variables,

> `H_E(θ) = Σ_{i~j} 2 c_ij cos(s_ij) · v_ij v_ijᵀ`,  `v_ij` = indicator of the arcs between `i` and `j`,

so each pair contributes a **rank-one PSD term iff `cos s_ij > 0`** and a **rank-one NSD term iff
`cos s_ij < 0`** (the lead's dichotomy: convex for short spans, concave for long ones). *Correction
(lead c43c244f):* a single negative-cosine term is **negative semidefinite**, **not indefinite** — the
sum of PSD and NSD rank-one terms is what can be indefinite. **No general convexity of `E` is claimed**
(it is false: e.g. two edges whose indicator vectors are non-orthogonal with opposite-sign cosines).

## 2. Which spans are guaranteed short (elementary, uses the lead's own bound)

* `L = 2 asin(0.38) < π/4` because `asin(0.38) < π/8` (from `sin(π/8) = √((1−√2/2)/2) = 0.3826834… > 0.38`)
  — this is the elementary bound already used for `w_min > 0`.
* Consequently `cos` is **decreasing** on every span range with `k ≤ 4` (`4L < π`), and:
  * **1-step**: `s ∈ [m, L] ⊂ (0, π/4)` ⟹ `cos s > cos(π/4) = 0.7071 > 0` — **guaranteed convex**;
  * **2-step**: `s ≤ 2L < π/2` ⟹ `cos s > 0` — **guaranteed convex** (and the bound is *tiny*: `s` is
    just below `π/2`, so `cos(2L) ∈ (0, cos(3·0.38·…) ]`, see §3);
  * **3-step**: `3L > 3·0.76 = 2.28 > π/2` ⟹ `cos(3L) < cos(2.28) < cos(5π/7) = −0.6235 < 0` — **can be concave**;
  * **4-step**: `4L ≥ 3.04 > π − 0.1` ⟹ `cos(4L) < cos(3.04) < −0.99` — **can be concave**.

## 3. Hessian lower matrix (the criterion the lead asked for)

Since `cos` decreases on `[0, π]` and `s_ij ≤ k_ij L < π`,

> `cos(s_ij) ≥ cos(k_ij L)`  ⟹  `H_E ⪰ M_L := 2 Σ_{i~j} c_ij cos(k_ij L) v_ij v_ijᵀ`  on the whole domain.

`M_L` is the **explicit lower matrix across `P`** built from the cosine interval bounds and the fixed
9-anchor cycle: its coefficients are the known constants

`cos L ≥ cos(π/4) = 0.70711`, `cos 2L ∈ (0, 0.0109]`, `cos 3L ≤ −0.6235`, `cos 4L ≤ −0.99`
(all certified by elementary comparisons; the 60-dps values `0.71090 / 0.01077 / −0.69446 / −0.99978` are
diagnostics only — the sign of `cos 2L` is *rigorously* positive via `2L < π/2`).

**Conditional criterion.** If `M_L ⪰ 0`, then for any base point `θ₀ ∈ P` (convex),

> `E(θ) ≥ E(θ₀) + ∇E(θ₀)·(θ − θ₀) + ½ (θ − θ₀)ᵀ M_L (θ − θ₀)` on `P`,

so the global obligation `E ≥ R*²` on `P` follows from the finite data `(E(θ₀), ∇E(θ₀), M_L)`: a
**polynomial/convex criterion**, not a grid.

## 4. Decision: is the criterion possible? (not automatic)

* The two safe coefficients are `cos L ≈ 0.71` (strongly positive) and `cos 2L ≈ +0.011` (**tiny**);
  the two dangerous ones are `cos 3L ≈ −0.69`, `cos 4L ≈ −1.00` (**strongly negative**).
* Therefore `M_L ⪰ 0` asks for **nearest-neighbour dominance** in the matrix sense. *Correction
  (lead c43c244f):* a substantial 3-step weight does **not** by itself break PSD — sufficiently strong
  1–2 step weights can dominate it (the criterion is a matrix inequality, so cross terms matter); what is
  true is only that the criterion is **not implied by `c_ij ≥ 0` alone** and that the 2-step coefficient
  is small (`cos 2L ≥ 0.01160`, only ~1.6 % of `cos L ≥ 0.70711`).
* **Bound direction (lead c43c244f).** Only **lower** bounds enter `M_L`: the coefficient of the PSD
  matrix `v vᵀ` must be a *lower* bound of `2 c_ij cos(s_ij)`, i.e. `2 c_ij·cos(k_ij L)` with the
  **two-sided interval** for the span used in the safe direction:
  `cos(L) ≥ cos(π/4) = 0.70711`; `2L ∈ [1.52, 1.5592]` ⟹ `cos(2L) ≥ cos(1.5592) = 0.01160 > 0`;
  `3L ∈ [2.28, 2.3388]` ⟹ `cos(3L) ∈ [−0.69470, −0.65123]`, **lower end `−0.69470` used**;
  `4L ∈ [3.04, 3.1184]` ⟹ `cos(4L) ∈ [−0.99973, −0.99484]`, **lower end `−0.99973` used**.
  Upper bounds (e.g. `cos 3L ≤ −0.6235`) are diagnostics only and are **never** used as certificates.
* Honest gaps: (i) the `c_ij` are not known to me, so the criterion is **conditional** — deciding it
  needs the weight structure (which the lead wants this route to be *independent* of, so this is an
  interface, not a derivation); (ii) `M_L ⪰ 0` alone is not yet `E ≥ R*²`: one still needs the finite
  evaluation of `(E(θ₀), ∇E(θ₀))` and the minimisation of the resulting convex quadratic over the
  8-polytope `P` (a finite QP, not a grid); (iii) the complementary-span/Fejér–Fourier route for
  *combining* the mixed signs is **not** derived here: the only mixed-sign-safe device used is the
  elementary `|f''| ≤ 2c` Taylor bound, which is what produces `M_L`; a genuine Fejér/majoriser
  improvement (sharper than `cos(kL)`) would need a literature check (my external search route is
  currently failing, see `ANGULAR-LEGAL-DOMAIN-COVERAGE.md` §3).
* **No general convexity of `E` is claimed** (and it is false).

## 5. CORRECTED unifying representation (retraction of the finite-vertices route, lead fd64d79e)

**Retraction.** The earlier version of this section put `E_α(U) = Σ_edges α_e |edge_e|²` (the *unreduced*
sum) and claimed the maximum over the simplex is attained at a vertex, giving a finite-vertex route. That
is **wrong on both counts** and is withdrawn:
* the correct object is `E_α(U) = min over the free nodes of Σ_e α_e |edge_e|²` (anchors `U` fixed) — an
  infimum of *linear* functions of `α`, hence **concave and generally nonlinear** in `α`;
* a concave maximum need not sit at a vertex. **Calibration (exact, `schur_stress_calibration.py`):** for a
  single-edge simplex vertex (one free endpoint, one anchor) `E = min_X |U−X|² = 0`, while for the two-edge
  path `U − X − W` with weights `(a, 1−a)`,
  > `E_a(U) = min_X (a|U−X|² + (1−a)|X−W|²) = a(1−a)|U−W|²` (stationary `X = aU + (1−a)W`),

  whose maximum over `a ∈ [0,1]` is at the **interior** point `a = 1/2` with value `|U−W|²/4 > 0`, whereas
  every vertex gives `0`. Elementary control: `−(x−1/2)²` maximises at `1/2`.

**Correct proof (written out).** Let the squared oracle be
`V(U)² = min_{X,t} t` subject to `|X_v − X_w|² ≤ t` for every edge `e = (v,w)`, with the anchors `U` fixed
and the free nodes `X` free (the free/unbounded-node issue is handled by Slater/coercivity, see below).
Take multipliers `α_e ≥ 0` and form the Lagrangian
> `L(X, t; α) = t + Σ_e α_e (|edge_e(X)|² − t) = t(1 − Σ_e α_e) + Σ_e α_e |edge_e(X)|²`.

* `inf_t L` is finite **iff `Σ_e α_e = 1`** (otherwise `→ −∞`), and then `L = Σ_e α_e |edge_e(X)|²`.
* `inf_X L` is `E_α(U) := min_X Σ_e α_e |edge_e(X)|²` (a convex quadratic in `X`, attained; the anchors
  enter only through the edge terms), which is **concave (nonlinear) in `α`** as an infimum of functions
  linear in `α`.
* **Weak duality:** `V(U)² ≥ E_α(U)` for every `α` in the simplex, so `V(U)² ≥ max_α E_α(U)`.
* **Slater/strong duality:** the feasible set of `(X,t)` is closed and convex; setting all free nodes to
  `0` and `t` large gives strictly feasible points, and bounded `t` bounds every free node by following
  graph paths to anchors (the graph is connected to the fixed anchors — `lead/FIXED-SWITCH-SOC-REDUCTION.md`
  §2), so coercivity holds and the primal value is attained; conic duality then gives
  > `V(U)² = max_{α ∈ simplex} E_α(U)`,

  a **concave maximisation over the simplex with interior optima allowed** — no vertex enumeration.

**Consequences.** (i) The identity is *pointwise in `U`*; no min–max exchange in `θ` is presupposed.
(ii) Since `V ≥ 0` and `V` is convex, `U ↦ V(U)²` is convex even though no single frozen `E_α` is a
definite quadratic form; `max_α E_α(U) ≥ E_{α₀}(U)` pointwise, so the maximum can be positive in
directions where one frozen `α₀` is negative (the "repair" property). (iii) The global obligation is the
pointwise disjunction with the *correct* `E_α`: for each admissible `U` there is `α` in the simplex with
`E_α(U) ≥ R*²` (equivalently `V(U) ≥ R*`) — with `α` chosen per point, and the optimum possibly interior.
(iv) Nothing here depends on the SLSQP stress or on C897 (the latter is `alternative`'s).

**Calibration evidence** (`schur_stress_calibration.out.txt`): K1 `E = 0` at a vertex; K2
`E_a = a(1−a)|U−W|²` (sympy, exact); K3 interior maximiser `a = 1/2`, value `|U−W|²/4`; K4 concave control;
K5 `d²/da² E_a = −2|U−W|² ≤ 0` (concavity confirmed symbolically).

Repro:
```
py -3 -B -X utf8 research-2026/team-current/r20-geometry/fixed_switch_stress_bounds.py
```
