# Quantitative no-improvement neighbourhood around the C891/C892 root — corrected design

Scope: `research-2026/team-current/r20-rigidity/` only (sole writer). **Status: design + scalar lemma,
no certification.** This file supersedes the first version and retracts three claims (see §6):
the neighbourhood is **not** the 12D symmetric box; "mixed Hessian = 0" holds only at the exact
reflection point (Sym/Anti split), not on a box and not for the `T/T^⊥` split; the pilot's finitely
many sampled directions do **not** bound all directions.

## 1. Setting and notation (unrestricted neighbourhood)

* `x* ∈ R^22` the exact C891/C892 configuration, `R*` its radius, `A` the 18 active branch functions
  `f_i` (9 face circumradii + 9 tie radii, explicit physical formulas), `w ∈ ri Δ_18` the exact C897
  weights with `Σ w_i ∇f_i(x*) = 0`, `Σ w_i = 1`, `w_i > 0`.
* `T = ker J_A(x*) ⊂ R^22` (dim 5 = 2 Sym + 3 Anti; the rotation direction `rot ∈ T`; structural
  proof + interval rank for the Anti part).
* For a displacement `v ∈ R^22` use the **orthogonal split** `v = k + t`, `k ∈ T`, `t ∈ T^⊥`
  (dim `T^⊥` = 17). This is *not* the reflection split: the mixed block `k^T H_W t` does not vanish
  in general — the Sym/Anti mixed block vanishes only at the exact `σ`-fixed point `x*`.
* `|v_quot| = dist(v, orbit)`: the norm after removing the rotation component (branches and objective
  are rotation invariant).
* Box: the **unrestricted** product box in the 22 centre coordinates
  `B(ρ) = { x* + Σ_s σ_s E_s + Σ_a α_a BA_a : |σ_s| ≤ ρ, |α_a| ≤ ρ }` (Sym block × Anti block; `R`
  enters only through the chart, so it is not a separate direction). All directions of `R^22` allowed.

## 2. The five constants (what has to be certified)

| constant | definition | how |
|---|---|---|
| `mu` | `min_{v ∈ T^⊥, |v|=1} max_i ∇f_i(x*)·v` (transverse rate) | one LP (18 facets, 17 dims), 18 vertex candidates |
| `lambda` | `(1/2)v^T H_W v ≥ (lambda/2)|v_quot|²` for `v ∈ T` | C893 (Sym 2×2) + C901 (Anti 2×2) + Sym/Anti mixed block `= 0` **at x*** (proved) |
| `M` | operator bound `‖H_W(x*)‖` | conservative `M ≤ Σ_i w_i L2_i` |
| `L2` | `max_i sup_{B(ρ)} ‖D²f_i‖` (all directions) | closed form from the branch geometry (§5) |
| `L3` | `max_i sup_{B(ρ)} ‖D³f_i‖` (all directions) | same sources (§5) |

`M` is not redundant: it is the constant of the mixed term created by the `T/T^⊥` decomposition.

## 3. Scalar lemma (uniform growth, corrected: sliced at the rotation first) — verified proof

**Slice first.** Fix the Euclidean slice `S := {v ∈ R^22 : v · rot(x*) = 0}` (dim 21), and put
`K := T ∩ S` (dim 4, `T = ker J_A(x*)`). For `v ∈ S` write `v = k + t` with `k ∈ K`,
`t ∈ S ∩ K^⊥` (dim 17). Inside `S` the rotation direction is absent, so `|k|` *is* the
rotation-quotient norm; this is what the earlier version failed to do (`|k_quot|` does not control
`|k|` on all of `R^22`).

**Hypotheses** (for all `v ∈ S` with `|v| ≤ ρ`):
```
 (B1)  Σ_i w_i ∇f_i(x*) = 0 ,  Σ_i w_i = 1 ,  w_i > 0 ;
 (B2)  max_i ∇f_i(x*)·v ≥ μ |t| ;
 (B3)  v^T H_W(x*) v ≥ λ |k|² − 2 M |k||t| − M |t|²              (equivalently the 1/2-form version) ;
 (B4)  |f_i(x*+v) − f_i(x*) − ∇f_i·v| ≤ (L2/2)|v|²   and   (B3)'s remainder ≤ (L3/6)|v|³ .
```
**Constants.** `M ≥ 1/4` (a bound may always be enlarged to 1/4), `η := min(1/4, λ/(16M))`, and
```
  (Hλ)      (λ/2)(1 − η²) − M η − M η²/2  ≥  λ/3          [scalar side condition, checked in §3.1]
  ρ := min( 1 , μη/L2 , λ/(2L3) ) ,        c := min( μη/(2ρ) , λ/4 ) .
```
**Conclusion.** For every `v ∈ S` with `0 < |v| ≤ ρ`:
```
      F(x*+v) − R*  ≥  c · |v|² ,        F := max_i f_i .
```
**Proof.** *Case A* (`|t| ≥ η|v|`): by (B2) and (B4),
`F ≥ R* + max_i∇f_i·v − (L2/2)|v|² ≥ R* + μη|v| − (L2/2)|v|²`. The function
`t ↦ μη t − (L2/2)t²` dominates `(μη/2)t` exactly for `t ≤ μη/L2`; hence
`F − R* ≥ (μη/2)|v| = (μη/(2|v|))|v|² ≥ (μη/(2ρ))|v|²` since `|v| ≤ ρ`. *Case B* (`|t| < η|v|`):
then `|k|² = |v|² − |t|² > (1−η²)|v|²` and, by (B3), (B4) and `F ≥ W`,
```
 F − R* ≥ [(λ/2)(1−η²) − Mη − (M/2)η²]|v|² − (L3/6)|v|³
        ≥ (λ/3)|v|² − (L3/6)ρ |v|²  ≥  (λ/3 − λ/12)|v|²  =  (λ/4)|v|² ,
```
using (Hλ), `ρ ≤ λ/(2L3)`, and `(L3/6)ρ ≤ λ/12`. Both cases give `F − R* ≥ c|v|²` with
`c = min(μη/(2ρ), λ/4)`. ∎

### 3.1 (Hλ) holds unconditionally (no side conditions; lead's simplification)

`η := min(1/4, λ/(16M))` gives `η ≤ 1/4` and `Mη ≤ λ/16` (equality in the first branch; in the second
branch `η = 1/4` means `λ ≥ 4M`, hence `Mη = M/4 ≤ λ/16`). Hence
```
 λ/2 (1−η²) ≥ (λ/2)(1 − 1/16) = 15λ/32 ,   Mη ≤ λ/16 ,   Mη²/2 ≤ (Mη)η/2 ≤ (λ/16)(1/4)/2 = λ/128 ,
```
so the left side of (Hλ) is `≥ (60 − 8 − 1)λ/128 = 51λ/128 > λ/3` (as `153 > 128`). **No condition on
`M` or `λ` is needed.** The previous version of this section is retracted in §6: it used `2μη/L2`
(only non-negativity at the endpoint, instead of `μη/2·|v|` for `|v| ≤ μη/L2`), `η = min(1, λ/(8M))`
(at `η = 1` the kernel case has `1−3η < 0`, no positive bound), and it failed to slice at `rot` first.
* **Regime 1: `λ ≤ 4M`** (so `η = λ/(16M)`, `η ≤ 1/4`). Then `Mη = λ/16` and
  `(λ/2)(1−η²) − Mη − (M/2)η² = 7λ/16 − ((λ+M)/2)η²`, with
  `((λ+M)/2)η² = λ²(λ+M)/(512M²) ≤ 5λ²/(512M) ≤ 5λ²/128` (using `λ+M ≤ 5M` in this regime and
  `M ≥ 1/4`). Hence the left side is `≥ λ(56 − 5λ)/128`, which is `≥ λ/3` iff `λ ≤ 8/3`; in
  particular for the registered curvature scale (`λ ≈ 0.165`) it is `≈ 0.42 λ > λ/3`.
* **Regime 2: `λ ≥ 4M`** (so `η = 1/4`). Then `(λ/2)(1−1/16) − M/4 − M/32 = 15λ/32 − 9M/32
  ≥ 15λ/32 − 9λ/128 = 51λ/128 ≥ λ/3` (as `51/128 > 1/3`).

So (Hλ) holds whenever `λ ≤ 8/3` and `M ≥ 1/4`; both are checkable side conditions on the constants,
not assumptions about the geometry. The earlier version of this section is retracted in §6: it used
`2μη/L2` (which only gives non-negativity at the endpoint) and `η = min(1, λ/(8M))` (with `η = 1` the
kernel case had no positive bound since `1−3η < 0`).

Remarks. (i) Purely scalar, no optimization. (ii) `M` enters only via `η`: larger `M` ⇒ smaller `η`
⇒ smaller `μη/L2`, so a large mixed term caps the box. (iii) The conclusion is a bound on `|v|` in the
slice `S`, i.e. on the rotation-quotient norm — nothing is claimed along the orbit itself (correct,
the configuration is rotation invariant). (iv) `L2`, `L3` must bound **all** directions of `S`;
sampled directions are inadmissible. (v) The slice `S` is a **fixed physical** slice in the 22 centre
coordinates (no chart coordinate, no `R` variable: the branch functions do not depend on `R`), so the
certificate never mixes the chart with the physical ball.

## 4. Representation

Reflection split `R^22 = Sym(11) + Anti(11)`, `R^23 = Sym(12) + Anti(11)`. Coordinates: `(σ_s)` for
Sym (7D chart box carried by the chart map) and `(α_a)` for Anti (integer basis, diagonal Gram
`diag(2,...,2,1,1,1)`). Consequences:
* the interval certificate for `λ` lives in two 2×2 blocks (C893, C901), because the Sym/Anti mixed
  block vanishes **at x*** exactly (σ-invariance of the weights + equivariance of the branches) —
  a statement about the single point whose Hessian enters (A3);
* the `T/T^⊥` mixed term is carried by the scalar `M`; it is never assumed away;
* `L2`, `L3` are needed as box-suprema over all directions — from the closed forms of §5, neither
  from sampled directions nor from a 22×22×22 tensor.

## 5. Coarse closed-form `L2`, `L3` (all directions, executable constants)

Two ingredients: **geometric margins over the ball** (interval-checkable) and **explicit numerator
bounds** from the rational branch formulas. Exponents are *derived*, not guessed.

**(M) margins.** `det_min := min over the 9 active face triples of |g_1 × g_2|` (= 2 x min area, the
registered strict-empty margin); `d_min := min over the 9 ties of |c_{k+1} − c_k|`;
`rad_min := min over the 9 ties of 1 − |A0|²` (the radical margin, `A0 = (κ/|d|²)d`);
`f_min := R* − ρ` (circumradius/tie radius stays `≥ f_min` on the ball since `|f_i − R*|` is bounded
by the displacement times the gradient bound). All four are interval-checkable on the chart box.

**(F) face branch.** With `g_1 = c_a − c_b`, `g_2 = c_a − c_c`, `P = |g_1|² g_2^⊥ − |g_2|² g_1^⊥`
(cubic in `g`), `det = g_1 × g_2` (quadratic):
```
   w = P / (2 det)              (exact circumcentre displacement, verified identity)
   |P| ≤ 16, |DP| ≤ 16, |D²P| ≤ 24, |D³P| ≤ 24     (using |g_i| ≤ 2, |g_i^⊥| = |g_i|)
   |det| ≤ 4, |Ddet| ≤ 4, |D²det| ≤ 4, |D³det| = 0
   => |Dw| ≤ (|DP||det| + |P||Ddet|) / det_min²                          ≤ 128 / det_min²
      |D²w| ≤ (|D²P||det| + 2|DP||Ddet| + |P||D²det| + 2|P||Ddet|²/det) / det_min³  ≤ 512 / det_min³
      |D³w| ≤ (|D³P||det| + 3|D²P||Ddet| + 3|DP||D²det| + 3|D²P||Ddet|²/det + ...) / det_min⁴
            ≤ 4096 / det_min⁴                                              (conservative, degree-explicit)
   f = |w| :  |Df| ≤ |Dw| ,  |D²f| ≤ |D²w| + |Dw|²/f_min ,
              |D³f| ≤ |D³w| + 3|Dw||D²w|/f_min + |Dw|³/f_min²   (differentiated chain rule, crude)
```
Note the exponents `det_min^{-2}, ^{-3}, ^{-4}` for `w` (not `^{-1}`: `P` is one degree higher than
`det` in `g`, so each derivative raises the exponent by one) — this is the point the lead flagged.

**(T) tie branch.** `A0 = (κ/|d|²)d`, `n = d^⊥/|d|`, `t = ±sqrt(1 − |A0|²)`, `p = A0 + t n`:
```
   |κ| ≤ |d| ,  |DA0| ≤ 4/d_min ,  |D²A0| ≤ 16/d_min² ,  |D³A0| ≤ 64/d_min³
   |Dn| ≤ 1/d_min ,  |D²n| ≤ 2/d_min² ,  |D³n| ≤ 8/d_min³
   |Dt| ≤ |DA0| / sqrt(rad_min) ,  |D²t| ≤ (|D²A0| + |DA0|²/rad_min)/sqrt(rad_min) ,  likewise for D³
   |Dp| ≤ |DA0| + |Dt| + |Dn| ,   |D²p| , |D³p| by the same product rule
   f = |p − c_k| : same |.|-chain rule as (F) with f_min
```
Numerically the tie denominators are harmless (`d_min ~ 0.3`, `rad_min ~ 0.1..1`), the face
denominator is the binding one (`det_min ~ 0.1`, exponents 2/3/4).

**(A) assembly.** `L2 := max_i L2_i`, `L3 := max_i L3_i` (max over the 18 active branches), and
`M ≤ Σ_i w_i L2_i` (using the certified weights). The fixed point `ρ = min(1, μη/L2, λ/(2L3))` with
`L2, L3` depending on `f_min = R* − ρ` is solved by two or three iterations (monotone decrease).

**(E) executable script.** `r20_operator_bounds.py` evaluates the margins (M) over the chart box in
interval arithmetic, inserts the explicit numerator bounds of (F)/(T), iterates the fixed point and
prints the constants `{μ, λ, M, L2, L3, η, ρ, c}` together with the branch-validity margins. Output:
`r20_operator_bounds.json/.log`. Any constant it prints is a *candidate* until the interval check of
the numerator bounds (a finite symbolic check of the coefficients) is done — that check is the next
obligation, listed in §7.

### 5.1 Executed: the naive substitution is vacuous — the bounds must be scale-aware

Running (E) with the coefficients as written above (worst-case numerator over `det_min`) gives on the
lead's box:
```
  margins:  det_min >= 0.30784 ,  d_min >= 0.45110 ,  rad_min >= 0.94594
  L2(face/tie) = 1.93e7 / 1.33e3 ,  L3(face/tie) = 1.40e11 / 1.03e5
  eta = lambda/(16 M) ~ 2.6e-10 ,  rho = mu eta / L2 ~ 2e-20 ,  c ~ 2e-2        <-- useless
```
The loss is *not* from the exponent bookkeeping (the exponents `det_min^{-2,-3,-4}` are right); it is
from the **coefficients**: the true face `‖Dw‖` is dimensionless `O(1)` (circumcentre derivatives are
scale-free), while the crude bound `256/det_min²` is `~2700`; the true `L2` is `~5`, the bound is
`~2e7`. Root cause: `w = P/(2 det)` with `P` cubic in `g`, so a worst-case numerator bound throws
away the exact **homogeneity** of `w` (degree 1) and of `Dw` (degree 0). The fix is to write the
bounds in scale-separated form:
```
   |w| <= (|g|^3-ish numerator) / (|g|^2 sin theta) = |g| * N_0 / sin theta ,
   |Dw| <= N_1 / sin theta ,  |D^2 w| <= N_2 / (|g| sin^2 theta) ,  |D^3 w| <= N_3 / (|g|^2 sin^3 theta)
```
with dimensionless `N_k` (bounded by small integers/half-fractions) and `sin theta = det/(|g_1||g_2|)`
the *dimensionless* conditioning factor (`>= det_min/(2·2)` under the registered margins). Only then
can the `L2/L3` be small enough for a non-vacuous `rho`. Same treatment for the tie branch
(dimensionless `|d|`-scaled denominators: `|D A0| <= N/|d|`, etc., with `kappa/|d|^2` homogeneous of
degree 0, as the executed run already shows — the tie side loses only a factor ~10, the face side
loses ~1e6). Consequence for planning: the symbolic scale-aware derivation of the `N_k` is the real
content of the operator-bound step, not the exponent bookkeeping.

## 6. Retractions and corrected reading of the first pilot

* **Retracted (v1 §1, second version §3):** the box is not the 12D symmetric box — the neighbourhood
  must be the unrestricted product box of §1.
* **Retracted:** "mixed Hessian = 0" as a *box* statement — it holds only at `x*`, only for the
  Sym/Anti split; the `T/T^⊥` mixed term exists and is carried by `M`.
* **Retracted (third version §3, errors found by the lead):** (a) `ρ ≤ 2μη/L2` only makes the linear
  bound *non-negative* at the endpoint (it gives `μη/2·|v|` only for `|v| ≤ μη/L2`); (b)
  `η = min(1, λ/(8M))` is inadmissible because at `η = 1` the kernel case has `1−3η < 0`, i.e. no
  positive bound; (c) `|k_quot|` does not control `|k|` on `R^22`, so the rotation must be sliced
  first. The corrected statement (§3) slices at `rot(x*)`, uses `K = T ∩ S` (4D) and
  `t ∈ S ∩ K^⊥` (17D), `η = min(1/4, λ/(16M))`, `ρ = min(1, μη/L2, λ/(2L3))`,
  `c = min(μη/(2ρ), λ/4)`, with (Hλ) verified by explicit arithmetic in §3.1.
* **Retracted:** "the pilot `ρ` can be fed into a global argument" — the pilot is numeric and
  uncertified, and its constants correspond to the erroneous version above.
* **Kept (numeric, design-stage only, not certificates):** `μ = 0.00143254` (full 18-vertex
  enumeration, reproduces W7's 0.0014325395); the point spectrum of `H_W` on the centred kernel
  `{0.164903, 0.221670, 0.254960, 0.281331}` (anti quotient + sym); `max_i‖H_i‖₂ = 4.572`; and the
  sampled directional third derivatives (max 2.29 over 4 kernel + 4 transverse directions) — the
  last item is **not** an `L3` bound.

## 7. Next executable obligations (all scalar, in order)

1. Check the lemma's two regimes (`M ≥ λ/4` and `M < λ/4`) and record the exact constants.
2. Derive the closed-form `L2_i`, `L3_i` of §5 over the box (Sym part via chart-Jacobian bounds, Anti
   part via the integer basis): explicit fractions in `area_min`, `d_min`, `rad_min`, `R*`, `ρ`.
3. Insert them into §3, report the resulting uniform `(ρ, c)`; only then consider interval
   certification of the scalars, and only after that any re-attachment to a global argument.

## 8. Determinant provenance (for the audited whole-matrix diff)

Three different determinants appear in this directory; they live in **different bases** and must not be
compared:

| value | object | basis / scope |
|---|---|---|
| [-4.00004e-4, -3.99635e-4] (nonzero) | 8x8 **witness minor** of the Anti gradient block | integer anti-basis columns [2,3,4,5,7,8,9,10] of A_anti (18x11); proves ank(A_anti) >= 8 |
| >= 0.217798969238 | **certificate 2x2** on the explicit rotation-free complement | coordinates (KV[0], KV[2]) of the 3D kernel (i.e. the $-basis 2-plane); this is the Sylvester object |
| 9.281962525266781324953 (lower) | **B2 pencil** = U^T B3 U | same $-coordinates as the certificate but the *unnormalised* coefficient basis; det(B2), B11, B22 also recorded in B_PD_sylvester |

Also in the JSON: B2_entries, G2_entries (full interval endpoints, 4 entries each) and
B3_entries, G3_entries (3x3 endpoints) — so the whole pencil, not just the two scalars, is
auditable from the artifact itself. The obsolete REPORT.md in this directory is **not** mine and its
float-matrix rational-determinant rank claim is not accepted (lead ruling).

(added 2026-09-25: determinant provenance block for the lead's whole-matrix diff)

## 9. Operator bounds, derived form (inverse-derivative recurrence; pointwise identities)

**Norm convention.** All norms are operator norms along unit directions of the 22-dimensional physical
centre space: for a vector-valued function F, |D^k F| := sup_{|v|=1} ||D^k_v F||_2 (no chart, no R).

**Face branch (exact, no guess).** With g_1 = c_a − c_b, g_2 = c_a − c_c,
A = [g_1ᵀ; g_2ᵀ],  = −(1/2)(|g_1|², |g_2|²)ᵀ, the relative circumcentre w = p − c_a satisfies
A w = b **exactly**. Since A is linear and  quadratic in the centres (D²A = 0, D³b = 0),
differentiating gives the closed recurrence
`
   Dw   = A^{-1} ( Db   − (DA) w )
   D²w  = A^{-1} ( D²b  − 2 (DA) Dw )
   D³w  = A^{-1} ( − 3 (DA) D²w )
`
with σ_min(A) ≥ |det A|/‖A‖_F, hence κ := ‖A^{-1}‖_2 ≤ 2√2 / |det A| (because ‖A‖_F ≤ 2√2,
|g_i| ≤ 2). The remaining factors are explicit and **derived**, not fitted:
|b| ≤ 2√2, |Db| ≤ 2√2, |D²b| ≤ 2, ‖DA‖ ≤ 2 (each D_v g_i has norm ≤ √2). Therefore
`
   |Dw|  ≤ κ ( |Db| + ‖DA‖ |w| )
   |D²w| ≤ κ ( |D²b| + 2 ‖DA‖ |Dw| )
   |D³w| ≤ 3 κ ‖DA‖ |D²w|
`
and for the branch value  = |w| the elementary chain rule gives
|Df| ≤ |Dw|, |D²f| ≤ |D²w| + |Dw|²/f, |D³f| ≤ |D³w| + 3|Dw||D²w|/f + |Dw|³/f².

**Tie branch.** A0 = (κ_d/|d|²) d, 
 = d^⊥/|d|, 	 = sqrt(1 − |A0|²), p = A0 + t n; the same
recurrence principle applies after writing A0 as the solution of the 2×2 projection system, the field
denominators being |d| and 	. The explicit factors used so far are
|DA0| ≤ 4/|d|, |D²A0| ≤ 16/|d|², |D³A0| ≤ 64/|d|³, |Dn| ≤ 1/|d|, |Dt| ≤ |DA0|/t (these are
*conjectural coefficients*, to be re-derived by the same recurrence before use).

**Point vs ball.**
* Pointwise (at x*): the identities above are exact and were verified numerically against the exact
  jets at the root over 9 faces x 6 random directions — max relative error D_v w = 4.24e-16,
  D²_v w = 1.63e-15 (20_recurrence_check.py/.json/.log); measured magnitudes at the root:
  ‖A‖_F ≤ 1.0275, |b| ≤ 0.3734, ‖DA‖ ≤ 1.4142, |Db| ≤ 0.5667, |D²b| ≤ 0.8087,
  ‖A^{-1}‖ ≤ 3.3522.
* Ball: the same recurrence holds pointwise at every x in the ball, but the *factors* move. The
  conversion must be perturbative (lead): |det A(x) - det A(x*)| ≤ Lip_det·ρ with the explicit
  Lip_det ≤ 2‖DA‖‖A‖_F ≤ 4·2√2-type bound, and likewise |d|, 1 - |A0|²; no chart-margin shortcut
  and no use of the 22D hull (which is only a coordinate envelope of the chart image).

**Branch-legal domain at the root (to be interval-certified, separate from the above).**
|det A| ≥ 0.30784 (min over the 9 active faces; = 2 x min area), |d| ≥ 0.45110,
1 - |A0|² ≥ 0.94594 (min over the 9 ties),  ≥ R* - ρ > 0. These are the only geometric inputs the
recurrence bounds need.

**Not reported here:** any ρ or c. The constants above are derived for the pointwise recurrence;
the ball version needs the perturbative margin step, so no quantitative claim is made yet.

## 10. Recurrence constants, corrected (lead audit) + tie recurrence

**Corrections to section 9** (the earlier |Db| <= 2 sqrt2 and |D^2 b| <= 2 were unsafe):

* |Db| <= 4, not 2 sqrt2: with |g_i| <= 2 and |D_v g_i| <= sqrt2,
  |Db|^2 = sum_i (g_i . D_v g_i)^2 <= sum_i |g_i|^2 |D_v g_i|^2 <= 4 sum_i |D_v g_i|^2, and
  sum_i |D_v g_i|^2 = |v_a - v_b|^2 + |v_a - v_c|^2 <= 2(|v_a|^2+|v_b|^2) + 2(|v_a|^2+|v_c|^2) <= 4
  (each |v_i|^2 <= 1 on the unit sphere of the 22D space). The joint use of both facts gives 4.
* |D^2 b| <= 2 sqrt2 safe, sharp 3/sqrt2: D^2_v b = -( |D_v g_1|^2, |D_v g_2|^2 ), and the exact
  sphere constraint is max over |v|=1 of max_i |D_v g_i|^2 = 3/2, attained by v_a = sqrt(2/3) e,
  v_b = v_c = -1/sqrt(6) e (lead counterexample: |D_v g_i|^2 = 1.5 each, hence
  |D^2_v b| = 1.5 sqrt2 = 3/sqrt2 > 2). Derivation: with x = |v_a|, |v_b| = |v_c|, collinear and
  antiparallel to v_a, |D_v g_i|^2 = (1+x^2)/2 + x sqrt(2(1-x^2)) <= 3/2 (max at x = sqrt(2/3)).
* |D_v g_i| <= sqrt2: |v_a - v_b|^2 <= 2(|v_a|^2 + |v_b|^2) <= 2.
* f >= R* - rho is WITHDRAWN: the circumradius is not globally 1-Lipschitz, so f must come from a
  certified positive lower bound over the domain (interval statement f_i >= f_lo > 0), separately from
  rho. Random-direction tests support the implementation of the recurrence only; they are not evidence
  for universal bounds.

**Tie branch recurrence (derived form).** With d = c_b - c_a, kappa_d = (|c_b|^2 - |c_a|^2)/2,
u = A0 = kappa_d d/|d|^2 (the minimiser of |u| under d.u = kappa_d), lam = kappa_d/|d|^2,
t = sqrt(1-|u|^2), n = d^perp/|d|, p = u + t n, f = |p - c_a|:

    lam     = kappa_d/|d|^2
    Dlam    = ( Dkappa_d |d|^2 - 2 kappa_d (d.Dd) ) / |d|^4
    Du      = Dlam d + lam Dd
    Dn      = (Dd)^perp/|d| - (d.Dd)/|d|^2 n
    Dt      = -(u.Du)/t
    Dp      = Du + Dt n + t Dn
    Df      = ((p-c_a).Dp)/f ,  D^2f = (Dp.Dp + (p-c_a).D^2p)/f - ((p-c_a).Dp)^2/f^3

Explicit sphere-constrained factors: |kappa_d| <= 1, |Dkappa_d| <= 2 (|c_i| <= 1, |D_v c_i| <= 1),
|D^2 kappa_d| <= 1, |Dd| <= sqrt2, |D^2 d| = 0, plus the denominators |d| and t = sqrt(1-|u|^2) whose
changes over the ball are controlled perturbatively (|D_v|d|| <= |D_v d|, |D_v(1-|u|^2)| <= 4|u||Du|).
Higher t-derivatives follow from t^2 = 1-|u|^2 by the same recurrence
(2t Dt = -2u.Du; 2(Dt)^2 + 2t D^2t = -2Du.Du - 2u.D^2u; ...).
Numeric verification of the tie identities against the exact jets is the next step. The face factors
printed in section 9 are superseded by the corrected list above.

## 11. Final corrections (lead audit) and the exact tie recurrence as a linear system

**Sharpness claims withdrawn.** The assertion max |D_v g_i|^2 = 3/2 is FALSE: taking
v_a = e/sqrt(2), v_b = -e/sqrt(2), v_c = 0 gives |v_a - v_b|^2 = 2 (the true maximum of that single
quantity). My "derivation" assumed |v_b| = |v_c|, which is not WLOG for an asymmetric objective. Hence:
* keep the SAFE |D^2 b| <= 2 sqrt2 (and |Db| <= 4, |D_v g_i| <= sqrt2);
* no sharpness claims anywhere; the constants are not to be optimised at this stage;
* the exact sphere constraint actually available is only |v_a - v_b|^2 <= 2(|v_a|^2+|v_b|^2) <= 2.

**Exact tie recurrence (identity form; linear system, no numeric rho).** The tie branch point p is the
intersection of the radical line d.p = kappa_d (d = c_b - c_a, kappa_d = (|c_b|^2-|c_a|^2)/2) with the
unit circle |p| = 1, and it satisfies both equations **exactly**:
```
   d.p = kappa_d            (since d.n = 0 and d.A0 = kappa_d)
   |p|^2 = 1                (since |A0|^2 + t^2 = 1 with t = sqrt(1-|A0|^2))
```
Differentiating along a unit direction v gives the 2x2 linear system
```
   M D_v p = rhs ,   M = [ d^T ; p^T ] ,   rhs = ( D_v kappa_d - (D_v d).p , 0 )^T ,
   det M = d x p = t |d|  (up to sign; because p = A0 + t n with n = d^perp/|d|, d.A0 = kappa_d),
   so   ||M^{-1}||_2 <= ||M||_F / ( t |d| ) ,   ||M||_F^2 = |d|^2 + |p|^2 = |d|^2 + 1 .
```
Second and third orders: differentiate the two equations again; the circle equation contributes the
nonlinear terms
```
   p.D^2_v p = -|D_v p|^2 ,
   p.D^3_v p = -3 (D_v p).(D^2_v p) ,
```
CORRECTED (lead audit, k=2 term): the line equation differentiates by Leibniz with d'' = 0, so
`d.D^k_v p = kappa^(k) - k (D_v d).(D^{k-1}_v p)`, where kappa^((1)) = D_v kappa_d,
kappa^((2)) = |D_v c_b|^2 - |D_v c_a|^2  (!= 0; kappa is quadratic), and kappa^((k)) = 0 for k >= 3.
Explicitly: k=1 `d.p' = kappa' - d'.p`; k=2 `d.p'' = kappa'' - 2 d'.p'`; k>=3
`d.p^(k) = -k d'.p^(k-1)`. The earlier k>=2 statement omitting kappa'' is retracted.
The recurrence therefore has exactly the same shape as the face branch, with the conditioning constant
`t|d| = sqrt(1-|A0|^2) |d|`, i.e. the radical margin times the chord norm -- which is exactly the
quantity already registered as strictly positive at the root (|d| >= 0.45110, 1-|A0|^2 >= 0.94594).
For the branch value f = |p - c_a| the chain rule closes as in section 9.

**Pause point.** Per the lead: the elaborate bound assembly is paused here; only the two exact
recurrences (face in section 9 with the safe constants of sections 10-11, tie above) are kept, and no
quantitative rho is reported. Outstanding before any bound assembly: plain-algebra audit of the
interface factors, the interval lower bounds f_lo, |d|_lo, (1-|A0|^2)_lo over the domain, and the
perturbative Lipschitz step for the ball version.
