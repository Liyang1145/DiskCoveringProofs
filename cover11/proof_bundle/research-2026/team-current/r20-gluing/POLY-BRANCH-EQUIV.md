# R20-TC-POLY — the 5 TC residuals as a polynomial root definition, with branch equivalence
### (r20-gluing, cline2 / DS v4.1f · own file set · **no claim registered** · no Gröbner, no elimination)

Companion to `REPORT-TC-IV3.md`. This file states the algebraic reformulation of the 5 residual
functions and the exact meaning of the word "equivalence" (it is a **local germ equivalence on a
declared branch**, not a global claim).

Source of truth for the analytic side: `r20_tc_iv1.symbolic_res5` (== `tc_s32_kraw.res5`, C366),
whose *interval* image is certified in `r20_tc_iv3.json`.

---

## 1. Variables (37 real) and the 35 equations

Notation: `m(k) = k` for `k ≤ 4`, `m(k) = 8−k` (the index mirror of `a = (a0,a1,a2,a3,a4,a3,a2,a1,a0)`).

| block | variables | meaning |
|---|---|---|
| 10 | `P_k, Q_k` (k=0..4) | `cos a_k`, `sin a_k` |
| 18 | `c_k, s_k` (k=0..8) | `cos θ_k`, `sin θ_k` |
| 5 | `t_k` (k=0..4) | `√(R² − sin²a_k)` (positive branch) |
| 4 | `h, y₀, y₁, R` | hub cap height and the two hub endpoints, covering radius |

`ρ_k := P_{m(k)} − t_{m(k)}` (the ring-centre distance), and

```
U^x_k = ρ_k c_k + ρ_{k+1} c_{k+1} − (c_k P_{m(k)} − s_k Q_{m(k)})      (indices mod 9)
U^y_k = ρ_k s_k + ρ_{k+1} s_{k+1} − (s_k P_{m(k)} + c_k Q_{m(k)})
```

**Definitional identities (30 equations — hold for every legal tuple, no content).**

```
(A1)  P_k² + Q_k² − 1 = 0                                k = 0..3            (4)
(A2)  W := Π_{k=0..3} (P_k + i Q_k);   P₄ + Re(W²) = 0 ,  Q₄ − Im(W²) = 0    (2)
(A3)  k = 5..8 :  c_k = c_{k−1}cosφ_k − s_{k−1}sinφ_k ,  s_k = c_{k−1}sinφ_k + s_{k−1}cosφ_k
               with cosφ_k = P_{m(k−1)}P_{m(k)} − Q_{m(k−1)}Q_{m(k)} ,
                    sinφ_k = Q_{m(k−1)}P_{m(k)} + P_{m(k−1)}Q_{m(k)}          (8)
      k = 0..3 :  c_k = c_{k+1}cosφ_k + s_{k+1}sinφ_k ,  s_k = −c_{k+1}sinφ_k + s_{k+1}cosφ_k
               with φ_k = a_k + a_{k+1}                                       (8)
(A4)  c₄ = 1 ,  s₄ = 0                                                       (2)
(A5)  t_k² = R² − Q_k²                                   k = 0..4            (5)
(A6)  h²  = R² − ((y₁ − y₀)/2)²                                              (1)
```

**Residual conditions (5 equations — the whole content).**

```
(A7)  (U^x_k − y_l)² + (U^y_k)² = R²      for (k,l) ∈ {(1,1), (2,0), (3,0), (8,1)}   (4)
      (m − ρ₆ c₆)² + (h − ρ₆ s₆)² = R² ,   m = (y₀+y₁)/2                           (1)
```

**Branch data (inequalities; open conditions, not equations).**

```
(B1) t_k > 0 (k=0..4)    (B2) h > 0    (B3) R > 0    (B4) Q_k = sin a_k > 0 (k=0..3)
(B5) P_k = cos a_k > 0 (k=0..3)        (B6) ρ_k > 0 (k=0..8)
```

All coefficients are in `ℤ[½]`; **total degrees** of the equations: `w4_*` 8, residuals 4,
rotations 3, unit/t/h 2, norm 1; **no `π`, no `Float`, no `sin/cos/sqrt` node survives anywhere**.
This is exactly the phenomenon found by the iv3 probe from the other side: SymPy's printer never
had to emit `π`, because `sin(π−2σ)→sin2σ`, `cos(π−2σ)→−cos2σ` and
`ρ₄ = cos a₄ − √(R²−sin²a₄) → −cos2σ − √(R²−sin²2σ)`. Hence the constant-handling question
*disappears* in this representation — it is an algebraic system over ℚ.

---

## 2. Branch equivalence (the precise statement)

**Lemmas** (CAS-verified symbolic identities, `r20_tc_poly.json → lemmas`):

```
L1  (cos x + i sin x)(cos y + i sin y) = cos(x+y) + i sin(x+y)          [simplify → 0]
L2  cos(π−2x) = −cos 2x ,  sin(π−2x) = +sin 2x                          [simplify → 0]
L3  cos²x + sin²x = 1                                                   [simplify → 0]
L4  (√q)² = q   (q ≥ 0 on the branch, supplied by (B))                  [simplify → 0]
```

**Proposition F (forward).** Let `x = (a₀..a₃,y₀,y₁,R)` be a solution of the analytic system
`res5(x) = 0` whose configuration is on the branch (B) (positivities; automatically true at the
certified root). Put
`P_k = cos a_k, Q_k = sin a_k`, `t_k = √(R²−sin²a_k)`, `c_k = cos θ_k, s_k = sin θ_k` (θ from the
recursion with `θ₄ = 0`), `h = √(R²−d²)`. Then the image point satisfies (A1)–(A7) and (B).

*Proof.* (A1) = L3. (A2) with the *pairwise* case of L1 (3 applications) gives
`W = e^{iσ}`, hence `W² = e^{2iσ}`; then (A2) is L2. (A3) is the same pairwise L1 with the θ-
recursions (for `k ≤ 3` a rotation by `−(a_k+a_{k+1})`, i.e. L1 with `y = −φ`). (A4) is `θ₄ = 0`.
(A5),(A6) are L4. (A7): by construction `U_k = C_k + C_{k+1} − e(θ_k+a_k)` and the algebraic
`U^x_k, U^y_k` with the definitions substituted **is literally the same expression** (checked
symbolically, 18/18 differences zero, `Uk_definitional_nonzero = []`); the analytic residual
`|U_k − (y_l,0)| = R` therefore squares to (A7). ∎

**Proposition B (backward, local).** Let `z ∈ ℝ³⁷` satisfy (A1)–(A7) and (B). Reconstruct
`a_k = atan2(Q_k,P_k) ∈ (0, π/2)` (k ≤ 3), `a₄ = π − 2σ`, `θ_k = atan2(s_k,c_k)`, `ρ_k = P_{m(k)} − t_{m(k)}`.
Then `(a₀..a₃, y₀, y₁, R)` satisfies `res5 = 0` with `θ_k ≡` recursion value `(mod 2π)`, and the
reconstructed geometric objects coincide with those coded by the algebraic variables.

*Proof.* (A1)+(A3)+(A4) make `(c_k,s_k)` a rotation orbit of `(1,0)`; iterating L1 with the θ-
recursions (`θ₄ = 0`) gives `(c_k,s_k) = (cos Θ_k, sin Θ_k)` for the recursion angles `Θ_k`, i.e.
`θ_k ≡ Θ_k (mod 2π)` — which is all the geometry sees (`C_k = ρ_k(cos θ_k, sin θ_k)`, and `e(θ_k+a_k)`
is a polynomial in `(c_k,s_k,P_{m(k)},Q_{m(k)})`). (A5) with `t_k > 0` gives `t_k = √(R²−sin²a_k)`,
so `ρ_k = cos a_k − √(R²−sin²a_k)` is the analytic ring radius. (A6) with `h > 0` gives
`h = √(R²−d²)`. So for each of the 5 rows, (A7) says `dist² = R²`, and with `R > 0` (B3) this is
`dist = R`, i.e. the residual `dist − R = 0`. ∎

**Corollary (germ equivalence at the certified root image) — restated with explicit inverses.**
The earlier version derived this from *numerical singular values* ("rank 5 / rank 35,
σ_min = 0.0856"); **that reasoning is withdrawn** (a numerical singular value is not an analytic
rank and cannot carry the corollary). Replacement, `r20_tc_germ.py` / `r20_tc_germ.json`, on the
same certified box:

* *Analytic side.* Keep the 5 columns `[0,1,2,3,6]` (chosen by QR-with-pivoting on the point
  Jacobian at the box centre — a recorded, reproducible rule), let `W_A` be the 5×5 float64
  inverse of that point subblock (recorded to 17 digits, hence an exact dyadic matrix), and let
  `M(U)` be the interval enclosure of that subblock over the box. Then
  `q_A := ‖I₅ − W_A·M(U)‖_∞ = 1.087921746e-5 < 1` (exact rational) ⟹ `W_A M(U)` invertible ⟹
  `M(U)` invertible ⟹ the **5×7 Jacobian has rank 5 at every point of the box** and `{res5 = 0}`
  is locally a smooth **2-manifold** (constant-rank theorem).
* *Algebraic side.* Same construction with 35 kept columns (pivoting drops `y₁, y₀`) and an
  explicit 35×35 `W_B`: `q_B := ‖I₃₅ − W_B·J_alg‖_∞ = 5.7122086e-6 < 1` (exact rational) on the
  image of the **full 1e-9 box** ⟹ `J_alg` has rank 35 there ⟹ the algebraic zero set is locally
  a smooth **2-manifold**.
* *Germ.* Both zero sets are smooth 2-manifolds on their certified sets and the smooth maps of
  Propositions F/B are mutually inverse on branch (B) by construction, so the germs correspond.
* The singular values (`34.03, 11.41, 3.955, 1.965, 0.666` analytic; `σ_min = 0.0856` algebraic)
  are kept in `r20_tc_germ.json` as **diagnostic only, explicitly non-bearing**.

**Where the branch data is really needed (and where not).**

* The **four squared-distance** substitutions in (A7) carry **no** ambiguity: `dist² = R²` with
  `R > 0` is equivalent to `dist = R` because `dist ≥ 0`. Sign choices: **0**.
* The **five t_k** and the **one h** are genuine branch choices: `t_k² = R²−Q_k²` has the two roots
  `±`, and `h` enters (A7) linearly. Branches: `2⁵ · 2 = 64`; the analytic model is exactly the
  all-positive branch. Controls: flipping `t₀` breaks `res_k8_l1` by **0.484**; flipping `h` breaks
  `res_hub` by **0.877**. (Both controls fail the system ⟹ the branch data is load-bearing.)
* The **a_k representatives** are `mod 2π` inert: `a_k` enters only through `(P_k,Q_k)` and the
  mirror pattern; `a₄` likewise. So the algebraic system is the correct "mod-2π" quotient of the
  analytic one, and (A2) pins `a₄ ≡ π − 2σ` unambiguously (cos **and** sin are both fixed).

---

## 3. Evidence (all in `r20_tc_poly.json`, log `r20_tc_poly.log`; germ addendum in `r20_tc_germ.json`)

| check | reading | level |
|---|---|---|
| 37 variables / 35 equations, split 30 identity + 5 condition | exact | structural |
| degrees, coefficients in `ℤ[½]`, `π / Float / sin / cos / sqrt` nodes = 0/0/0/0/0 | exact | structural |
| L1–L4 simplify to 0 | 0, 0, 0, 0 | CAS symbolic |
| 30 identities at 3 **random legal tuples** | max `4.7e-51` (dps-50 floor) while the 5 conditions read `−0.20 … −0.30` | numeric (identity/condition split is real) |
| own root refinement (own model, `mp.dps = 60`) | `max|F| = 1.2e-60`; root inside the **certified** iv3 box | numeric |
| all 35 equations at the root image | max `5.5e-61` | numeric |
| branch data at the image | `t₀..t₄ = 0.1107, 0.1807, 0.2600, 0.0687, 0.0331`; `h = 0.31588`; `R = 0.37998`; `sin a_k, cos a_k > 0`; `ρ_min = 0.70087` — all > 0 | numeric |
| backward reconstruction | `θ` mismatch `7.8e-62` (mod 2π), `t` mismatch `0.0`, rebuilt 5 residuals ≤ `7.0e-61`, `h` mismatch `0.0` | numeric |
| controls | `a₀ + 1e-6` ⇒ conditions `1.2e-5`; wrong `t₀` branch ⇒ `0.484`; wrong `h` branch ⇒ `0.877` | numeric, discriminating |
| ranks (replaced 20:40) | **explicit-inverse certificates**, not SVD ranks: `q_A = ‖I₅ − W_A M(U)‖_∞ = 1.087921746e-5 < 1` (5×7 Jacobian rank 5 on the box) and `q_B = ‖I₃₅ − W_B J_alg‖_∞ = 5.7122086e-6 < 1` (35×37 Jacobian rank 35 on the image of the full box) | **proved-interval** (`r20_tc_germ.py/.json`); σ values demoted to diagnostic |

**Useful structural remark (no Gröbner performed).** The two degree-8 equations `w4_*` can be
lowered to degree 2 by carrying the four complex partial products as auxiliary variables
(`w₀₁ = w₀w₁`, `w₂₃ = w₂w₃`, `W = w₀₁w₂₃`, `W₂ = W·W`; 8 extra variables, 8 quadratic equations),
making the whole system degree ≤ 4. This is recorded as a remark only; no elimination was run.

---

## 4. Scope guards

* **Local only.** Propositions F/B are pointwise/definitional; the corollary is a *germ* statement
  at the certified root image. Nothing here says the algebraic variety has no other components, nor
  that the analytic 2-dimensional solution set is globally the image of the branch it is cut from.
* This does **not** touch the covering-radius question or the unconditional n=11 global target; a
  root definition is not an optimality statement.
* The algebraic system is a *representation change*: its payoff is that all transcendental
  evaluation (and with it the π/constant-handling risk) is gone, which is what a global
  interval/elimination attack on this system would need. It is not itself such an attack.
* Numeric readings above are `mp.dps = 60` point evaluations; the interval statements are the
  one-box enclosure of `REPORT-TC-IV3.md` and the two explicit-inverse rank certificates of
  `r20_tc_germ.json`.

Repro: `py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_poly.py`;
`py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_germ.py`.
