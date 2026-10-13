# SOCP-DUAL-EXACT-FORM — corrections, exact dual, tie-derivative identity

**Lane**: r20-gluing (cline2-r23-gluing). Read-only for others' files; **no claim registered**.
This note retracts two errors of mine in `SOCP-RELAXATION-INDEPENDENT-CHECK.md` and writes the exact
convex dual of the fixed-switch SOCP. Repros: `socp_fixed_switch_check.py`, `tie_derivative_identity.py`.

## 0. Retractions (both lead corrections accepted)

1. **"The free-site min-r dual degenerates to 0" is WRONG.** I argued `inf_c (‖c−U‖) = 0` by taking
   `c = U`; but a site `c_i` carries *two* endpoint constraints at the **distinct** points
   `U_{i−1} ≠ U_i`, so the correct elementary infimum is
   `inf_c (‖c−U‖ + ‖c−V‖)/2 = ‖U−V‖/2 > 0`. The dual is therefore a **normal, positive** dual; the
   equality `Σ|y_e| = 1` on the *paired* loads already yields the chord bound.
2. **The tie-radius derivative is NOT a sum of two unit vectors nor a ½/½ split.** With the tie point
   `U ∈ ∂D` solving `‖U−c‖ = ‖U−c'‖ = ρ` (so `U` itself depends on the two sites), the total
   derivative is a **positive weighted combination** with weights fixed by the **tangent-slope
   cancellation** — see §2 for the exact formula (verified symbolically, not by finite differences).
   Consequently the split of a switch-branch weight onto the two fixed-switch endpoint constraints must
   use those weights `(α, 1−α)`, and `½/½` is wrong in general.

## 1. The exact primal and its exact convex dual

**Primal** (fixed switches `U_0..U_8 ∈ ∂D`, q0 graph with face set `F`, `|F| = 11`):
```
min r   over   c ∈ R^{22} (11 sites),  z ∈ R^{22} (11 aux, one per face),  r ∈ R
s.t. for i ∈ Z_9 :   ‖c_i − U_i‖ ≤ r ,   ‖c_i − U_{i−1}‖ ≤ r            (18 endpoint cones)
     for f ∈ F, c ∈ sites(f) :   ‖c − z_f‖ ≤ r                          (33 face cones)
```
Each constraint is a second-order cone in the variables with radius coordinate `r`; the objective is
linear; `z_f` is free (the face cone is the MEC/existence form, never the circumradius form).

**Dual (load/force form).** Attach a vector load `y_e ∈ R²` to every cone constraint `e` — write each
cone as `‖A_e x + b_e‖ ≤ c_e·x + d_e`, with `b_e = −U_e` for endpoint cones and `b_e = 0` for face
cones (they contain `c − z_f`), and `c_e·x = r`. Then
```
maximize   Σ_{endpoint e} ⟨y_e , U_e⟩                      (objective = Σ boundary fixed U_i · loads)
subject to  node balance:   for every site c_i :  Σ_{e at c_i} y_e = 0
                            for every face f  :  Σ_{c ∈ sites(f)} y_{f,c} = 0
            norm budget:    Σ_e ‖y_e‖ ≤ 1        (equality at the optimum)
```
**Chord-bound sanity check** (recovers the elementary bound): for one site `i` with endpoints `U, V`
put `y_U = ½ (U−V)/‖U−V‖`, `y_V = −y_U`, all other loads `0`. Node balance holds at `c_i`;
`Σ‖y_e‖ = 1`; the objective is `½ ⟨(U−V)/‖U−V‖, U⟩ + ½⟨(V−U)/‖U−V‖, V⟩ = ½‖U−V‖`. Hence
`r* ≥ ½‖U−V‖` for every admissible choice — and, pairing independently over the nine switches,
`r* ≥ ½ max_i ‖U_{i+1} − U_i‖`.

**Strong duality / Slater.** For `r` large enough every cone constraint is *strictly* satisfiable
(take `c_i` inside both switch balls and `z_f = c`), so Slater's condition holds, the dual is attained,
and the primal optimum equals the dual supremum. There is **no obstruction**: a positive certified
oracle bound is possible; a certificate is a dual-feasible load field whose objective is the bound.

## 2. The tie-derivative identity (exact, analytic)

Let `c, c'` be the two sites adjacent at the switch, `U ∈ ∂D` the tie point,
`u = (U−c)/ρ`, `u' = (U−c')/ρ` (unit, site → switch, `ρ = ‖U−c‖ = ‖U−c'‖`), and
`t = J U = (−U_2, U_1)` (unit tangent, counter-clockwise). Then, with `U` moving as the tie requires,
```
∇_c ρ = A · u ,     A = ⟨U − c' , t⟩ / ⟨c' − c , t⟩ ,
∇_{c'} ρ = B · u' , B = ⟨U − c , t⟩ / ⟨c − c' , t⟩ ,      and identically   A + B = −1 ,
```
so the **positive split weights** are `(α, 1−α) = (−A, −B)` (positive, summing to 1) — determined by
the tangent slopes, equal to `½/½` **only** in the symmetric case. Verified symbolically
(`tie_derivative_identity.py`: `∇_c ρ − A·u ≡ 0`, exact simplification) and calibrated numerics on
asymmetric instances give `α ∈ {0.2060, 0.3074, 0.4156, 0.4487, 0.5203, 0.5703}` — never `½`.

## 3. Candidate load field (what the dual certificate should use)

* **Face loads from the MEC barycentrics.** For the tight faces the circumcentre `z_f` lies strictly
  inside (all 11 faces of the candidate are acute; barycentric coordinates all `> 0.22`), and the
  face-node balance `Σ_{c ∈ f} y_{f,c} = 0` is solved by loads proportional to the barycentric
  displacements `y_{f,c} = λ_c (c − z_f)`, `Σλ_c = 1`, whose norm sum is `Rc_f = r` on the tight
  faces (zero weight on the two slack fan faces `(5,6,9)`, `(7,8,9)`, `Rc = 0.378831172`).
* **Endpoint loads from the tie split.** At the candidate all nine switches are tight
  (`ρ_i = r = 0.379983853…`), and the split coefficients come from §2 as `(α_i, 1−α_i)`. Exact
  assembly rule: with `A_i, B_i` as in §2 (so `A_i + B_i = −1` and `α_i = |A_i|`, `1−α_i = |B_i|`),
  put the loads `y = α_i μ_i · u_i` on the constraint `(c_i, U_i)` and `y = (1−α_i) μ_i · u'_i` on
  `(c_{i+1}, U_i)`, where `μ_i` is C897's physical weight of the switch branch `ρ_i`. Then the two
  loads' contributions to the site balances are exactly `μ_i(∇_{c_i}ρ_i, ∇_{c_{i+1}}ρ_i)`, i.e. the
  branch's gradient — so C897's 22-coordinate stationarity is reproduced verbatim.
* **Face loads, exact scaling.** For a tight face `f` with weight `ν_f` (fan) or `λ_f` (central), put
  `y_{f,c} = ν_f · λ_c (c − z_f)/r` with `λ_c` the barycentric coordinates of `z_f` in the face
  (`Σλ_c = 1`, `Σ_c λ_c(c − z_f) = 0`). Then the face-node balance `Σ_{c ∈ f} y_{f,c} = 0` holds
  identically and `Σ_{c∈f} ‖y_{f,c}‖ = ν_f` (all three distances equal `r` on a tight face). Zero
  loads on the two slack fan faces.
* **Norm budget.** With C897's physical weights summing to exactly 1 (`weight_total_1: true` in
  `r20-stress/out/phase7_interval_cyclic_nu.json`), the assembled field satisfies `Σ_e ‖y_e‖ = 1`
  automatically; the only thing left to compute numerically is the objective `Σ_{endpoint}⟨y_e, U_e⟩`
  (a positive number ≤ `r*`, the certified oracle bound).

## 4. Status of the earlier note

`SOCP-RELAXATION-INDEPENDENT-CHECK.md` (a) representation and (b) candidate numbers stand unchanged;
its §(a′) "degenerate dual / use Farkas instead" conclusion and the "halves" split are **retracted**
here. The remaining obligation is the explicit dual-feasible load field and its objective value.
