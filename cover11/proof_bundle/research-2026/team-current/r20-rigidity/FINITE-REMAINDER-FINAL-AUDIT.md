# Finite-remainder derivations (C919/C920): independent analytic audit (r20-rigidity)

Documents audited: `lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md`, `lead/ANISOTROPIC-STRESS-REMAINDER.md`,
`lead/RELATIVE-STRESS-BASIS.md`. Method: I re-derived the expansion from the minimised ("min_free")
Dirichlet energy myself and checked each step that the two documents rely on. No constant is re-run
here; no claim is added; nothing outside this directory is touched.

## Independent re-derivation

Let `E_α(U) = UᵀΛ_αU` be the carrying-graph Dirichlet energy (weighted Laplacian `Λ_α`), `U0` the root
embedding, and `V² = V²(U(x))` the oracle's squared radius. The minimised energy is a **lower bound**:
`V² ≥ E_{α(x)}` after the free-node minimisation, with **equality only at the exact root** (and at the
anchors' tangential data used there); it is *not* an identity away from the root. `α(x) = α0 + τN(G^T x)`,
`q = ‖x‖`, `p = ‖G^T x‖`, `U(x) = U0 + δ`, `δ = v + w` with `v` the tangential (first-order) part.

1. **Base root equilibrium.** `BN = 0` (the stress variation is a circulation on the free block) means
   `U0` remains a free-node equilibrium for *every* `α` on the line; strict positivity of the weights
   gives a unique Dirichlet minimiser. All carrying lengths equal `R*`, and `Σ_e α_e = 1`, hence
   `E_α(U0) = Σ_e α_e ℓ_e² = R*²` for all such `α`. The expansion of `E_{α(x)}(U0+δ)` therefore starts
   at `R*²`, and since `Λ_{α(x)}U0` has zero free components, the first-order term is exactly the
   **anchor flux** `2⟨l0 + Mx, δ⟩`. Verified as the structural core of both documents.
2. **Adaptive normalised positive stress.** Here `BN` *includes the normalisation row*, so membership of
   the kernel gives **both** the free-node balance and `Σ_e N_e = 0` (`1ᵀN = 0`) simultaneously; the
   latter implies `1ᵀ N G^T = 0`, i.e. every column of `Q = τNG^T` has zero entry-sum, so `α(x)` is
   normalised for all `x`. (Phrasing as "a generic circulation implies normalisation" would be too
   weak: the normalisation is part of `BN` itself.) Positivity is the direct condition `α_e = α0_e + (Qx)_e > 0` for every edge `e`; the max-relative
   bound `β(x) := max_e |(Qx)_e|/α0_e < 1` is a **sufficient** criterion for it (not an equivalence). Also `|(Qx)_e| ≤ τ‖N_e‖·‖G^Tx‖ = τ‖N_e‖ p`, so
   `β(x) ≤ τBp` with `B = max_e ‖N_e‖/α0_e` — the comparison `(1−β)Λ0 ⪯ Λ_{α(x)} ⪯ (1+β)Λ0` is the
   exact variational-comparison statement (minimised energies, not interval implementations).
3. **Direction `p` cancellation.** Every stress-dependent loss in the derivation is bounded by `p`
   rather than `q`: `β(x) ≤ τBp`, and the anchor-flux Taylor term is `‖Mx‖ ≤ τ‖A‖p` with
   `A: t ↦` the anchor flux of the stress `Nt`. Both vanish on the critical kernel `G^Tx = 0`, which is
   the structural gain over the older `bq`, `mq` bounds. Checked: these two bounds are exactly
   `β(x)`'s definition and `M`'s definition plus the operator norm; no hidden `q`-only estimate is used.
4. **Cubic and quartic mixed terms.** With `R_i = U_i(x) − (U_i + v_i) + (x_i²/2)U_i` one has
   `cos θ = 1 − θ²/2 + O(θ⁴)`, `sin θ = θ − θ³/6 + O(θ⁴)`, hence `‖R‖ ≤ Σ_i|x_i|³/6 ≤ q³/6`; this is
   sign-symmetric (valid for either sign of `x_i`). I reproduced the decomposition
   `2⟨v, Λ0w⟩ = −xᵀC x^{(2)} + 2⟨v, Λ0R⟩` structurally: the quadratic-in-`x` part of `w` gives the
   cubic loss with `C_cross = ‖J8ᵀ(Λ0⊗I2)Rad8‖_op`, and the `R`-part gives `d·(q³/6)·q = (d/3)q⁴` using
   `Λ0 ⪯ dI`, `‖v‖ ≤ q`. The documents' remark that the **full i,j sum is indispensable** (off-diagonal
   terms do not vanish) is consistent with this: the cross term is genuinely cubic in general and is
   *not* eliminated by symmetry.
5. **Complete the square.** `(τ−τ0)p² − τ(Bd+‖A‖)pq² ≥ −τ²(Bd+‖A‖)²q⁴/(4(τ−τ0))` is the standard
   `ap² − bp ≥ −b²/4a` with `a = τ−τ0 > 0`, `b = τ(Bd+‖A‖)q²`. Correct as written.
6. **Full-domain ball, closed boundary.** The conclusion is an inequality for all `x` with `‖x‖ ≤ ρ`
   in the raw-`θ8`-pinned chart, and it is *strict* (`> 0`), so boundary points are included: the
   certified statement is a closed ball, not an open one. The scope lines of both documents say
   "local, not global" and RELATIVE-STRESS-BASIS explicitly fixes the oracle and chart; no over-claim.

## Arithmetic cross-check of the C920 bracket (my own)

With `τ0 = 734`, `τ = 1468`, `μ0 = 0.0018`, `B = 0.495`, `‖A‖ = 0.00858`, `Gnorm = 0.015363`,
`C_cross = 0.0358`, `d = 0.08`, `q = 0.01458`:

```
τ·B·Gnorm·q            ≈ 0.1625 < 1                              (companion condition holds)
0.5μ0                  = 0.0009
C_cross·q              ≈ 0.000522
(d/3 + τ²(Bd+‖A‖)²/(4(τ−τ0)))·q²
   = (0.026667 + 1468²·(0.0396+0.00858)²/2936)·0.0002126
   ≈ (0.026667 + 1.7029)·0.0002126 ≈ 0.000368
bracket ≈ 0.0009 − 0.000522 − 0.000368 ≈ 1.0e-5   > 0        (matches the document's "> .00001")
```

## Issues worth flagging (documentation, not derivation)

* **Graph 45 vs 51 (not an inconsistency).** The 45-edge graph is the *carrying subgraph* of the
  51-edge graph (the stress audit maps 45 ⊂ 51 with six zero weights), so both descriptions refer to the
  same oracle; the documents are consistent once that nesting is stated.
* **"Replaces the cubic loss" phrasing.** The stress-dependent cubic `bd·q³` is indeed replaced by a
  quartic `τ²(Bd+‖A‖)²q⁴/(4(τ−τ0))`, but the *geometric* cubic `−C_cross q³` remains in the final
  bracket. The ANISOTROPIC document states the final form correctly; the phrase should not be read as
  "no cubic term remains".
* **Status.** Both documents state the result as an analytic implication conditional on certified root
  constants; that matches what I verified (the derivation itself uses no numerical rank, no LP
  optimality, and no interval-implementation assumption). The `μ = 0.0018` vs `0.00199` note in
  RELATIVE-STRESS-BASIS is explicitly a certification-width limit, not a negative-Hessian witness — the
  distinction is correctly drawn there.

## Scope and limits

Audited: the analytic expansion and each structural claim listed by the lead (base equilibrium,
normalised positive stress, mixed cubic/quartic, `p`-cancellation, closed ball). Not audited here: the
numerical certification of the constants (`certify_anisotropic_stress_ball.py`,
`certify_relative_stress_ball.py`), the modelling chain from the oracle to `E`, and any global
statement. No new claim is added.
