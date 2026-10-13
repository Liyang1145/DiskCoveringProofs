# MULTIFIELD-SIMPLEX-GAME — mixing dual fields for per-cell lower bounds (pure analysis)

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. **No claim registered.** No script, no
sub-agent. Units throughout: the covering radius `V` (never `V²`). Companions:
`SIMPLEX-CELL-DUAL-BOUND.md` (§7 lemma), `SIMPLEX-TREE-COVERAGE.md` (cells, verifier),
`lead/SIMPLEX-CONCAVITY-BOUND.md` (y-chart, Popoviciu proof), `lead/UNIFORM-SECTOR-CERTIFICATE.md`
(C911 exact rational fields).

## 0. Setting

A finite family `F = {f_1,…,f_m}` of **dual-feasible vector fields** (each: exact zero divergence at the
22 free nodes, `Σ_e‖p_e‖ ≤ 1`). For field `f` let `l_{f,i}` be its signed anchor loads and
`f_f(θ) := Σ_i l_{f,i}·U_i(θ_i)`. Weak duality gives, for **every** field and **every** anchor tuple,

```
V(U) ≥ f_f(U) .                                                        (0)
```
A cell `σ` (in the `y`-chart, vertices `Δ^{(v)}`, `θ^{(v)}`, ranges `range_i = max_v θ_i^{(v)} −
min_v θ_i^{(v)}`) is a simplex in `θ`-space: every `θ = Σ_v λ_v θ^{(v)}`, `λ ∈ Δ_9`.

## 1. κ-corrected pointwise lower bound, per field (from the variance bound)

For each `(f,i)` choose `κ_{f,i} ≥ max over the cell of (0, −l_{f,i}·U_i)` — computable in closed form
(the cos rule on the `θ`-interval, since `φ_{f,i}` depends on `Δ` only through the affine `θ_i`; see the
companion §7), and put

```
φ_{f,i}(t) := l_{f,i}·U_i(t) ,   φ''_{f,i} = −φ_{f,i} ,   w_{fv} := f_f(θ^{(v)}) ,
p_f := Σ_i κ_{f,i} range_i² / 8 .
```
**Lemma.** For every `λ ∈ Δ_9`: `f_f(θ(λ)) ≥ Σ_v λ_v w_{fv} − p_f`.
*Proof.* (i) `(φ_{f,i} − ½κ_{f,i} t²)'' = −φ_{f,i} − κ_{f,i} ≤ 0` on the cell, so
`ψ_{f,i} := φ_{f,i} − ½κ_{f,i}t²` is concave and so is `g_f := f_f − ½Σ_i κ_{f,i}θ_i² = Σ_i ψ_{f,i}`.
(ii) Concavity: `g_f(θ) ≥ Σ_v λ_v g_f(θ^{(v)})`. (iii) Expanding,
`f_f(θ) = g_f(θ) + ½Σ_iκ_{f,i}θ_i² ≥ Σ_vλ_v f_f(θ^{(v)}) − ½Σ_iκ_{f,i}[Σ_vλ_v(θ_i^{(v)})² − θ_i²]`,
and the bracket is the variance `Var_λ(θ_i)` by the identity `Σ_vλ_v(θ_i^{(v)})² = Var_λ(θ_i) + θ_i²`.
(iv) Popoviciu, with the exact proof `E[(X−a)(b−X)] = (mean−a)(b−mean) − Var ≥ 0` and
`(mean−a)(b−mean) ≤ (b−a)²/4`, gives `Var_λ(θ_i) ≤ range_i²/4`. Hence
`f_f(θ) ≥ Σ_vλ_v w_{fv} − Σ_iκ_{f,i}range_i²/8 = Σ_vλ_v w_{fv} − p_f`. ∎

## 2. Maximising over the family (the direction)

(0) holds for every field **at the same point**, so for every `λ`

```
V(θ(λ)) ≥ max_f f_f(θ(λ)) ≥ max_f ( Σ_v λ_v w_{fv} − p_f ) = max_f (Aλ)_f ,
A_{fv} := w_{fv} − p_f ,                                                             (2)
```
the middle step by the Lemma per field. Note the directions: the Lemma gives a *lower* bound for each
field, and taking a **max** over fields is legitimate (it is still a lower bound for `V`).

## 3. β-mixing is always legitimate (no optimality assumed)

For **any** `β ∈ Δ_m`, at every `λ`:

```
max_f (Aλ)_f ≥ Σ_f β_f (Aλ)_f = Σ_v λ_v (βᵀA)_v ≥ min_v (βᵀA)_v .
```
Therefore **for every `β ∈ Δ_m`** the number `LB_β(σ) := min_v (βᵀA)_v` is a valid lower bound:
`LB_β(σ) ≤ min_{θ ∈ σ} V(θ)`. Nothing is assumed about the fields beyond (0) for each of them, and no
independence between fields is used — the same pointwise inequality `V ≥ f_f` is instantiated
simultaneously for all `f`.

## 4. The game value, and the min–max equality

The best bound this family can produce on the cell is the value of the finite zero-sum game with payoff
matrix `A`:

```
LB_F(σ) := min_{λ ∈ Δ_9} max_f (Aλ)_f  =  max_{β ∈ Δ_m} min_v (βᵀA)_v .             (4)
```
*Proof of the equality.* The left program is the LP `min t s.t. t ≥ (Aλ)_f ∀f, λ ∈ Δ_9`; its dual is
`max s s.t. s ≤ (βᵀA)_v ∀v, β ∈ Δ_m`. Both are feasible and bounded (the simplex constraints are
compact; `t` is bounded below by any vertex value), and Slater holds on the primal side (`t` large and
`λ` in the relative interior of `Δ_9`), so strong duality gives equality; weak duality gives `≥` in
general. Attainment: `λ ↦ max_f(Aλ)_f` is convex (a max of finitely many affine functions) on a compact
simplex, hence attains its minimum, and the dual likewise. ∎
Consequently the family's cell bound `LB_F(σ)` is realised by *some* `β`, and by §3 **any** `β` yields a
certified (possibly weaker) value.

## 5. Certificate with rational/interval `β` — no LP optimality needed

To certify `LB(σ) ≥ R*` it suffices to exhibit **one** `β ∈ Δ_m` (rational coordinates) and verify, in
outward-rounded interval arithmetic:

1. each field's exact zero divergence at the 22 free nodes and `Σ_e‖p_e‖ ≤ 1` (C911's rational fields);
2. each `κ_{f,i}` against `max_cell(0, −l_{f,i}·U_i)` (closed-form cos rule on the `θ`-interval, using
   the rational enclosures of `L` from the `y`-chart);
3. the vertex works `w_{fv}` and the penalties `p_f`, hence `A`;
4. `min_v (βᵀA)_v` via the **lower** endpoints of the interval entries (taking the min over vertices of
   the lower endpoints is sound for a lower bound) and compare with `R*`.

Validity depends only on this verification: how `β` was found (a heuristic, a descent, or an LP) is
irrelevant, so no solver and no grid is required for soundness.

## 6. Dominance, scope and honest limits

* **Dominance.** `β = δ_f` gives `min_v (A_{f·})_v`, so `LB_F(σ) ≥ max_f min_v (A_{f·})_v`: the
  multifield value dominates the best single-field value, and by (4) it can strictly improve it — this
  is the "cross-field cell" upgrade (a game over the cell's vertices, not a grid).
* **Scope.** Per-cell statements only, and conditional on the finite certificate tree of the companion
  note for any global conclusion. No rate, no sampling, no global claim, and no upper bound for `R*`
  (C891's exact-root radius is the only threshold).
* **Limits.** `LB_F ≤ min_σ V` by construction; a cell where `LB_F(σ) < R*` leaves that cell **open**
  (route information — more fields, or an extra necessary condition), never a refutation.
