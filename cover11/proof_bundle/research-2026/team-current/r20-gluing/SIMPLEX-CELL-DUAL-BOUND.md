# SIMPLEX-CELL-DUAL-BOUND — per-cell lower bounds on `P` from one C911 vector-force field

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. **No claim registered.** Checked first:
this lane's `STATUS.md` (incl. the "do not resurrect" list) and `DEAD.md` (no dead mechanism revived;
the direction/label/interface discipline is applied step by step below). Inputs read:
`lead/FIXED-SWITCH-SOC-REDUCTION.md` (§2 oracle `V`, §3 vector-force certificates),
`lead/UNIFORM-SECTOR-CERTIFICATE.md` (**C911**: an exact rational **vector** force field `p_e ∈ R²` on
the fixed graph with exact zero divergence at the 22 free nodes and `Σ_e‖p_e‖ < 1`, plus per-anchor
angular bounds). Units: everything below is in the covering radius `V` (length), never in `V²`.

## 1. What C911 supplies, and the certificate it yields

`p_e ∈ R²` on the 51 edges; **divergence zero at every one of the 22 free nodes** (exact rational);
`Σ_e ‖p_e‖ < 1` (interval). Let `l_i := Σ_{e incident to anchor i} ±p_e` be the **signed anchor
divergence** at anchor `i`. Then for every anchor tuple `U` (lead note §3: free-node terms cancel and
`Σ_e ‖p_e‖ ‖X_v−X_w‖ ≤ V(U) Σ_e‖p_e‖ ≤ V(U)`):

```
V(U) ≥ f(U) := Σ_i l_i · U_i          (units: V ; one field is valid for EVERY U)
```
**Corrections accepted.** This is a *vector*-force object: no scalar normalised energy stress `α`
appears and no Schur complement is used. (The squared-distance stress of
`lead/NETWORK-ENERGY-INTERFACE.md` yields `V²`; it is a different object and is **not** mixed in here.)

## 2. Per-anchor angular form and the exact second-derivative identity

With `t_i(θ) = J U_i(θ) = (−sin θ, cos θ)` and `a_i := l_i·U_i(θ_i⁰)`, `d_i := l_i·t_i(θ_i⁰)` at a
reference angle `θ_i⁰`:

```
φ_i(t) := l_i · U_i(θ_i⁰ + t) = a_i cos t + d_i sin t ,        φ_i''(t) = −φ_i(t) ,
```
i.e. the angular Hessian is exactly the diagonal `−l_i·U_i` with no cross terms at this level, and the
integral form of Taylor's theorem gives, for every `t` with `|t| ≤ h_i`,

```
φ_i(t) = a_i + d_i t + ∫_0^t (t−s) φ_i''(s) ds  ≥  a_i + d_i t − R_i ,
R_i := ∫_0^{h_i} (h_i−s)( |a_i| + |d_i| s ) ds = |a_i| h_i²/2 + |d_i| h_i³/6 ,
```
the bound `|φ_i''(s)| = |φ_i(s)| ≤ |a_i| + |d_i||s|` being taken **uniformly over the whole segment**
`[−h_i, h_i]`, never at a single point. **Correction accepted**: a point value (of `φ_i` or of a
gradient) may not serve as a remainder bound for a segment; the remainder above uses only
`a_i, d_i, h_i`.
*Conservative norm version*: `|a_i| ≤ ‖l_i‖`, `|d_i| ≤ ‖l_i‖`, so with `L₀ := max_i‖l_i‖` and
`h := max_i h_i`, `R_i ≤ ‖l_i‖(h_i²/2 + h_i³/6)` and `Σ_i R_i ≤ 9 L₀ (h²/2 + h³/6)` — the uniform
`max‖l_i‖` bound.

## 3. Cell bound: coupling in the linear part, minimum at the cell's vertices

Cell `σ ⊂ P = {Δ ∈ [m,L]^9 : ΣΔ = 2π}` (a simplex of a fixed decomposition), reference point `Δ⁰`
(a vertex or the centroid), `δΔ = Δ − Δ⁰` (so `Σ_i δΔ_i = 0`, `lo_i ≤ δΔ_i ≤ hi_i`), and
`δθ_i(Δ) = θ_i(Δ) − θ_i⁰ = Σ_{j<i} δΔ_j`. Then

```
f(U(Δ)) ≥ Σ_i a_i + Σ_i d_i δθ_i(Δ) − Σ_i R_i = Σ_i a_i + ⟨w, δΔ⟩ − Σ_i R_i ,
w_j := Σ_{i>j} d_i ,
```
and `min_{Δ ∈ σ} ⟨w, δΔ⟩` is attained at a **vertex of the true simplex cell** (a linear function on a
polytope). Hence, keeping the Δ-sum identity and the ±caps exactly as they are (no box relaxation,
no LP relaxation needed):

```
LB_tan(σ) := Σ_i a_i + min_{v ∈ vert(σ)} ⟨w, δΔ^{(v)}⟩ − Σ_i R_i   ≤   min_{Δ ∈ σ} V(U(Δ)) .
```
*Proof.* For `Δ ∈ σ`: `V(U(Δ)) ≥ f(U(Δ))` (§1, one field valid everywhere), and `f(U(Δ)) ≥` the
right-hand side (§2 applied per anchor, then the linear term bounded below by its value at the
minimising vertex). ∎
Every step is in the sound direction for a **lower** bound: certificate → single field; each summand →
its Taylor lower bound; the linear part → its minimum over the cell. The coupling between neighbouring
anchors enters exactly through `w_j = Σ_{i>j} d_i`, i.e. through the Δ-sum structure that an
independent per-anchor angle box cannot see.

## 4. Second sound bound, same units, and the combination

Per anchor alone, the exact minimum of `φ_i` over its own interval `[θ_{i,lo}, θ_{i,hi}]` is the cos
rule (minimiser `arg(l_i) + π` if it falls in the interval, otherwise an endpoint) — call the sum
`LB_sep(σ)`. It is sound by the same certificate with the anchors treated independently, and **it is in
the same units `V`**; this was the units error of the previous draft (`LB_cell` in `V²`), which is now
impossible because no square appears anywhere. Hence

```
LB(σ) := max( LB_tan(σ) , LB_sep(σ) )   ≤   min_{Δ ∈ σ} V(U(Δ)) .
```

## 5. Algorithm on a general simplicial cell (analytic, implementable, no LP/sampling)

```
input: cell vertices Δ^(v) (v = 1..9), C911 fields p_e (exact rational), reference Δ⁰
1  l_i ← signed anchor divergence of p_e ;  a_i ← l_i·U_i(θ⁰) ;  d_i ← l_i·t_i(θ⁰)
2  w_j ← Σ_{i>j} d_i                                  (carries the Δ-coupling)
3  for each vertex v:  s_v ← ⟨w, Δ^(v) − Δ⁰⟩
4  h_i ← max_v |δθ_i(Δ^(v))|                           (exact rational/interval)
5  R_i ← |a_i| h_i²/2 + |d_i| h_i³/6                   (or the conservative L₀ version)
6  LB_tan ← Σ_i a_i + min_v s_v − Σ_i R_i ;  LB_sep ← per-anchor cos rule ;  LB ← max(·,·)
7  certify LB with interval arithmetic; return LB and both components
```
Cost: a handful of rational operations per cell; no optimisation, no sampling, no non-convex angular
minimum, and nothing from the energy/stress formulation.

## 6. Scope and caveats

* Per-cell claim only: `min_{Δ ∈ σ} V(U(Δ)) ≥ LB(σ)`. Covering `P` by cells with `LB(σ) ≥ R*` is the
  intended *use*, not a result claimed here.
* The field is used once for all cells (C911's field is valid on the whole domain). A low cell value is
  *route information* (a varying field or an extra necessary condition), never a refutation of the
  target.
* No upper bound for `R*` is used anywhere (C891's exact-root radius is the only threshold).
* Floats are for calibration only; the bound itself is rational/interval. No sampling control is added.

## 7. Vertex-concavity lemma (stronger; exact on vertices when `κ = 0`)

The per-anchor angular functions satisfy `φ_i'' = −φ_i` (§2), i.e. **each `φ_i` is concave exactly
where it is nonnegative**. This is exploited directly, with no Taylor remainder at all.

**Lemma.** Let `σ` be a simplex cell with vertices `Δ^{(v)}`, `θ^{(v)} = θ(Δ^{(v)})` (the map
`Δ ↦ θ` is **affine**: `θ_i = θ_0 + Σ_{j<i} Δ_j`, so the cell's `θ`-image is a simplex and every point
of the cell is a convex combination `θ = Σ_v λ_v θ^{(v)}`, `λ ≥ 0`, `Σλ = 1`). For the fixed C911 field
let `φ_i(t) = l_i·U_i(t)`, `range_i := max_v θ_i^{(v)} − min_v θ_i^{(v)}`, and set
```
κ_i := max( 0 , − min_{t ∈ [min_v θ_i^{(v)}, max_v θ_i^{(v)}]} φ_i(t) ) ,
```
computable in closed form by the cos rule (minimiser `arg(l_i) + π` if it lies in the interval, else an
endpoint; the minimum over the cell equals the minimum over this interval because `φ_i` depends on `Δ`
only through the affine `θ_i`, whose range on the simplex is exactly that interval). Then for every
`Δ ∈ σ` with `θ = θ(Δ)` and barycentric `λ` of `Δ` in `σ`,
```
f(θ) ≥ Σ_v λ_v f(θ^{(v)}) − ½ Σ_i κ_i Var_λ(θ_i) ≥ min_v f(θ^{(v)}) − Σ_i κ_i range_i² / 8 .
```
*Proof.* (i) `(φ_i − ½κ_i t²)'' = −φ_i − κ_i ≤ 0` by the definition of `κ_i` on the interval, so each
`ψ_i := φ_i − ½κ_i t²` is concave, and so is `g := f − ½Σ_i κ_i θ_i² = Σ_i ψ_i`. (ii) Concavity gives
`g(θ) ≥ Σ_v λ_v g(θ^{(v)})`. (iii) Hence
`f(θ) = g(θ) + ½Σ_i κ_i θ_i² ≥ Σ_v λ_v f(θ^{(v)}) − ½Σ_i κ_i [Σ_v λ_v (θ_i^{(v)})² − θ_i²]`, and the
bracket is the variance identity `Σ_v λ_v (θ_i^{(v)})² = Var_λ(θ_i) + θ_i²` (as `θ_i = Σ_v λ_v θ_i^{(v)}`),
so `f(θ) ≥ Σ_v λ_v f(θ^{(v)}) − ½Σ_i κ_i Var_λ(θ_i)`. (iv) Popoviciu's inequality
`Var_λ(θ_i) ≤ range_i²/4` together with `Σ_v λ_v f(θ^{(v)}) ≥ min_v f(θ^{(v)})` finishes it. ∎

**Corollary (`κ = 0`: no loss).** **Corrected (lead).** A fixed radial load `l_i = β_i U_i*` does
**not** give `φ_i ≡ β_i`: one has `φ_i(t) = β_i U_i*·U_i(t) = β_i cos(θ_i(t) − θ_i*)`, which equals
`β_i` only **at** the reference angle. What is true: (i) at the reference point `φ_i = β_i > 0`, so by
continuity `φ_i > 0` on every cell small enough, whence `κ_i = 0` by its definition; (ii) whenever
`φ_i ≥ 0` on the whole cell for every `i`, the lemma gives `f(θ) ≥ min_v f(θ^{(v)})` — the minimum over
the cell is attained **on the vertices**, with **no Taylor loss**, and the cell bound is
`min_v f(θ^{(v)})`. **Wording corrected (lead)**: `certify_uniform_simplex.py` is not an "empirical"
instance — its readings are **certified interval evaluations** (κ ≡ 0, `LB > 0.380123127`) on the
tested simplex, i.e. a certificate, never a sample; the mechanism is (i) above, and the retracted
`φ ≡ β` was simply wrong.

**Units and direction.** `f`, `κ_i` and the correction `Σ_i κ_i range_i²/8` are all in the covering
radius `V` (angles are dimensionless), so this bound, §3's Taylor bound and §4's separable bound are
mutually comparable and may be combined with `max`. Every step is in the sound direction for a lower
bound; the inputs are only `l_i` (from C911's exact rational field) and the vertex `θ`-values.

**Why it can cover the far region.** At `U*` the field's work attains its maximum (`= R*`, C909 §2), so
no cell containing `U*` can be certified by this (or any) fixed-field bound — the local patch (C912)
remains necessary there. Away from `U*` this cell bound is exactly what can certify
`min_{Δ ∈ σ} V(U(Δ)) ≥ R*`, and it needs no non-convex angular minimum: only vertex values, the
closed-form per-anchor `κ_i`, and the affine `Δ ↦ θ` ranges.
