# BARYCENTRIC-SUBDIVISION — λ-guided stellar subdivision of a simplex cell (exact union, no lost regions)

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. **No claim registered.** Pure analysis; no
run, no sub-agent. Companions: `SIMPLEX-TREE-COVERAGE.md` (tree schema, verifier, LEB rule),
`MULTIFIELD-SIMPLEX-GAME.md` (the game value and its adversarial `λ`). Units: radius `V`.

## 1. Stellar subdivision at a point `p`

Let a cell be the simplex `S = conv(v_0,…,v_8)` (in the `y`-chart) and let
`p = Σ_{v} λ_v v_v`, `λ ∈ Δ_9` (rational coordinates; the game's adversarial `λ` or any rational point).
Define the **children**

```
S_i := conv( p , { v_k : k ≠ i } )        (i = 0..8) .
```

**Tiling theorem.** Let `support(λ) := {k : λ_k > 0}`, and for `x ∈ S` let `μ` be its barycentric
coordinates w.r.t. `v_0..v_8` (`μ ≥ 0`, `Σμ = 1`).
(a) `vol(S_i) = λ_i · vol(S)` for every `i`.
(b) **Coverage, pointwise (corrected; no hyperplane chambers).** For every `x ∈ S` there is
`i ∈ support(λ)` with `x ∈ S_i`; hence `S = ⋃_{i ∈ support(λ)} S_i` exactly.
(c) **Interiors are disjoint.** `int S_i ∩ int S_j = ∅` for `i ≠ j`; the common boundary of `S_i` and
`S_j` (both in the support) lies where the two ratios `μ_i/λ_i`, `μ_j/λ_j` are equal and minimal.
(d) **Zero coordinates.** If `λ_i = 0` then `p ∈ F_i` and `S_i = F_i := conv{v_k : k ≠ i}`; moreover
`F_i ⊆ ⋃_{k ∈ support(λ)} S_k` by (b) applied at `p` itself.
*Proof.* (a) `λ_i` is the affine function equal to 1 at `v_i` and 0 on `F_i`; the affine map
"fix `F_i`, send `v_i ↦ p`" scales the height over `F_i` by `λ_i`, hence the volume by `λ_i`.
(b) Choose `i ∈ support(λ)` where `μ_i/λ_i` is **minimal** over the support and set `t := μ_i/λ_i`.
Then `t ≤ 1`: if `t > 1` then `μ_k > λ_k` for every `k ∈ support(λ)`, so `Σ_k μ_k > Σ_k λ_k = 1`,
contradicting `Σ_k μ_k = 1`. Write
```
x = t·p + Σ_{k≠i} (μ_k − t λ_k) v_k .
```
This is a convex combination: the `v_i`-coefficient reproduces `μ_i = tλ_i`; for `k ≠ i` in the
support, `μ_k − tλ_k ≥ 0` by minimality of `t`; for `k ∉ support(λ)`, `λ_k = 0` so the coefficient is
`μ_k ≥ 0`; and the coefficients sum to `t + (1 − μ_i) − t(1 − λ_i) = 1`. Hence `x ∈ S_i`, with
`i ∈ support(λ)` — and `i` may be chosen independently for each `x`.
(c) In the `S_i`-representation the `p`-coefficient is exactly `μ_i/λ_i` and the `v_k`-coefficient is
`μ_k − (μ_i/λ_i)λ_k`. A point is interior to `S_i` iff (i) `μ_i/λ_i > 0` and (ii) `μ_k/λ_k > μ_i/λ_i`
for every `k ≠ i` in the support. Two distinct indices cannot both satisfy (ii), since "strictly
minimal" is unique; the shared boundary is therefore the tie locus `μ_i/λ_i = μ_j/λ_j` (with both
minimal). ∎

(Only (a) is a volume statement — it is a norm identity, kept for the ledger; the coverage and
disjointness claims are the pointwise argument above and use no volume, no closedness and no
arrangement of hyperplanes.)

Consequences for the ledger: the children overlap only in boundary (tie-locus) sets, exact and
dimension-free; the positive-`λ` children are a *volume-exact* cover by (a) with `Σ_{support}λ = 1`; and
a zero-`λ` child is recorded explicitly (below) rather than silently dropped.

## 2. Rational certificate schema and verifier extension

A node's record extends the `SIMPLEX-TREE-COVERAGE.md` schema by its subdivision type:

```
subdivision : { kind = "stellar", p, lambda[0..8] }   |  { kind = "LEB" }
children    : for kind = "stellar": one record per i = 0..8, each with
              vertices = [ p , v_{k_1}, …, v_{k_8} ]     (k_j the parent indices ≠ i, increasing)
              status   = "node" | "facet-contained"      (the latter iff lambda_i = 0)
              witness  = (if "facet-contained") the reference to Theorem 1(d)
```
Verifier checks (exact rational): `λ ≥ 0`, `Σλ = 1`; `p = Σ_v λ_v v_v` exactly; every child's vertex
list equals the canonical list above (positional, so the parent↔child relation is unambiguous); each
`"facet-contained"` child has `λ_i = 0`; each child's vertices are distinct and affinely independent
(else the node is marked *nonconforming, open*, never a stop). All checks are rational; nothing here
needs a solver, and no rate/diameter statement is used or claimed.

**No lost regions for mixed trees.** A finite tree whose internal nodes use either rule is accepted iff
every leaf is a stop-node (with a certificate) or an explicit `open` obligation. *Proof.* Each internal
node's children **exactly** cover it — LEB by the union theorem of the companion note, stellar by
Theorem 1(b) (pointwise, every `x` lies in some positive-`λ` child) with Theorem 1(d) accounting for
the omitted zero-`λ` children — so induction over the
finite tree gives `⋃ leaves = root`, and the stop certificates give `V ≥ R*` on each leaf. Hence the
conclusion holds on the root (`= P` in the `y`-chart), conditionally on all leaves being stopped. ∎

## 3. Why guide by the game's `λ` (and what is *not* claimed)

The multifield game returns an adversarial `λ` (the minimiser over `Δ_9` of `max_f (Aλ)_f`) and its
**active face** `{v : λ_v > 0}`. A stellar subdivision at `p = Σ λ_v v_v` places the new vertex exactly
where the game's value is balanced, and its children separate the active vertices from the inactive
ones: the active face becomes the boundary between children rather than an arbitrary cut, so a
non-stopped node is refined along the direction the certificate says is critical, instead of blindly
bisecting the longest edge. The two rules are interchangeable in the ledger, so a mixed tree remains
verifiable, and neither rule needs a convergence rate: soundness only requires that the finite tree's
leaves are stopped.

**Not claimed:** any rate or termination guarantee; that the `λ`-guided rule is better than LEB in any
quantitative sense; any global coverage (that remains conditional on producing a fully stopped finite
tree). A cell where the game value is `< R*` stays `open` — route information, never a refutation.

## 4. Scope

Per-cell/per-tree statement, conditional on the certificates; all geometry is exact rational
(`λ` rational ⇒ `p` rational ⇒ children rational); zero-`λ` children are recorded and never silently
dropped; no sampling, no grid, no solver, no rate, no global claim, no upper bound for `R*` (C891's
exact-root radius is the only threshold).
