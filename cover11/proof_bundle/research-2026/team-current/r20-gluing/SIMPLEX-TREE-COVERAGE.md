# SIMPLEX-TREE-COVERAGE — exact longest-edge bisection on the y-simplex, certificate tree, no lost regions

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. **No claim registered.** Purely analytic; no
sweep, no solver. Companion: `SIMPLEX-CELL-DUAL-BOUND.md`; domain parametrisation and the vertex
certificate are from `lead/SIMPLEX-CONCAVITY-BOUND.md`.

## 1. Domain: one exact simplex, in `y` (no dyadic outer cover needed)

With `L = 2asin(19/50)` and `D := 9L − 2π > 0`, put
```
y ≥ 0 ,  Σ_{i=1..9} y_i = 1 ,      Δ_i := L − D y_i  (i = 1..9) .
```
Then `Δ_i ∈ [2π − 8L, L]` and `Σ_i Δ_i = 9L − D = 2π`, so **all of `P` is this single 8-simplex** in
`y`, whose vertices are the standard basis vectors `e_i` — exact rationals — with the inverse
`y = (L − Δ)/D`. The tree below lives **entirely in `y`**; `L` (transcendental) enters only through
rational enclosures when the angular intervals are formed for the lower-bound certificate. For a cell
with `y`-vertices the anchors are `θ_i = θ_0 + Σ_{j<i} (L − D y_j)`, and its `θ`-ranges `[a_i,b_i]`
are computed from the vertices with outward-rounded rational arithmetic on `L`.

## 2. Bisection rule (longest edge, exact, in `y`)

For a cell `S = conv(v_0,…,v_8)` in `y`-coordinates:
1. compute all `36` squared edge lengths `|v_a − v_b|²` exactly (rational);
2. pick `(i,j)`, `i<j`, of longest length, ties broken by lexicographically smallest `(i,j)` — the
   tie-break is part of the rule, so a verifier can reproduce the choice;
3. `m := (v_i + v_j)/2` (exact rational);
4. children: replace position `j` by `m` (`S⁻`), and position `i` by `m` (`S⁺`).

**Union theorem (exact, dimension-free).** For a non-degenerate parent, `S = S⁻ ∪ S⁺` and
`S⁻ ∩ S⁺ = conv(m, {v_k : k ≠ i,j})`.
*Proof.* Let `H = aff(m, {v_k : k ≠ i,j})`. The parent is full-dimensional, so `v_i, v_j` lie strictly
on opposite sides of `H` (the segment `v_i v_j` meets `H` exactly at its midpoint). A hyperplane
splitting a simplex's vertices strictly between two sides separates it into the two convex hulls of the
two vertex sets — exactly `S⁻`, `S⁺` — with intersection `S ∩ H = conv(m, {v_k})`. ∎
Replacing `v_j` by the non-trivial affine combination `(v_i+v_j)/2` preserves affine independence, so
both children are again full-dimensional. *Verifier obligation*: if `m` coincides with another vertex,
the child is degenerate; that node is marked **nonconforming and open** (never a stop-node).

## 3. Rational bookkeeping

All vertices are rational (the root is `{e_i}`; midpoints keep rationality), with denominators
multiplying by 2 per level, so every node's data — vertices, midpoint, edge lengths, angular ranges —
is exact rational. **No rate statement is made or needed**: the union theorem and the verification below
concern a *finite* recorded tree; nothing here claims any diameter-decay rate in 8D, and soundness
requires only that the tree is finite with every leaf covered by a certificate.

## 4. Certificate tree: recording schema

```
node_id, parent_id (null for the root), depth,
vertices   : [v_0 … v_8]           exact rational y-vectors
chosen_edge: (i, j)                longest edge under §2
midpoint   : m                     (= (v_i+v_j)/2 exactly)
children   : [child⁻_id, child⁺_id]          (internal nodes only)
--- leaves only ---
certificate: { id, kind = "cell-LB", value ≥ R*, method }      (companion file)
status     : "stop" | "open"       (a leaf without a passing certificate is "open"; never deleted)
root extra : the affine identity certificate  { y ≥ 0, Σy = 1 } ⟷ P   (exact, algebraic)
```

## 5. Verifier checks and the no-lost-regions theorem

* **V1** the tree has a single root whose vertices are the standard basis `{e_i}`, and whose certificate
  records the exact identity of §1 (`Δ = L − D y`, `Σ Δ = 2π`, ranges in `[2π−8L, L]`).
* **V2** for each internal node, the recorded `(i,j)` is a longest edge under the mandated tie-break
  (recomputed exactly from the node's vertices).
* **V3** `m = (v_i+v_j)/2` exactly.
* **V4** `child⁻`'s vertex list is the parent's with **position `j`** replaced by `m`, and `child⁺`'s
  with **position `i`** replaced by `m` (positional, so the child↔parent relation is unambiguous).
* **V5** each child's nine vertices are distinct and affinely independent (else → "nonconforming,
  open").
* **V6** every leaf is `stop` with a certificate that verifies (`kind = "cell-LB"`, `value ≥ R*`) or
  `open` (reported as an outstanding obligation; `open` leaves may not be silently dropped).
* **V7** the tree is acyclic, every node has exactly one parent, ids consistent.

**Theorem (no lost regions; finite tree).** If the verifier accepts a tree all of whose leaves are
stop-nodes, then `⋃ leaves = root = S` (the whole `y`-simplex, hence all of `P`), and the requirement
`V ≥ R*` holds on `P`.
*Proof.* By V3+V4 the children are exactly the §2 children, so by the union theorem each internal node
is tiled by its two children; induction over the finite tree gives `⋃ leaves = root`. V6 gives the
requirement on each leaf, V1 identifies the root with `P`. ∎
*Conditional form.* Any `open` leaf leaves its region unresolved; the conclusion is then reported as a
**partial** statement over the stopped leaves only — never as global coverage.

## 6. Small-dimensional exact-Fraction controls (specification; not written in this pass)

1. **2D**: a rational triangle, 3 levels of §2 bisection (including a forced tie); check exactly that
   `area(S⁻) + area(S⁺) = area(S)` at every node and that the intersection has area 0.
2. **3D**: a rational tetrahedron; the same with volumes, plus V3/V4 on the positional replacement.
3. **Negative controls**: (a) swap the `i`/`j` replacement in one child → V4 must fail; (b) flip the
   tie-break where two longest edges tie → V2 must fail; (c) delete one `open` leaf → the verifier must
   reject the tree (a missing child), so no region can be lost by editing the ledger.
These test the verifier's discrimination only; the 8D statement uses the same dimension-free proof.

## 7. Scope

* No global claim: the theorem is conditional on a finite tree whose leaves all carry valid
  certificates. Producing that tree is a separate obligation, as is the per-cell bound itself.
* No rate, no sampling, no solver; all verifier checks are exact rational.
