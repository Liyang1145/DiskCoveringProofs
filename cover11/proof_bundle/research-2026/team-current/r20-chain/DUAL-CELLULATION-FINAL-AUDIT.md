# DUAL-CELLULATION-FINAL-AUDIT (r20-chain) — embedded dual disk from connected arcs, without genericity

Strict check of `lead/VORONOI-BOUNDARY-REDUCTION.md` and `lead/DUAL-DISK-INTERFACE-AUDIT.md`.
Reasoned independently; **claim scope is never used as evidence**.  Audit only, `lead/` untouched,
no subagents, no new certificate.

**Correction log (2026-09-25k, lead's review).**  My earlier "zero-width wedge" finding and its repair
suggestions (repeated dual nodes / pseudogons) are **retracted as impossible** — see §2, where the
positive-width statement is now proved.  The ear-counting premise is **proved elsewhere** (C9²:
3-cliques are consecutive triples), so §6 no longer marks it conditional and the hub audit is not
reopened.

## 0. Inputs actually used

From the connected-ownership statement only: eleven distinct sites; the clipped nearest-site cells
partition `D` with **disjoint interiors**, are **convex** (Voronoi cells ∩ a convex disk) and have
nonempty interiors; nine ring cells contain exactly one positive-length boundary arc each, cyclically
ordered, with nine pairwise distinct switches, each involving exactly two adjacent ring sites, and each
ring cell owning exactly one boundary interval.  Two hub cells are compact in `int D` and own no
boundary point.  No genericity and no trivalence are assumed.

## 1. Simplicity of the dual (lemma, no genericity)

For `A ≠ B` convex with nonempty interiors and `int(A ∩ B) = ∅` (disjoint Voronoi interiors), the set
`A ∩ B` is convex with empty interior, hence lies in a line: it is a **point or a segment**.  So two
cells share at most one positive-length boundary piece (dual is **simple**), and a point contact yields
**no** dual edge while retaining the **co-point witness**.

## 2. Positive width at every primal vertex (proof; my earlier repair is withdrawn)

Let `x` be a finite Voronoi vertex with incident distinct sites `c_1,…,c_k`, all at the common distance
`|c_j − x| = ρ > 0`.  For a unit direction `v`, the ray `x + tv (t ≥ 0 small)` belongs to the cell of
`c_j` iff for all `j'`:

`|x + tv − c_j|² ≤ |x + tv − c_{j'}|²`  ⟺  `(x − c_j)·v ≤ (x − c_{j'})·v`  ⟺  `(c_j − x)·v ≥ (c_{j'} − x)·v`,

because the `O(1)` terms cancel by equal radius `ρ`.  Hence cell `j` owns the ray iff directions are
projected on `c_j − x` maximally, i.e. each site's wedge is

`W_j = { v : ⟨c_j − x, v⟩ > ⟨c_{j'} − x, v⟩ for all j' ≠ j }`,

an **open** set.  Take `v_j := (c_j − x)/ρ`: then `⟨c_j − x, v_j⟩ = ρ`, while for `j' ≠ j`,
`⟨c_{j'} − x, v_j⟩ = ρ cos∠(c_{j'} − x, c_j − x) < ρ` **strictly** (sites distinct and on the common
circle).  So `v_j ∈ W_j` with strict inequalities, and by openness `W_j` contains a neighbourhood of
`v_j`: **every incident cell has a locally positive-width wedge**, the sites are in strictly convex
position on the circle, the wedges occur in a cyclic order with each cell once, and consecutive cells
are adjacent along a genuine positive-length bisector ray.  Therefore:

* **no zero-width wedges exist**, so no repeated dual nodes and no pseudogons are needed;
* the link is a single simple cycle and the spokes bound **one** simple dual polygon — the source's
  "cyclic order without repeats (each convex cell has only one local angular sector)" is correct and
  needs no repair.  My earlier §2 finding is **withdrawn**.

## 3. Outer cycle, collar, and the dual disk

At a boundary switch only its two ring sites are equidistant and `≤ r` while all others are `> r`
(strict separation persists locally), and the bisector is **secant** (distance from origin
`||c_i|²−|c_j|²|/(2|c_i−c_j|) ≤ (|c_i|+|c_j|)/2 ≤ √(1−r²) < 1`), so exactly one ray enters `D`: each
switch has degree 3 (two circle edges, one interior edge).  Each ring cell owns a single boundary
interval, so its two switch-spokes enclose one boundary sector; the nine sectors form the collar between
`∂D` and the outer dual cycle, and removing it leaves a cellulation of a disk with faces corresponding
to interior primal vertices.  An outer dual edge cannot join two switches without interior endpoint
(that would force the same two ring cells at two distinct switches); independently, ties on `∂D` lie in
`I_i ∩ I_j`, which is empty for non-adjacent pairs and contains exactly one tie for adjacent pairs.

## 4. Boundary no-triple ≠ planar no-triple

The ledger's no-triple concerns **boundary arcs** only; in the interior `k ≥ 3` (even `≥ 4`) cells may
share a point.  Hence the counts stay inequalities: `e = v + 10` from Euler, `2(e+9) ≥ 3v+27` from
degree ≥ 3, so `v ≤ 11`, `e ≤ 21`, with equality only in the all-trivalent case.  Dual faces may have
many sides and any triangulation must be performed inside each face (on its link).

## 5. Triangulation preserves the co-point witness

Each original interior primal vertex `x` is nearest to every incident site, so `|x − site| ≤ r` for each
(covering): every diagonal between two ring sites of a refined face has the genuine common point `x`, so
the witness survives refinement.  The source's cautions stand: artificial triangles are not a
perturbation of the centers, some primal edges have zero length, and **counts never certify positive
metric lengths**.

## 6. Ear counting (premise proved elsewhere; hub audit not reopened)

The skip-one-ear dichotomy uses the premise that a 3-clique of ring disks can only be a **consecutive
triple** of ring sites.  Per the lead this is proved in **C9²** by an independent argument: the adjacent
differences of the ring distances give `9 ≥ 7`, so pairwise distance `≤ 2` for three sites is possible
only for three consecutive indices.  With that premise, the long-side ring-only 8-gon would need `12`
original cycle edges where only `7` are available — consistent, and now sourced rather than assumed.
The link argument (delete one hub from the other hub's simple link cycle → simple ring path with
distinct endpoints = the two faces of the common hub edge → every path edge is a core boundary edge →
the two hubs force the two boundary `u–v` paths → exactly two fans plus two hub-hub triangles) stands,
and correctly avoids the false claim that the interior hub-hub edge alone splits the disk.  No hub audit
is reopened here.

## 7. Verdict

* **Sound**: embedded dual (one node per clipped cell, one edge per positive-length shared piece,
  simple), **positive-width wedges proved at every primal vertex** so each primal vertex gives one simple
  dual face with no repeats and no repair needed, outer dual cycle with exactly nine spokes and exactly
  one interior face per outer edge, counts as inequalities, refinement preserving co-point witnesses.
* **Sourced, not conditional**: the ear premise now rests on C9²'s 3-clique ⇒ consecutive-triple
  statement; the two structural facts the source itself leaves open (hub cells sharing an edge;
  absence of ring-ring chords; full trivalence) remain open and are not needed here.
* No scope-as-evidence: every step uses convex-cell + disjoint-interior + connected-ownership hypotheses
  explicitly.
