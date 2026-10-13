# q11_polytope_split.py — reusable exact polytope bisection (member scope; no claims)

Deliverables: `q11_polytope_split.py` (library, import-safe), `q11-polytope-split-tests.json`
(self-test output), this note. Nothing runs on import; only `run_tests()` / `__main__` computes.

## API

```python
Triple = (cL, cB, cP)          # Fractions; means cL*L + cB*B + cP*(2pi)
Vertex = tuple of `dim` Triples
Inequality = (normal, rhs, label)     # integer/Fraction normal, meaning  normal . d >= rhs
Equality   = (normal, rhs) or None

default_decider(u=0.33173203427623414)   # own asin/pi enclosures -> IntervalDecider (rigorous)
RationalDecider(l, b, t)                 # exact evaluation at given rational symbol values
IntervalDecider(l_bounds, b_bounds, t_bounds)  # raises UndecidedSign on a straddle

Polytope(dim, vertices, inequalities, equality=None, decider=None, name="")
    .vertices .active .active_rank .edges .degrees      # cached
    .value(v, normal) -> Triple
    .side(v, normal, rhs) -> -1 | 0 | 1
    .face_dim(i, j) -> int                              # dim of minimal face containing i, j
    .is_feasible(v) / .is_vertex(v) -> bool
    .split(normal, rhs, label="cut") -> (child_ge, child_le, report)
       child_ge = P ∩ {normal.d >= rhs}, child_le = P ∩ {normal.d <= rhs}, BOTH CLOSED
    .to_dict(include_vertices=True)

midrange_split(P, normal, label)      # RHS = componentwise average of the min/max coordinate Triples
                                      # (its value is the numeric midpoint of the range)
split_all_coordinates(P)              # all dim midrange coordinate splits
coverage_report(source, ge, le)       # structural coverage facts
enumerate_vertices_rank_dfs(dim, inequalities, equality, decider, cap, max_nodes)
                                      # independent complete enumeration, rank-pruned DFS with caps
verify_children_by_enumeration(source, ge, le, cap)
build_D11(decider) / build_one_chord(middles, decider)   # canonical instances
```

## Guarantees

* **Exactness.** Coordinates are Fractions throughout; only the *sign* of a Triple needs the
  numeric symbols, and that is delegated to a `Decider`. Supply your own to use your constants.
* **Both closed children.** Vertices of `P ∩ {>=}` = vertices of P with side ≥ 0 plus crossings of
  edges that straddle the cut; the two closed children therefore cover P as sets
  (`{n.d ≥ c} ∪ {n.d ≤ c}` is everything). Crossings are obtained by **solving** the active system
  (equality + independent common facets of the edge + the cut row). No interpolation: the
  interpolation scalar is a ratio of two module elements and is generically irrational although the
  crossing point is a rational combination of (L, B, 2π).
* **Adjacency.** `face_dim(i,j) = dim − rank(eq + common active normals)`, i.e. the equality is
  counted exactly once; `face_dim == 1` is the edge test.
* **Degeneracies.** Vertices on the cut belong to both children; an edge lying in the cut yields no
  crossing; a cut beyond the range gives one full child and one empty child; a constant functional
  gives two copies of the source with a redundant cut row. Reports carry `empty`, `cut_binding`,
  `cut_redundant`, `possibly_lower_dimensional`, and counts of infeasible / non-extreme vertices.
* **Inherited completeness.** A child's vertex set is complete for its own system by the standard
  cutting theorem, so completeness inherits from the source's vertex and edge data. The independent
  DFS enumerator is provided for spot verification with explicit caps; the full 11-dimensional DFS
  is *not* run in the self-tests (it is far outside the small-instance budget).
* **Chaining.** `split` returns new `Polytope` objects with their own constraint list (the cut rows
  appended), so recursive bisection is just repeated `split`/`midrange_split` calls; child edge sets
  are computed lazily, only when a child is split again.

## Self-tests (`q11-polytope-split-tests.json`, ~16 s)

1. Canonical regression with the equality present: **D_11 = 110 vertices / 550 edges** (and the
   rank-based edge set is *identical* to the independently hand-derived combinatorial list
   V(k,j)~V(k,j′), V(k,j)~V(j,k)); one chord 54 / 270; two chords 24 / 132.
2. All 11 midrange coordinate splits of the one-chord polytope: children feasible and extreme, all
   new vertices appear in both children and are exactly the crossings, kept/crossing accounting
   exact, source fully covered, no vertex in neither child.
   Per coordinate: j ∈ {0,1,2}: 34 kept-below/20 kept-above with 34 crossings → children 54 and 68;
   j ∈ {3..10}: 48/6 with 48 crossings → children 54 and 96.
3. Degenerate cuts: cut containing a face **and** edges (10 vertices on the cut, 0 crossings; the
   10 on-cut vertices appear in both children), cut beyond the range (one empty child, other =
   source), constant functional (equality normal → both children = source, redundant cut row).
4. Toy calibrations with full independent enumeration and hand-checkable answers: unit square cut at
   x = 1/2 → 4 / 4 vertices with 2 shared crossings; triangle x+y+z = 1 (ambient dim 3, equality
   present) cut at x = 1/3 → 3 / 4 vertices; DFS enumerations match the split children exactly.

## Bugs caught in pre-acceptance review (fixed here)

* `face_dim` double-counted the equality (`dim−1` and then subtracting `rank(eq+common)`), which
  selected 2-faces as edges and made the crossing rank unreachable. Now
  `dim − rank(eq + common)`; the regression is the 550-edge D_11 count *with the equality present*.
  The same wrong target `(dim−1)−1` in the crossing routine is now `dim − 1`.
* A straddling edge whose crossing failed silently produced `None` and was discarded; it now
  **raises**, since a straddling edge must have exactly one crossing.
* Self-test data bug (found by the tests themselves): the toy square's y-cap RHS was written in the
  wrong symbol slot (`(0,−1,0)` = −B instead of `(−1,0,0)` = −L), which silently removed one edge.
* Test-only timeout: the 11-dimensional DFS verification was removed from the self-tests (bounded
  small-instance calibration instead); the function stays available with explicit caps.

Lead-side status acknowledged: the independent lead enumerator reconstructs all child vertex sets
exactly; that audit is not coupled to this note.
