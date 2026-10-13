# n14 k=11 branch: three-hub core geometry (structural note, v2)

Scope: `research-2026/next-cover-global/members/three-hub/` (writes here only).
Setting (from `CORE-COUNT-REDUCTION.md`): r ≤ U = 0.33173203427623414 < 1/3,
**a = 1−2U = 0.33653593144753172** > U ≥ r, k = 11 active disks, three strictly
inactive hubs with |h_j| < 1−r whose disks cover the closed core K = B(0,a).

## Errata of v1 (Lead review, all confirmed)

- **Deleted false lemma.** v1 justified steps by "boundary suffices for a finite
  union of disks since f = min|x−h_j|² has no interior local maximum". That is
  FALSE: three disks around a hole have an interior Voronoi maximum. What is true
  and all that is used below is the trivial direction: **if K is covered then
  S(0,a) is covered**. (For two disks the no-interior-maximum statement is true;
  for three it is not.)
- **Separation vector must be unit** (now stated).
- **Helly misuse removed.** For three sets in R², pairwise intersection does NOT
  imply a common point (equilateral counterexample: side 1.9U gives circumradius
  1.9U/√3 > U). The equivalence MEC(h₁,h₂,h₃) ≤ U ⟺ B(h₁,U)∩B(h₂,U)∩B(h₃,U) ≠ ∅
  is the definition, not Helly; "pairwise d_ij ≤ 2U" is necessary but not sufficient.
- **No dimension reduction.** Three centres modulo global rotation are 5-dimensional;
  a diameter bound constrains but does not reduce dimension. The wording
  "3-parameter family" is withdrawn (bounded/diameter-constrained 5D is correct).
- **Gap-bridging claim withdrawn.** The statement "coverage forces
  β_k + β_{k+1} ≥ g_k for consecutive centres" is FALSE: the third arc may cover the
  middle of a gap. Only Σβ_j ≥ π survives (measure argument), and that is what is used.

## Proved (analytic, degeneracies allowed)

**P1 (distinctness).** The three hubs occupy three distinct positions.
*Proof.* If two coincided, the union would have at most two distinct disks and hence
meet S(0,a) in at most two arcs, each of halfwidth < π/2 (see P3), total length < 2π,
contradicting that K (hence S(0,a)) is covered. ∎

**P2 (origin inside the triangle).** 0 ∈ int conv{h₁,h₂,h₃}.
*Proof.* Otherwise, by the separating hyperplane theorem for the compact convex set
conv{h_j}, there is a **unit** u with ⟨h_j,u⟩ ≥ 0 for all j. Then p = −a u ∈ K has
|p−h_j|² = a² + |h_j|² + 2a⟨h_j,u⟩ ≥ a² > r², so p is uncovered. Contradiction. ∎
*Consequence.* The three hub directions are not contained in any closed half-plane;
equivalently all three cyclic gaps between consecutive directions are < π.

**P3 (uniform arc bound).** The arc A_j = B(h_j,r) ∩ S(0,a) has halfwidth
β_j ≤ asin(r/a) < π/2 when nonempty (t_j = sqrt(a²−r²) is the equality case), and is
empty otherwise; hence |A_j| = 2β_j < π.
*Proof.* cos β = (a²+t²−r²)/(2at) = (t + (a²−r²)/t)/(2a) ≥ √(a²−r²)/a by AM-GM. ∎

**P4 (essential arcs).** Every A_j is nonempty and A_j ⊄ ⋃_{i≠j}A_i.
*Proof.* The A_j cover S(0,a). Two arcs of halfwidth < π/2 have total length < 2π, so
two of them cannot cover the circle; hence each is essential. ∎

**P5 (counting).** Σ_j β_j ≥ π.
*Proof.* The union covers S(0,a), so 2π ≤ Σ_j |A_j| = 2Σ_j β_j. ∎
*(v1's gap-bridging refinement is withdrawn, see errata.)*

**P6 (three arcs shorter than a semicircle that cover S¹ meet pairwise).**
Let A,B,C be three closed arcs of S¹, each of length < π, with A∪B∪C = S¹. Then each
pair meets.
*Proof.* Suppose A∩B = ∅. Both are nonempty proper arcs, so S¹\(A∪B) has exactly two
nonempty components X,Y separated by A (and by B). Since C is a connected arc and
X∪Y ⊆ C, C must also contain a connecting piece, i.e. C ⊇ X∪Y∪A or C ⊇ X∪Y∪B;
in either case |C| ≥ 2π − |A| − |B| + min(|A|,|B|) = 2π − max(|A|,|B|) > π,
because max(|A|,|B|) < π. Contradiction. ∎

**P7 (the three hub disks share a point of the core).** ⋂_j (B(h_j,r) ∩ K) ≠ ∅.
*Proof.* Let S_j := B(h_j,r) ∩ K. These sets are convex (intersections of convex
sets), nonempty, and their union is K (given). By P6 applied to the arcs A_j ⊂ S_j on
S(0,a) — which cover S(0,a) and have length < π by P3 — each pair S_i ∩ S_j is
nonempty (the pairwise arc intersection point lies in S(0,a) ⊆ K). All nonempty
intersections of the S_j are convex, hence contractible, and K is contractible
(a disk). If S₁∩S₂∩S₃ were empty, the nerve of the cover {S₁,S₂,S₃} would be the
3-cycle (a circle), contradicting the nerve lemma for a finite closed cover by sets
with contractible intersections of the union being homotopy equivalent to the nerve
(equivalently, elementary KKM form). Hence the triple intersection is nonempty. ∎

**P8 (consequences).** min enclosing radius of {h₁,h₂,h₃} ≤ r ≤ U; pairwise
|h_i − h_j| ≤ 2r ≤ 2U; in particular the three radius-U disks about the hubs have a
common point, and the hub triangle is "fat" (all sides ≤ 2r).
*Proof.* Immediate from P7 (the common core point witnesses the enclosing circle of
radius r) and the triangle inequality. ∎

*Independent numeric support (diagnostic only, superseded by P7):*
`three_hub_probe.py` maximised the minimum enclosing radius over randomly restarted
Nelder–Mead runs with r = U and the exact arc-covering condition; best ≈ 0.32675 < U
(≈ 4000 trials, 240 s). This is consistent with P8 but proves nothing.

## What remains for the k11 exclusion

With P1–P8 the hub triple lies in the compact, diameter-constrained 5-dimensional
family {0 ∈ int conv, all |h_i−h_j| ≤ 2r, |h_j| < 1−r, arcs cover S(0,a) and each is
essential}. The domain is still 5D modulo rotation; no parameter reduction is claimed.
The next interface to build is the exposed-boundary capacity on ∂D together with the
three hub circles (the ring arcs must cover ∂H and ∂D), in the atomic-dual form used
for n12, with the three hubs confined by P1–P8. Degeneracies to keep: tangencies
(A_i∩A_j a single point), empty arcs, hubs collinear with 0 on the boundary of the
triangle (excluded by P2), and the case r < U strictly (P5 gives β_j ≤ asin(r/a),
so the numeric readings quoted at r = U are the worst case).

Files: this note; `three_hub_probe.py` + `three_hub_probe.json` (diagnostic).
No claim registered; P1–P8 are analytic statements awaiting independent review.
