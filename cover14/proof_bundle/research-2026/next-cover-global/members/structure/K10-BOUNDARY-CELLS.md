# n14, k=10: boundary ownership cells and the clipped Voronoi outer cycle
# (rev. 2 — replaced the invalid cone/convexity connectedness argument)

Scope: `research-2026/next-cover-global/members/structure/` (this file only).
Bridge from the analytic no-chord theorem to the boundary-cell combinatorics of
the ten boundary-active disks. The ownership argument is the one PROVED in the
n12 branch (`lead/NINE-BOUNDARY-OWNERSHIP.md`, §"same-radius inner-root pair has
at most one tie in any actual arc" and §"nearest ownership"), re-used with the
general-k interface checked. No step is claimed that is not either proved here,
inherited from a proved/audited source, or explicitly marked as conditional.

## 0. Setting and inputs

D = closed unit disk; 14 equal closed disks of radius r cover D; exactly k=10
are boundary-active, m=4 are hubs. After the same-arc inner-root replacement
(read-only input INNER-ROOT-REDUCTION) the active centres satisfy
|c_i| ≤ s := √(1−r²) and ≥ 1−r; hubs satisfy |h| < 1−r. We use the goal's upper
bound U := Fraction('0.33173203427623414') = 16586601713811707/50000000000000000,
which satisfies U < 1/3 by exact rational comparison, so every admissible n14
radius obeys r ≤ U < 1/3 (this is why all constants below can be rational).

Inputs: (a) the n14 k=10 no-chord theorem (`NO-CHORD-n14.md`): for r < 1/3,
non-adjacent active disks have NO common point; (b) the counting package
`SELECTION-n13-n14-n15-n25.md`.

## 1. Ownership is Voronoi clipping; hubs never own boundary points

cell(i) := {x ∈ D : |x−c_i| ≤ |x−c_j| for all sites j}. The cells cover D.

**Lemma 1.** If x ∈ cell(i) then |x−c_i| ≤ r: the cover supplies a site j with
|x−c_j| ≤ r and |x−c_i| ≤ |x−c_j|.
Consequences: hub cells lie strictly inside D; and for x ∈ S¹ every hub h has
|x−h| ≥ 1−|h| > 1−(1−r) = r while the nearest site to x is at distance ≤ r, so
**the nearest site to any boundary point is active**. All boundary ownership is
by the ten active sites.

## 2. Corrected ownership argument (replaces the invalid cone step)

The rev. 1 text claimed that convexity of cell(i) plus 0 ∉ cell(i) makes
cell(i) ∩ S¹ connected via the cone over the cell. That is WRONG: a narrow
convex rectangle crossing the circle yields two caps without containing 0, and
the cone over a set is not its intersection with the circle. The following is
the n12 argument instead.

**(a) Essential arcs and short length.** Write A_i := B(c_i,r) ∩ S¹. An active
centre has norm in [1−r, √(1−r²)], and the arc half-width α(t) is increasing in
t with maximum asin(r) at t = √(1−r²) (see `NO-CHORD-n14.md` §2(1)), so
|A_i| ≤ 2·asin(r) < 2·asin(1/3) < π/4. Nine arcs cannot cover S¹, since
9·2·asin(r) < 18·(17/50) = 6.12 < 2π (rational chain in
`nochord_n14_constants.py`). Hence every A_i is **essential**: it is not
contained in the union of the other nine, so all ten arcs have positive length,
are distinct, and none contains another. In particular **no two active centres
coincide**.

**(b) Midpoint order = endpoint order.** For non-nested arcs shorter than π/4
the left and right endpoints have the same cyclic order as the midpoints, by
lifting around an overlap (this is the n12 step, whose length hypothesis
< π/4 is re-verified in (a)).

**(c) At most two arcs meet at a point.** If three met at x, unwrap around x:
all three lie in an interval shorter than π/2 (each extends < π/4 in each
direction, as in the n12 proof), so sorting left endpoints gives the same order
of right endpoints (no nesting), and the middle arc is contained in the union of
the other two - which meet at x - contradicting its essentiality.

**(d) Tie spacing (the key lemma, k-independent).** Let c_i ≠ c_j be two active
centres and L their perpendicular bisector. L passes through the midpoint
m = (c_i+c_j)/2, which satisfies |m| < s: the midpoint of two DISTINCT points of
the closed disk B(0,s) lies strictly inside it, by strict convexity (equality
|m| = s would force c_i = c_j = m). Hence dist(0,L) ≤ |m| < s, and the two
intersection points L ∩ S¹ have angular separation
    2·acos(dist(0,L)) > 2·acos(s) = 2·asin(r) ≥ |A_i|.
So **no single actual arc contains both tie points of a pair**: within any A_i,
the comparison between c_i and c_j changes at most once. This lemma uses only
|c| ≤ √(1−r²) — it contains no k.

**(e) Competitors are neighbours only (via the no-chord theorem).** If x ∈ S¹
lies in disk j while also lying in A_i, then x is a common point of disks i and
j, so by the no-chord theorem of `NO-CHORD-n14.md` (non-adjacent ⇒ no common
point) j is a cyclic neighbour of i. This replaces the n12 "exclusive pieces
traversal" step, which that document itself flags for an independent
combinatorial check; the substitute inherits the endpoint-order step (b)
instead.

**(f) Ownership is one interval.** Each A_i contains an exclusive relatively
open piece: the other nine arcs form a closed set not containing A_i, so
A_i ∖ ∪_{j≠i} A_j is nonempty and open in A_i. On that piece c_i is the unique
nearest centre among ALL sites (hubs are farther than r from S¹, other active
disks do not meet the piece, and c_i is within r). Only the two neighbours can
compete, and by (d) each comparison has at most one zero in A_i. A continuous
function on an arc with at most one zero has a sublevel set that is either the
whole arc, a prefix subarc, or a suffix subarc; hence each win-set against a
neighbour is one of these, and the ownership A_i ∩ (win vs left) ∩ (win vs
right) is the intersection of a prefix and a suffix of A_i, i.e. a single
(possibly empty) subarc. It is nonempty because it contains the exclusive
piece. Walking from the exclusive piece therefore reaches exactly one switch on
the left and one on the right, and the win-set cannot vanish in the middle and
reappear.

**Corollary.** The ten nearest-owned sets on S¹ are nonempty closed arcs
containing their exclusive pieces, pairwise interior-disjoint, covering S¹, and
consecutive ones meet in exactly one switch, which is a two-site tie (a
three-site tie would put a non-adjacent pair at a common point, contradicting
the no-chord theorem).

## 3. Each switch carries a facet entering D with positive angle

Let θ be a switch, owned by the two active centres c_i ≠ c_j. Their Voronoi
facet is the part in D of the bisector L_ij, and θ ∈ L_ij ∩ S¹. By (d),
dist(0,L_ij) ≤ |m| < s = √(1−r²) < 1, so L_ij is not tangent to S¹ at θ: it
crosses S¹ at θ and at a second point θ' ≠ θ, and L_ij ∩ D is a chord whose
relative interior lies in the open disk. At θ exactly two sites are at the
minimal distance (a third would be a triple tie, excluded by the Corollary), so
by continuity of the finitely many distance functions there is a neighbourhood
of θ in which i and j are the two nearest sites; intersecting that
neighbourhood with the chord gives a genuine 1-dimensional facet issuing from θ
strictly into the interior of D. Hence the inward angle is positive.

This is where the inner-root norm bound is used: without |c| ≤ √(1−r²) the
bisector could be tangent to S¹ and the facet would degenerate to the single
point θ. Note also that the facet need not reach the second intersection point
θ′: other cells may cut it, which is consistent with (and required by) the
Corollary that consecutive ownership arcs meet in exactly one switch.

## 4. Clipped Voronoi diagram and outer cycle

Piecing together §1–§3:

* boundary ownership is a partition of S¹ into the ten nonempty arcs of §2,
  belonging to the ten active cells in their cyclic order;
* every consecutive pair of active sites shares a facet, so the outer boundary
  of the clipped Voronoi dual is the **10-cycle** on the active sites in that
  order;
* hub cells are strictly interior (Lemma 1);
* CONDITIONAL on the existence of a triangulated embedded dual (see §6),
  Euler's identity for a k=10 boundary cycle with m=4 interior vertices gives
  T = k + 2m − 2 = 16 triangles, matching `SELECTION-n13-n14-n15-n25.md` (V).

## 5. General-k interface check

k-INDEPENDENT steps, reusable verbatim for any k:
* cover ⇒ cell ⊆ own disk (Lemma 1);
* hubs never own boundary points (Lemma 1);
* tie spacing (Lemma 2(d)) — uses only |c| ≤ √(1−r²);
* positive inward facet (Lemma 3) — same bound;
* ownership is one interval (Lemma 2(f)) — uses (d) and (e).

k-DEPENDENT inputs, each verified only for k=10 here:
* the essentiality inequality (k−1)·2·asin(r) < 2π, i.e. nine arcs insufficient;
* the length bound |A| < π/4 used in (b) and (c);
* the no-chord theorem in the form π ≤ asin(2r) + (k−3)·asin(r) being false.

Therefore an n14 **k=11** branch may reuse §1 and the first list of §5, but must
prove its own instances of the second list (10·2·asin(r) < 2π and the k=11
no-chord).

## 6. Not proved here (explicit obligations)

1. **Embedded triangulated dual.** Only the outer 10-cycle and the interiority
   of hub cells are established. Resolving co-circular/collinear degeneracies,
   choosing a triangulation, and showing straight dual edges need not cross are
   separate tasks; §4's T = 16 is conditional on this.
2. **Hub adjacency** (which hub cells meet which active/hub cells).
3. **Every triangle meets the hub set** — follows only after 1 and 2 with a
   declared convention.
4. **Inherited flag.** Step (b) inherits the endpoint-order argument, and
   `NO-CHORD-n14.md` inherits the crossing-pair measure step from the audited
   k=9 source; those are the two places where an independent combinatorial
   re-check is most valuable. Rev. 2 does not claim them as independently
   audited.
5. Nothing here concerns k=11, and nothing here is a lower bound.

## 7. Status of this note

Self-contained here (no inherited input): Lemma 1; §2(a) essentiality with the
rational constants of 
ochord_n14_constants.out.txt; §2(c); §2(d); §3.

Proved MODULO the two inherited inputs, both explicitly flagged:
  • §2(f) and the Corollary rest on §2(e), which rest on the n14 no-chord theorem
    (NO-CHORD-n14.md), itself stated modulo §2(b)-type endpoint ordering
    inherited from the audited k=9 source;
  • §2(b) is inherited verbatim, with only its length hypothesis π/4 re-checked
    for k=10.

Conditional on a further obligation: §4's Euler count T=16.
Open: §6 items 1–3. Nothing here is independently audited, and no claim is
registered; this is an interface document intended to be attacked.
