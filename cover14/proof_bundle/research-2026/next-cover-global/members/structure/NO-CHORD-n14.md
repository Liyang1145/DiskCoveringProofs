# n14, k=10: non-adjacent active disks are disjoint (no-chord, rigorous)

Scope: `research-2026/next-cover-global/members/structure/` (this file only).
Object: D = closed unit disk covered by n = 14 equal closed disks of radius r,
r < 1/3; exactly k = 10 of them meet S¹ ("active"), m = 4 do not ("hubs").
Centers arbitrary in R², repeats and tangency allowed. Labels 1..10 denote the
active disks ordered by the midpoints of their actual arcs on S¹.
This note proves the k=10 instance of inequality (III) of
`SELECTION-n13-n14-n15-n25.md`, adapting the verified k=9 theorem C933
(`research-2026/n12-global/lead/NINE-RING-NO-CHORDS.md`, audited in
`.../finite-reduction/CHECK-no-chords.md`, constants in
`.../finite-reduction/evidence/no-chords-constants.txt`).

## 1. Theorem

**Theorem (n14 k=10 no-chord).** Let 0 < r < 1/3 and let 10 closed disks of
radius r cover a set containing S¹ (in particular, let them be the active disks
of a 14-disk cover of D). Label them by the midpoint order of their actual arcs
A_1,…,A_10 ⊂ S¹. Then for every pair with cyclic distance ≥ 2 the two *closed
disks* are disjoint (no common point in R²).

Since U(14) = 0.331732034276234187830212518528 < 1/3 (exact rational
comparison against the certified bound of
`research-2026/session2/n1314/STATUS.md`), the theorem applies to every
putative n14 cover at radius r ≤ U(14).

Note the clean hypothesis: **r < 1/3**, not r ≤ some decimal. The margin at
r = U(14) is asin(2r)+7asin(r) = 177.18° vs π, i.e. +2.82°; at r = 1/3 it is
178.11°, i.e. +1.89°. The proof below is stated for r < 1/3 so that the
constants can be verified with rational arithmetic only.

## 2. Proof

Throughout, arcs are measured on S¹; α_i denotes the half-width of A_i.

(1) **Half-width bound and arc essentiality.** An active disk of radius r has
    centre norm in [1−r, √(1−r²)]; writing t for that norm, the arc half-width is
    α(t) = arccos((1+t²−r²)/(2t)), whose argument has derivative
    (t²+r²−1)/(2t²) < 0 on that interval, so α is INCREASING in t and is
    maximal at the OUTER end t = √(1−r²) (there α = arccos(√(1−r²)) = asin(r); at
    the inner root t = 1−r the arc degenerates with α = 0), giving α_i ≤ asin(r) < asin(1/3) < 17/50
    = 0.34 (rational Taylor bound, §3). Hence each arc has length
    < 2·0.34 = 0.68 rad < π/4, and any nine arcs have total length
    < 18·0.34 = 6.12 < 2π (rational π-bound, §3). Therefore no nine of the ten
    arcs cover S¹: **every A_i is essential**.

(2) **Order consistency.** Because each arc is essential, no arc contains
    another. With arc lengths < π/4 < π, lifting the circle to an interval
    around any overlap makes the endpoint order agree with the midpoint order
    (an inversion would force the shorter interval inside the longer, which
    essentiality forbids). This is step for step the C933 argument, whose
    length hypothesis (< π/4) is satisfied here by (1).

(3) **A crossing pair spans a short arc.** Suppose non-adjacent active disks
    i,j share a point p ∈ R². Their arcs are contained in the actual arc
    J := S¹ ∩ B(p, 2r): for x ∈ A_i, |x−p| ≤ |x−c_i| + |c_i−p| ≤ r + r = 2r.
    Since 2r < 2/3 < 1, J is a single closed arc; its chord is at most the
    diameter 4r of B(p,2r), so its angular length satisfies
    2 sin(|J|/2) ≤ 4r, i.e. |J| ≤ 2·asin(2r) < π.

(4) **At least three complete arcs inside J.** Cut S¹ outside J and lift it to
    an interval, choosing lifts of A_i, A_j contained in J and ordering their
    left endpoints. Every intervening arc of the endpoint order also lies in J,
    because both its endpoints lie between the corresponding endpoints of A_i
    and A_j. Non-adjacency in the 10-cycle means the cyclic distance is in
    {2,…,8}, so in *both* circular directions at least one label lies strictly
    between i and j; hence whichever lift is chosen, J contains the complete
    arcs A_i, A_j and at least one further complete arc — at least three in
    total.

(5) **Measure contradiction.** Those ≥3 arcs cover at most |J|, and the
    remaining at most 7 arcs have total length ≤ 7·2·asin(r). Covering S¹
    therefore forces
        2π ≤ |J| + 7·2·asin(r) ≤ 2·asin(2r) + 14·asin(r),
    i.e.
        π ≤ asin(2r) + 7·asin(r).                                     (∗)
    But r < 1/3 gives, with asin increasing,
        asin(2r) + 7·asin(r) < asin(2/3) + 7·asin(1/3) < 73/100 + 7·17/50
                             = 3.11 < π,
    contradicting (∗). Hence no non-adjacent pair shares a point, and since the
    disks are closed, non-adjacent active disks are disjoint. ∎

## 3. Constant verification (exact rational, no decimal inverse-trig)

Script: `nochord_n14_constants.py` in this directory; output
`nochord_n14_constants.out.txt`. Chain:

* U(14) < 1/3: the certificate bound of this goal,
  331732034276234187830212518528/10^30 (displayed elsewhere as .33173203427623414),
  is < 1/3 by exact Fractions. The theorem keeps the clean hypothesis r < 1/3.
* sin(73/100) > 2/3 via the alternating Taylor lower bound
  sin x ≥ x − x³/6 + x⁵/120 − x⁷/5040 on [0,1]; hence asin(2/3) < 73/100.
* sin(17/50) > 1/3 by the same bound; hence asin(1/3) < 17/50.
* 9·(17/50) = 3.06 < π: from the inscribed regular 12-gon,
  π > 12 sin(π/12) = 3(√6−√2) > 3(2449/1000 − 1415/1000) = 3.102 > 3.06
  (rational enclosures of √6, √2).
* 73/100 + 7·17/50 = 3.11 < π: from the inscribed regular 16-gon,
  π > 16 sin(π/16) with sin(π/16) = √(2−√(2+√2))/2; using √2 < 14143/10000
  gives 2+√2 < 3.4143, hence √(2+√2) < 1.8480, hence
  2−√(2+√2) > 0.1520 and sin(π/16) > √0.1520/2 > 0.19490, so
  π > 16·0.19490 = 3.1184 > 3.11.
* The only non-rational ingredient is the elementary fact that the perimeter
  of an inscribed regular polygon is < 2π (definition of π as half the
  circumference); no trig function is evaluated numerically.

## 4. What the theorem does and does not give (Voronoi vs disk non-adjacency)

This distinction is the reason the C933 source is quoted rather than
paraphrased; it matters more for k=10 than for k=9 because a 10-cycle admits
more non-neighbour relations.

* **Proved (about disks / common covered points):** non-adjacent active disks
  are disjoint as closed disks. Consequences (each a direct logical
  consequence, not an extra assumption):
    – no three active disks have a common point (any three labels of a 10-cycle
      contain a non-adjacent pair);
    – a *common-point / nearest-site* edge between two active sites can only
      join labels adjacent in the circular order;
    – no triangle all of whose vertices are active can arise in a refinement
      whose triangles carry a common empty-circle centre in D of radius ≤ r.
* **Not proved here (separate obligations):**
    – that every pair of consecutive labels really is Voronoi/Delaunay adjacent
      (the theorem is one-directional: non-adjacent ⇒ disjoint);
    – that an embedded straight-line dual triangulation exists for the
      10-boundary + 4-hub configuration, or that its edges are chords of the
      circle;
    – any statement about hub adjacency, or that every triangle of such a dual
      meets the hub set;
    – that arbitrary straight segments between centres are absent. C933's own
      closing sentence says the same for k=9, and no stronger reading may be
      imported here.
* **Cell-level is NOT stronger (correction).** Under a cover, every x ∈ D is
  within r of some site, hence within r of its NEAREST site; so every clipped
  Voronoi cell lies in the disk of its own site:
      cell(i) ∩ D ⊆ B(c_i, r).
  Hence disjoint disks give DISJOINT clipped cells, full stop: a common cell
  point would satisfy |x−c_i| = |x−c_j| ≤ r and thus lie in both disks,
  contradicting their having no common point. No facet-sharing qualification
  applies to such a pair. What
  remains a genuinely separate obligation is only the EXISTENCE of an embedded
  straight-line dual (and hub adjacency in it) - see K10-BOUNDARY-CELLS.md.

## 5. Where this sits in the n14 route

Together with the counting package of `SELECTION-n13-n14-n15-n25.md`, the n14
admissible range is k ∈ {10,11} and the minimal case k=10 now carries the same
no-chord structure as the solved n12 k=9 case, with parameters
k=10 boundary vertices, m=4 hubs and T = k + 2m − 2 = 16 triangles. The
remaining gaps are unchanged and explicitly listed there: the 10+4 dual
classification and sharp lower bound (§4.3), the k=11 case with m=3 (§4.4),
the sharp m-disk covering thresholds (§4.2), and the lower-bound side (§4.5).

Status: theorem proved modulo (i) the C933-inherited steps (1)–(4) (the k=10
argument is the same argument with the k−3 coefficient; the |J| ≤ 2asin(2r)
step is inherited and re-used verbatim, with the same length hypotheses
re-verified above) and (ii) the elementary polygon facts of §3. Both are set
out above so that an independent checker can attack them separately.
