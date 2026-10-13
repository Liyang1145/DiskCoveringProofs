# Metric gluing sufficiency (superseded draft — corrected)

**This file replaces a 242-line draft of mine that had a wrong premise.** I assumed the
abstract boundary was the polygon `P_0 c_1 P_1 ... c_9 P_0` including the ring centres, and
built a "Case A / Case B" dichotomy on top of it. That was invented: the listed 29 faces
(verified incidence `V=20, E, F=29` in `lead/check_metric_gluing.py`) fix the abstract boundary
to be **`P_0...P_8` with chords `P_(i-1)P_i`** — the sector chord is the sole-incidence edge and
each endpoint-copy edge is shared by a sector and a switch triangle. There is no unspecified
boundary datum; the "boundary gap" I claimed does not exist, and the Case A/B discussion is
withdrawn. Ring sites and arcs attach only **after** the development, not as boundary pieces.

## What is correct (audit in `AUDIT-METRIC-GLUING.md`)

* **Flat development.** Interior vertices are the 11 sites; angle sum `2 pi` at each makes the
  cone angle zero, so the disk is flat and the developing map is path independent (the
  dual-graph cycles are spanned by the vertex circuits, whose rotation is by the full `2 pi`).
* **Boundary identification.** The induced boundary data — chord `2 sin(w_i/2)` and left-turn
  `(w_i + w_(i+1))/2` — coincide with those of the canonical cyclic polygon
  `Q_i = exp(i sum_{j<=i} w_j)`; congruence follows by induction over the nine edges and
  closure from `sum w_i = 2 pi`. So the boundary develops to a strictly convex polygon traversed
  once, and the injectivity follows by the proper-map degree argument (winding `1` inside,
  `0` outside).
* **Covering.** The barycentric circumcircle identity, the midpoint split of the switch
  triangle, the convexity of the sector triangle and the minor-arc lemma (`Z = aP + bQ`,
  `a, b >= 0`, `a + b >= 1`, hence `|Z - c| <= max(|P-c|, |Q-c|)`) are all correct as in the
  lead's draft; together they cover `D` by the 11 disks of radius `R`.

## Scope

Sufficiency holds for **positive** metric assignments (all 29 triangles nondegenerate, all
radii `> 0`, widths in `(0, pi)`, prescribed sums). It supplies no bound and says nothing about
whether that positive domain is nonempty; the sharp value remains open. Degenerate assignments
need the compact-limit treatment of `lead/POSITIVE-METRIC-INFIMUM.md`, audited separately in
`AUDIT-POSITIVE-INFIMUM.md`.
