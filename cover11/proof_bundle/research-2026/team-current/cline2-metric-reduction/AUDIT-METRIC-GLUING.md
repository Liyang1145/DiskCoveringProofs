# Audit of `lead/METRIC-GLUING-SUFFICIENCY.md` (compact, corrected)

Scope: exact audit of the stated lemma. The abstract boundary is `P_0...P_8` (chords
`P_(i-1)P_i`); ring sites and arcs are **not** boundary pieces and attach only after the
development. My earlier note (superseded, filed under `GLUING-SUFFICIENCY.md`) wrongly assumed
a `P c P c ...` boundary and is withdrawn; there is no unspecified boundary gap.

## Verdict: the proof is correct on its stated positive domain.

**A. Flat development.** Interior vertices = the 11 sites; `2 pi` at each gives zero cone
angle, so the disk is flat; the developing map is path independent because the dual-graph
cycles are spanned by vertex circuits (identity, since the rotation about the vertex is by the
full `2 pi`) plus the boundary loop (next point). **Correct.**

**A. Boundary = canonical polygon.** The induced boundary data — chord
`|P_(i-1)P_i| = 2 sin(w_i/2)` and left-turn `(w_i+w_(i+1))/2` — are exactly those of the
cyclic polygon `Q_i = e^{i sum_{j<=i} w_j}`; the induction gives congruence, and `sum w_i = 2 pi`
gives closure. Hence the boundary develops to a strictly convex polygon traversed once CCW.
**Correct, and this is the load-bearing step.**

**A. Injectivity.** Regular points: preimages distribute over face interiors, each
orientation-preserving, so the degree equals the winding number of the boundary, `1` inside and
`0` outside; interiors of the developed triangles partition the polygon with multiplicity 1.
Edge/vertex clause: replace by the standard statement — the development is a proper local
homeomorphism of degree 1, hence a homeomorphism onto its image. **Correct in substance.**

**B1. Barycentric circumcircle identity.** `sum_j lambda_j |x-c_j|^2 = rho^2 - |x-O|^2 <= rho^2`
for barycentric `x`; so some `|x-c_j| <= rho`. Independent of where `O` lies, so obtuse faces
included. **Correct and complete.**

**B2. Switch triangle.** `|c_i-c_j| <= 2R` gives `|c_i-M|<=R` for the midpoint `M`; the two
half-triangles `(c_i,M,P)`, `(c_j,M,P)` sit in the convex balls. **Correct.**

**B3. Sector triangle.** All three vertices lie in `B(c_i,R)`; convexity. **Correct.**

**B4. Exterior circular segment.** `c.P, c.Q >= (1+|c|^2-R^2)/2 > 0` for `R<1`. For `Z` on the
minor arc, `Z = aP+bQ` with `a = sin(w-phi)/sin w`, `b = sin phi/sin w`, `a,b>=0` and
`a+b = cos(w/2-phi)/cos(w/2) >= 1`; hence `c.Z >= min(c.P,c.Q)` and so
`|Z-c|^2 <= max(|P-c|^2,|Q-c|^2) <= R^2`. The inequality is **not** the triangle inequality —
positivity of the dots plus `a+b>=1` is what does the work; state it that way. **Correct (and
the bound can be strengthened to `max` of the endpoint distances).**

**B5. Coverage of `D`.** The nine minor arcs partition the circle (`w_i>0`, `sum=2 pi`), so `K`
(B1–B3) plus the nine disjoint-interior segments (B4) is `D`. **Correct.**

**C. Interface / scope.** The component identities are the established ones. Note again that
with the correct conventions the closure rows are *identities* of the geometry, so the
interface adds no independent equation. The sentence "the full simultaneous system is
sufficient" is right in this precise form: *if* the factor system has a solution in the strictly
positive domain, then the development is injective and the 11 radius-`R` disks cover `D`, so no
planar/circle-realization condition is missing. It gives **no bound** and says nothing about
nonemptiness of that domain; add that proviso.

**D. Count (my earlier remark withdrawn).** `E = 48` is exact as the lead enumerated:
hub degrees `6 + 7 = 13` counts the hub-hub edge `AB` twice, so the ring-hub edges number `11`
(not `13`), internal edges `9 + 11 + 1 + 18 = 39`, boundary `9`, total `48`, Euler `1` for the
open disk convention used in the factor system. My `47/2` claim was an arithmetic error.

## Withdrawn from my earlier message

* **D (count).** `E = 48` is exact as the lead enumerated: hub degrees `6+7 = 13` counts the
  hub-hub edge twice, so ring-hub edges are `11`, internal edges `9 + 11 + 1 + 18 = 39`,
  boundary `9`. My `E = 47` / "Euler should be 2" was an arithmetic error and is withdrawn.
* The wording points 1–4 below are optional presentation notes only; my §1–§4 remarks are local
  checks and are **not** independent certification of the lead's interfaces, and the lead's
  proofs stand unchanged.

## Optional presentation notes (not corrections)

1. The edge/vertex injectivity clause can equivalently be read through the proper-map degree
   statement; the draft's own argument is not wrong.
2. The interior-vertex/boundary identification is already stated by the 29-face list.
3. In B4, `a+b >= 1` and the `max`-form inequality can be stated explicitly.

No error found in the substance: positive metric gluing of this factor model does suffice.
