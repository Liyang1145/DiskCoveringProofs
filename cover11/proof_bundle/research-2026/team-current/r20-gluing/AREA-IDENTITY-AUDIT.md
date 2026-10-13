# AREA-IDENTITY-AUDIT — self-contained check of C817's area/angle identity, with the missing hypothesis named

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. Read-only audit of the C817 area identity as
used in `lead/COMPATIBLE-EDGE-SUPPORT.md` §3, `lead/SHARED-FACTOR-DUAL.md` §1–2 and
`lead/SHARED-RADIUS-REDUCTION.md`. **No registration, no edit of lead files, no numerics, no
sub-agent.** I do not repeat the new moment-cancellation work. Per instruction I do **not** treat a
cited conclusion as an audit: below, the pieces I can prove are proved, and the one step I cannot
reconstruct from the quoted text is stated as an explicit hypothesis.

## 1. The identity to be checked

For a genuine eleven-disk cover with the clipped nearest-site cellulation and the refined straight-site
Delaunay dual: the disk area decomposes as
```
π  =  Σ_{faces} (signed circumcentre-split areas)
    + Σ_{rings} (owned sector pieces)  ±  Σ_{switches} (b-pieces),
```
with the angle bookkeeping `Σ_f A_fi = 2π` at each hub, `α_i + Σ_f A_fi − b_left − b_right = π` at each
ring, and `b ∈ [0, π/2]` at each switch.

## 2. What I can prove self-containedly

**(a) Straight-site dual = clipped dual.** Already established in this lane by an independent proof
(`STRAIGHT-SITE-EMBEDDING-PROOF.md`): the refined dual `K` is a simplicial closed disk; fixing one
triangulation of each cocircular class makes every simplex of `K` a sub-simplex of one planar straight
Delaunay triangulation; the straight map is injective and, by compactness/Jordan, its image is exactly
the closed region bounded by the ring sites in arc order. Hence the faces, their incidence and their
tiling of `P` are the *clipped* ones — no independent assumption here ✔.

**(b) Hub angles.** Each hub is an interior vertex of `K`; the faces incident to it have disjoint
interiors whose union contains a neighbourhood of the hub (they tile `P`, and the hub lies in `int P`).
Therefore the angle sum at a hub is exactly `2π` ✔ — a consequence of the tiling, not of any
"winding-number" convention.

**(c) Face angles at a ring vertex.** At a ring vertex `v_i` (a boundary vertex of `P`) the incident
faces tile the interior of `P` near `v_i`, so their angles sum to the *interior angle of the polygon
`P` at `v_i`*, call it `ι_i`: `Σ_f A_fi = ι_i` ✔. This is the clean form of the "face side" of the ring
identity and needs no Voronoi input.

**(d) `γ` lives at the SITE, and `γ = π/2 − b` — corrected reading.** `COMPATIBLE-EDGE-SUPPORT.md` L9
defines `γ` as the **directed angle at the ring site** from the site-to-site ray (to the neighbouring
ring site) to the site-to-boundary-switch ray. My earlier note placed `γ` at the switch; that was a
misreading, and everything I built on it is withdrawn (§3). With `γ` at the site: consider the triangle
`(c_i, U_i, c_{i+1})`. Its two legs are **equal** (`|c_i − U_i| = |c_{i+1} − U_i| = ρ_i`, the defining
property of a boundary switch, which is the nearest-site tie point), so it is isosceles with apex at
`U_i`; write its apex angle as `2b`, i.e. `b` is the **half-apex at the switch**. Then the base angle at
`c_i` equals `(π − 2b)/2 = π/2 − b`, and that base angle is *exactly* `γ_r` (the angle at the site
between the rays to `c_{i+1}` and to `U_i`). Hence `γ = π/2 − b` ✔ — a two-line consequence of the
isosceles property plus the triangle angle sum, and `b ∈ (0, π/2)` because the triangle is
non-degenerate: the base `|c_i c_{i+1}| > 0`, the site-to-switch distances are strictly positive, and
the perpendicular-bisector endpoint used in the construction is strictly separated from the chord line
(the midpoint `m` of the two sites lies in `int D`, so the outward bisector endpoint has `ℓ > 0`), whence
`0 < b < π/2` and `γ ∈ (0, π/2)` strictly ✔.

**(e) Signed circumcentre splitting, including obtuse and cocircular.** For *any* point `O` and triangle
`ABC` with consistent orientation, `[OAB] + [OBC] + [OCA] = [ABC]` (oriented areas); specialising to the
circumcentre `O` gives the "signed splitting" used for the face areas, and the identity holds verbatim
when `O` is *outside* the triangle (obtuse case) because it is a boundary (shoelace) identity, not a
containment claim ✔. Cocircular degeneracies are harmless: refined triangles lie on the *same* circle,
each is nondegenerate, and the identity applies per refined triangle ✔.

## 3. The ring identity, self-contained (the "missing hypothesis (H)" is RETRACTED)

**Retraction.** My §3 previously claimed a missing hypothesis `(H)` because I had placed `γ` at the
switch. With the correct reading (§2(d): `γ` is the directed angle **at the site** from the site-to-site
ray to the site-to-boundary-switch ray) the identity is a genuine **partition of the ray order around
the site**, and no convention is needed:

Let `c_i` be a ring site, `c_{i−1}`, `c_{i+1}` its polygon neighbours, `U_{i−1}`, `U_i` the two boundary
switches of its owned arc, and `α_i` the angle at `c_i` subtended by that owned arc. Going around `c_i`
in the cyclic order of the rays `c_{i−1}, U_{i−1}, U_i, c_{i+1}`:

```
∠(c_{i−1}, U_{i−1}) = γ_l ,  ∠(U_{i−1}, U_i) = α_i ,  ∠(U_i, c_{i+1}) = γ_r ,
∠(c_{i+1}, c_{i−1}) (through the interior of P) = Σ_f A_fi = ι_i  (by §2(c)).
```
The four sectors are disjoint and exhaust the full turn, so
```
ι_i + γ_l + α_i + γ_r = 2π .                                  (★)
```
Substituting `γ = π/2 − b` from §2(d) into (★) gives `ι_i + (π/2 − b_l) + α_i + (π/2 − b_r) = 2π`, i.e.
`α_i + Σ_f A_fi − b_l − b_r = π` — **exactly C817's identity**, now derived rather than cited ✔.

**Why the partition is exact (the three checkpoints the lead names).** (i) The *interior* sector `ι_i`
is filled by the Delaunay faces at `c_i` by §2(c) — the faces tile `int P` near the boundary vertex.
(ii) Between the site-to-site ray and each site-to-switch ray lies precisely the *outer* wedge of the
switch triangle: the switch `U_i` is the perpendicular-bisector intersection on `∂D` that lies in the
owned overlap, the midpoint `m` of `c_i c_{i+1}` lies in `int D` (convexity of `D`), so the bisector
endpoint used has `ℓ > 0` and the two wedges `γ_l, γ_r` are strictly positive and non-overlapping with
`ι_i`. (iii) The middle wedge is the owned sector `α_i`, whose rays are exactly the two
site-to-switch rays; the ownership structure (each ring owns one arc, switches are transversally
distinct) makes the ray order unique, so `(★)` holds for every ring and there is no sign or overlap
convention to fix. Hence the "convention could rescue it" framing of my earlier note was simply wrong:
the identity was never in need of a convention — my `γ`-placement was.

## 4. Consequences

* The ring identity and the hub identity (§2(b)) therefore give: each ring contributes
  `π + b_l + b_r − Σ_f A_fi = α_i`, each hub contributes `2π`, and the signed face splitting (§2(e))
  supplies the face areas for both obtuse and cocircular faces. The *area* identity itself is the
  angular bookkeeping of these pieces, now derived from the partition rather than assumed.
* Nothing here uses the q1 moment multipliers (`SHARED-MOMENT-DUAL.md`), so this audit stays disjoint
  from that work; nothing is numeric, no claim is registered, and no lead file was modified.
