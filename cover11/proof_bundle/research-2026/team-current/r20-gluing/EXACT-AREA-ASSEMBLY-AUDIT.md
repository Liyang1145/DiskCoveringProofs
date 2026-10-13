# EXACT-AREA-ASSEMBLY-AUDIT — is the shared-factor area formula really a clipped-Voronoi consequence?

Author: r20-gluing (cline2 / DS v4.1f), sole write scope this directory. **No claim registered.**
Audited sources (read-only): `lead/SHARED-FACTOR-DUAL.md` §"Exact area alternative",
`lead/BOUNDARY-SWITCH-ANGLE-PROOF.md` §1 and §4 (plus §3 for the wedge identity).

**Scope of this audit (framing).** This is an **audit of the sources' derivation of step (L)** —
the main proof in `BOUNDARY-SWITCH-ANGLE-PROOF.md`/`SHARED-FACTOR-DUAL.md` is **taken as correct**;
nothing here is offered as an independent theorem, and no correction below changes the conclusion
of (L). I re-derive (L) with *directed (signed) area*:

```
  pi = sum_{faces f} 2 rho_f^2 sinA_f sinB_f sinC_f
     + sum_{switches i} sigma_i^2 sin(2 b_i)/2
     + sum_{rings i} [ sigma_(i-1) sigma_i sin(alpha_i)/2 + (w_i - sin w_i)/2 ]          (L)
```

and I check *whether it follows from the clipped Voronoi partition plus the co-circular
refinement*, as opposed to assuming that the topological embedding is a straight-site
triangulation. Residual points, all presentation-level, are collected in §8 item 5. I do **not**
re-audit the closed `b`-direction (switch half-angle domain), and no numeric calibration is
offered as a substitute for the identity: every step below is exact algebra; the only numbers are
in §7, explicitly marked non-bearing.

---

## 1. Objects and hypotheses actually used

**Caliber correction (lead audit):** this obligation covers the **q1 and q0 exclusions**, not only
the canonical (6,7) configuration. Everything below is therefore phrased in terms of an
**arbitrary reduced 9 + 2 configuration** (any q-league whose exclusion uses the 29-factor area
dual), with the **clipped refined dual disk** as the object — **no** global/convex assumption on
the site polygon, and **no** assumption that the 11 faces are the Delaunay faces of a globally
triangulated site set. Correction on the vertex location: the **primal vertices of the *selected*
clipped dual disk lie in `int D`** (H3), so the boundary-adjacent Voronoi edges need no
truncation; only the *unselected* global diagram may have further vertices outside `D`, and those
are not part of the chosen object.

`D` = closed unit disk; `r <= 19/50`; the reduced 9-ring + 2-hub configuration:

* ring sites `c_0..c_8`, **inward-root**: `|c_i|^2 <= 1 - r^2` (hence `|c_i| <= sqrt(1-r^2)`);
* hubs `a, b` (written `c_9, c_10`), **strictly inner**: `|a|,|b| <= 1 - r`;
* **switches** `U_0..U_8 in bd D`, each with `|U_i - c_i| = |U_i - c_{i+1}| =: sigma_i > 0`
  (the nearest-cell boundary switch between the two ring sites), and each ring site owning the
  boundary interval `(U_(i-1), U_i)` of width `w_i in (0, pi)` (`w_i <= 2 asin r`);
* **the clipped refined dual disk**: the *interior* face list = **the 11 refined triangles of the
  chosen clipped dual disk, whatever they are** — not only the canonical hub-fan family: for the
  q1 leagues this includes the **ear** triangle(s), and in general any list of refined triangular
  faces whose edge lengths and opposite angles are read locally. Each face is an ordered triple of
  sites; the *boundary* structure is the 9 switch triangles, the 9 sectors and the 9 circular
  segments. The faces are **not** assumed to be the Delaunay faces of a globally triangulated site
  set; each is used only locally, through its own edge lengths and opposite angles;
* "co-circular refinement": cocircular (artificial) primal edges are listed in the graph; their
  **area** content is zero (§6 (D2)), while they remain genuine *shared-side* constraints of
  positive primal length (a point the lead corrected — see §8 item 3).

**Hypothesis ledger (what the derivation needs; new items flagged ★).**

| # | hypothesis | where it is used | status |
|---|---|---|---|
| H1 | sites pairwise distinct | Voronoi cells have nonempty interiors; `c_i in int V_i` | geometric |
| H2 | ring sites inward-root, hubs strict inner | ★ every site lies in the **closed** inner half-plane of **every** chord: for a chord subtending `w`, its distance from the origin is `cos(w/2) >= sqrt(1-r^2)`, and `|c| <= sqrt(1-r^2)` for every site (`1-r <= sqrt(1-r^2)`); with `<=` this places each site weakly on the inner side of its own chord. **Equality is allowed and is a legal degeneration** (it is the `alpha = pi` cap case, where the sector-triangle term `(1/2)sigma_L sigma_R sin alpha` vanishes and the segment term remains — the cap formula still holds, §4) | ★ supplied by the reduction, non-strict |
| H3 | the inside-`D` part of each bisector where the two sites are the nearest exits `bd D` at the switch `U_i`; the **other end is a primal vertex of the selected clipped dual disk, hence in `int D`** | ★ identifies the boundary Voronoi edge with `[z_i, U_i]`, `z_i in int D` | by the definition of "nearest-cell boundary switch" + the selection of the clipped dual disk (there are no "two-switch" edges: the 9 switches come from the 9 distinct adjacent ring pairs) |
| H4 | for the boundary-adjacent (ring-ring) primal edges, the incident face's circumcenter `z` satisfies `t < ell` along the outward bisector (equivalently `ell + rho cos theta >= 0`, §6 (D3)) | ★ the crux identity of §6 | **proved in `lead/BOUNDARY-SWITCH-ANGLE-PROOF.md` §1** (exterior-side argument, no acuteness assumed) |
| H5 | face list + artificial primal edges as above; each interior primal edge of the refined disk has either two incident faces (use (D2)) or one and a switch (use (D3)) | the face-area dictionary | geometric (refinement); **local, not a global triangulation claim** |
| H6 | nondegenerate face (`area > 0`) for `cot`; `sigma_i > 0`; `w_i in (0,pi)` | division by `sin`, `cot` | geometric |

H2, non-strict, in one place: it places each site weakly on the inner side of its own arc chord,
which is what the cap decomposition of §4 needs. It follows from inward-rootness, so it is not an
extra geometric premise — and it is **no longer a missing statement**: the lead has since added it
to `BOUNDARY-SWITCH-ANGLE-PROOF.md` §4, so the earlier remark that "it is stated in neither source
document" is withdrawn. It must be quoted **non-strict** (`<=`): the equality case `alpha = pi` is
a legal degeneration and is covered by the same cap formula (§4).

---

## 2. Step A — the clipped Voronoi partition (not a triangulation)

For distinct sites let `V_i = {x : |x - c_i| <= |x - c_j| for all j}`. Then

```
  D = disjoint union over i of (V_i cap D)   up to measure-zero boundaries,
  hence  pi = sum_i area(V_i cap D).                                              (A)
```

This is a partition by *nearest-site cells*; no straight-line triangulation of the sites is
assumed, and none is needed. Note also that no site occupies a boundary arc unless it is a ring
site: for `x in bd D` and any ring site with `|x - c_i| <= r` we have
`|x - a| >= 1 - |a| >= r >= |x - c_i|`, so a hub is never the *unique* nearest site on `bd D`
(ties are measure-zero). Hence hub cells contribute no arc piece.

## 3. Directed-area lemma (the tool)

**Lemma.** Let `R` be a convex region, `p in int R`, whose boundary consists of straight pieces
`e_1..e_k` plus **one** circular arc `A` of `bd D` with chord endpoints `P,Q` and width `w`.
Assume `p` lies in the **closed** inner half-plane of the chord. Then

```
  area(R) = sum_j (1/2) dist(p, e_j) |e_j|  +  (1/2) |pP| |pQ| sin angle(PpQ)  +  (w - sin w)/2.
                                                                                  (L3)
```

*Proof.* `R` is star-shaped with respect to `p` (convex, `p` interior), so the fan from `p` over
the boundary is a partition of `R`: the straight pieces give the triangles with base `e_j` and
apex `p`, i.e. `(1/2) dist(p,e_j)|e_j|`. The fan over the arc is the set of rays from `p` to arc
points; the **closed** half-plane hypothesis makes each ray meet the chord in the closed segment
`[P,Q]`, so the fan over the arc is exactly the triangle `(p,P,Q)` **plus** the circular segment
over the chord, of area `(1/2)|pP||pQ| sin angle(PpQ)` and `(w - sin w)/2` (unit circle;
`w in (0,pi)`). In the boundary case `p in [P,Q]` (equivalently `angle(PpQ) = pi`) the "triangle"
flattens to the segment `[P,Q]` with zero area and the same formula holds verbatim: the fan is the
segment plus the full circular segment. ∎

Remarks that matter for the two named traps: **no circumcenter and no auxiliary vertex appears**
in (L3) — the apex is the *site* `c_i`, which is strictly interior to its own cell. The arc is
"seen" from `c_i` under an angle in `(0,pi]`; this is the ray-order fact proved in
`BOUNDARY-SWITCH-ANGLE-PROOF.md` §3 (the site-to-owned-arc polar angle increases strictly), and
H2 is what makes the chord crossing legal (weakly, with the `alpha_i = pi` flattening above). A
**hub** cell has no arc piece (hubs own no boundary point); a **ring** cell always has its arc —
including the degenerate-looking case `alpha_i = pi`, where the arc is still a genuine arc of width
`w_i in (0,pi)` and the cap formula holds with its sector-triangle term equal to zero and the
segment term unchanged.

## 4. Step B — per-cell fan decomposition

Apply (L3) to `R = V_i cap D` for a ring site: its boundary is the owned arc
`U_(i-1) -> U_i` plus a chain of straight pieces, each of which lies on a bisector between `c_i`
and a neighbour site. Hence

```
  area(V_i cap D) = sum_{straight pieces e of V_i cap D} (1/2) dist(c_i,e)|e|
                  + (1/2) sigma_(i-1) sigma_i sin(alpha_i) + (w_i - sin w_i)/2,
  alpha_i := angle(U_(i-1) c_i U_i).                                              (B)
```

Hub cells: same formula with no cap term.

## 5. Step C — pairing across shared Voronoi edges

Every straight piece of a cell boundary is contained in a **Voronoi edge** of the site set
(a maximal segment of a bisector which lies inside `D`). Such an edge is shared by exactly the
two cells of its two own sites `c_i, c_j`, and every point of it is equidistant from them, so the
two one-sided contributions of (B) add up to

```
  (1/2) dist(c_i,e)|e| + (1/2) dist(c_j,e)|e| = (|c_i - c_j|/2) |e|.               (C1)
```

Because `D` is convex, each Voronoi edge inside `D` separates exactly two cells — *including*
the edges that end on `bd D` at a switch (H3). Summing (A) with (B) and (C1):

```
  pi = sum_{Voronoi edges e in D} (|c_i - c_j|/2) |e|  +  sum_i caps_i,            (C2)
  caps_i := (1/2) sigma_(i-1) sigma_i sin(alpha_i) + (w_i - sin w_i)/2.
```

(C2) is the *clipped-Voronoi* form of the area accounting. It contains no convexity assumption
on the ring chain and no straight-site triangulation.

## 6. Step D — Voronoi–Delaunay dictionary, obtuse circumcenters, artificial edges

**No global hull is assumed.** Let `e` be an *interior* primal edge of the clipped refined dual
disk, of length `d`, between sites `c_i, c_j`; by H5 it has either **two** incident faces (angles
`theta`, `theta'` opposite `e`, in the two faces) or **one** incident face plus a switch (angle
`theta`, and the switch `U` on the bisector). Both cases are handled **locally**: only `d`, the
opposite angles, the circumcenter(s) and the switch enter. **Every primal vertex of the *selected*
clipped dual disk lies in `int D`** (H3): so the boundary-adjacent edge is the genuine segment
`[z, U]` with `z in int D` and needs **no truncation** by `bd D`; what is *not* restricted is the
unselected global diagram (further Voronoi vertices outside `D`, and other cells, are simply not
part of the chosen dual disk).

**(D1) Circumcenter projects to the midpoint.** The circumcenter of a triangle is equidistant
from the two endpoints of each side, hence lies on that side's perpendicular bisector: its
projection onto the side's line *is* the side's midpoint. (This is the only place the
circumcenter is used; it is never treated as a vertex of a tiling.)

**(D2) Interior edges with two incident faces.** By (D1) both circumcenters lie on the same
perpendicular bisector, at signed offsets `+(d/2)cot theta` and `-(d/2)cot theta'` from the
midpoint (signs relative to the two faces' half-planes; `d/2 = rho sin theta`). Hence the Voronoi
edge length is the **signed sum**

```
  |OO'| = (d/2)(cot theta + cot theta') = (d/2) * sin(theta + theta') / (sin theta sin theta'),
```

which is `>= 0` **because of the Delaunay condition `theta + theta' <= pi`** (`sin(theta+theta') >= 0`),
**not** because the two circumcenters lie on different sides of the edge: when `theta > pi/2` the
first circumcenter is on the *same* side as the second face, and the individual offsets' side
pattern is irrelevant — only the signed sum is used. (Correction recorded: an earlier version of
this audit wrote "they are not both strictly on the same side"; that inference is wrong.) The
paired contribution (C1) is therefore

```
  d^2/4 (cot theta + cot theta') = (d^2/4)cot theta + (d^2/4)cot theta'.          (D2)
```

*Obtuse handling:* `cot theta < 0` exactly when `theta > pi/2` (circumcenter beyond the edge's
line); the formula is *signed* and stays correct; no acuteness is assumed anywhere.
*Artificial (cocircular) edges:* `theta + theta' = pi` gives `cot theta + cot theta' = 0`, so the
paired **area** contribution is exactly zero — the two circumcenters coincide and the dual
Voronoi edge has zero length. Note (lead correction, see §8 item 3) that this says nothing about
the `rho^2 sin^2(theta)` atom of the shared-side factor: that atom is built from the **opposite
angle** in the face, not from the wedge, so it does **not** vanish, and a cocircular primal edge
is a genuine *shared-side* constraint of positive length. It is only its **area content** that
vanishes here.

**(D3) Boundary-adjacent (ring-ring) edges (crux step).** For a ring-ring edge, the Voronoi edge
is the genuine segment `[z, U_i]` — **no truncation**: `z` is the circumcenter of the single
incident face and, being a primal vertex of the selected clipped dual disk, lies in `int D` (H3),
while `U_i` is the switch on `bd D`. Both `z` and `U_i` lie on the bisector (D1 and the switch
definition), so with `m` the edge midpoint, `ell := |mU_i|` and (signed) distance
`z`-to-side-line `= rho cos theta`, one has

```
  |zU_i| = |ell + rho cos theta|   and   d/2 = rho sin theta,  a := d/2,
  a*|zU_i| = a (ell + rho cos theta) = a*ell + a^2 cot theta = sigma_i^2 sin(2b_i)/2 + d^2/4 cot theta,
                                                                            (D3)
```

because `sigma_i^2 sin(2b_i)/2 = a*ell` (the switch triangle `(c_i, c_(i+1), U_i)` has base `d`
and height `ell`) and `a^2 cot theta = a * rho cos theta`. **The step uses the *sign* condition
`ell + rho cos theta >= 0`, i.e. `U_i` lies at least as far along the outward bisector as the
circumcenter's projection — this is exactly the `t < ell` exterior-offset statement proved in
`lead/BOUNDARY-SWITCH-ANGLE-PROOF.md` §1** (which itself uses nearest-site validity at the
switch and therefore needs no acuteness). So (D3) is an identity *under H4*, and it says:
*the boundary Voronoi piece splits into the face's allocated piece plus the whole switch triangle.*

**(D4) Reassembly (the cotangent identity).** For any nondegenerate triangle with sides
`d_a, d_b, d_c`, opposite angles `A, B, C` and circumradius `rho`:

```
  (1/4)[d_a^2 cot A + d_b^2 cot B + d_c^2 cot C] = (rho^2/2)[sin2A + sin2B + sin2C]
                                                 = 2 rho^2 sinA sinB sinC = area,     (D4)
```

because `d = 2 rho sin(angle)` gives `(1/4)d^2 cot = (rho^2/2) sin2(angle)` (**corrected: the
earlier version of this audit wrote `rho^2 sin2(angle)`, off by a factor 2**), and
`sin2A + sin2B + sin2C = 4 sinA sinB sinC`. Each term `(1/4)d^2 cot A = area(z; two vertices)`
is the signed area of the triangle spanned by the circumcenter and that side; the sum is the
ordinary area. This handles obtuse triangles (negative terms) and pins the face-area formula:
**`2 rho^2 sinA sinB sinC` is an identity for every triangle, acute or obtuse.**

Assembling (C2) with (D2), (D3), (D4): the interior-edge pairings plus the boundary-edge pairings
allocate to every face exactly its three pieces, which sum to its area; the boundary (ring-ring)
pairings additionally produce exactly the switch triangle of the corresponding switch; and the
remaining unpaired terms are precisely the caps. Therefore

```
  pi = sum_faces 2 rho_f^2 sinA sinB sinC + sum_switches sigma_i^2 sin(2b_i)/2 + sum_rings caps_i,
```

which is (L). ∎

## 7. Non-bearing numeric consistency (explicitly NOT the proof)

Internal localisation (`r20_area_localize.py`, the same configuration as the oracle export
`r20-alternative/socp_anchor_export.json`): `sum faces = 1.853209564160097`,
`sum switches = 0.621086860024960`, `sum sectors = 0.409282513054057`,
`sum segments = 0.258013716350679`, total `= 3.141592653589793 = pi` with difference `0.0e+00`
in float64; per-face `2 rho^2 prod sin` vs `area` agrees to `<= 1.1e-16` for all 11 faces; and the
crux identity (D3) was checked edgewise: `a|zU_i| = (d^2/4)cot theta + sigma_i^2 sin(2b_i)/2`
holds for all 9 ring edges with residual `<= 5.6e-17`. This is a *consistency check of the
bookkeeping*, not evidence for (L) — the proof is §2–§6.

## 8. Verdict on the question asked

1. **The identity is a genuine consequence of the clipped Voronoi partition plus the
   co-circular refinement** — it does not require (and does not use) the claim that the
   topological embedding is a straight-site triangulation. The straight-site structure enters
   only through the Voronoi–Delaunay *dictionary* (D2)–(D4), i.e. through edge lengths and
   opposite angles, never through placing circumcenters or auxiliary vertices as tiling vertices.
2. **Obtuse circumcenters:** harmless. The face area is `2 rho^2 sinA sinB sinC` for every
   triangle (D4), and the only place a circumcenter's location enters (D3) is controlled by the
   *sign* hypothesis H4 (`t < ell`), which `BOUNDARY-SWITCH-ANGLE-PROOF.md` §1 proves without
   acuteness.
3. **Artificial (cocircular) primal edges:** contribute exactly zero **to the area identity** —
   interior ones by `cot theta + cot theta' = 0` (D2; the two circumcenters coincide, so the dual
   Voronoi edge has zero length). *Correction (lead audit):* this must **not** be read as saying
   that the `SHARED-FACTOR-DUAL.md` atom `rho^2 sin^2(theta)` vanishes — that atom uses the
   **opposite angle of the face**, not the wedge `pi - A - B`, so it stays positive; a cocircular
   edge is a genuine **shared-side constraint of positive primal length**, and only its *area*
   content is zero. The earlier sentence claiming the atom vanishes is deleted.
4. **No global geometric assumption is used.** The derivation needs neither convex position of
   the ring sites nor a global Delaunay triangulation: only the *clipped* cells, the *interior*
   face list, and the local signed-offset identities (D2)/(D3) at each primal edge. What is used
   is that every primal vertex of the *selected* clipped dual disk lies in `int D` (H3) — so the
   boundary-adjacent edge is the untruncated segment `[z, U]`; *unselected* global diagram objects
   (other cells, further vertices outside `D`) are simply not part of the chosen dual disk and are
   not restricted. The two cases of H5 (two incident faces / one face plus a switch) cover the
   whole clipped dual disk; in particular the obligation covers the **q1 and q0 exclusions**,
   not only the canonical (6,7) configuration.
5. **Residual points of presentation (the main proof of the sources is correct; this audit is an
   audit of it, not an independent theorem):** (i) H2 — sites in the *closed* inner half-plane of
   every chord, **non-strict**, with the equality case `alpha = pi` legal and the cap formula
   intact — has since been **added to `BOUNDARY-SWITCH-ANGLE-PROOF.md` §4** by the lead, so it is
   no longer a missing statement (the earlier "not written in either source document" remark is
   withdrawn); (ii) H3 (the inside-`D` bisector exits at the switch, other end `in int D`) holds by
   the definition of the switch plus the selection of the clipped dual disk; (iii) H4 (`t < ell`)
   is the load-bearing sign condition for the boundary-adjacent edges — proved in §1 of
   `BOUNDARY-SWITCH-ANGLE-PROOF.md`; whether §4 restates it is a presentation matter only;
   (iv) the identity is a statement about *genuine configurations*; the certificate's relaxed
   domains (zero radii, zero angles) merely enlarge the range and must not be read as extending
   (L) to arbitrary factor tuples.
