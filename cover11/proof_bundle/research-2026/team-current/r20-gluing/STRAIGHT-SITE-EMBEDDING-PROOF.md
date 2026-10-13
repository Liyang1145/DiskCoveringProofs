# STRAIGHT-SITE-EMBEDDING-PROOF — (E-ext) is a topological consequence of the refined dual

**Lane**: r20-gluing (cline2-r23-gluing). **No claim registered.** This note writes out the proof route
given by the lead and independently audits its hinges; it replaces the "candidate control" reading of
`GRAPH-INTERFACE-CHECK.md` §2′ (the control there is now illustrative only).

Inputs used (all already proved elsewhere):
* **I1** — the refined nearest-site dual `K` is a **simplicial closed disk** with 11 vertices (9 ring +
  2 hub), boundary = the 9-cycle of ring vertices, hub vertices interior: `GLOBAL-TOPOLOGICAL-REDUCTION.md`
  §1(1.1)–(1.2) plus the refinement of §1(1.3).
* **I2** — a face of `K` corresponds to an **interior primal (Voronoi) vertex** `x ∈ D`; its vertices
  are exactly the sites at minimum distance from `x`, so they are **cocircular** on `∂B(x, r_x)` with
  `r_x = min_i |x − c_i| ≤ r`, and no site is strictly closer (empty circle): VORONOI §1/§3, GLOBAL §1.
* **I3** — non-degeneracy: at `x` the sites are distinct points of a circle of finite positive radius,
  so no three are collinear (`COMPATIBLE-EDGE-SUPPORT.md` §3 ¶34).
* **I4** — the straight-site realization: map each vertex of `K` to its site, each simplex affinely.

## The proof

**(1) Face ↔ empty-circle polygon, uniformly triangulated.** For every face `F` of `K`, let `x_F` be
its primal vertex and `S_F` its site set (I2). The straight image of `F` is the polygon through `S_F`
in the cyclic order induced by the cells around `x_F`; by I3 it is non-degenerate, and it is
triangulated by the diagonals chosen in the refinement step of `GLOBAL…` §1(1.3) — those diagonals are
chords of the same circle, i.e. **zero-length primal edges = cocircularity, not collinearity**. Fix,
once and for all, a triangulation of every cocircular class of the eleven sites (any consistent rule);
choose the refinement of §1(1.3) to be *that* triangulation face by face. This is legitimate because
§1(1.3) allows *any* triangulation of each face's own vertices, and the quantities that must not be
read off the refinement (`q`, `K`, degrees, strict edge estimates) are flagged there as
refinement-dependent / not to be fed into strict estimates. **Consequence:** every triangle of `K` is
a face of one fixed planar straight-line Delaunay triangulation `𝒟` of the eleven sites, and every
edge of `K` is an edge of `𝒟`.

**(2) Disjointness and exact intersections.** In `𝒟` (a planar straight-line triangulation, classical
for the empty-circle rule), distinct faces have disjoint interiors and two faces meet exactly in their
common sub-simplex (empty or a shared vertex/edge). Because every simplex of `K` is a sub-simplex of a
face of `𝒟` (step 1) and `𝒟` is planar, for any two simplices `σ, τ` of `K`:
`f(σ) ∩ f(τ) = f(σ ∩ τ)` — in particular images of disjoint simplices meet at most in common
vertices, and no image edge passes through a site (a site in the *open* Delaunay edge `uw` would be
strictly closer to the empty-circle centre than `u, w`, contradicting emptiness; also inherited from
`𝒟`'s planarity).

**(3) `f` is injective.** Let `x, y ∈ |K|` with `f(x) = f(y)`. Write `x = Σ λ_i v_i`,
`y = Σ μ_j w_j` with barycentric supports `σ = supp x`, `τ = supp y`. If `σ = τ`, affine
non-degeneracy of `f|σ` (I3) gives `x = y`. If `σ ≠ τ`, then `f(σ) ∩ f(τ) = f(σ ∩ τ)` (step 2);
`f(x) ∈ f(σ)`, `f(y) ∈ f(τ)` and `f(x) = f(y)` force the common point to lie in `f(σ ∩ τ)`; for a
point of the relative interior of `σ`, lying in `f(σ ∩ τ)` is impossible unless `σ ⊆ τ`
(step 2 again, applied to the faces of `𝒟` containing `σ` and `τ`) — so supports coincide. Hence `f`
is injective.

**(4) `f` is an embedding.** `|K|` is compact (finite complex), `R²` is Hausdorff, and `f` is
continuous and injective ⇒ `f` is a homeomorphism from `|K|` onto its image. (No metric input: `f` is
affine on each simplex, so continuity is immediate.)

**(5) Jordan ⇒ the image is exactly the Jordan region of the boundary 9-cycle.** `|K| ≅` closed disk
(I1), so `∂|K| ≅ S¹`; its image is the polygonal curve through the nine ring sites **in arc order**
(boundary edges of `K` are the nine switch-pair adjacencies, I1). By (4) this image is a **simple**
closed curve, and by Jordan–Schoenflies `f(|K|)` is exactly the closed region it bounds.

**(6) Consequences — all automatic.** `f(int |K|) = int f(|K|)`: hence
* the two hubs map **strictly inside** the arc-order polygon `P`;
* there are **no holes and no missing faces**, and the faces of `K` **tile** `P` exactly;
* no extra "exterior" Delaunay triangle is mixed into `K`'s face list: a Delaunay face of `𝒟` outside
  that Jordan region simply is not a face of `K`, and by step 2 it cannot overlap or intrude;
* `P` is simple (a conclusion, not an assumption).
**Not needed:** radial-wedge / angular order; `P = conv(sites)`; convexity of `P`; "the retained
complex is the full triangulation"; "all Delaunay circumcentres lie in `D`".

## Independent audit of the hinges (what the lead asked to check)

1. **Can two distinct primal vertices have the same site triple?** No. A primal vertex with site set
   `S` is the centre of an empty circle through `S`; for three non-collinear sites (I3) the
   circumcentre is **unique**, so the same triple yields the same point and the same face. For a
   cocircular class of size `k ≥ 4` the same holds for the whole *polygon* (one point `x`, one face).
   ⇒ the correspondence face ↦ primal vertex is injective and the "uniform triangulation" of step 1
   is well defined (different faces of `K` cannot share the same primal point).
2. **All-or-nothing inclusion for a cocircular polygon** (no "partial true vertex"): inclusion in the
   clipped dual is decided by the single point `x`: if `x ∈ D` all cells containing `x` are the
   polygon's sites and the whole face is present; if `x ∉ D` none of it is. Moreover a ≥3-fold Voronoi
   vertex **cannot lie on `∂D`**: a boundary point is nearest to at most two ring sites (arcs own
   points one-by-one; switches are ties of exactly the adjacent pair), and VORONOI §3 / R2 prove at a
   switch only the two adjacent ring sites are at distance `≤ r` with the others strictly `> r`. Hence
   no face of `K` has its circumcentre on `∂D` — the "boundary" alternative never arises.
3. **The classical input** is only the planarity of the straight-line Delaunay triangulation
   (non-crossing faces with exact common-subsimplex intersections) for a finite planar site set with
   the empty-circle rule, including the cocircular case handled by fix-any-triangulation — and the
   refinement freedom already stated in `GLOBAL…` §1(1.3).
4. **Small print.** (i) The chosen triangulations must be fixed *before* applying the argument, and
   the refinement-dependent quantities must not be re-read (as §1(1.3) warns). (ii) The proof is
   insensitive to whether a Delaunay triangle's circumcentre lies inside or outside `D`; those
   triangles are simply present or absent in `K`. (iii) Nothing here uses the ring-hub metric bounds
   beyond I1–I3, so the statement is purely topological.

## Where this leaves the interface list

(E-ext) is **discharged** as a topological consequence of the already-proved refined dual (I1) plus the
empty-circle structure of its faces (I2–I3) and the classical Delaunay planarity. The residual list of
`GRAPH-INTERFACE-CHECK.md` §4 therefore drops item 1 and keeps: hub-edge bridge (P3, conditional on
C450); the inward-representative bound (C451/C464); realizability of `q ≥ 1` (not needed);
global (E) for the central-face interface (only box-certified).

**Repro / evidence**: this note is analytic; the previously recorded control
(`straight_site_control.py`) is retained only as an illustration.
