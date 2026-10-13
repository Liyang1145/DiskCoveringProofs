# LOCAL-PRIMAL-TO-COVER-TRANSFER — necessary interfaces for transferring C902's strict local to the 8-angle domain

**Lane**: r20-gluing (cline2-r23-gluing). Read-only audit; **no claim registered**.

**Retraction (lead, accepted).** In `GLOBAL-8ANGLE-LOWERBOUND-LOGIC.md` I closed with "derive a local
theorem `V ≤ R* − c‖δθ‖²` from the dual bound". That is **backwards**: the dual only gives *lower*
bounds `V ≥ bound`, and `bound < R*` says the dual is weak, never that `V` is small. The sentence is
withdrawn; §4′'s finite-family conclusion holds only on a sufficiently small punctured neighbourhood
(non-attaining fields only by local continuity), and a genuine varying/continuum dual or local theorem
is needed for sharpness. This note lists what a local theorem would have to prove.

## 0. Target statement

`(T)` There is a punctured neighbourhood `𝒩 ⊂ P` of `U*` with `V(W) ≥ R*` for all `W ∈ 𝒩`
(sharpness at `U*`), which together with a separate argument on `P \ 𝒩` would give `min_P V ≥ R*`.
Equivalently (contrapositive): every feasible oracle point at anchors near `U*` with value `< R*` is
impossible. Since the oracle's feasible set also contains non-cover configurations, `(T)` needs a
**local primal ⇒ cover** transfer.

## 1. Two lemmas that make the transfer work (new; short proofs)

**L1 (no-hole criterion).** Let `c_1..c_11 ⊂ D`, radius `t > 0`, `φ(x) = min_i |x − c_i|`. If
(i) `∂D` is covered (`φ ≤ t` on `∂D`) and (ii) every **interior Voronoi vertex** of the site set has
`φ ≤ t`, then `D` is covered.
*Proof.* If not, `{φ > t} ≠ ∅` is open, relatively closed in the compact `D`, and misses `∂D` by (i),
so `φ` attains a maximum `> t` at an interior point `x*`. On the relative interior of a Voronoi cell
`φ = |x − c_i|` has no interior local maximum (outward gradient, and `c_i ∈ D`); along a Voronoi edge
`φ` is a convex function of the arc parameter restricted to the straight bisector segment, so its
maxima there are at the edge's endpoints. Hence a local maximum of `φ` in `int D` is an interior
Voronoi vertex, contradicting (ii). ∎

**L2 (endpoint ⇒ whole owned arc).** Let `c` satisfy `|c − U| ≤ t` and `|c − V| ≤ t` at the two switch
endpoints of an owned arc of angular width `Δ < π`. Then the whole arc lies in `B(c,t)`.
*Proof.* `B(c,t) ∩ ∂D` is either empty or a single arc of width `≤ 2asin(t) < π`; it contains `U` and
`V`, and an arc of width `< π` containing two points contains the (unique) *shorter* arc between them;
the owned arc has width `Δ < π`, so it **is** that shorter arc. ∎
(No inward/near-side hypothesis is needed beyond `Δ < π`; the endpoint inequalities are exactly the
oracle's 18 constraints, so with L2 the boundary coverage follows from the oracle constraints alone.)

**L3 (MEC = circumradius for acute faces).** For a strictly acute triangle the MEC centre is the
circumcentre, so `MEC ≤ t ⇔ Rc ≤ t`; and at the circumcentre the nearest-site distance equals `Rc`
provided the triangle is a Delaunay face (empty circle). Hence the oracle's 33 face constraints hold
with equality `z_f =` circumcentre on acute faces, and their content is `Rc_f ≤ t`.

## 2. Necessary interfaces (list with status)

**No new metrics are needed for I1/I3/I4/I5/I6/I7**: `lead/check_tc_root_geometry.py` already certifies
them interval-wise at the exact root (C892): strict switch criticality
(`sqdist(B[k],c[j]) − r² > 0.01` for all non-adjacent `j`, l.26), fixed combinatorial object with `21`
edges and hull edges (l.35), angles `a ∈ (0.28, 0.40)`, `ρ ∈ (0,1)` (l.36–37), **empty-circle
strictness** `sqdist(cc,c[k]) − rad_sq > 0.15` for every non-face site (l.53) with circumcentre in `D`
(l.54), slack faces `rad_sq − r² < −0.0008` (l.55), face nondegeneracy `> 0.14` (l.56), hub strictness
`(1−r)² − |c|² > 0.3` (l.58/62), angle margin `r² − sin²a > 0.001` (l.59/63) and **strict convex
position** `cross(c_k, c_{k+1}, c_j) > 0.05` for all other `j` (l.61/64). Acuteness of the 11 faces and
the tie slopes are interval-audited in the C897 lift (`lead/FIXED-SWITCH-SOC-REDUCTION.md` §5).

| # | interface | needed for | status |
|---|---|---|---|
| I1 | candidate's 11 faces **strictly acute** with margins | L3 + stability under perturbation | verified numerically (barycentric coords all `>0.22`); needs interval version (stress lane) |
| I2 | fixed incidence/triangulation stable under small site perturbations | faces ↔ circumcentres identification | combinatorial; stable since Voronoi vertices are transversal (VORONOI §3/R2) |
| I3 | switch ownership stable (bisector secant, distance `< 1`) | the nine owned arcs persist; arcs tile `∂D` | proved in `lead/VORONOI-BOUNDARY-REDUCTION.md` §1/§3 + `REVIEW-…` R2 |
| I4 | each owned arc has width `Δ_i < π` | L2 | candidate chords `0.554–0.757`, so `Δ_i ≈ 0.55–0.76 < π` with margin (needs the interval version) |
| I5 | hubs strictly interior (`|h| + r < 1`), hub disks own no boundary point | boundary coverage only from ring arcs | verified (strict-hub margins in the screened box) |
| I6 | sites distinct / no coincidences with margins | L1's cell structure nondegenerate | verified numerically; interval version needed |
| I7 | empty-circle strictness for the 11 faces (other sites strictly outside the circumcircles) with margin | L3's Delaunay-face hypothesis | numerically true (11 faces, all with circumcentre in `D`); a strict margin must be extracted |
| I8 | **C902** (physical strict local minimality of the covering radius at the exact candidate, up to its symmetry) | the contradiction `radius < R*` | external (stress lane); not assumed here |
| I9 | **no distant optimizer at `U*`** (uniqueness: no feasible oracle point far from the candidate attains `≤ V(U*)`) | `V(U*)`'s identification; keeping the local argument from being bypassed | **provided**: `r20-geometry/FIXED-U-PRIMAL-UNIQUENESS-LEMMA.md` (conditional on (H1′) + its symbolic combinatorial premise) + compactness corollary; see §5 |
| I10 | `P \ 𝒩` (far anchors) handled by boxes or another global argument | `min_P V ≥ R*` | open; §4 of `GLOBAL-8ANGLE-LOWERBOUND-LOGIC.md` |

## 3. The transfer, spelled out (conditional on I1–I9)

Let `W ∈ 𝒩` and let `(C, Z, t)` be oracle-feasible at `W` with `t < R*`, and suppose `(C,Z)` is close to
the candidate's data (I9 removes the alternative).
1. Endpoint constraints + I3/I4 + **L2** ⇒ `∂D` is covered by the nine ring disks of radius `t`.
2. I1 + **L3** ⇒ each face's constraint is `Rc_f ≤ t` and its circumcentre — the face's interior
   Voronoi vertex (I2) — has nearest-site distance `Rc_f ≤ t`; I5/I6 make the cellulation
   nondegenerate.
3. **L1** ⇒ `D` is covered by the eleven disks of radius `t`: `C` **is a genuine cover with radius
   `≤ t < R*`**.
4. `C` is close to the candidate (I9), and its positional symmetry orbit is the candidate's, so **I8**
   (C902) gives the covering radius `≥ R*` — contradiction.
Hence `(T)` holds on `𝒩`. Consequences: near-`U*` sharpness does not need a varying dual at all — it
follows from the primal geometry provided I8/I9 are in place; the varying-dual/per-box fields remain
the tool for `P \ 𝒩` (I10) and for the `U*`-attainment question.

## 4. Caveats

* Nothing here uses an upper bound for `R*`; the only threshold is C891's exact-root radius.
* `(T)` is **local**: it cannot replace I10. The two together are what `min_P V ≥ R*` would need.
* I9 is genuinely open and cannot be replaced by convexity (the oracle is not convex in the angular
  variables).
* L2 removes the need for an "inward" hypothesis, but *does* need `Δ_i < π` with margin (I4), and L1
  needs `∂D`-coverage plus all-vertex coverage — i.e. exactly the oracle's two constraint families.

## 5. Existential form of the local transfer (primary task; no explicit ρ, no new metrics)

**Registered versions supersede this sketch**: `lead/FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md`
(**C909** exact sharpness + fixed-`U*` site uniqueness, **C910** local transfer). Its §2 gives the
*exact* vector-force certificate (C897's `μ_i>0`, `ν_f>0` with sum exactly 1; all 45 carrying edges of
length `R*`; zero tangential and strictly positive radial load at every anchor), its §3 pins **all 11
site coordinates** at `t ≤ R*` (the two slack auxiliaries stay non-unique, immaterial), and its §4
strengthens my step 2: *for every site neighbourhood `O` of `C*` there is an anchor neighbourhood `N`
of `U*` such that **every** oracle-feasible solution at `U ∈ N` with `t ≤ R*` has sites in `O`* (no
solver-continuity assumption). Its §5 proves the cover transfer (short-arc ⇒ boundary coverage, acute
⇒ MEC = circumradius, critical-point/no-hole ⇒ full disk), i.e. the same content as my L1/L2/L3, which
were derived independently here. **This closes the geometry lane's "reading vs theorem" caveat**: the
dual-positivity input is now the certified C909 certificate, so the local statement below is
*conditional on C909 + C902* rather than on floating readings.

**Inputs now in place.** (a) the strict margins at the exact root, interval-certified in
`lead/check_tc_root_geometry.py` (see §2 above); (b) the 11 faces strictly acute and the tie slopes,
interval-audited in the C897 lift; (c) **I8 = C902** (physical strict local minimality of the covering
radius at the exact candidate, up to its symmetry); (d) **I9 = the geometry lane's**
`r20-geometry/FIXED-U-PRIMAL-UNIQUENESS-LEMMA.md`: conditional on (H1′) (active dual force set
`E⁺ = {e : p_e ≠ 0}`, the 6 slacked fixed-switch edges carrying zero force) plus its *symbolic*
combinatorial premise (every free node lies in an anchor-containing component of `E⁺` — proved there
without dual data), the fixed-`U*` primal minimiser has sites exactly `C*`; its §4 compactness
corollary uses the **full 51-edge** graph to get uniform boundedness, hence compactness of the
`t*`-level feasible set and convergence of subsequential limits to optimizers at `U*`. (Their `t` is
the **squared** variable; the lead's `V` is the radius, `t = V²`.)

> **Theorem (existential local transfer; conditional on (a)–(d)).** There exists a punctured
> neighbourhood `𝒩 ⊂ P` of `U*` such that `V(W) ≥ R*` for every `W ∈ 𝒩`.
>
> *Proof.*
> 1. *(Margins persist.)* The certificate list (a) is a finite set of strict inequalities in the
>    configuration data; hence there is `δ₁ > 0` such that every configuration `C` with
>    `max_i |c_i − c*_i| < δ₁` has the same Delaunay incidence and triangulation, the same nine owned
>    arcs and switches, all owned-arc widths `< π`, all 11 faces strictly acute, hubs strictly interior,
>    sites distinct, and the two slack faces still slack. (Continuity, no computation needed.)
> 2. *(Optimisers stay local.)* By (d) the optimiser set at `U*` has sites exactly `C*` (up to the
>    announced symmetry); the `V`-level feasible sets are compact and the optimiser correspondence is
>    therefore upper semicontinuous in `W`; hence there is a neighbourhood `𝒩` of `U*` such that every
>    optimiser at every `W ∈ 𝒩` has its sites within `δ₁` of `C*`.
> 3. *(Primal ⇒ cover.)* Take `W ∈ 𝒩` and an optimiser `(C, Z, √t)` at `W` (with `C` in the `δ₁`-ball).
>    The endpoint constraints plus the ownership margins and **L2** cover `∂D` by the nine ring disks
>    of radius `√t`. **L3** with strict acuteness turns each face constraint into `Rc_f ≤ √t`; with the
>    stable incidence each face's circumcentre is an interior Voronoi vertex of `C` with
>    `φ = Rc_f ≤ √t`; **L1** (no-hole) then gives that the eleven disks cover `D`. So `C` **is a
>    genuine cover, with covering radius `≤ √t = V(W)`**. (No claim about where the auxiliary `z_f`
>    lie is needed — the aux simply witness the MEC/`Rc` inequality.)
> 4. *(C902 closes it.)* `C` is a cover within `δ₁` of `C*`, so (c) gives its covering radius `≥ R*`,
>    hence `V(W) ≥ R*`. ∎

**Corrections (lead, accepted).**
* The `E⁺`-connectivity statement is about **20 free nodes — the 11 sites plus the 9 active
  auxiliary `z_f` of the C897-active faces** — not "all 22": the **2 slack auxiliaries are isolated**
  (their faces carry zero force), and they are harmless because they are bounded by their own distance
  constraints. My earlier "22 free nodes / `G`" sentence is withdrawn.
* No "`z_f` near the actual circumcentre" claim is needed or made (see step 3).
* The quantitative issue is **not** the numerically tiny coefficients: **C909 proves strict positivity
  of all 45 forces as real positives**; the only missing item is an **explicit neighbourhood**
  (i.e. quantitative `δ₁`/`𝒩`), which is not required for the existential statement.

**Scope.** The statement is **local** (nothing for `P \ 𝒩`) and **existential**; no upper bound for
`R*` is used, and no new metric beyond the existing certificates. Nothing here picks a box "outside
`𝒩`" — with `𝒩` unspecified that would be meaningless; the per-box tool for the far region is the
convex angular-sector relaxation (separate note).
