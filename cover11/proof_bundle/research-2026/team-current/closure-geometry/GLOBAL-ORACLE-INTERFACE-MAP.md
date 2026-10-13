# GLOBAL-ORACLE-INTERFACE-MAP — the minimal chain cover → fixed 51-edge oracle

Assigned structural audit. Question: in the implication
"any better cover ⇒ the selected fixed 51-edge (45-variable) oracle is feasible at
some `Δ ∈ P`", **which global hypothesis is still missing?** Answer assembled
below as the minimal chain, each link with its exact source, plus the four
degeneracy checks asked for. No new claim, no subagent, only this file written.

Cited sources are under `research-2026/team-current/` unless noted:
`lead/FIXED-SWITCH-SOC-REDUCTION.md` (FS), `lead/VORONOI-BOUNDARY-REDUCTION.md` (VBR),
`lead/INWARD-ARC-SWITCH-UNIQUENESS.md` (IASU), `lead/CLIPPED-DUAL-STRAIGHT-EMBEDDING.md` (CDSE),
`lead/DUAL-DISK-INTERFACE-AUDIT.md` (DDIA), `lead/CENTRAL-FIBER-HELLY-REDUCTION.md` (CFHR),
`lead/Q0-CLOSURE-EXCLUSIONS.md` (Q0CE),
`lead/Q1-BALANCED-EXCLUSION.md` (Q1BE), `lead/Q0-DEGREE4-EXCLUSION.md` (Q0D4),
`lead/RADIUS-TRANSFER-MOMENT-DUAL.md` (RTMD, the transfer for C818/C819/k3/k4),
`../solo-20260922/N11-LOW-RADIUS-REDUCTION.md` (C450/C451),
`../solo-20260922/M10-038-EXCLUSION.md` (the `m = 10` exclusion theorem),
`../solo-20260922/INNER-ROOT-DOMINANCE.md` (C464),
`../team-max-20260922/n11-structure/ARC-COORD.md` (P1⇔P2 ledger).
`lead/STRICT-EMPTY-FACET-COMPLETENESS.md` (SEFC) is **not used** in this map (it is
candidate-specific).

---

## 0. Answer

**The necessity of the oracle's constraints is not a new lemma: `FS` §2 already
states it.** What this map adds is the accounting — which source supplies each link
(Steps 1–9 below) — and the list of statements that must **not** be asserted on the
way. I withdraw the following over-strong claims from my previous version:

1. **"the composite lemma is new"** — false; `FS` §2 ¶1–2 states the witness
   argument for the 51 constraints. The correct framing is that `FS` §2's sentence is
   a short consequence of arc ownership (`VBR` §1) plus the covering hypothesis;
   §2 below records that consequence for reference, not as a contribution.
2. **"the covering radius equals `r`"** — false in general. The hypothesis "the
   eleven radius-`r` disks cover `D`" yields only `max_{x∈D} dist(x,S) ≤ r`. The
   oracle needs only the **inequality** `V(U) ≤ r`; no equality, no minimality of
   `r`, and no identification with the true maximum is used anywhere.
3. **"the maximum is attained only at the 9 switches and the 11 Voronoi vertices"** —
   not proved as stated and withdrawn. The only boundary fact the witness argument
   uses is that at a switch both incident sites are nearest, and the covering
   hypothesis bounds their distances by r. No convexity along a circular arc
   or boundary maximum-location assertion is used.
4. **"`m ≥ 9` and `m ≤ 10` give `9`"** — false as a deduction; the pair gives
   `m ∈ {9,10}`. Excluding `m = 10` is a **separate theorem**: C450 /
   `../solo-20260922/M10-038-EXCLUSION.md` (ten disks touching and covering `∂D`
   plus an eleventh covering `D` forces `r > 19/50`), proved by a two-circle weighted
   capacity with two independent arithmetic kernels over 36 closed `e`-segments.
   Step 1 now cites that.
5. **"a non-essential boundary arc ⇒ its disk is deletable"** — false in general
   (the disk may be needed for interior coverage). Essentiality is **not** what the
   witness argument consumes; it consumes `VBR` §1's ownership statement (each
   boundary disk owns exactly one positive-length connected nearest-center arc, and
   there are exactly nine distinct switches), derived there from the
   affine-line ∩ circle argument. Step 2 is corrected accordingly.
6. The candidate-specific `SEFC` material is no longer used anywhere in this map.

The genuinely open global object remains `(G) min_{Δ∈P} V(U(Δ)) ≥ R*` (§5).

---

## 1. The minimal chain, step by step with exact sources

**Step 0 (object).** Unit closed disk `D`; eleven centers `S`, congruent closed
disks of radius `r` covering `D`; `r < R*` in the hypothesis. Note: `r` is the
**given cover radius**, not necessarily the minimal covering radius of `S`; only
`max_{x∈D} dist(x,S) ≤ r` is used (see §0 item 2).

**Step 1 (foundational class: 9 boundary + 2 interior).** Two separate inputs:

* **The count bounds.** `m ≥ 9`: each boundary disk meets `∂D` in an arc of half-width
  `≤ asin r` (a radius-`r` disk's intersection with the unit circle has angular
  half-width `≤ asin r`), and these `m` arcs must cover `∂D`, so
  `m·asin(r) ≥ π`; with `r ≤ 19/50` we get `m ≥ 9` from `8 asin(.38) < π`
  (exact square comparison `790321 > 781250`). `m ≤ 10`: no boundary center can cover
  the origin, since a boundary disk has `|c| ≥ 1 − r > r` for `r ≤ 19/50`, while
  the eleven disks cover `D`; so at least one disk is interior, i.e. `m ≤ 10`. These
  two bounds give `m ∈ {9,10}` — **not** `m = 9`.
* **The exclusion of `m = 10`.** *C450 / `../solo-20260922/M10-038-EXCLUSION.md`*:
  if ten disks touch and cover `∂D` while the eleventh covers `D`, then `r > 19/50`.
  That file's proof fixes `r = 19/50`, uses `e = |h| ≤ 3R − 1 = 7/50` from
  `B(0, 1−2R) ⊂ B(h,R)`, and derives a contradiction from a two-circle
  weighted-capacity inequality, certified by two independent arithmetic kernels over
  36 closed `e`-segments (`directional_e_cover.json`, `directional_low_cover.json`,
  `directional_fixed_all.json`; manifest `DUAL-MANIFEST.json`; author self-audit,
  independent review pending). Its scope note is explicit that it does not cover the
  9 + 2 case.
* **Consequence.** With `r ≤ 19/50` and `m ≠ 10`, `m = 9`; the remaining two disks
  are then interior (`|h| + r < 1`, by the connectedness argument in
  `N11-LOW-RADIUS-REDUCTION.md` §"两个非边界盘必须都真正位于内部"), and neither is
  deletable (same file; a deletable disk plus a tangent replacement disk would give
  the excluded ten-boundary configuration).
→ **interface: unconditional given C450 (the `m = 10` theorem).**

**Step 2 (boundary arcs: ownership, positivity, order).** *VBR §1*: each boundary
disk `i` owns **exactly one** connected closed nearest-center boundary arc `I_i` of
**positive length**, and there are **exactly nine distinct switches** `P_i`, one per
neighbouring pair. The derivation there is purely the **affine-line ∩ circle**
argument: in an overlap `I_i ∩ I_{i+1}` only those two disks can win the
nearest-center comparison; the difference of squared distances is the restriction of
a nonconstant affine function to the circle; opposite endpoint signs force an odd
number of transverse intersections; a tangent zero cannot coexist with a transverse
zero; an overlap of zero length contributes its common endpoint as the unique tie.
The arc ledger equivalence is *ARC-COORD.md* Prop. P, `P1 ⇔ P2`, with
`t_i ≤ arcsin r`, `o_i ≥ 0`, `Σo_i = 2Σt_i − 2π`, `ℓ_i = 2t_i − o_{i−1} − o_i > 0`;
the file's audit note records that `t_i ≤ arcsin r` **must** be in the domain, and
that the ledger corresponds to the **inner root** convention (C464).
→ **interface: unconditional given Steps 1 and C464.**
**Correction of my earlier text (twice).** (i) Essentiality of the arcs is **not**
needed for the witness argument, and "non-essential arc ⇒ deletable disk" is **not**
valid (the disk may be needed for interior coverage); what the witness argument
consumes is only the *ownership* statement — positive-length arcs whose endpoints are
the switches, with the nearest site on the arc being its owner. (ii) The witness
argument also does **not** use any convexity of `|· − c_i|` along the arc nor a
"maximum attained at an endpoint" claim; those sentences are deleted from §2 below.
The ledger's `ℓ_i > 0` is cited here only for the width bounds of Step 9.

**Step 3 (inward-root representative).** *C464*
(`../solo-20260922/INNER-ROOT-DOMINANCE.md`): for two same-radius centers on a ray
with `ρ_-ρ_+ = 1 − r²`, `D ∩ B(ρ_+u, r) ⊂ D ∩ B(ρ_-u, r)`. Hence **each** boundary
disk's outer root can be replaced independently by its inner root, preserving `D`
coverage and the actual boundary arcs; after replacement all ring centers satisfy
`|c_i| ≤ sqrt(1 − r²)`. *ARC-COORD.md* records the same as `ρ_i = cos t_i −
sqrt(r² − sin² t_i) ≤ sqrt(1−r²)`, with the double root at `t_i = arcsin r` allowed.
→ **interface: unconditional; this is the hypothesis the oracle's `u, v ∈ [0,1]`
boxes and the `qmin` filter silently use.**

**Step 4 (switch uniqueness for every adjacent pair).** *IASU*: for two distinct
centers with `|a|, |b| ≤ sqrt(1−r²)` whose proper arcs intersect without
containment and have length `< π`, **at most one** unit-circle point is equidistant
and covered by both; and exactly one exists. This is what makes `U_i` well defined
for each adjacent pair, and it uses the inward bound `a·b + r² < 1`
(the file's own control notes the "arbitrary ring centers" case is NOT covered).
→ **interface: unconditional given Step 3.**

**Step 5 (cellulation and the 11 faces).** *VBR §2–§3*: both hub Voronoi cells are
compact inside `int D`; intersecting all cells with `D` gives eleven faces with
nonempty interiors, nine degree-3 boundary switches (their bisector is a secant:
distance `≤ (|c_i| + |c_j|)/2 ≤ sqrt(1−r²) < 1`), and the Euler count
`(v+9) − (e+9) + 11 = 1` ⇒ `e = v + 10`, degree counting ⇒ `v ≤ 11`, `e ≤ 21`, with
equality iff all interior vertices are trivalent and **cocircular coincidences
decrease** `v` (explicitly: "High-order cocircular coincidences decrease the counts,
not increase them. Degenerate zero-length edges are not counted").
→ **interface: unconditional given Steps 1–4.**
**Covers the "cocircular Voronoi" question**: cocircularity is *handled* here
(vertex counts drop, zero-length dual edges are not counted).

**Step 6 (abstract dual disk, straight embedding, 11 triangles).** `CDSE`: the
clipped nearest-site dual `K` is homeomorphic to a closed disk; its boundary cycle is
the nine ring labels in arc order; its only interior vertices are the two hub labels;
each interior Voronoi vertex is in `int D`; boundary switches have exactly two
winning sites. Every dual polygon corresponds to one full Voronoi vertex `x`, its
vertices are exactly the sites nearest `x`, they lie on one **strictly convex empty
circle**, and after triangulating each polygon (`K'`) the straight realization is
injective, Jordan gives image = the enclosed polygon, both hubs strictly inside, and
"every refined triangle has the SAME circumcenter `x` and radius `≤ r`". *DDIA*
supplies the independent check of the same statement (embedded dual, one boundary
sector per ring cell, no two cells sharing two disjoint edges, link argument for the
two fans). That the eleven exhibited strict empty circles are **all** the Delaunay
faces follows from the general count `2n − h − 2` (this is the *general* planar lemma,
not the candidate-specific interval check).
**Covers the "non-triangulation" question**: if a Voronoi vertex has `k > 3` sites
on its empty circle, `CDSE` refines the `k`-gon; **all** its vertices lie on the same
circle of radius `≤ r`, hence every refined triangle's minimum enclosing radius is
`≤ r` — so the refinement is harmless for the oracle. Artificial diagonals may have
zero primal length but the triangles have positive area (`CDSE`, last paragraph).

**Step 7 (the graph is `(6,7)` with two fans and two central faces).** This is the
one step where I must be careful not to over-claim, and it splits into two parts.

*7a (unconditional, from Steps 4–6 + C799 + C802).* The dual disk `K` of
`CDSE`/`DDIA` has the nine ring labels as its boundary cycle and the two hub labels as
its **only** interior vertices. Note that the boundary edges of the dual correspond to
the nine boundary switches, but **further interior ring-ring chords are not excluded
by that alone**, and the fans cannot be read off the boundary cycle. Two imports are
therefore required and are supplied by separate claims: **the hub adjacency** is
C802 (`lead/HUB-ADJACENCY-DUAL.md`, `lead/DUAL-SEMANTIC-AND-ADJACENCY-AUDIT.md`),
which proves the hub-hub edge exists in the whole 9+2 branch conditional on C450's
per-single-disk capacity certificate — `DDIA` §17 explicitly takes "adjacent hubs" as
GIVEN and allows ears, so it cannot be the source; and **the ring-ring locality**
inside a face is C799 (`flash-structure/LOCALITY-LEMMA-RING.md`, `proved-exact`),
which is not implied by the boundary structure alone. With those two imported, the
ear/`q` classification and the two-fan structure are C801
(`flash-structure/GLOBAL-TOPOLOGICAL-REDUCTION.md` §0–4, `proved`, reviewed in
`DDIA`), whose link proof gives "exactly the two fans plus the two hub-hub triangles".
This is what the oracle's graph in `FS` §1 encodes (hubs over ring edges `0–3` and
`4–8`, central faces `(c0,a,b)`, `(c4,a,b)`).

*7b (conditional on the class enumerations).* That the surviving configurations are
precisely `q0(6,7)` — rather than `q0(5,8)` or `q0(4,9)`, or the `q1` (ear) class —
is supplied by the exclusion certificates: C818/Q1BE for all `q1`, C819/Q0D4
(`2.97871288… < π`) for `(4,9)`, and the k3 closure certificate (`3.09579300… < π`,
`Q0CE` item 1) for `(5,8)`, with the single-radius-to-range transfer furnished by
RTMD. *Status:* I did **not** re-derive a graph-theoretic exclusion of the degree
pairs by counting here; my earlier attempted counting ledger for this step was
wrong (it double-counted the switch-ring incidences and produced an impossible
`t_F`), and I have removed it rather than patch it. The degree pair is therefore
taken from the cited class exclusions, exactly as `FS` §6 says ("The graph may be
fixed only after the q0(6,7) reductions; all other classes are excluded by their own
bearing dependencies"). **Labelled gap: a self-contained counting proof that the
cellulation of Steps 5–6 can only have the `(6,7)` hub degree split is not
established in this note.**
→ **interface: 7a unconditional; 7b unconditional given C818/C819/k3/k4 + RTMD;
the counting derivation is a gap in *my* presentation, not in the cited sources.**

**Step 8 (the oracle constraints are necessary).** *FS §2*: for fixed anchors
`U_0..U_8`, minimize `t` subject to `|c_i − U_{i−1}| ≤ t`, `|c_i − U_i| ≤ t` (18)
and `|c_s − z_f| ≤ t` for the three vertices of each of the 11 faces (33). FS §2
states the true cover gives a feasible point with `t = r` ("choose its sites and
`z_f` the original interior Voronoi vertex of the refined face … boundary switch
incident sites likewise have distance `≤ r`"). §2 above records the two readings of
the covering hypothesis that make this immediate. This is the only place in the
chain where a global statement about the cover (rather than about the cellulation)
is consumed, and it is **not** new work: it is `FS` §2's own sentence.

**Step 9 (the anchors lie in `P`).** FS §4: each owned arc has width
`Δ_i ≤ 2 asin r ≤ L := 2 asin(19/50)`, `ΣΔ_i = 2π` by the boundary-cycle tiling
(*BOUNDARY-CYCLIC-CLOSURE.md* §1; *ODD-BOUNDARY-SCALE-ELIMINATION.md* derives
`Σw_i = 2π` independently), hence `Δ_i ≥ m := 2π − 8L > 0`; so
`Δ ∈ P = {Δ ∈ [m,L]^9 : ΣΔ = 2π}` after fixing the rotational orbit. FS §4 is
explicit that `m` is *derived* and adds no relaxation.
→ **interface: unconditional given Steps 1–4.**

**Step 10 (sufficiency of the global lower bound).** FS §6: if
`V(U(Δ)) ≥ R*` for every `Δ ∈ P`, then no true cover has `r < R*`. Chain:
`r < R*` ⇒ Step 8 gives `V(U(Δ)) ≤ r < R*` ⇒ contradiction. (Both directions of
this implication were re-checked in `GLOBAL-ORACLE-INTERFACE-AUDIT.md` §1.)

---

## 2. Why the 51 constraints hold at `t = r` (already in `FS` §2; recorded here)

`FS` §2 ¶1–2 states the witness argument: for a genuine cover, taking `z_f` to be the
original interior Voronoi vertex of each refined face, all incident sites are
equidistant from it with distance `≤ r`, and the boundary-switch incident sites
likewise have distance `≤ r`; hence `t = r` is feasible and `V(U) ≤ r`. The
consequences used are only these two, each a direct reading of the covering
hypothesis:

1. **Boundary (18 constraints).** Each owned arc `I_i` (Step 2) has its two endpoints
   among the switches, i.e. `U_{i−1}` and `U_i`, and on `I_i` the nearest site is the
   owner `c_i`; so `|U_{i−1} − c_i| ≤ r` and `|U_i − c_i| ≤ r` because every point of
   `D` is within `r` of some site and the owner is the nearest one there.
   **No convexity, no "maximum attained at an endpoint", no extremal claim of any
   kind is used** — only the pointwise inequality at the two endpoints.
2. **Faces (33 constraints).** Each face has its Voronoi vertex `z_f` (Steps 5–6),
   which lies in `int D`, and every site of that face is nearest to `z_f`; hence
   `|z_f − c_s| ≤ r` for its three sites, so `min_z max_{s∈f} |c_s − z| ≤ r`. This is
   the **minimum-enclosing-circle** form, with free `z`, exactly the oracle's shape.
   For an obtuse (or collinear) face no circumradius condition is used;
   `CFHR` §"For each fixed a …" states the correct form ("common intersection exists
   iff `MEC(u,v,w) ≤ r`. This includes obtuse and collinear triples; a
   circumradius-alone condition would be false").

**Withdrawals.** My earlier versions additionally claimed (i) that the covering radius
equals the maximum over exactly the switches and the 11 Voronoi vertices, (ii) that
this was a new lemma, and (iii) that `dist(·,S)` restricted to the circle is convex in
the position so its maximum lies at an endpoint. All three are withdrawn: `FS` §2
already supplies the witness argument; the equality form is unnecessary (only `≤ r`
is used); and the convex-along-circle claim is not proved here (and is not needed).

---

## 3. The four checks requested

| class | covered? | exact source |
|---|---|---|
| **cocircular Voronoi vertices** (`k > 3` sites on one empty circle) | yes | VBR §3 ("high-order cocircular coincidences decrease the counts"); CDSE ("a dual polygon corresponds to one full Voronoi vertex … triangulate each such polygon"); the general count `2n − h − 2` forces the face list to be complete |
| **obtuse faces** | yes | the face condition is `MEC ≤ t` (free `z_f`, FS §2), so obtuseness is irrelevant; `CFHR` states the `MEC` form explicitly and warns a circumradius-only condition would be false. The *acuteness* assumption appears only in the **reverse** (local) direction, `FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` §5, where it is legitimately needed |
| **non-triangulation faces** (`k`-gons) | yes | CDSE: refine each polygon on its own vertices; all its vertices lie on the **same** circle of radius `≤ r`, so every refined triangle has `MEC ≤ r`; positive areas even for artificial diagonals |
| **arc redundancy** (non-essential / contained arcs) | yes | Step 2: essentiality is `ℓ_i > 0` in the `P1 ⇔ P2` ledger (ARC-COORD §1–§2, `t_i ≤ arcsin r` required in the domain) and non-deletability is C451; FS §4's width analysis uses exactly the resulting `Δ_i ≤ L`, `ΣΔ_i = 2π` |

---

## 4. What is *not* needed (so not a gap)

* **No** convexity, star-shapedness, or hull-order of the ring polygon: CDSE's
  payoff section says so explicitly.
* **No** non-degeneracy of the triangulation as a primal metric: artificial diagonals
  may have zero Voronoi-edge length.
* **No** uniqueness of the triangulation: FS §2 fixes one triangulation per Voronoi
  vertex and the oracle is only used as a lower bound (FS §2: "these omitted
  constraints only relax the problem and preserve the direction of the lower bound").
* **No** symmetry, saturation, or specific bearing regime: FS §1/§4 impose only the
  width bound and the cyclic order.

---

## 5. The genuine remaining global object

The chain above terminates at

```
   (G)   min_{Δ ∈ P}  V(U(Δ))  ≥  R* ,
```

`P` being the 8-dimensional polytope of Step 9. Status:

* `V` is well defined, continuous and convex in the Cartesian anchors (FS §3);
  `P` is compact, so the minimum is attained.
* `V(U*) = R*` exactly at the candidate (C909), so `min_P V ≤ R*`; a proof of `(G)`
  is therefore exactly what is needed and nothing less.
* `(G)` is currently proved only **on an existential angular neighbourhood of the
  candidate orbit** (C910, whose own caliber says "no global bound on the 8D angular
  polytope `P`").
* The external certificates (C818, C819, k3, k4 — all `q`-class exclusions) and
  their `r → R` transfer (RTMD) are about *other* classes and do not touch `(G)`.
* `min_P V ≥ R*` is **sufficient** to exclude every `r < R*` cover and **necessary**
  for this route; both directions were verified in
  `closure-geometry/GLOBAL-ORACLE-INTERFACE-AUDIT.md` §1. So `(G)` is not a hidden
  premise — it is the openly acknowledged remaining obligation, and no local
  candidate-root argument (C892/C897/C902/C907/C909/C910) can substitute for it:
  those are statements about one anchor tuple, whereas `(G)` quantifies over all of
  `P`.

**Therefore, restricted to the oracle side:** the chain
cover → 9+2 → arcs → inward root → switches → cellulation → dual disk → `(6,7)`
fans → 51-edge oracle → `P` consumes no hypothesis beyond the registered ones, and
the necessity of the 51 constraints is `FS` §2's own statement (§2 above). The class
exhaustion feeding the `(6,7)` step is catalogued in
`closure-geometry/CLASS-EXHAUSTION-SOURCES.md`; per that ledger every degree pair that
can occur is excluded by a registered certificate (`q = 0`: C819 for `(4,9)`, k3 for
`(5,8)`, k4 for `(6,7)`; `q = 1`: C812 + C813 for `(4,8)`, C817 for `(5,7)`, C818 for
`(6,6)`; `q ≥ 2`: C809), so the only open class is `q0(6,7)` at `3/8 < r ≤ 19/50`,
which is exactly `(G)`. My two earlier "gap" reports on that ledger were reading
errors and are retracted there. The genuinely open global object remains `(G)` of §5.

---

## 6. Citations used (exact locations)

| step | source passage / id |
|---|---|
| 1 | claim **C451** (statement + caliber); `../solo-20260922/N11-LOW-RADIUS-REDUCTION.md` §"边界盘个数", §"两个非边界盘必须都真正位于内部"; constant check `790321 > 781250` |
| 2 | `VBR` §1 (ownership, nine switches); `ARC-COORD.md` §1 (P2 domain incl. `t_i ≤ arcsin r`), §2.1–2.2 (`P1 ⇔ P2`), audit note (a) |
| 3 | claim **C464**; `../solo-20260922/INNER-ROOT-DOMINANCE.md`; `ARC-COORD.md` §1 inner-root convention |
| 4 | `IASU` §"At most one covered equality point", §"Existence", §"Degeneracies" |
| 5 | `VBR` §2, §3 (Euler `e = v + 10`, `v ≤ 11`, `e ≤ 21`, cocircular decrease, transversality) |
| 6 | `CDSE` §"Input and scope", §"Exact straight realization", §"Circumradius and degeneracies"; `DDIA` (the eleven strict empty circles are all the Delaunay faces; no candidate-specific input) |
| 7 | `VBR` §3 (switch degree 3); `DDIA` §"Ear counting and the link proof"; `CDSE` §"Payoff" (q0 degree (6,7), two central constraints, C906); claim **C819**; `Q0CE` item 1 (k3) |
| 8 | `FS` §2 ¶1–2 (already states the witness argument); `CFHR` (MEC form, obtuse/collinear) |
| 9 | `FS` §4; `BOUNDARY-CYCLIC-CLOSURE.md` §1; `ODD-BOUNDARY-SCALE-ELIMINATION.md` §"Euler angle sum" |
| 10 | `FS` §6; `GLOBAL-ORACLE-INTERFACE-AUDIT.md` §1 |

**Declared dependencies not re-audited here:** C450 (m10 exclusion, reproducing
`M10-038-EXCLUSION.md`), C818/C819/k3/k4 (with RTMD for the `r`-transfer),
C801/C802 findings cited by VBR/CDSE, C892/C897/C902/C907/C909/C910 (candidate and
local radius side).

No claim registered; no subagent; no lead file modified.
