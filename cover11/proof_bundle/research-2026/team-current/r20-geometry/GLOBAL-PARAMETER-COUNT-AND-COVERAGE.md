# Outstanding global parameter count, branch/degeneracy coverage checklist, and what can actually exclude a family

Author: r20-geometry (sole writer of this directory; no subagents; **no claim registered**).
Inputs read: `lead/CENTRAL-FIBER-HELLY-REDUCTION.md` (authoritative conditional reduction, cited as
`[L]`), `r20-alternative/CENTRAL-HELLY-SCREEN.md` (box-level (H2) test, code under repair),
`STRICT-HUB-FINITE-DISJUNCTION.md`, `RADIAL-INWARD-LOCAL.md`, `central_tight_triple.py/.out.txt`.

## 1. Outstanding global parameter count (no symmetry, no saturation imposed)

| stage | variables | dimension | source / status |
|---|---|---|---|
| raw configuration | 1 radius `r` + 9 ring centres + 2 hubs | `1+18+4 = 23` | object of the problem; `r = R(11)` unknown |
| modulo global rotation | −1 | `22` | rotation is a symmetry of the covering problem (not of the labelled data) |
| eliminate the second hub `b` | −2 | `20` | `[L]`: fiber theorem + finite planar Helly-3, **conditional on (E)** |
| ring reparametrisation (legal boundary rings) | 9 rings → `(ρ_i, θ_i)` (arc centre direction + radial parameter) | same dimension, but the rotation is now visibly inside the ring angles: `17` ring dof | legal-chain chart; **no** saturation/symmetry assumed (each ring keeps its own overlap/slack parameter) |
| **outstanding** | `r` (1) + rings (17) + hub `a` (2) | **20** | hub `b` gone exactly on certified-(E) regions; `a` still a genuine 2-D problem (`[L]` §"Eliminate b") |

So the surviving object is **20-dimensional**: `(r; ρ_1..ρ_9, θ_1..θ_9; a ∈ K_A)`, with the ring
angles carrying the one rotation redundancy and **no** saturation (the nine boundary-arc overlaps,
the arc-tangency branch `t_+ = k`, and all the ring-slack parameters are still free).

**Can the finite-cell elimination of `a` still contain the outer-ring freedom?** Not by itself.
Two facts must be kept apart:

* The `a`-cell decomposition is *pointwise in the ring data*: the witness loci (H1–H6 of
  `CENTRAL-COUPLING-NORMAL-FORMS.md` §2.1 and the 25 central triples of `[L]`) move with the rings
  (the pins `q_k` and the sites `c_0,c_4` are ring functions; the moving centres `p_σ(a,c_i)` are
  of course `a`-dependent). A cell structure proved for one ring tuple says nothing for another.
* Therefore a global reduction needs a **second, uniform layer**: either (i) interval/box bounds of
  the witness inequalities over ring boxes in the 17-D `(ρ,θ)` space, or (ii) a second finite
  stratification with the *same* witness list. The branch loci of the `a`-cells (root-choice flips at
  `|c_i−a| = 2r`, collinearity `b ∈ line(a,c_i)`, tangency `ψ = r`, and the (E)-boundary) are
  ring-dependent; a uniform treatment must prove the checklist below **on ring boxes**, not at a point.

Verdict: the finite `a`-cell scheme is a *conditional slice* of the 20-D object; it does **not**
absorb the outer-ring freedom. The 20-D count above is the honest outstanding count after `[L]`.

## 2. Branch / degeneracy coverage checklist (what a global proof must discharge)

Each item: statement, status, where.

1. **Per-edge C879 legality** (unique common-boundary tie; `p_out ∉ int D`; `d < 2r`): *assumed*
   per chain edge. Status: the tie-uniqueness hypothesis itself is **unproved** (bounded search only,
   A3: min `F = +8.5·10⁻⁶`, no uniform margin; `|p_in| = 1−Θ(d)`).
2. **Arc-tangency branch** `t_+ = k ⟺ p_out ∈ ∂D`: legal and realised by the certified object on all
   nine edges (`|p_out| = 1` to 5e−17); `d = 2r` (`k = 0`) is impossible under the hypotheses. Status:
   covered (A2/A6), exactness only to the object's stored precision.
3. **Root/branch choice per site** `(q_i, q'_i)` for `i ∈ {0,4}`: may vary over `a`-pieces and must be
   specified/verified per piece (`[L]`); the switch locus is `|c_i−a| = 2r` (root collision, Thales
   stratum) — both signs `σ_i ∈ {±}` must be listed. Status: structure stated; **no** piecewise proof.
4. **The (E) obligation** (`∀a ∈` piece, `∀b ∈ K_B`: `|b−q'_i(a)| > r`): an *inequality* obligation,
   uniform over `a` and over an enclosing localization region of `K_B`; `[L]` states explicitly it is
   **not** implied by numeric candidate values. Status: **open**; the only numeric work
   (`central_crescent_interval.py` v1) is withdrawn; v2 numbers are recorded but **uncited**.
5. **Degenerate strata** in the fiber theorem: `b` on the chord line `a c_i` (excluded by the strict
   far-disk factor, `[L]`), `a = c_i`, `b = c_i`, `a = b`, coincident pins (deduplicated). Status:
   covered by `[L]`'s proof plus the open-status of (E); these are *not* additional branches.
6. **Helly list truncation**: with `m = |P_B|` and `K_B` known nonempty (Theorem A/B), only triples
   containing a new central disk need checking: `m = 4` ⟹ **25 triples** (12 + 4 + 8 + 1), `[L]`; my
   theorem-B forms give the emptiness semantics. Status: covered (counting), including
   `MEC ≤ r` for *all* triples (obtuse/collinear included; a circumradius-only test is false).
7. **Open-ball semantics**: fiber nonempty ⟺ `min_{S}|b| < ρ` **strict** (`[L]`); hence the H5/ball
   witness fires at `≥ ρ` (equality = tangency is a witness). Status: covered (Theorem B §3, control C4).
8. **Hub strictness and distinctness**: `|a|,|b| < ρ`; `a ≠ b`; `c_i ∉ {a,b}`; ring centres distinct.
   Status: listed; strictness is used, not assumed away.
9. **Ring-space coverage** (the 17-D layer): boundary coverage of `∂D` by the nine ring arcs, the hole
   `K` covered by the two hubs, the nine arc-overlap parameters, and the two fan chains (4 and 5
   edges, degree-(6,7) graph). Status: *class-level* reductions cited; **no** uniform coverage proof.
10. **Radius range**: `r ∈ [3/8, U]`, `U = 37999/100000`, with the C249 upper bound; `ρ = 1−r > 0` and
    `2r > 1` regime for the certified object. Status: domain, not a branch.

## 3. Which inequalities can genuinely exclude a family (joint with `alternative`)

Only inequalities that can be **bounded uniformly over the ring (and `a`) region** can exclude a
family. Classified:

* **Ring-data-only (uniform in `a`)**: H1 (two *fixed* pins disjoint, `|q_k−q_l| > 2r`) and the
  fixed-pin half of H4 (`|q_k| ≥ ρ+r`). These are conditions on the ring tuple alone ⟹ one interval
  evaluation on a ring box excludes the whole family on that box. **Genuinely family-excluding.**
* **Moving-disk witnesses (H2, H3, the moving half of H4, H5, H6)**: each is a condition on `a` (and
  the rings). Family exclusion requires the **∀`a`** form ("for every `a ∈ K_A` some witness fires"),
  which is *strictly stronger* than the per-`a` fiber test; it can be attacked by interval bounds over
  `a`-boxes (`[L]`'s structure), but it is an inequality obligation, not a pointwise verdict.
* **(E)**: a hypothesis, not an exclusion; if (E) fails on a box, one must fall back to the exact
  crescent (no exclusion).
* **Tight (equality) triples**: cannot exclude — see §4.

## 4. Tangency-type 3-disk triples at the candidate: readings only, plus the conditional normal-cone lemma

**Correction (lead, 11dc6a88).** The earlier version of this section drew **"intersection = singleton"**
conclusions from near-zero readings. That is not legitimate: at the stored data one has `ψ < r` (or at
best `ψ ≈ r` within `10⁻¹⁷`), and `ψ < r` together with positive barycentric weights means the three
disks have a **small interior** (the MEC centre is strictly inside all three) — **not** a singleton.
Only after an **exact** proof that all three boundaries pass through `b` may one apply the normal-cone
criterion. The specific singleton claims are **deleted**; what remains is the conditional lemma:

> **Conditional normal-cone lemma (kept).** *Assume* `b` lies exactly on all three boundaries
> (`|b − q_i| = r`, `i = 1..3`). Then a direction `v` is admissible (`b + sv` stays in all three
> closed disks for all small `s > 0`) iff `v·(q_i − b) > 0` for every `i`; consequently
> `max gap ≤ 180°` ⟺ the normals do not lie in an open half-plane ⟺ **no** common strict inward
> direction ⟺ the intersection is `{b}`; and `max gap > 180°` ⟺ **interior**. (No claim is made that
> the hypothesis holds at the candidate.)

Readings at the candidate (`a =` hub A, `b =` hub B), triples among `{central0, central4, fan-B pins}`
(45-digit mpmath; readings, not certificates):

| triple | `ψ − r` | MEC branch | barycentric weights | max gap | status |
|---|---|---|---|---|---|
| `central0, central4, pin(9,10)` | `−4.31·10⁻¹⁷` | circumcircle | `(0.3214, 0.3214, 0.3573)` all > 0 | 123.77° | nonempty; interior near the MEC centre (all weights > 0) |
| `central4, pin(9,10), pin(3,5)` | `−6.09·10⁻¹⁷` | circumcircle | `(0.4060, 0.2552, 0.3388)` all > 0 | 141.24° | nonempty |
| `pin(6,4), pin(9,10), pin(3,5)` | `−4.58·10⁻¹⁷` | circumcircle | `(0.4600, 0.0800, 0.4600)` all > 0 | 170.02° | nonempty |
| `central0, pin(6,4), pin(9,10)` | `−2.73·10⁻¹⁷` | circumcircle | `(0.4060, 0.3388, 0.2552)` all > 0 | 141.24° | nonempty |

**Genuine acute positive-barycentric triple (lead's request):** 12 triples are acute with all
barycentric weights positive; the one with the largest `ψ − r` is
`{central0, pin(6,4), pin(9,10)}` (`ψ − r = −2.73·10⁻¹⁷`, weights `(0.406026, 0.338816, 0.255158)`,
max gap `141.24°`).

**Emptiness-witness search: not found.** Every triple has `ψ ≤ r` as read (the largest value is
`−2.7·10⁻¹⁷`), so none is an emptiness witness at this candidate; and by the correction above this
also means the triples at the candidate are *nonempty with interior*, not tangency-singletons.
The `mec()` routine itself is calibrated on the lead's instance: `MEC((0,0),(2,0),(1,0.05)) = 1`,
**diameter** branch (circumcentre barycentric weights `(100.25, 100.25, −199.5)`, one negative;
circumradius `≈ 10.03`) — i.e. obtuse triangles never take the circumcircle branch.

## 5. Non-claims

* No global domain coverage, no global optimum, no symmetry or saturation assumption.
* The 20-D count is bookkeeping after `[L]`; the (E) obligation and the ring-space layer are **open**;
  `alternative`'s v2 numbers remain recorded-but-uncited pending independent audit.
* The tight-triple table is a reading of the stored exact-rational candidate (45-digit mpmath), not a
  certificate.

Repro:
```
py -3 -B -X utf8 research-2026/team-current/r20-geometry/central_tight_triple.py
```
