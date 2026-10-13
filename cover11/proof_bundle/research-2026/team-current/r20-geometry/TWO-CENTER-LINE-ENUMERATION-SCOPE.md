# Two-center splitting line: can the line parameter be eliminated by finitely many residual vertices? (scope note)

Author: r20-geometry (sole writer of this directory; no subagents; **no claim registered**; no sampling
used as proof).
Inputs read: `lead/R20-RESIDUAL-TWO-CENTER.md`, `lead/R21-RESIDUAL-FINITE-VERTICES.md` (quoted as
`[R]`), `lead/CENTRAL-FIBER-HELLY-REDUCTION.md` (`[L]`), `r20-alternative/CENTRAL-HELLY-SCREEN.md`.

## 1. The two reductions and their exact quantifiers

* **Two-center line split (`[R20]`)**: two hubs cover `K` iff `∃ n, t` with `M_H(K^-) ≤ r²` and
  `M_H(K^+) ≤ r²`, where `K^∓ = K ∩ {n·x ≶ t}`, `H` the hub ball, `M_H(S) = min_{h∈H} max_{x∈S}|x−h|²`.
  The line is a **2-parameter** object (`n ∈ S¹`, `t ∈ R`).
* **Finite vertices (`[R21]`)**: for a **fixed** line `L = {n·x = t}`, with `S = K ∩ {n·x ≤ t}`,
  `V(L) = (A) ∪ (B)`, (A) all pairwise **ring–ring** circle intersections in `S`, (B) all intersections
  of `L` with a ring circle that belong to `K`; then `max_{x∈S}|x−h|² = max_{v∈V(L)}|v−h|²` for every
  `h`, so the constrained one-center problem on `S` is an exact finite-point problem on `V(L)`
  (≤ `2·C(9,2) + 2·9 = 90` pre-filter points for n11). Membership in `K` must be decided by the closure
  of strictly uncovered cells, not by equality tests.
* `[R]` itself states the caveat: **"This does NOT say two disks containing all unsplit residual
  vertices cover the residual: the dividing line adds new vertices B."**

## 2. What is proved, what is open

* **Necessity (proved).** If `K` is covered by two hubs with a splitting line `L`, then the ring–ring
  vertices in each side are covered by the corresponding hub with the induced bipartition. So
  "coverable" ⟹ "some bipartition of the fixed ring–ring vertices is coverable".
* **Sufficiency (open, and false at the hub level — §3).** The converse would need: covering the fixed
  (line-independent) ring–ring vertices of a side implies covering that whole side. `[R]` explicitly
  warns against this, because the cut creates the moving vertices (B). Below is an exact exhibit of the
  failure of that implication at the level of a single hub.

## 3. RETRACTIONS (lead 11cfd04d) and what survives

The earlier version of this section claimed (i) an "exact exhibit" with `p` labelled as a *ring–ring*
vertex — **wrong**: the configuration had a single ring, so `p` is just a point of that ring's circle;
(ii) "single pieces up to ~120° are always coverable" — **wrong**: the maximal cap half-angle bound does
not imply that an *arbitrary* arc (whose angular width may exceed the cap) is coverable; (iii) the
conclusions "the moving vertices (B) are indispensable" and "the 2-D line parameter is not eliminable"
— **withdrawn as unjustified**; they remain a **gap**.

What actually survives and is proved here:

* **Necessity** (§2) is unchanged.
* **Single-hub lemma (proved, with the `h = c` exception stated separately — lead 2c68db35).** For
  `h ≠ c` the direction set of `∂B(c,r)` covered by the hub is a cap of half-angle
  `β = arccos(|c−h|/(2r)) ∈ [0, π/2)`. **Exception:** for `h = c` the hub disk contains the *whole*
  circle (`|c + ru − c| = r` for every `u`), so the covered set is the entire direction circle, **not**
  a cap of half-angle `π/2` — the limit `|c−h| → 0⁺` is not attained at `|c−h| = 0`. In the canonical
  domain `|c| ≥ ρ > |h|` we have `h ≠ c`, so the exception never applies there (but it must be stated). Hence, if an arc of width `≤ π` ("short side") has **both endpoints covered
  by the same hub**, then the whole arc is covered (a cap of half-angle `< π/2` is an angular interval
  of width `< π`, and a short arc with both endpoints in it is contained in it). This confirms the
  lead's reading: for *equal radii and a single hub*, endpoint coverage implies arc coverage as long as
  the arc is the short side.
* Therefore the only place where "endpoint/key-point coverage" can fail to imply arc coverage is when
  the covering is done by **two different hubs** — which is exactly the lead's next question.

## 4. The requested construction: two hubs, two endpoints, one short arc, middle missed — exact

All quantities rational (`two_hub_arc_check.py`, verified with `Fraction`s, no sampling):

* `r = 19/50 = 0.38`, `ρ = 31/50 = 0.62`, ring centre `c = (19/20, 0)` (`|c| = 0.95 ≥ ρ`);
* short arc of `∂B(c,r)` from direction `u₁ = (−4/5, 3/5)` to `u₂ = (−4/5, −3/5)` through
  `u_mid = (−1, 0)`: width `73.74° ≤ 180°`, endpoints
  `x₁ = (0.646, 0.228)`, `x₂ = (0.646, −0.228)`, middle `x_mid = (0.57, 0)`;
* hubs `h₁ = (749/2000, 987/2000)`, `h₂ = (749/2000, −987/2000)`, with
  `|h₁|² = 153517/400000 < ρ² = 361/2500` (inside `H`), and exactly:
  `|h₁−x₁|² = 57681/400000 ≤ 361/2500 = r²` (covers `x₁`),
  `|h₁−x_mid|² = 22541/80000 > r²` (misses the middle, margin `10989/80000 ≈ 0.137`),
  `|h₁−x₂|² = 1188549/2000000 > r²` (does not cover the other endpoint); symmetric for `h₂`.

So **two hubs in `H`, each covering one endpoint of a short arc, can miss the middle** — the requested
counterexample structure, exact.

**Embedding — domain label corrected (lead 2c68db35).** `|c_i| = 0.95 > √(1−r²) ≈ 0.924986` violates
the **canonical inward-root domain** (`|c_i| ≤ √(1−r²)`, `[R21]`'s `s = √(1−r²)`), so this construction
must be labelled a **boundary-cover outer-root** configuration, **not** "legal in the main domain".

**Embedding in a boundary-cover 9-ring residual (checked, with margins; `two_hub_arc_check.out.txt`).** Take nine
rings of radius `r = 0.38` with `|c_i| = 19/20 = 0.95 < 1`, equally spaced `40°`, our ring at angle `0`.
Then: each ring covers a boundary arc of half-width `α = 22.284°`, so `2α − 40° = 4.57° > 0` and the nine
radius-`r` disks **cover the unit boundary**; the neighbours' caps on our circle have half-width `31.23°`
centred at `±110°`, leaving clearance `+1.90°` to the arc; deeper rings have no cap at all (`|c_j−c|>2r`).
Hence the exact rational arc `[143.13°, 216.87°]` is a sub-arc of the residual arc of that configuration
(`≈[141.2°, 218.8°]`), lies inside `D` (`|x| ∈ [0.57, 0.783]`), and is **uncovered by the other eight
rings** — the construction embeds in a legal 9-ring residual (hypotheses of `[R21]`: distinct centres,
`|c_i| ≤ s < 1`, boundary covered; note `r = 0.38 > r*`, i.e. a legal-but-not-threshold configuration,
which is what the construction needs).

## 4bis. Deterministic linearized central-face search (lead b43463af): STRICT COUNTEREXAMPLE FOUND

Method exactly as directed (no blind sampling): fix `r = 0.38` and the nine certified rings; let the two
hubs move; central faces `φ_i(a,b) = ∠(a,c_i,b) − arcsin(|a−b|/(2r)) ≥ 0` (`i ∈ {0,4}`, `c_i` the central
sites), pin faces `s_k(h) = r − |h − pin_k| ≥ 0`, hub balls `ρ − |h| > 0`. Take the **steepest-descent**
direction of the most sensitive central face (central gradients by central differences at `1e−6`), then
the admissible step from the pin first-order conditions (`t_max = min_k s_k /(loss rate)`), and
**recompute all nine pins and both central faces** at the stepped point
(`linearized_central_search.py/.out.txt/.json`).

Readings at the candidate (`r = 0.38`): `φ_0 = φ_4 = +2.841·10⁻⁵` (central faces have small slack — not
tight, unlike at `r*`), pin slacks A `3.9–4.8·10⁻⁵`, B `3.6·10⁻⁵ … 2.88·10⁻³`, hub balls large.

Chosen direction (steepest descent of `φ_0`, both hubs moving), `t_max = 5.813·10⁻⁵`, step `t = 5.232·10⁻⁵`:

| quantity | value at the stepped point |
|---|---|
| pin slacks A | `+9.71·10⁻⁶, +4.70·10⁻⁵, +8.27·10⁻⁵, +7.10·10⁻⁵` (all strict) |
| pin slacks B | `+6.49·10⁻⁵, +2.916·10⁻³, +6.28·10⁻⁵, +2.868·10⁻³, +3.60·10⁻⁶` (all strict) |
| `φ_0` | **`−7.07·10⁻⁶` ⟹ central face VIOLATED** |
| `φ_4` | `+4.20·10⁻⁵` (still feasible) |
| hub balls | `A +3.470`, `B +4.706` (plenty) |

So on this fixed-rings family there is a hub configuration where **all nine pin (vertex) constraints are
strictly satisfied while a central face is violated**: **vertex/pin coverage is NOT sufficient** for the
residual (central) coverage. Scope discipline (lead): this is *not* a statement that the 2-D line
parameter cannot be eliminated, and it is not a global obstruction — it is a first counterexample of the
"vertex coverage insufficient" kind, found deterministically.

**Status of intervalification (lead: "找到严格反例再 intervalify"): PENDING.** The witness is currently a
high-precision reading (`mp.dps = 60`); the violation margin is `7.1·10⁻⁶` and the tightest pin slack is
`3.6·10⁻⁶`, both large compared with the evaluation error at this precision, but no interval certificate
has been produced yet. The next action is to intervalify exactly this witness (rational hub coordinates
+ outward-rounded `φ` and `|h−pin|` evaluations).

## 4ter. EXACT witness verification (lead 04663b59): uncovered point with rational signs only

Hubs rationalised to a `10⁻⁷` grid: `A = (2653/10⁷, 2729979/10⁷)`,
`B = (−241/1250000, −1494489/10⁷)`; `r = 19/50`; the nine certified ring centres are exact rationals
(scale `10¹⁷`). Take `p` = the **rational circumcentre** of the central triangle `(A, c_0, B)`
(cert 5), obtained by solving the two perpendicular-bisector equations in `Fraction`s:

```
p = (257455287618977498388871611632228596889/814917795710482079541275000000000000000,
     200247950757832605654046290292032042423/3259671182841928318165100000000000000000)
```

**Certificate-grade sign computation (exact `Fraction`s, no arcsin / Delaunay branch):**

* `|p|² − 1 = −1904965…/2125091… < 0` ⟹ **`p` lies inside the unit disk**;
* all nine ring centres and both **moved** hubs: `|p − c|² − r² > 0`, e.g.
  `ring 5: +6469548614306402579287424946618188833094320673118615777995529757487872813/21250912440500192153547700938449427709261716020000000000000000000000000000000000 > 0`,
  and the same value for `hub A (moved)` and `hub B (moved)` (they equal `R_c² − r² > 0`):
  ⟹ **`p` is strictly outside all eleven radius-`r` disks** (nine rings + both moved hubs).

So `p` is a point of the unit disk covered by none of the eleven disks: **the vertex/pin coverage is not
sufficient** — witnessed by a single point, with exact rational signs and **no branch/Delaunay
interface**. This is the certificate form the lead asked for (the angular form is only motivation:
`φ_0 = −7.049·10⁻⁶`, `R_c = 0.380004006 > r = 0.38`).

**Two-representation comparison (as asked, before any registration).** Same witness, two encodings:
(i) *angular/heuristic*: `φ_0(a,b) = ∠(a,c_0,b) − arcsin(|a−b|/(2r)) < 0`, i.e. `R_c > r`;
(ii) *exact direct*: the eleven rational signs above plus `|p|² < 1`; the three quantities
`|p−A|² − r² = |p−c_0|² − r² = |p−B|² − r² > 0` are exactly `R_c² − r²`. Only (ii) is used as the claim.

**Pin check repaired and EXACT (lead 2c01d868).** The kernel `sign_of(alpha, beta, Q, target)` had
`rhs = −beta²Q` (wrong sign) and no separate `Q = 0` case; after the fix it passes the controls
`(2,1,1) → +1`, `(1,2,1) → −1`, `(−2,−1,1) → −1`, `(−1,−2,1) → +1`, `(1,1,1) → 0`, plus
`(1,2,0) → +1`, `(0,2,0) → 0`, `(−1,2,0) → −1`. With the repaired kernel **all nine pin constraints
are strictly satisfied exactly** (`sign(|h−pin|² − r²) = −1` for each of the nine; the near-root
criterion `m·perp(d)` was already correct, so there was no root bug). A bogus printed line
(`rho − 0`, line 134) was deleted. Both halves are now exact: pins covered (`Fraction + sqrt`) and
`p` uncovered (rationals).

**Superseded note (kept for history):** the exact `Fraction + sqrt` check of the nine **pin** constraints
(`|h − pin_k|² < r²`) is implemented but currently mis-selects the near root (all nine report “not
covered” although the 60-digit readings give slacks `≥ 3.6·10⁻⁶`); the pin feasibility therefore rests
for now on the high-precision readings, and the exact radical-form check must be repaired before it can
be quoted. (This does not affect the exact eleven-sites certificate above, which uses only rationals.)

## 5. Rigorous scope (as requested): what this shows, what stays open

1. **Proved.** (a) Necessity of vertex coverage. (b) The **single-hub lemma** (§3): for a short
   (`≤ π`) arc, one hub covering both endpoints covers the arc. (c) The **exact two-hub construction**
   (§4): two hubs in `H`, each covering one endpoint of a short arc, can miss the middle; and it
   **embeds** in a legal 9-ring boundary-covering residual (margins as stated).
2. **Withdrawn (was claimed earlier, unjustified).** "The moving vertices `(B)` are indispensable" and
   "the 2-D line parameter is not eliminable by the fixed ring–ring-vertex enumeration". These remain a
   **gap**, not a disproof.
3. **Bounded single test case (done; `two_arc_switch_check.py/.out.txt`).** In the canonical domain
   (`r = 0.38`, `|c_i| = 0.92 ≤ √(1−r²)`, nine rings equally spaced `40°`, coverage margin `+4.66°`), with
   the splitting line `y = 0` through the arc middle `x_mid = (0.54, 0)`, the two-arc switch was tested:
   each side contains ring–ring vertices whose pairwise distance reaches `1.283 > 2r = 0.76`, so **no
   single hub can cover a side's vertices — the vertex test already rejects**. Per the lead's rule
   ("if the vertex test already rejects, do not scale"), this construction is **not** scaled further and
   yields **no test-level counterexample**. (A crude hub-distance remark in the script output was
   corrected: `|x_mid| − 0.30 = 0.24 < r`, so no impossibility follows from it.)
4. **Remaining direction (flagged, not attempted).** The interesting regime per the lead is the one with
   the two hubs near the candidate / ring-norm inside the canonical domain and only the **switch of the
   two arcs** tested; a sub-arc example must never be read as "ALL vertices".

5. **Bounded near-candidate experiment (lead 9b06ab5b): NOT FOUND — and why.** With the certified nine
   ring centres **fixed** and the nine chain pins (`4 + 5`) assigned to the two hubs as in the certified
   fan structure (`near_candidate_hub_perturb.py/.out.txt`): the pin margins at the candidate are
   `+0.000000` for the four fan-A pins and for three of the five fan-B pins (the other two: `+0.0028`),
   i.e. the assignment is **saturated**; at `r = 0.38` the tightest pin margins are only
   `≈ 4·10⁻⁵`. Consequently, within the bounded search (20 perturbations, moving hub `B` away from the
   largest residual arc's interior point — ring 1, width `70.65°`) no perturbation keeps the pin
   assignment feasible while creating a miss: **no test-level counterexample of this kind exists near the
   candidate**, because the vertex coverage there is *rigid*, not slack. (Recorded as a bounded method
   limit, not as a disproof of anything; per the lead, no scaling, no 12-D numerics.)
6. **Fallback (per lead): when is endpoint coverage sufficient for short arcs under a cyclic assignment?**
   Let `U ⊆ S¹` be a residual arc of angular width `≤ π` on a ring circle `∂B(c,r)` (the "short side"),
   with endpoints `μ₁, μ₂`, and let `C_i = C(h_i)` be the cap of directions covered by hub `h_i`
   (half-angle `< π/2` for `h_i ≠ c`, whole circle iff `h_i = c`). Then:
   * **(i) single hub.** `μ₁, μ₂ ∈ C` for one hub ⟹ `U ⊆ C` (cap = angular interval of width `< π`,
     and a short arc with both endpoints inside it is contained in it) — the earlier lemma.
   * **(ii) switch assignment, exact criterion.** If `μ₁ ∈ C₁`, `μ₂ ∈ C₂` (endpoints covered by
     *different* hubs), then `U ⊆ C₁ ∪ C₂` **iff** `C₁ ∩ C₂ ∩ U ≠ ∅`. Proof: `C_i ∩ U` is an interval
     containing `μ_i` (intersection of two intervals), so `U ⊆ C₁ ∪ C₂` fails exactly when the two
     pieces `C₁∩U` and `C₂∩U` are disjoint — which is the same as `C₁ ∩ C₂ ∩ U = ∅`.
   * **Hence the extra condition requested.** For a cyclic assignment of the pins to the two hubs (two
     consecutive blocks), the two *switch arcs* (one on each side of the split) are each covered by the
     two hubs' caps together **iff the two caps overlap inside each switch arc**. So "endpoint coverage
     ⟹ arc coverage" holds for short arcs under the cyclic assignment precisely when the two caps
     overlap within every switch arc; this is exactly what fails in the exact outer-root two-hub example
     of §4 (there the caps meet outside the arc, leaving the middle uncovered).
7. **Next concrete obligation (this single construction, per lead).** Turn the miss-middle example into a
   *test-level* statement: put the splitting line through the middle `x_mid` (so the residual arc is cut
   into two pieces, each with one ring–ring-type end and the line-circle vertex `x_mid` in its closure),
   then check whether a vertex-only test can accept (each side's fixed vertices covered by its hub) while
   the true side test rejects (because `x_mid` belongs to *both* closures and is covered by neither hub).
   This requires checking **all** ring–ring vertices of each side in the constructed configuration —
   not only the arc's ends — so it is genuinely an inequality obligation over the whole side, and it has
   to be done for the specific line (per-line first; the ∃-over-lines or ∀-over-lines statement is a
   separate, larger obligation).
4. **No global conclusion** is drawn here: nothing in this note kills or validates the two-center line
   route, and no sampling is used as proof (the §4 checks are exact rational inequalities; the embedding
   checks are high-precision with explicit margins and are flagged as such).

