# BRIEF 2026-09-25 — C880–C889 audit, q0 mapping resolution, 5-chain elimination, chain transfer map

Author: r20-chain line (single writer to `research-2026/team-current/r20-chain/`; read-only elsewhere).
Evidence only — **no new claims registered**. Raw logs: `out/audit_lead_q0_map.txt`,
`out/audit_c880_889.txt`, `out/r20_5chain_elimination.txt`, `out/r20_transfer_map.txt`.
Tools: `tools/audit_lead_q0_map.py`, `tools/audit_c880_889.py`, `tools/r20_5chain_elimination.py`,
`tools/r20_transfer_map.py`.

---

## §1 Claim audit C880–C889 (each read via `claim_get` + its evidence files)

| id | old status | verdict | root cause (one line) | action |
|---|---|---|---|---|
| C880 | proved-exact | **FALSE** | single-arc extremum phase sign: `arg(H−C)` is the **min** phase; the max sits at `arg(C−H)`; claim's own evidence `out/identities2.txt:4` reports 2003/4000 violations, not 0 | retracted |
| C881 | proved-exact | **necessity false** | "triangle covered by its 3 vertex disks ⟺ ρ ≤ r" fails for obtuse triangles (circumcentre outside); flat counterexample ρ=5.05 covered at r=0.51 | retracted |
| C882 | proved-exact | **(iii) false** | "exactly one closed disk" fails at circle-boundary intersections (`h=m+(r−k)n`: both disks contain h, ρ=r); degenerate set is collinearity with c_i,c_j, not the perpendicular bisector | retracted |
| C883 | retracted | ok (was already retracted; not re-scanned per instruction) | interface hypothesis H1 violated by the witness pair | untouched |
| C884 | proved-exact | **(b) wrong, conclusion inverted** | chain assignment/active counts mis-read; rigid C879 case **does** occur (hub A) | retracted |
| C885 | dead | **root-cause wrong** (L1–L4 and "do not cite" stand) | "cap/width type mixing" is false: θ_i ≤ s_i+s_{i+1} is valid; the files die from implementation/wiring + criterion weakness | retracted |
| C886 | retracted | **retraction reason refuted; reading correct** | hw ≠ arccos(|H−c_i|/(2R)) for 6/9 rings, so the "label swap" story fails; |p_out|−1 = +2.6e−17…+8.1e−17 on all **nine** edges | review event `rejected` |
| C887 | proved-exact | **calibration false** | "extent = 2 s_i for all 9 rings" holds only for rings 7,1,8; 2s_i is the **hub-covered** arc length | retracted |
| C888 | numeric | **false** | same identity, 6/9 rings off by 5e−3…2.5e−1; "max=R" holds only per covering hub | retracted |
| C889 | numeric | **false + control false** | formula π−2arccos contradicts its own data (ring 7: 2.2756 vs 0.865997); the two "independent sources" agree only on rings 7,1,8 | retracted |

Correct replacements (all verified in the logs above):

* **(F1′)** `|x(s)−H|² = R²+|C−H|²−2R|C−H|cos(s−arg(H−C)))`; the interior maximum of `|x−H|` on the
  arc is at `s = arg(C−H)` (the anti-pole), the minimum at `arg(H−C)`. A containment test must check
  the maximum phase. Corrected harness: 0/4000 violations vs 8001-point sampling.
* **(F2′)** For a **non-obtuse** triangle, covered by the three vertex disks ⟺ ρ ≤ r. For obtuse
  triangles only ⟸ holds (ρ > r does not imply non-coverage; the exact threshold is the 3-centre
  covering radius c(T) < ρ).
* **(F3′)** For h non-collinear with c_i,c_j: ρ ≤ r ⟺ `(|h−p_in|²−r²)(|h−p_out|²−r²) ≤ 0`
  (lead's Lemma 2 identity, 4y²(ρ²−r²) = product). With the **domain hypothesis** `|p_out| ≥ 1`,
  `|h| < 1−r` the outer factor is positive and ⟺ `|h−p_in| ≤ r`. Product test vs direct ρ:
  0/20000 mismatches (non-collinear); "exactly one" is only the strict-product subclass.
* **(C887′)** The points of `Λ_i` at distance exactly R from H are exactly two, at angular offset
  `±s_i` from `arg(H−c_i)`; hence the **hub-covered** arc of `Λ_i` is `[arg(H−c_i)∓s_i]`, length
  `2s_i`. The exposed rim arc is bounded by the neighbouring ring circles (= pins) and is generally a
  proper sub-arc; for the record object `extent = 2s_i` only for rings 7,1,8 (hub B's interior rings).
  Independent 4e5-point-per-rim sampling control: analytic vs sampled extents agree to ≤9.5e−6.

---

## §2 q0 mapping resolution (the lead's `check_r20_chain_variance.py`) — read the code, no label guess

`lead/q0_exact_closure_radius.py` builds `c = C[[(i+shift)%9] + ([10,9] if swap else [9,10])]` with
`C = [rings sorted by atan2] + [row0, row2]`, and selects `(shift,swap)` by matching
`Delaunay(c).simplices` to `q0_graphs.json[2]["faces"]`. **The match is unique: (shift,swap) = (4,1)**
(verified by enumerating all 18 combinations; `out/audit_lead_q0_map.txt`). Consequences:

* `c[10] = C[9] = object row 0 = hub A`, `c[9] = C[10] = object row 2 = hub B`.
  So `h = c[10]` **is hub A** — there is **no label bug** in the lead's script; AUDIT-A-B.md's
  "label bug" attribution (c[10] reads as hub B) is itself a mapping mis-read.
* Recomputed `q0 [4,6,8]` (the lead's own index space, min-norm roots of lead edges (i,i+1)):

  | lead id | object edge | pin (x,y) | \|H_A−pin\|−r | \|H_B−pin\|−r |
  |---|---|---|---|---|
  | 4 | (row6,row4) | (−0.378668736514, −0.115955861337) | −1.7e−16 | +1.630e−1 |
  | 6 | (row9,row10) | (−0.000574102353, −0.529412040784) | 0.0 | +4.224e−1 |
  | 8 | (row3,row5) | (+0.378416356737, −0.116776858375) | −5.6e−17 | +1.630e−1 |

  `c[10] = (−0.000162042987, −0.149428411085)`, `|c[10]| = 0.149428498946` (object row 0), and the
  lead's weights `(0.45997773056271785, 0.08004453927415564, 0.45997773016312643)` reproduce it with
  residual **6.83e−18**; V − r² = −1.94e−16 (double) / **−3.63e−17** (60-digit). The lead's variance
  calibration is correct and is a genuine C879 instance **for hub A**.
* Source discipline: the lead's ring order = polar order about the origin, rotated by shift = 4, so
  lead edge (i,i+1) = object edge `(rings[i+4], rings[i+5])` with
  `rings = [4,9,10,3,5,7,1,8,6]`. The old node mapping (`r20geom/clean_measurement/arc_account`) uses
  this same polar order but **without** the shift and with hubs at rows 0/2 — the two index systems
  differ by the rotation; `[4,6,8]` in one is *not* `[4,6,8]` in the other.
* Audit-A's other claims (H1 fails for the C883 pair) stand; only the "label bug" reading is corrected.
* C886's numeric reading is confirmed: **all nine** ring edges have `|p_out|−1 = +2.62e−17 … +8.11e−17`
  (60-digit), i.e. every outer root sits on `∂D` and the convexification's interface hypothesis holds
  with equality; `|p_out| − (R+|serving hub|) > 0.10`, so the outer disks are far from the hub balls
  (the pin relaxation is domain-valid there).

---

## §3 5-chain elimination (hub A) and the V<R² deviation bound

**Chain structure (from the Delaunay complex).** Hub A (row 0) serves the 5-edge chain
`(6,4),(4,9),(9,10),(10,3),(3,5)`; hub B (row 2) serves the 4-edge chain `(5,7),(7,1),(1,8),(8,6)`.
The two chain-ends ("switch rings") are **row 5 and row 6** and they are shared by both chains.

**Theorem (elimination identity; no saturation assumed).** For pins `p_1..p_m`, radius r, any
`λ ∈ Δ`, `h_λ = Σλ_k p_k`, `V(λ) = Σ_{i<j} λ_iλ_j|p_i−p_j|²`:

```
Σ_k λ_k |h−p_k|² = |h−h_λ|² + V(λ)                       (exact, all h, all λ)
K := {h : |h−p_k| ≤ r ∀k} = ⋂_{λ∈Δ} B(h_λ, sqrt(r²−V(λ)))
⟹  diam K ≤ 2 sqrt(r² − Vmax),  Vmax = max_Δ V;  K = ∅ whenever Vmax > r²
```

Every member disk contains K, and the family adds no restriction beyond the vertices (the constraint
is affine in λ). Random verification: identity residual ≤4.1e−15; containment/vertex-separation/
empty-set/diameter tests 0 violations (`out/r20_5chain_elimination.txt §A`).

**Vmax structure.** On a 3-support face `V(λ) = ρ_S² − |h_λ−O_S|²` (verified 1.1e−13), so
`Vmax = max( max_{pairs} d²/4 , max_{3-supports with O_S ∈ conv S} ρ_S² )`.

**Equality geometry (the 5-chain, hub A) — NUMERIC READING, not a certificate (corrected per lead).**
3 of the 5 pins are active: `|H_A−p_k| − r ≤ 1.7e−16` and the barycentric weights of `H_A` in their
triangle are **all positive** `(0.45998, 0.08004, 0.45998)`. In the *idealised saturated* case
(`V(λ*) = r²` exactly) the C879 argument gives `K = {h_λ*}` and the hub equals the circumcentre of
the active pin triangle (a function of the ring data alone). At the recorded 17-digit-rounded object
the reading is `V(λ*) − r² = −3.63e−17` (60-digit), which is **not** an interval/proof-grade
certificate: the honest content is the conditional bound `|h−h_λ*| ≤ sqrt(r²−V(λ*)) = 6.03e−9` for
any `h` with `|h−p_k| ≤ r`, *given* the numerically computed pins/weights and the numerically
verified feasibility of the recorded `h`. This does **not** say the hub is forced (no uniqueness
claim beyond the ε-confinement) and `diam K ≤ 1.21e−8` is a numeric bound, not a certified one.
The remaining two pins are strictly inside (`|H_A−p_k| = r − 2.839e−3`) and only shrink `K`.

**V<R² case (hub B's 4-chain).** All four pins are active (`|H_B−p_k| − r ∈ [−3.3e−16, 0]`) but
their azimuths about `H_B` are `4.93°/54.55°/125.33°/174.95°` — max gap 189.98° > 180°, so the
directions **do not surround** `H_B` and the tangent cone of K at `H_B` is a wedge of aperture
≈9.98°: non-rigid. `Vmax = d²/4` for the pair (lead edges 0,3), `d = 0.757085538`, `2r−d = 2.882e−3`,
bound `2 sqrt(r²−d²/4) = 0.066124`, and the **bound is attained**: K is exactly the lens of diameter
0.066124 (verified vertex computation). So the deviation bound is tight in the non-rigid case and
degenerate (0) in the rigid case.

---

## §4 Central-endpoint coupling (how the two hubs are glued)

* Each switch ring's exposed rim arc has **one end tight for each hub**:
  row 5: left end = pin(8,0) with `|·−H_A|−r = −5.6e−17`, right end = pin(0,1) with
  `|·−H_B|−r = −1.1e−16`; row 6: left = pin(3,4) tight for `H_B`, right = pin(4,5) tight for `H_A`.
  So the joint coverage of a switch-ring arc is split between the two hubs at a pin, and each hub is
  pinned to one end of each switch-ring arc: the coupling is carried by four *equalities*, not by an
  inequality budget.
* The two central faces `(h_A,h_B,row5)` and `(h_A,h_B,row6)` have sides `0.716909/0.736132/0.422406`,
  circumradius `ρ = 0.379983853120 = R` (tight to 1.7e−16) and are **acute** (max angle 75.6°); on
  acute faces the circumradius criterion is two-sided, so `ρ ≤ R` may be used as a necessary glue
  condition there (see (F2′)).
* Calibration that the ring data determine the hubs (no use of the recorded hubs):
  `h_A^pin` := circumcentre of the three active pins (2 linear equations) gives
  `(−0.000162042986772, −0.149428411085191)` with radius `ρ_A − R = −1.1e−16`, matching the record to
  **1.29e−16**; then `h_B^glue` := solution of the two central equations `ρ(h_A^pin, ·, row5) = R`,
  `ρ(h_A^pin, ·, row6) = R` gives `(0.000296021328919, 0.272977305851806)`, matching the record to
  **5.4e−15** (residual ≤8.9e−16, and all four of B's active-pin margins ≤4.3e−15). The recorded
  hub pair is thus *reconstructed from the ring data* (to the rounding level) — the two-hub part of
  q0(6,7) reduces to a finite system in the ring variables.

---

## §5 Chain transfer map / rotation number (lead's analytic thread)

**Per-edge transfer map (exact).** With `d_i = |H−c_i|`, `s_i = arccos(d_i/(2r)) ∈ [0,π/2]`,
`θ_i = ∠(c_i−H, c_{i+1}−H)`:

```
ρ(c_i,c_{i+1},H) ≤ r    ⟺    |s_i − s_{i+1}| ≤ θ_i ≤ s_i + s_{i+1}
```

**Scope (corrected per lead).** Hypotheses: `d_i ∈ (0,2r)` strict, `θ_i ∈ (0,π)` (i.e.
`H, c_i, c_{i+1}` non-collinear, so `ρ = |c_ic_{i+1}|/(2 sin θ_i)` is defined); `d_i = 0` (ring at the
hub) and `d_i = 2r` (`s_i = 0`, tangency) lie outside. Endpoint reading: the upper endpoint
`θ_i = s_i+s_{i+1}` always lies in `(0,π)`, is non-degenerate and gives `ρ = r`; the lower endpoint
`θ_i = |s_i−s_{i+1}|` gives `ρ = r` only when it is `> 0` — if `s_i = s_{i+1}` the endpoint is
`θ_i = 0`, i.e. **collinear-degenerate, `ρ` undefined, and no pin equality there.**
Proof: law of sines `ρ = |c_ic_{i+1}|/(2 sinθ_i)` + law of cosines gives a quadratic in `cos θ_i` with
roots `cos(s_i+s_{i+1})`, `cos(s_i−s_{i+1})`. Verification: 0/3020 map mismatches; all-tight
construction `θ_i = s_i+s_{i+1}` gives `ρ = r` in 3000/3000; the other extreme `θ_i = |s_i−s_{i+1}|`
also gives `ρ = r` in 3000/3000 (non-degenerate instances). This **is** the "transfer map / rotation
number" form: the state is the spoke `s_i`, the transfer is the turn `θ_i`, and the per-edge extremes
are exactly the active pins — no pole cap needed. Note this **validly** re-derives the old
`cap = s_i + s_{i+1}` (law of sines), so `Σθ_i ≤ Σ(s_i+s_{i+1})` is a correct necessary condition;
D-CHAIN-6's "type mixing" verdict is corrected (C885 retraction) while its file family stays
non-citable.

**Chain-level corollaries.** `Σ|s_i−s_{i+1}| ≤ Σθ_i ≤ 2Σs_i − s_1 − s_m`; for a closed cycle about the
hub (all spokes ≤ 2r, `Σθ = 2π`): `Σ_i s_i ≥ π`, i.e. `Σ_i arccos(|H−c_i|/(2r)) ≥ π` — a genuine
(rotation-number) necessary condition linking the hub to the whole ring cycle.
Record cross-check: hub A's chain span `Σθ = 3.818062` vs cap sum `3.845880` (slack +0.0278), and the
tight edges are exactly the three active pins (edges 4,6,8; slack 0) while edges 5,7 have slack
`1.391e−2`; hub B's chain: `Σθ = 3.643824 =` cap sum (all four edges tight) — matching §3 exactly.

**Turn extremum vs abstract fan (scope, corrected per lead).** For the **turn** functional the
extremum is attained at pin equality, and an all-tight configuration exists for any spoke sequence —
**but that construction lives on an abstract fan** (arbitrary `H` and ring positions): it does *not*
produce a legal unit-`D` ring chain, where the spoke is additionally bounded by the annulus
(`s_i ≤ arccos((1−r−|H|)/(2r)) < π/2` from `|c_i| ≥ 1−r`) and the azimuth must realise the annulus
band. Hence it must not be cited as "the extremum over legal unit-`D` ring chains is tight"; that
question is the fixed-endpoint variation of §5.5.

**Earlier coverage-family example — relabelled (corrected per lead).** It moves **two** rings at once
(a common radial parameter), i.e. it is a 2-ring family, **not** the fixed-endpoint internal-ring
elimination: hub `(0.5,0)`, `r = 0.38`, pair at azimuths `±α`, common radius `L`, functional monotone
in `β(L)=arccos((1+L²−r²)/(2L))` whose max is the interior ridge `L* = sqrt(1−r²)`. It only exhibits
that a coverage-type functional can peak at an interior ridge with the legality slack (α = 20°:
`ρ = 0.320146`, slack `+5.985e−2`; α = 25°: maximiser at `ρ = 0.379999`, tight). The fixed-endpoint
version is treated next.

---

## §5.5 Fixed-endpoint local variation: identity, then deformation to an active pin

**Setting (lead's question).** Strict hub `H` (`|H| < 1−r`), radius `r`, two ring endpoints `c_L, c_R`
fixed, one internal ring `c` free; hypotheses: (H1) inward branch (`|H−p_in| ≤ r` with
`|H−p_out| > r`, so the pin criterion is equivalent to `ρ ≤ r`), (H2) the two **actual covered ties**
(the unit-circle equal-distance point of each pair is covered by both of its disks), (H3) the two fans
`ρ(c_L,c,H) ≤ r`, `ρ(c,c_R,H) ≤ r`, (H4) coverage (the internal ring's disk covers the boundary gap
between the two endpoint arcs), (H5) annulus `1−r ≤ |c| ≤ 1`. Evidence:
`out/r20_fixed_endpoint_variation.txt`, `tools/r20_fixed_endpoint_variation.py`.

**(Q1) The total span is an identity.** With the endpoints fixed and the internal arc inside the
endpoint span, the union's extreme boundary points are the endpoint arcs' outer ends, so
`span = 2(α + β(1))` is **independent of the internal ring** (verified in the instance:
`span = 1.811846137` rad, the two endpoint arcs already ending at `±51.9°` while every coverage-feasible
internal arc stays inside). Only the union **measure** can still depend on `c` (plateau/bridging vs
disjoint regime). So with fixed endpoints the internal ring is a pure *feasibility* variable — the
deformation question below is the right one.

**(Q2) Deformation to an active pin — affirmative in the tested family, via an explicit path.**
Instance: `r = 0.38`, `H = (0.5,0)`, `c_L, c_R` on `∂D` at azimuths `±α`, gap endpoints
`A', B'` at `±(α − 21.9056°)`. The feasible set
`F = {c : |c−A'| ≤ r, |c−B'| ≤ r, 1−r ≤ |c| ≤ 1, ρ(c_L,c,H) ≤ r, ρ(c,c_R,H) ≤ r}`.
Computed `sup_F max(ρ_1,ρ_2)` (≤ r by construction) for α = 22°,25°,27°,30°,33°,36°,40°,44°:
**the sup equals `r` in every case** (margin ≤ 2e−12), i.e. `F` meets the fan boundary and an active
pin is reachable. At the α = 30° witness `c = (0.669429096, 0.037145872)`:
`ρ_1 = r` (margin 1.4e−12), `ρ_2 = 0.312674685` (slack 6.7e−2) — **exactly one active pin**; both ties
actual (`|U−X| = |U−Y| = 0.344/0.370 ≤ r`), inward branch holds (`|p_out| = 1.042/1.013 ≥ 1`,
`|H−p_in| − r ≤ 0`). Explicit legal path: the straight segment from the natural configuration
`c_0 = (L_0, 0)`, `L_0 ∈ {0.70, 0.80, 0.90, 1.00}`, to the witness, sampled at 2e5 points, keeps
coverage slack `≥ +1.33e−2`, annulus slack `≥ 0`, `ρ_1 ≤ r`, `ρ_2` slack `≥ 5.9e−2` — so the
deformation is realized, not merely assumed.
**Scope**: this is a numeric exploration of one symmetric family (endpoints on `∂D`, hub on the
symmetry axis) and — decisively — **it lies outside the C464 canonical domain**: `|c_L| = |c_R| = 1 > L*`
(the old "annulus `[1−r,1]`" domain is likewise not the inward-root domain). It therefore **cannot**
be used as a global normal form. The canonical-domain version is §5.6, whose answer is negative.
Keep the two notions apart: the **inner-pin branch** (`|H−p_in| ≤ r`, hub-side, per edge) is *not* the
**ring radial inward root** (`|c_i| ≤ L*`, the C464 representative condition).

---

## §5.6 O5 is FALSE in the canonical domain: fixed-endpoint saturation fails, even strictly inward

Lead's counterexample (`lead/FIXED-ENDPOINT-SATURATION-COUNTEREXAMPLE.md`), independently audited
here by exact symbolic computation (no sampling): `tools/r20_o5_strict_inward_audit.py` →
`out/r20_o5_strict_inward_audit.txt`.

**`ε = 0` pinned configuration (verified exactly).** `r = 3/8`, `A = asin r`,
`q = cos A = √55/8 = √(1−r²)`, `H = (1/2,0)`, `c = (q,0)`,
`c_± = q(cos2A, ±sin2A) = (23√55/256, ±165/256)`; `cos2A = 23/32`, `sin2A = 3√55/32`, `|c_±| = q`; the
arc half-width at `|c| = q` equals `A`, so the endpoint arcs are `[A,3A]`, `[−3A,−A]` and the gap is
`(−A,A)`. The gap closure contains `U_± = (cos A, ±sin A) = (q, ±r)` with `|U_+ − U_-| = 2r` **exactly**
⟹ `B(U_+,r)` and `B(U_-,r)` are tangent and their intersection is the single point `(q,0)`: the
internal centre is **forced by coverage alone**, with no inward/outward-root hypothesis. There
`Rc² = 71/220 − 23√55/880` **exactly** (sympy difference `0`); `r² − Rc² > 0` ⟺ `√55 > 641/92`
(`55·92² = 465520 > 641² = 410881`), margin `r − Rc = 0.015980763`. So the internal ring is pinned with
both fans strictly slack and no deformation can activate a pin.

**Strict-inward robust family (verified; corrections per lead).** `t = q − ε`, `g = A − ε`,
`α = β(t) + g`, `c_±(ε) = t(cos α, ±sin α)`, `c_0(ε) = (t,0)`: `β(q) = A`, `β'(q) = 0`,
`β''(q) = −1/(qr) = −64√55/165`, so `β(t) − g = ε − (32√55/165)ε² + O(ε³) > 0` **for sufficiently
small `ε > 0`** — the Taylor form is orientation only, the remainder is not bounded here, and **no
explicit ε-threshold is claimed**; existence for small `ε` is all that is used. The gap is exactly
`(−g,g)`; every ring radius is `t < q` (strictly inward, the inner root of its own arc) and `t > 1−r`.
Every bridging centre lies in `L_ε = B((cos g,sin g),r) ∩ B((cos g,−sin g),r)`; summing the two
squared-distance inequalities gives `|c − (cos g,0)|² ≤ r² − sin²g`, and `r² − sin²(A−ε)` has the
**exact** closed form `−(23/32)sin²ε + (3√55/64)·sin2ε` (the expression `ε(3√55−23ε)/32` is only its
second-order truncation, not an equality), with centre `(cos g,0) → (q,0)`, so `L_ε → {(q,0)}`
uniformly. **Audit sharpening:** `L_ε` is *exactly* the bridging set for `2g < π` (a feasible `c`
with the antipode of its direction in the arc would need `|c| + 1 ≤ r`, impossible; hence the max of
`|c−x|` over the gap is at an endpoint). Continuity of both circumradius functions on the shrinking
lens (non-degenerate limit determinants) and the strict limit margin then give uniform strict slack
for all `c ∈ L_ε` at sufficiently small `ε` — hence no gap-preserving replacement can be tight: the
fixed-endpoint saturation normal form **fails on a compact family of
strictly inward configurations**, not only at the branch-merger radius.

**Scope.** This kills O5's universal form (fixed endpoints, internal ring free) inside the canonical
domain; it is a *local normal-form* failure and asserts nothing about a global 11-disk cover of `D`
(no claim that the patch extends to a cover). Method lesson: extremal elimination must also vary the
hub/endpoints, or carry explicit slack parameters.

---

## §5.7 Endpoint shape derivative under central-preserving hub variation (lead task)

Evidence: `tools/r20_endpoint_shape_derivative.py` → `out/r20_endpoint_shape_derivative.txt`
(40-digit mpmath; local derivatives by Richardson-extrapolated central differences; no grids).

**CORRECTION (per lead) — the "support selector" is WITHDRAWN.** For `K = ⋂_j B(p_j,r)` one only has
`h_K(u) ≤ min_j (p_j·u + r|u|)`, and the inequality is **strict in general**; the earlier
`h_K(u) = min_k(⟨p_k,u⟩+r)` and the "derivative carried by the active pin" were wrong.
Calibration (lead): two unit disks at `(±1/2,0)`, `u` vertical ⟹ `min_j h = 1` but `h_K = √3/2`.
Correct methods (`tools/r20_dual_support.py` → `out/r20_dual_support.txt`): (A) **dual / infimal
convolution** `h_K(u) = inf{Σ_j (p_j·u_j + r|u_j|) : Σ_j u_j = u}` (strong duality under Slater,
limits otherwise); (B) **finite boundary candidates** (no CQ): the support point is either on some
`∂B(p_j,r)` with outer normal `u/|u|` (`x = p_j + r u/|u|`, in all disks) or a pairwise circle-circle
intersection in all disks — the max over this finite set *is* `h_K`. Both agree on the calibration
(`√3/2`, dual weights **split**: `u_0^* = (1/(2√3), 1/2)`, `u_1^* = (−1/(2√3), 1/2)`). Correct
shape-derivative replacement: `∂h_K/∂p_j = u_j^*` (dual weight), finite-difference-verified on the
calibration (`±0.2886751`, `+0.5` vs predicted `±0.288675`, `+0.5`). On the record bodies the old
min-h overstates materially (`K_B`, `u = (0,1)`: `min-h = 0.685613` vs true `h_K = 0.339101`).
**Also withdrawn:** `M_A = 3.5e−17` is a *numerical* reading of a rounded object, not a proof of exact
zero (no "zero tolerance"); and first derivatives cannot bound a finite excursion
(`M_B/0.2047` came from an unbounded Taylor remainder) — they are local rates only.

**Quantifiers (fixed first).** Data: `r = lo`, the record ring 9-tuple in the resolved lead index
space, chain assignment (A = lead edges 4..8, B = 0..3), the two central faces `(h_A,h_B,row5)` and
`(h_A,h_B,row6)`. Family: `h_A` fixed, all ring centres fixed except one switch ring
`c_sw(t) = c_sw(0) + t·d`, and `h_B(t)` chosen on the same branch of **both central faces tight**
(`ρ(h_A,h_B,row5) = ρ(h_A,h_B,row6) = r`; closed-form circle-pair intersections of the tight sets,
branch-tracked). Control: at `t = 0` the re-solved hub B equals the recorded hub B to `1.8e−16`.

**Base readings (record object).** `M_A := r² − Vmax(A-chain) = +3.48e−17` (the A-chain is *exactly
saturated*, active triple = lead edges 4,6,8); `M_B = +1.0931e−3` (B-chain lens); `|h_A−h_B| =
0.422405965`; rotation slacks `slackA = 0.027818`, `slackB = 2.8e−15` (B-chain all edges tight);
central radii held `= r` by construction.

**Candidate derivatives `d/dt` at `t = 0`** (moved ring / direction → `M_A`, `M_B`, `slackA`, `slackB`):

| move | direction | dM_A/dt | dM_B/dt | d slackA/dt | d slackB/dt |
|---|---|---|---|---|---|
| c[4]=row6 | radial-out | −2.287e−1 | −2.311e−1 | −4.914 | −1.368e+1 |
| c[4]=row6 | radial-in | +2.287e−1 | +2.311e−1 | +4.914 | +1.368e+1 |
| c[4]=row6 | tangential+ | +1.115e−1 | −2.047e−1 | +2.396 | −3.300 |
| c[4]=row6 | tangential− | −1.115e−1 | +2.047e−1 | −2.396 | +3.300 |
| c[0]=row5 | radial-out | −2.287e−1 | −2.311e−1 | −4.914 | −1.368e+1 |
| c[0]=row5 | tangential+ | −1.115e−1 | +2.047e−1 | −2.396 | +3.300 |
| c[0]=row5 | tangential− | +1.115e−1 | −2.047e−1 | +2.396 | −3.300 |

**Verdict on the candidates.**
* The **rotation slack ledger is not a monotone quantity**: `slackB ≈ 0` at the record object
  (identity-like there) and both slacks' derivatives are O(1)–O(10) with direction-dependent signs
  that merely track the moves. Confirms the lead's warning: do not repackage it as a monotone
  invariant.
* The **chain-feasibility margins** `(M_A, M_B)` (equivalently `Vmax(chain pins) ≤ r²`) are the active
  quantities: the radial-outward motion of a switch ring (with the central faces kept tight) decreases
  **both** margins at rate ≈ 0.23, while `M_A = 3.5e−17` is numerically zero — so the radial-outward
  direction is the one in which the A-chain inequality is already at its boundary value (as a numeric
  reading of the rounded object, **not** a proven exact zero and **not** a zero-tolerance statement).
  Tangential directions have one margin increasing and the other decreasing (e.g. c[4] tangential+
  gives `dM_A/dt = +0.1115`, `dM_B/dt = −0.2047`). These are **local rates only**: no finite allowed
  excursion is claimed from them (first derivative + unbounded remainder cannot bound an excursion).
  So the candidate *stationarity direction* of the global chain inequality is the **radial-outward**
  one — the direction in which both chain inequalities move toward violation at first order.
* The **support functions**: WITHDRAWN as stated (see the correction block above). The true support is
  computed by the dual / finite-candidate method; its shape derivative is the **dual weight**
  `∂h_K/∂p_j = u_j^*` (split in general, concentrated only in the arc-interior case). On the record
  bodies the true supports differ materially from the old min-h values (`K_B`, `u = (0,1)`:
  `0.339101` vs `0.685613`), and the old table's `hK*` rows are superseded by
  `out/r20_endpoint_shape_derivative.txt` (regenerated with clear `hK` = true support vs
  `hmin` = upper-bound labels) and `out/r20_dual_support.txt`.

**Scope.** Local derivative readings at the rounded record object; `h_A` fixed and the two central
faces held tight are *choices* (a different choice gives a different family); nothing global is
claimed. The result identifies the pair `(M_A,M_B)` as the quantity to carry into the global
argument and the radial-outward direction as its active boundary — the finite-hub normal form (other
worker) supplies the complementary half of the argument.

---

## §5.8 Fiber infeasibility / separation certificates (Farkas + Helly-3)

Evidence: `tools/r20_fiber_farkas_certificate.py` → `out/r20_fiber_farkas_certificate.txt`.

**(F) Homogeneous Farkas ray (exact, no CQ).** If vectors `u_j` satisfy `Σ_j u_j = 0` and
`Σ_j (p_j·u_j + r_j|u_j|) < 0`, then `⋂_j B(p_j,r_j) = ∅`. Proof: a common point `x` would give
`⟨p_j − x, u_j⟩ ≥ −r_j|u_j|` for every `j`, i.e. `p_j·u_j + r_j|u_j| ≥ x·u_j`; summing yields
certificate value `≥ ⟨x, Σ_j u_j⟩ = 0`, contradiction. It is a dual ray for *primal infeasibility*,
so **no constraint qualification** is used. Sharpness: two unit disks at distance `d` with the axial
ray give value `2 − d` — `0` exactly at tangency `d = 2`, `< 0` only when the intersection is empty.

**(S) One-direction separation (same certificate in normal form; SIGN FIXED per lead).** For
`|u| = 1`, `u·q − r > h_K(u) ⟹ K ∩ B(q,r) = ∅`; the sharpest direction is `u = (q − x*)/|q − x*|`
with `x*` the point of `K` closest to `q`, and then `u·q − h_K(u) = |q − x*| = dist(q,K)`, so
**separation margin `= dist(q,K) − r` (> 0 needed)** and **Farkas objective `= r − dist(q,K)`**
(< 0 needed: it is *minus* the margin — never write "Farkas value = dist − r"). **Closure/CQ caveat
(lead's correction):** the infimal-convolution identity
`h_{⋂_j K_j}(u) = inf{Σ_j h_{K_j}(u_j) : Σ_j u_j = u}` holds in general only for the **closed**
inf-convolution; without a CQ (e.g. a common interior point) it is not an equality. We therefore rest
no weight on it: `h_K(u)` is computed directly from **finite boundary candidates** (arc points with
outer normal `u/|u|` plus pairwise circle intersections — a direct geometric argument, no duality),
and the certificate used is the **CQ-free product/diagonal separation** of (F)/(N). Dual weights are
quoted only as an interpretation. **Attainment caveat:** without Slater the dual optimum need not be
attained — for a *strict* gap an approximate dual certificate along an infimising sequence suffices,
so no attained optimum is assumed. This is the correct replacement for the withdrawn min-h
"selector": the weights are dual weights, not an active-pin indicator.

**(N) Necessity (analytic; added per lead).** For **any** finite family of closed disks with empty
intersection there **always** exist `u_j` with `Σ_j u_j = 0` and `Σ_j (p_j·u_j + r_j|u_j|) < 0`.
Proof by *diagonal strong separation in the product space*: `P = ∏_j B(p_j,r_j)` is compact convex,
`D = {(x,…,x)}` is a closed convex cone (a subspace), and `⋂_j B_j = ∅ ⟺ P ∩ D = ∅`. Compact `P` vs
closed convex `D` gives a linear functional `Λ = (Λ_1,…,Λ_m)` on `(R²)^m` with
`sup_P Λ < inf_D Λ`; `D` is a subspace through 0, so `inf_D Λ ∈ {0, −∞}`, forcing `Λ|_D = 0`, i.e.
`Σ_j Λ_j = 0`, while `sup_P Λ = Σ_j (p_j·Λ_j + r_j|Λ_j|) < 0`. So `u_j = Λ_j` is the certificate, and
**no constraint qualification is used**. Equivalent dual view (equal radii `r`):
`⋂_j B(p_j,r) ≠ ∅ ⟺ Rc(p) ≤ r` (Chebyshev-centre/minimum-enclosing-radius problem), so the criterion
is complete: *the Farkas ray exists iff the intersection is empty*.

**(H3) Universal exact three-disk witness (non-equilateral included).** Let `B(p_1,r),B(p_2,r),B(p_3,r)`
be closed disks with `Rc(p_1,p_2,p_3) > r` (then they have no common point, since a common point `x`
would give `|x−p_j| ≤ r` for all `j`, hence an enclosing circle of radius ≤ `r`). Let `m` be the
Chebyshev centre, `Rc` its radius, and `λ_j ≥ 0` with `Σλ_j = 1`, `Σλ_j p_j = m`, supported on the
active indices (`|m − p_j| = Rc`; for an **acute** triangle these are all three and `λ` is the positive
barycentric vector of the circumcentre). Put `u_j = λ_j(m − p_j)`. Then
`Σ_j u_j = (Σλ_j)m − Σλ_j p_j = 0`, and with `|p_j|² = Rc² + 2p_j·m − |m|²` (active `j`) one gets
`Σ_j (p_j·u_j + r|u_j|) = |m|² − Σλ_j|p_j|² + rRc = Rc(r − Rc) < 0`. Equilateral (`λ = 1/3`) is the
special case; the obtuse case is the diameter/MEC-on-two-points version (`λ = (1/2,1/2)` on the
longest side's endpoints).

**Exact non-equilateral control (rational, no radicals).** Triangle `p_1 = (0,0)`, `p_2 = (2,0)`,
`p_3 = (1,2)` (acute: largest side² `5 < 2² + 5 = 9`), circumcentre `m = (1, 3/4)`, `Rc = 5/4`,
barycentric `λ = (5/16, 5/16, 3/8) > 0`; take `r = 6/5` (so every pair of disks meets:
`max side/2 = √5/2 ≈ 1.118 ≤ 6/5`) while `r < Rc` (triple empty). Sympy-exact:
`u_j = λ_j(m−p_j) = [(5/16,15/64), (−5/16,15/64), (0,−15/32)]`, `Σ_j u_j = (0,0)` exactly, and the
Farkas objective is exactly `−1/16 = Rc(r − Rc) = (5/4)(6/5 − 5/4)` ✓ — a genuine Helly-3-necessary
case with an exact witness.

**Control at the record object.** For hub A, `dist(q,K_A) = r` **to 1e−16 for all four central fan
disks** — the hub lies exactly on each of the four tight circles, i.e. all four central faces are
saturated; `dist − r` and `r − dist` are `~1e−16` (boundary, no certificate). For hub B, one fan disk
is at distance exactly `r` (tight) and the others at `0.377101685 < r`; no certificate fires — as it
must, since the configuration exists. (The SLSQP dual cross-check agrees to `~1e−5` only.)

**Scope.** (F)/(N)/(S) give a complete CQ-free infeasibility criterion for the *convex disk* part of
the fiber. The non-convex fan condition (`(B(q_+) ∪ B(q_-)) \ (int B(q_+) ∩ int B(q_-))`, two
crescents) is **not** Farkas-reachable: excluding it needs the vertex/containment analysis (candidate
vertices of `K` inside the lens, or the crescents missed) — the piece to coordinate with the
geometry/Helly side. Numeric readings are 40-digit; no global claim.

---

## §5.9 Independent MEC/active-set audit of the central fiber triples (read-only on r20-geometry)

Evidence: `tools/r20_central_triple_mec_audit.py` → `out/r20_central_triple_mec_audit.txt`.
The geometry file `r20-geometry/central_tight_triple.py` was **read but not modified**.

**The exact criterion (no circumradius confusion).** For closed disks `B(p_j,r)` with centres `p_j`,
let `Rc` be the **MEC radius** of the centres and `m` the MEC centre. Uniqueness of `m` is justified
via the **squared** form (lead's correction): `max_j|x − p_j|` is *not* strictly convex (a single norm
is linear along rays), but `max_j|x − p_j|² = |x|² + max_j(|p_j|² − 2p_j·x)` is strongly convex plus a
max of affine functions, hence uniquely minimised, and the two problems are equivalent (`t ↦ t²`
increasing on `[0,∞)`). Then:
`⋂_j B(p_j,r) = ∅ ⟺ Rc > r`; `⋂_j B(p_j,r) = {m} ⟺ Rc = r`; `⋂_j B(p_j,r)` has interior `⟺ Rc < r`.
Moreover `m` is the MEC centre ⟺ `0 ∈ conv{(m − p_j)/|m − p_j| : j active}` (max cyclic gap ≤ 180°);
in the *saturated* configuration (all `|m − p_j| = r`) this vertex test is equivalent to the
singleton test — which is why the half-plane test is legitimate **only** under saturation, and why
the branch matters: the circumcircle is the MEC **only** in the acute branch, elsewhere the diameter
branch is the MEC.

**Audit results (reproducing geometry's `ψ` list exactly, plus λ and the MEC centre).** All 35 triples
of `{central0, central4, five fan pins}`: the four triples geometry flags are indeed the only ones with
`Rc − r` numerically zero (`−6.09e−17`, `−4.58e−17`, `−4.31e−17`, `−2.73e−17`, all circumcircle
branch), and for each of them the MEC centre coincides with the hub B to `~1e−16` — the independent
consistency check the theorem predicts. For the lead-quoted triple
`(central0, central4, pin(9,10))`: `Rc − r = −4.31e−17`, active set = all three, positive barycentric
`λ = (0.321374, 0.321374, 0.357253)`, MEC centre = hub B to `8.5e−17`, cyclic gaps
`(112.47°, 123.77°, 123.77°)` — **max gap 123.77° ≤ 180°, not 189°**; the 189° figure belongs to
geometry's other (fan-A/4-pin) gap list, exactly as their own correction note in
`central_tight_triple.py` line 99 states. Every entry is a **numerical** reading: `|Rc − r| ~ 1e−17`
is reported as "numerically tight" and **no exact equality is inferred** (lead's rule). The Farkas
objective `Rc(r − Rc)` is `+1.6e−17` (0 to rounding) for that triple — correctly *no* infeasibility,
since the triple is feasible and, at exact saturation, its intersection is the singleton hub.

---

## §5.10 Chain extent as an optimal-control problem — **ROUTE RETRACTED (lead audit)**, definitions only

**Status: all inferential claims withdrawn, item by item; see DEAD.md D-CHAIN-16/16b.** What survives
is only the *definitional* framework; nothing here may be cited as a bound, a normal form, or an
optimisation identity.

Retractions (each with its reason):
* **Direction error.** `s = arccos(|H−c|/(2r))` is **decreasing** in `|H−c|`, so maximising `Σ_int s_i`
  pulls rings **toward** the hub — my text said "away". Any optimisation claim built on the reversed
  direction is void.
* **No tightness from monotonicity + compactness.** The assertion "at the extremum every `|H−p_j| = r`"
  was never proved, and extremality does not imply *deformability* (that was a conflation).
* **No convexity.** The ring domain (annulus) is not convex and the pin map is not convex, so the
  "convex problem, boundary-attained" claim is unsupported.
* **`Θ ≤ cap` is pointwise only** — it does not give `Θ_max = cap_max` nor identify a maximiser.
* **`K ≠ ∅` eliminates `H` only from feasibility.** When the objective (`s_i`, `Θ`) depends on `H`, `H`
  must be carried (or optimised over `H ∈ K`); dropping it and then evaluating `H`-dependent quantities
  is illegal.
* **The "legal chain" counterexample (D-CHAIN-16b) is withdrawn as stated**: that 3-ring example
  satisfies only the *pin–hub* condition, not the C879/chain interface (its arcs are disjoint), so
  calling it a legal chain was wrong; it shows only that the pin–hub condition alone does not force
  contiguity of the covered arcs.

**Definitional framework (kept, no inference).** Domain per ring `D_ring = {c : 1−r ≤ |c| ≤ L*}`; pin
map `p_i = Pin(c_i,c_{i+1})` (inner root of the two radius-`r` circles through the pair, defined iff
`|c_i − c_{i+1}| ≤ 2r`); running hub body `K_i = ⋂_{j≤i}B(p_j,r)` with `K_i ≠ ∅ ⟺ MEC(p_1..p_i) ≤ r`
(ring-only feasibility, no hub variable); transition `K_{i+1} = K_i ∩ B(p_{i+1},r)`. `K` is intended as
a *region*, so all-slack configurations are representable (the lead's FIXED-ENDPOINT-SATURATION state
included) — but that only says the state space is expressive, **not** that any DP value has been
computed or bounded.

**Record readings kept only as observations** (not as bounds): prefix-MEC walk
`−3.800e−1, −2.394e−1, −9.985e−2, −1.759e−2, −4.580e−17`; `Θ = 3.818062137` vs cap `3.845880194`;
covered-arc span (E1) `227.733°` *under the contiguity hypothesis*.

---

## §5.11 Fixed-H single-ring phase optimisation — exact max/min and admissible phase intervals

Evidence: `tools/r20_single_ring_phase_exact.py` → `out/r20_single_ring_phase_exact.txt`.
This is the lead's new concrete obligation: **one ring, fixed hub, exact** — no chain inference.

Setting: unit boundary circle, radius `r`, fixed strict hub `H` (`|H| < 1−r`), ring centre `c` with
fixed inward radius `rho = |c| ∈ [1−r, L*]`; spoke angle `s(c) = arccos(|H−c|/(2r))`.

**(P1) Covering a gap = covering its endpoints.** Along the gap, `x ↦ |c−x|` is maximal at an endpoint
unless the antipode of `c`'s direction lies inside the gap; there `max = |c| + 1 > r` because
`|c| ≥ 1−r`, so such `c` cannot cover the gap anyway. Hence for admissible `c`:
`c overs the gap ⟺ |c−U_1| ≤ r and |c−U_2| ≤ r` (`U_j` = the gap's endpoints).

**(P2) Admissible phase interval.** With `c = rho(cos φ, sin φ)` and `a := arccos((1+rho²−r²)/(2rho))`
(the ring's own boundary half-width, `a = β(rho)`):
`|c−U_j| ≤ r ⟺ cos(φ−v_j) ≥ cos a ⟺ φ ∈ [v_j − a, v_j + a]`, so the admissible phase set is exactly
`Φ(rho; v_1,v_2) = [v_2 − a, v_1 + a]`, **nonempty ⟺ `v_2 − v_1 ≤ 2a`** (gap not wider than the ring's
arc). The antipode condition of (P1) is automatic (`a < π/2`).

**(P3) Distance quadratic.** `|H−c(φ)|² = |H|² + rho² − 2 rho|H| cos(φ − ψ_H)`, `ψ_H = arg H`: unimodal
on the circle, minimum at `φ = ψ_H`, maximum at `ψ_H + π`.

**(P4) Exact extrema.** Since `s` is *decreasing* in `d = |H−c|`:
`s_max = arccos(d_min/(2r))` at the **closest angular phase** (the projection of `ψ_H` onto `Φ`), and
`s_min = arccos(d_max/(2r))` at the **endpoint phase** `φ_lo` or `φ_hi` (or at `ψ_H + π` if it lies in
`Φ`). All closed-form, no iteration.

**(P5) Two constraints.** If the ring must serve two gaps, the admissible set is the **intersection of
the two intervals** — listed rigorously as empty / a single phase / an interval.

Calibrations in the output: (i) the lead's O5 configuration (`r = 3/8`, `H = (1/2,0)`, `rho = √55/8`,
gap `(−A,A)`): `a = A` exactly and `Φ = {0}` — the singleton pinning reproduced by the exact formula;
(ii) record-object values (`rho = 0.700870`, `β(rho) = 0.280822`): gap `0.4 rad` gives
`Φ = [−0.080822, 0.080822]`, `s_max = 0.383073159272` at the closest phase `−0.080822`,
`s_min = 0.288862878919` at `+0.080822`; (iii) two-gap cases: overlapping → interval, "touching" →
single-phase interval `[−0.319222, −0.319178]`, far-apart → intersection empty.

**Scope.** One ring, fixed hub, exact phase statements only. No chain/tightening inference is drawn.

**Corrections applied (lead, 2026-09-25b).** (P1) needs the **short-gap hypothesis** (`v_2 − v_1 ≤ π`):
with the same endpoints the *long* arc is not covered by a disk that covers both endpoints (a disk
covers at most `2a ≤ π`), so the equivalence is stated for the short gap only. (P4) `s` is **defined
only for `d ≤ 2r`**, so the true domain is `Dome = Φ ∩ {φ : d(φ) ≤ 2r}` (again a cosine interval),
intersected before optimising; the projection of `ψ_H` and the farthest phase are computed
**circularly mod 2π**; `H = 0` is handled separately (`ψ_H` undefined, `s ≡ arccos(rho/(2r))`).

---

## §5.12 Single-chain span bound from inner-pin body + arc order — slack test at the saved candidate

Evidence: `tools/r20_chain_span_bound.py` → `out/r20_chain_span_bound.txt`. Task per lead: build a
**necessary** span inequality (no tightness), eliminate `φ` in closed form, allow **upper bounds only**
(no "equal max"), then **compare the saved candidate's slack** and decide whether to continue.

**(T1) φ-free per-ring upper bound.** `s(c) = arccos(|H−c|/(2r))` is defined for `|H−c| ≤ 2r` and is
decreasing in `|H−c|`; over all phases `|H−c| ≥ ||H| − rho|`, with equality at the radially aligned
phase. Hence `s_i ≤ arccos(||H| − rho_i|/(2r))` — closed form, **no phase knowledge needed**.
**(T2)** the phase-restricted version is `s_i ≤ arccos(d_min(Dome_i)/(2r))` with `Dome_i = Φ_i ∩
{d ≤ 2r}` and `d_min` at the circular projection of `ψ_H`.
**(T3) chain span inequality (necessary; upper bound only; pointwise):**
`Θ = Σθ_i ≤ s_1 + s_{m+1} + 2Σ_int s_i ≤ s_1^max + s_{m+1}^max + 2Σ_int s_i^max` (transfer cap, valid
for every legal chain; **no attainability claimed**).
**(T4) cover width (necessary):** `Σ_all 2β(rho_i) ≥ 2π` for an n11 cover (the dual's "total width"),
and `Σ_chain 2β(rho_i) ≥ L_chain` for a chain serving the arc `L_chain`.

**Slack test at the saved candidate** (record object; hub A's 6-ring chain; `|H| = 0.149428`).
Per-ring `s_max(T1) − s_actual` = `+5.078e−1, +2.494e−1, +3.601e−2, +3.601e−2, +2.494e−1, +5.078e−1`;
chain bound (T3) `= 6.003071810957` versus actual `Θ = 3.818062137086` ⟹ **slack `+2.185`** (the
transfer cap's own slack is `2.78e−2`; the φ-free relaxation multiplies it) — **does not vanish**.
(T4): global `Σ 2β(rho_i) = 6.283185307180` vs `2π` ⟹ slack `+4.43e−16`; chain union
`3.974694425868` = `Σ 2β` ⟹ slack `+4.44e−16` — **vanishes to rounding** (arcs tile), i.e. exactly the
*total width* slack already carried by the closure dual C817/C818.

**Verdict (lead's decision rule).** The span bound built from the inner-pin body + arc order does
**not** vanish at the saved candidate (slack `≈ 2.19`; even the bare transfer cap is slack by
`2.8e−2`), so it is **not worth continuing as a dual-active constraint**; the vanishing quantity is the
width/tiling identity the dual already contains. The transfer cap stays a valid per-configuration
inequality but is slack at the optimum. No tightness or attainability claim is made anywhere.
**Status: the span route is PAUSED as non-sharp (lead).**

---

## §5.13 Gradient margin from positive weights + σ_min(A|T_perp) (analytic; rigidity interface)

Evidence: `tools/r20_gradient_margin_bound.py` → `out/r20_gradient_margin_bound.txt`.

**Setting.** 18 active gradient rows `g_1..g_18` in the rotation 21-dimensional slice; row map
`A: R^21 → R^18` of rank 17, kernel `K = ker A` of dimension 4, `T_perp = K^⊥`; positive weights
`w_i ≥ w_min > 0`, `Σ_i w_i = 1`, `Σ_i w_i g_i = 0`.

**Lemma (proved; no LP, no CQ).** For `t ∈ T_perp`, `t ≠ 0`, put `a = At` (`a_i = ⟨g_i,t⟩`). Then
`Σ_i w_i a_i = 0`, hence `Σ_i w_i|a_i| = 2Σ_{a_i>0} w_i a_i`; if all `a_i ≤ 0`, positive weights force
`a = 0`, i.e. `t ∈ T_perp ∩ K = {0}`. So for `t ≠ 0` some `a_i > 0` and
`max_i a_i ≥ (Σ_{a_i>0} w_i a_i)/(Σ_{a_i>0} w_i) ≥ ½Σ_i w_i|a_i| ≥ (w_min/2)‖a‖_1 ≥ (w_min/2)‖a‖_2`,
giving **`max_i ⟨g_i,t⟩ ≥ μ‖t‖` with `μ = w_min·σ/2`**, `σ := σ_min(A|_{T_perp})` (the smallest
*nonzero* singular value of `A`). The suggested `w_min·σ/√18` is valid but weaker: sign control comes
from the weights (`Σw = 1`, `w ≥ w_min`), not from `‖a‖_∞ ≥ ‖a‖_2/√18`.

**Exact interface for σ (minor inverse; SQRT CORRECTED per lead, 2026-09-25c).** With `G = A A^T` one
has `λ_min(G) = 1/‖G^{-1}‖_2`, hence
**`σ = √(λ_min(G)) = 1/√(‖G^{-1}‖_2) ≥ 1/√(‖G^{-1}‖_F)`** — the earlier form `1/‖G^{-1}‖_F` (which I
had used) is valid but weaker, and my synthetic calibration did not expose the missing square root
because there `‖G^{-1}‖_F > 1`. For rank-17 `G` and any 17-row set `S`, Cauchy interlacing gives
`λ_min(G_{S,S}) ≤ σ²`, so if `G_{S,S}` is invertible then
**`σ ≥ 1/√(‖G_{S,S}^{-1}‖_F)`** and **`μ ≥ w_min/(2√(‖G_{S,S}^{-1}‖_F))`** — finite, exact, SVD-free.
**Stronger, on the corrected rank-18 object** (deflated Gram `G' = G − σ18²u18u18^T`, see the
correction block below): `σ17 ≥ 1/√(‖(G'_{S,S})^{-1}‖_F)`, measured `5.674473e−2 ≤ σ17 = 5.841991e−2`
⟹ rigorous `μ_lower = 2.808861e−4`.

**Calibration** (random instances with `Σw_i g_i = 0` built exactly; 200 random `t ∈ T_perp` each):
worst `max_i a_i/‖t‖` = `1.238, 1.157, 1.231` versus `μ = 0.006362, 0.003657, 0.003990` ✓; interface
`1/√(‖G_S^{-1}‖_F)` ✓ (now with the sqrt) with `μ_interface ≤ μ` ✓; the lead's weaker form ✓. Random
runs are calibration only; handed to rigidity as an interface, no operator construction duplicated.

**CORRECTION 2026-09-25d — my 2026-09-25c "correction" was itself based on a float64 FD artifact, which
`cline2-r23-rigidity` then refuted with the exact-formula jet.** The float64 differenced matrices
(`r20-rigidity/r20_J60.npy`, `r20_JA_analytic.npy`) have a finite-difference noise floor of order
`1e-9`, so their tiny singular value `σ18 = 2.411015e−9` and the "no exact positive relation"
conclusion (`τ = 6.57e−10`) are **numerical artifacts, not geometry**. With the exact-formula jet
(`r20_physical_kkt_kernel.py`, dps = 50, no differencing) the same physics gives `σ18 ≈ 6e−17` and the
**exact** kernel has dimension **5 = 2 Sym + 3 Anti (including rotation)**, so **on the rotation slice
the kernel is 4-dimensional, `rank = 17`, and `T_perp` is 17-dimensional** — i.e. the lead's original
premise ("rank 17, kernel 4") is the correct one. Moreover on the exact jet
`τ = min_{λ∈Δ}‖J^Tλ‖ = 1.8e−59` with the minimising vector's 18 components all **positive**
(min `9.8947e−3`), so the **exact positive-weight relation of C897 holds** and **(C1) IS applicable**
on this object; (C2) is only its numerical surrogate (still valid, with my factor-2 `ρ` refinement).
Consequently:
* the "`v18` soft direction / first-order descent" piece of (C3) **is dropped**: that direction is in
  the kernel, not a near-null direction of the real operator; the architecture is
  `21 = K(4) ⊕ T_perp(17)`;
* the "vacuous bound" reading is withdrawn as an artifact; with (C1) available the relevant margin is
  `μ = w_min·σ17/2` with `σ17 = 5.841991e−2` (both sides agree on this well-separated value);
* **method lesson (also in DEAD.md)**: verifying a claim by *loading a saved float64 differenced
  artifact* reproduces the artifact's noise floor — bearing checks must use the exact-formula jet
  (or interval) data, and a singular value at the FD noise scale must be treated as zero until the
  exact jet says otherwise.
Rigidity side (current, r23): square-minor interval route (no sqrt, per lead) gives
`σ17 ≥ 1/‖M^{-1}‖_F ≥ 2.242496e−3` with pivot guards and a candidate interval `μ ≥ 1.109440e−5`
(`r20_anti_sigma_interval.py/.json/.log`). The Gram-based sqrt route
`σ ≥ 1/√(‖G_S^{-1}‖_F)` remains available as an independent (usually stronger) interface.

**Retraction (lead audit, 2026-09-25): the whole block that stood here (the §5.10 "optimal-control route") is WITHDRAWN** — item-by-item reasons in `DEAD.md` D-CHAIN-16/16b and in the header of this section.  It is kept only as a pointer so the withdrawn claims are not re-derived.

---

## §6 Scope, caveats, open items

* All §3–§5 statements about the record object are **numeric readings at the 17-digit-rounded
  coordinates** with `r = certified_interval.lo` (60-digit where stated); the "equality" readings
  (V−r², ρ−R, |H−pin|−r) are ~1e−16-level, i.e. the recorded object is a rounded optimum. The
  idealised (exactly saturated) versions are the theorems; the numbers are their ε-versions. In
  particular the 5-chain "`V ≈ r²`" reading must **not** be written as "the hub is forced" nor as a
  certified `diam ≤ 1.21e−8` (§3); it is a conditional numeric confinement.
* The pin relaxation used for K is valid **under the domain hypothesis** (`|p_out| ≥ 1`,
  `|h| < 1−r`), which holds on all nine edges of the record object (§2); without it only the product
  form (F3′) applies.
* Not re-scanned: the C883 counterexample pair (already retracted, out of the convexification's
  domain). r21 route inactive; no sub-delegation used; sole writer for this directory.
* Open: (i) interval/proof-grade certification of the §3/§5 equalities (currently 60-digit numeric);
  (ii) whether the ring-determined hub pair (circumcentre + 2 central equations) can be upgraded to a
  *counting* statement for the global bound; (iii) **O5 is closed negatively** (§5.6): the
  fixed-endpoint "make one pin active" normal form fails (audited counterexample + strict-inward
  family), so the chain ledger must carry explicit slack parameters or vary the hub/endpoints;
  (iv) whether the *whole-cover* version (allowing hub and endpoints to move) has a valid normal form
  is untouched by §5.6 and remains open.

## §7 Repro

```
cd research-2026/team-current/r20-chain/tools
py -3 audit_lead_q0_map.py             # -> out/audit_lead_q0_map.txt
py -3 audit_c880_889.py                # -> out/audit_c880_889.txt
py -3 r20_5chain_elimination.py        # -> out/r20_5chain_elimination.txt
py -3 r20_transfer_map.py              # -> out/r20_transfer_map.txt
py -3 r20_fixed_endpoint_variation.py  # -> out/r20_fixed_endpoint_variation.txt
py -3 r20_canonical_tight_boundary.py   # -> out/r20_canonical_tight_boundary.txt
py -3 r20_o5_strict_inward_audit.py     # -> out/r20_o5_strict_inward_audit.txt
py -3 r20_endpoint_shape_derivative.py  # -> out/r20_endpoint_shape_derivative.txt
py -3 r20_dual_support.py               # -> out/r20_dual_support.txt
py -3 r20_fiber_farkas_certificate.py   # -> out/r20_fiber_farkas_certificate.txt
py -3 r20_central_triple_mec_audit.py   # -> out/r20_central_triple_mec_audit.txt
```
