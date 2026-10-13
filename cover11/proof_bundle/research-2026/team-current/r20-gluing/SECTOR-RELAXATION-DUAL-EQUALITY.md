# SECTOR-RELAXATION-DUAL-EQUALITY (repaired) — convex angular-sector box bound, exact duality, and a pilot B&B design

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. **No claim registered.** Conventions: the
oracle value `V(U)` is the *radius* (`‖c−U‖ ≤ V`, lead's `FIXED-SWITCH-SOC-REDUCTION.md` §2); the
geometry lane's squared variable is `t = V²`. Loads follow the lead note §3: vectors `p_e` with
divergence `0` at every free node and `Σ_e‖p_e‖ ≤ 1`, giving `V(U) ≥ Σ_i l_i·U_i`. The only threshold
mentioned is `R*` (C891 exact-root radius).

## 1. Per-box sector relaxation — keep the anchor `U_i` JOINT

A box gives each anchor an angular interval `[θ_{i,lo}, θ_{i,hi}]`; `A_i` is the closed arc and
`S_i = conv(A_i) = (unit disk) ∩ (one chord half-plane)` its sector.

```
min r  over  c (11 sites), z (11 aux), U (9 anchors), r
s.t.  U_i ∈ S_i
      ‖c_s − U_i‖ ≤ r   (each endpoint incidence, with the SAME U_i shared by its two sites)
      ‖c_s − z_f‖ ≤ r   (each face incidence)
```
*Convexity*: the set `{(c, U, r) : U_i ∈ S_i, ‖c_s − U_i‖ ≤ r}` is convex in the **joint** variables
(second-order cone intersected with a convex sector constraint), and the face cones are second-order
cones; the objective is linear. So the relaxation is convex.

**Correction (lead).** One must **not** replace each endpoint incidence by `dist(c_s, S_i) ≤ r`: the two
sites of one anchor share the same `U_i`, and although single-edge projection is equivalent
(`∃U∈S_i: ‖c−U‖≤r ⟺ dist(c,S_i)≤r`), the **conjunction** is not — both balls can each meet the sector
while their common intersection with the sector is empty. The joint variable `U_i` must be kept.

*Soundness*: for every genuine anchor tuple `U⁰` with `U⁰_i ∈ S_i`, the fixed-switch feasible set at
`U⁰` is contained in the relaxed feasible set, so `LB(box) := (relaxed optimum) ≤ min_{U∈box} V(U)`.

## 2. Conic dual (repaired: budget `≤ 1`, no anchor balance)

Loads `y_e` (18 endpoint cones) and `y_k` (33 face cones); the anchors are *variables* minimised over
their sectors, so no balance condition is imposed at them:
```
norm budget:        Σ_e ‖y_e‖ + Σ_k ‖y_k‖ ≤ 1        (a BALL — the equality Σ‖·‖ = 1 is a sphere and
                                                      is NOT used; with r ≥ 0 the ball is the right
                                                      dual-feasible set, equality at the optimum)
free-node balance:  Σ_{e,k at s} y = 0 at each of the 22 free nodes (11 sites + 11 aux)
objective:          max  Σ_i min_{U ∈ S_i} ⟨ l_i , U ⟩ ,    l_i := Σ_{e at anchor i} y_e
```
*Attainment/duality*: for a non-degenerate arc, `S_i` has non-empty interior, so a strictly feasible
primal point exists (`U_i ∈ int S_i`, `c_s = U`, `z_f = c`, `r` large) and Slater gives strong conic
duality with the dual attained. For a **degenerate (singleton) arc** no strict interior exists; use the
minimax route of §3 instead of Slater — it needs only compactness/convexity.

## 3. No hidden loss, and the degenerate/major-arc cases

**Extremality.** `⟨l_i, ·⟩` is linear and `S_i` is compact convex with extreme points exactly `A_i`, so
`min_{U ∈ S_i} ⟨l_i, U⟩ = min_{θ ∈ [θ_{i,lo}, θ_{i,hi}]} ⟨l_i, U(θ)⟩`. Hence the relaxed optimum equals
```
max over dual-feasible loads  Σ_i  min_{θ ∈ [θ_{i,lo},θ_{i,hi}]} ⟨l_i , U(θ)⟩  ,
```
i.e. exactly the **standard fixed-force angle-min** (separated per anchor; cos endpoint/critical rule
with the minimiser at `φ_i + π`, `φ_i = arg l_i`) — no hidden loss.

**Minimax route (also covers degeneracies).** The dual-feasible load set is compact convex (linear
balances + the norm *ball*) and `S = Π_i S_i` is compact convex; the pairing is biaffine and the inner
problems are convex, so Sion's minimax theorem gives `max_P min_S = min_S max_P`, matching the
separated form. This route needs no strict interior, hence it is the one to quote for singleton arcs.

**Corrections on arc length (lead).** (i) For an arc with `length < 2π` — including **major arcs**
`> π` — the sector is the **disk cap** `disk ∩ chord half-space`, *not* the whole disk; its extreme
points are the arc, and the extremality argument is unchanged. (ii) Only the **full circle** gives
`S_i =` the whole disk (extreme points = the circle itself). (iii) A **singleton** arc gives
`S_i = {U_i}` (degenerate, no interior) — handled by the minimax route.

## 4. Pilot B&B design (proposal only — not implemented)

**Domain.** `P = {Δ ∈ [m, L]^9 : ΣΔ = 2π}`, `L = 2asin(19/50)`, `m = 2π − 8L > 0`, 8-dimensional,
compact, with `U_0` fixed by rotation. Every vertex of `P` has at most one coordinate strictly between
`m` and `L`; `P` is the base simplex `{Δ ≥ m, ΣΔ = 2π}` with its corners cut by `Δ ≤ L` — a *deficit*
polytope.

**Sector relaxation per simplex.** Take a simplicial piece `σ` of a decomposition of `P` (a
"deficit tetrahedral" decomposition in the 8D sense: simplices whose vertices are vertices of `P`).
For `σ`, each cumulative angle is a linear image of `σ`, so its exact range is an interval
(`θ_i ∈ [θ_0 + Σ_{j<i} lo_j, θ_0 + Σ_{j<i} hi_j]` with the simplex's own `lo_j, hi_j`); this defines
the arcs/sectors of §1 and hence `LB(σ)` — a small convex problem (22 free nodes + 9 sector anchors).

**B&B loop (proposed).** Maintain a list of pieces with `LB(σ) < R*` (start: the whole `P`, or the
first-level simplices). Split a piece (e.g. bisect its longest `Δ`-range) and re-solve; discard any
piece with `LB(σ) ≥ R*` (certified). Terminate when the list is empty — that proves `min_P V ≥ R*`
(modulo the local neighbourhood of C909/C910, which covers `U*` and needs no box) — or when a piece
stops shrinking above `R*`, which is *route information* (a missing necessary condition there), never a
refutation of the goal.

**Cost/flags.** Each node is a tiny SOCP; the simplex decomposition must be fixed before the loop (so
that pieces are comparable); the anchor sectors use exact interval ranges (no grid); no upper bound for
`R*` is used anywhere; and `𝒩` (the existential local neighbourhood) is never selected against.

**Calibration (cheap, allowed).** On a single small test piece, evaluate both routes of §2–§3 — the
convex relaxation and the separated load-field bound with a certified field — and compare; agreement
measures the "no hidden loss" statement in practice and fixes the per-piece budget before any sweep.
