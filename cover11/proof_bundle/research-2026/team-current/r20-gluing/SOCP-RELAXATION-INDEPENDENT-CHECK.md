# SOCP-RELAXATION-INDEPENDENT-CHECK — fixed-switch relaxation, candidate numbers, and the dual question

**Lane**: r20-gluing (cline2-r23-gluing). Read-only; **no claim registered**. Checked item: the lead's
fixed-switch SOCP relaxation (message + `lead/CLIPPED-DUAL-STRAIGHT-EMBEDDING.md`), against claim
**C897** (positive KKT split weights at the exact candidate) and **C906** (pin/fan-only sufficiency
fails). Own computation: `socp_fixed_switch_check.py` / `.json`.

## (a) Is the representation valid? — YES, with the exact scope stated

Fix the nine boundary switches `U_i ∈ ∂D` and the q0 graph (11 faces). Variables `c` (11 sites, 22),
`z_f` (11 aux, 22), `r`; constraints

* **18 endpoint constraints**: for each ring `i`, `|c_i − U_i| ≤ r` and `|c_i − U_{i−1}| ≤ r`;
* **33 cone constraints**: for each face `f` and each of its three sites, `|c − z_f| ≤ r`
  (equivalently: the face's MEC ≤ r, which is the convex/existence form; the *circumradius* form
  would be non-convex).

Every constraint is a second-order cone with a variable radius, the objective `min r` is linear, and
the variables are unrestricted ⇒ **SOCP / convex** ✔. **Necessity (relaxation) ✔**: from a genuine
cover, take `c` = sites; `z_f` = the primal Voronoi vertex `x_f ∈ int D` of face `f`, so each face site
satisfies `|c − z_f| = r_{x_f} ≤ r` (the vertex is covered); at a switch `U_i` the two adjacent sites
are at distance `ρ_i ≤ r` while all others are `> r` (VORONOI §1/§3), so the endpoint constraints hold.
Hence `SOCP_min(U) ≤ r(cover)` ✔, and the global bound reduces to a search over the **8 switch angles**
(9 points on `∂D` up to rotation) with a convex inner problem ✔ — a genuine reduction from the 17
ring coordinates. The relaxation need not be realizable by an embedding ✔ (sites are otherwise free).

**One structural finding the dual question must respect.** In this *free-site* form the Lagrange dual
of `min r` is **degenerate**: `g(w) = inf_{c,z,r} [r + Σ w_j(‖·‖ − r)] = 0` whenever `Σ w_j = 1`
(choose `c = U`, `z_f = c`), and `−∞` otherwise. So **no non-negative multiplier vector certifies a
positive value for this min-r problem**; a *positive* bound has to be certified in the **fixed-r
infeasibility form** (Farkas/Helly on: the 9 lens constraints `c_i ∈ B(U_{i−1},r) ∩ B(U_i,r)` plus the
11 MEC cones), where the pairing of the two endpoint constraints per ring already yields the elementary
certificate `r ≥ max_i |U_{i+1} − U_i| / 2`.

## (b) Candidate numbers (`socp_fixed_switch_check.py`)

* **All nine switches are tight**: `ρ_i = |c_i − U_i| = |c_{i+1} − U_i| = r = 0.3799838531198387…`
  (nine digits shown; consistent with VORONOI §3's `ρ_i = r ⟺ o_i = 0`, i.e. the arcs touch at the
  candidate). So all 18 endpoint constraints are active at the candidate.
* **Chord bound**: `max_i |U_{i+1} − U_i|/2 = 0.378542769 < r` — a valid but weaker bound; the
  individual chords are `0.747432, 0.757086, 0.747432, 0.554291, 0.668564, 0.726975, 0.726975,
  0.668564, 0.554291` (diameter-2 arcs).
* **The 11 faces: all eleven are acute** ✔ — every circumcentre lies strictly inside its triangle
  (barycentric coordinates all `> 0.22`), so no MEC/circumradius discrepancy arises and the per-face
  cone condition below is strictly solvable. Face types: 2 central (both hubs: `(0,9,10)`, `(4,9,10)`)
  and 9 fan (5 with hub 9, 4 with hub 10) — hub degrees `(7,6)`, `E = 21` ✔.
* **Tight/slack**: exactly **9 of 11 faces are tight** at `r` — the 7 fan + 2 central matching C897's
  active-branch list — and the two slack faces are the fan triangles `(5,6,9)` and `(7,8,9)` with
  `Rc = 0.378831172`, i.e. slack `1.153e-3`. (This is the lead's "两个 slack 不用 tight": they may be
  given zero dual weight.)

## (c) Can C897's positive KKT split weights certify a dual?

* **The split is exact** ✔: `∇_{c_j} ρ_i = (c_j − U_i)/|c_j − U_i|` for the two adjacent sites `j`, so a
  switch branch's 22-coordinate gradient is *literally* the sum of the two endpoint-constraint
  gradients; assigning `μ_i/2` to each endpoint constraint reproduces C897's 22-coordinate stationarity
  unchanged (finite-difference cross-check agrees to 6 decimals, the remainder being the difference
  step).
* **Per-face cone condition** ✔: for each face, `Σ_{c ∈ f} w_c · unit(c − z_f) = 0` with `w_c > 0` is
  solvable at `z_f` = circumcentre **iff** `z_f ∈ int conv(face)`, i.e. iff the face is acute — true for
  all 11 faces here (verified via barycentric coordinates). So a strictly positive per-face weight
  triple exists for every tight face, and the two slack faces take weight 0.
* **Verdict**: the assembled object is a *valid multiplier vector* for the candidate's active set — it
  encodes C897's stationarity plus the split and the per-face positivity — but it **cannot certify a
  positive optimum of the free-site min-r SOCP**, because that dual is degenerate as shown in (a).
  What it *does* certify:
  1. **fixed-site** problem: with the candidate's sites frozen, `min r` = the max of the active
     distances = `r_cand` trivially, and C897's weights are the KKT certificate for that value ✔;
  2. the candidate's **stationarity in the covering problem** (C897's own scope ✔).
  For a *positive* oracle bound one must use the **fixed-r infeasibility certificate**; the elementary
  part is the paired-lens chord bound (`0.378542769` at the candidate's switches), and any stronger
  certificate must combine the 9 lens constraints with the 11 MEC cones — a well-posed Farkas problem
  over the same 8 switch angles, and the natural next obligation.

## Summary

| item | result |
|---|---|
| (a) representation | valid: SOCP, necessary relaxation, global bound reduces to 8 switch angles ✔ |
| (a′) caveat | free-site min-r dual degenerates to 0 ⇒ KKT multipliers cannot certify a positive value; use fixed-r infeasibility (Farkas) form |
| (b) switches | all 9 tight (`ρ_i = r`), chord bound `0.378542769 < r` |
| (b) faces | all 11 acute; 9 tight (7 fan + 2 central), 2 fan slack `(5,6,9),(7,8,9)` at `1.153e-3` |
| (c) split identity | exact ✔ (reproduces C897's 22-coordinate balance) |
| (c) per-face positivity | ✔ (acuteness ⇒ strictly positive weights) |
| (c) dual verdict | valid multipliers, but they certify the fixed-site/covering stationarity, **not** a positive SOCP optimum |

**Repro**: `py -3 -B -X utf8 research-2026/team-current/r20-gluing/socp_fixed_switch_check.py`.
