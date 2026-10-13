# R20-GLUING — why the 29-factor relaxation's high-value combination is not gluable

Author: cline2 / DS v4.1f (single member, no sub-agents used).
Scope of this round: **diagnostic + calibration only** (no claim registered, no lead file
modified, no proof asserted). All outputs written under `research-2026/team-current/r20-gluing/`.
Object of the main goal (unchanged): unconditional sharp n11 optimum; proven floor is
C825 `r_D(11) > 3/8 = 0.375`, certified ceiling C249 `0.3799838531198386897...`.

---

## 0. Object, units, caliber

| item | value |
|---|---|
| problem | 11 equal disks, unit closed disk `D`, reduced inward-root q0(6,7) graph (span-4: hub 9 in faces (9,0,1)..(9,3,4)+(9,10,0),(9,10,4); hub 10 in (10,4,5)..(10,8,0)+(9,10,0),(9,10,4)) |
| relaxation | 29 independent factor suprema: 11 face (=site-triangle) + 9 switch + 9 ring (=sector) factors, 121-column dual `z`, indices: 0–10 site/hub angle sums, 11–31 squared side, 32–49 squared radius copies, 50–70 kappa/Delaunay, 71 lam, 72 eta, 73–93 first-moment side, 94–111 first-moment radius copies, 112–120 cyclic closure |
| saved solution used as "strongest pure 29-factor relaxation solution" | `lead/q0_lower375_dual_0_4.json` (`z`, 9-decimal literals), certified at R=3/8 by `lead/q0_lower375_dual_certificate_0_4.json` (**C825**, total < 3.10879 < π) |
| allowance R | 3/8 for the calibration leg, **19/50 = 0.38** for the frontier leg |
| units | lengths in units of `D`'s radius; `R` = allowance; `y = rho/R in [0,1]` local radius copies; angles in rad; the factor value is in "π-units" (the assembled bound is compared with `π`) |
| saved genuine candidate | `lead/q0_exact_closure_radius.json` `x0` (from `n11/upper/certified_object.json`), actual covering radius `r = 0.3799838531198388 < 19/50` |

**Why this z and not `joint_nested_frozen.json`**: the frozen joint-nested coefficients are a
*joint* 7-atom dual (indices {1,2,12,13,21,22,23} handled with shared variables by C854), so
maximising its 29 factors independently is meaningless — measured: total = **57.64** at R=19/50
(factor side), i.e. the joint coupling of those 7 atoms is load-bearing and the file cannot be
used as a pure 29-factor relaxation. The C825 z is a pure 29-factor dual with a *certified*
per-factor band for every factor, which makes the two-sided calibration below possible.

---

## 1. Calibration A — my pointwise factors reproduce the certified kernel

`r20_factor_probe.py` re-derives the three factor forms (face / switch / ring) independently
from the kernel's assignment and maximises each pointwise (grid + deterministic pattern search,
1 start per factor, no multistart). Result at R = 3/8 with the C825 z:

* all 29 pointwise maxima **lie inside the certified `[lower, upper]` band** of
  `q0_lower375_dual_certificate_0_4.json` (0 violations);
* `upper − mine` is 5.5e-5 … 1.5e-3, i.e. ≈ the branch-and-bound tolerance (termination tol 1e-3),
  which is exactly the expected relation (certified upper ≥ true sup ≥ my value).

Evidence: `r20_factor_probe.json` (per-factor `val`, argmax variables), comparison script
output in §7. ⇒ the factor implementation and the maximisation are calibrated on a certified
instrument.

## 2. Calibration B — the residual definitions vanish at the genuine candidate

`r20_candidate_calibration.py` maps the saved genuine candidate into the same variables and
evaluates every residual family that the dual dualizes:

| residual family | max abs value at the candidate |
|---|---|
| site angle sums (9), hub angle sums (2) | 4.4e-16, 0.0 |
| cyclic closure `G_i` (9) | 8.9e-16 |
| total width `Σw − 2π` | 0.0 |
| squared radius copies (18) | 0.0 |
| first-moment radius copies (18) | 0.0 |
| first-moment side matching (21) | 4.4e-16 |
| squared side matching (21) | 5.6e-16 |
| direct sine-law side gaps `ρ₁sinθ₁ − ρ₂sinθ₂` (21) | 2.2e-16 |
| Delaunay slacks (21) — strict inequalities | min 0.502, max 1.963 |

⇒ the residual apparatus is calibrated on a *known-feasible* object (the apparatus reproduces
"all dualized equalities hold exactly" where they must hold).
Evidence: `r20_candidate_calibration.json`.

## 3. The exact gap identity

With `A(x)` = the sum of the assembled piece areas (11 site triangles `2R²y²∏sin`,
9 switch triangles `R²y²sin(2b)/2`, 9 sector triangles `R²uv sinα/2`, 9 unit-circle segments
`(w−sin w)/2`), the factor assembly and the constraint assembly agree exactly:

```
V(z) = const + Σ_k F_k(z;x*_k) = A(x*) + Σ_c (±) z_c g_c(x*)
```

verified to **|err| ≤ 2.2e-15** at both R=3/8 and R=19/50 for the product-domain argmax `x*`
(`r20_mechanism.py`, `r20_mechanism.json`; the sign of the site/hub family is negative:
`−Σ z_i R_i`; all other families carry `+z_c g_c`). The identity was also checked at the
candidate (where it reduces to the lead's `D = area + κ·slack + λW + h·cls` with κ=λ=0 here).

## 4. Result 1 — the high-value combination and its residual profile

C825 z at **R = 19/50**: `V = 3.188780840078`, `π = 3.141592653590`, **gap `V − π = +0.047188`**.

Product-domain argmax (the "high-value combination"):

| variable | value at argmax | value at the genuine candidate |
|---|---|---|
| face radii `y_face` (11) | all **1** (saturated) | 0.9969–0.99996 |
| switch radii `y_sw` (9) | all **1** (saturated) | 0.9999575 |
| sector endpoints `u,v` (18) | 1 except `u₄=0.9912`, `v₆=u₇=0.9957` | 0.9999575 |
| `α` (9) | 1.89 … 2.81 | 1.63 … 2.97 |
| `b` (9) | 0.750 … 0.962 | 0.636 … 1.051 |

Residuals at the argmax (rad / normalized units) and their multiplier-weighted contributions in
the identity of §3:

| family | max abs residual | weighted term |
|---|---|---|
| site+hub angle sums | 0.2711 | −0.001679 |
| squared side matching `m2` | **0.038865** | **−0.045479** |
| first-moment side matching `m1` | 0.025545 | +0.020165 |
| cyclic closure `G_i` | **0.089452** (Σ|G| = 0.394) | **−0.044445** |
| squared radius copies | 0.017490 | +0.003983 |
| first-moment radius copies | 0.008784 | −0.001485 |
| Delaunay slacks / width | (κ=λ=η=0 in this z) | 0 |
| **piece-area inflation `A − π`** | — | **+0.116128** |

So `V − π = +0.116128 − 0.045479 − 0.044445 + 0.020165 + 0.003983 − 0.001679 − 0.001485`.

**Reading**: the high-value combination is the *all-radii-saturated corner* with independently
chosen angles; its piece-area sum exceeds the disk area by +0.116, and the only dual terms that
push back are the two side-matching families and the closure.

## 5. Result 2 — the two sector-chain couplings are EMPTY at the frontier

The user's priority hypothesis ("connect the sector chain's global position closure") was tested
as **one mechanism each**, at fixed z (same coefficients):

**(a) exact cyclic sharing of the switch-point radii** `y_i(switch) = v_i(ring i) = u_{i+1}(ring i+1)`
(max-plus cycle DP, 41 y-nodes, inner α/b grids; the finite grid makes the reported value a
*lower* bound on the true sharing value, hence the gain an *upper* bound):

| R | `V_indep` (probe) | `V_cycleDP` | gain ≤ |
|---|---|---|---|
| 19/50 | 3.188780840 | 3.188763694 | **1.8e-5** |
| 3/8 | 3.085409838 | 3.084883069 | 5.3e-4 |

The DP optimum is `y ≡ 1` — the same corner the independent argmax already sits on. ⇒ the sector
chain's **radius position is already consistent** at the high-value combination; it carries
~0 of the 0.047 gap. (`r20_mechanism.json`)

**(b) exact cyclic closure** by replacing the switch's free `b` with the closure-determined
`b_i^cl = (π − T_i − L_{i+1} − (w_i+w_{i+1})/2)/2` (C820), the rings held at their independent
argmax (a feasible point of the constrained problem, so its drop is an upper bound on the gain):

| R | gain ≤ | max \|G_i\| before |
|---|---|---|
| 19/50 | **4.2e-4** | 0.0895 |
| 3/8 | 2.65e-2 (degenerate switches whose own optimum is at `b = 1.0`) | 2.75 |

⇒ the closure's content is already absorbed by the `h_i` dualization at the frontier z; imposing
the individual equations buys ≤ 4.2e-4. (`r20_closure_coupling.json`)

Both mechanisms are therefore **falsified as the missing coupling** at this solution. (They may
still matter for *other* z; this is a statement at the saved z.)

## 6. Result 3 — the gap is DIFFUSE, not a corner defect

Exact causal decomposition (uses `D(z;x_cand) = π` at the genuine candidate):

```
V(z) − π = Σ_k [ sup_k(z) − F_k(z; x_cand,k) ] = 0.047188186
```

| group | Σ δ_k | largest single δ |
|---|---|---|
| 11 face factors | 0.026285 | face8/face4 0.003725 |
| 9 ring factors | 0.015803 | ring2 0.006397 |
| 9 switch factors | 0.005100 | switch4 0.001005 |

No factor exceeds 14 % of the gap; every factor is slightly (1e-3 … 6e-3) *better* than the
genuine candidate's configuration. Evidence: `r20_gap_decomposition.py`,
`r20_gap_decomposition.json`.

**Consequence for the question asked.** The high-value combination does not fail to glue because
of one missing constraint that a single added coupling could supply: it fails *uniformly* —
each of the 29 pieces is a little larger than its genuine counterpart, and the two
sector-chain couplings that could enforce positional consistency are already satisfied by the
corner. The residual families that are still violated at the argmax and still carry dual weight
are the **shared-side (sine-law) matchings** (`m2` 0.0389 → −0.0455, `m1` 0.0255 → +0.0202) —
i.e. the pieces' *edge lengths* — plus the site angle sums (violated up to 0.271 rad, but
weighted only −0.0017 because the corresponding multipliers are small).

## 6b. Result 4 — the high-value combination is **not gluable at all** in the side-matching sense

At fixed angles the 21 shared-side equalities are **linear in the 20 log-radii** (11 faces +
9 switches): `M·logρ = rhs(angles)` with `M` the signed incidence of the 20-node face/switch
graph. Measured (`r20_holonomy.py`):

| quantity | at the genuine candidate | at the high-value combination |
|---|---|---|
| rank `M` | 19 | 19 |
| dimension of the left null space (cycle rank `E−V+1 = 2`) | 2 | 2 |
| **consistency (holonomy) defect `‖U_nullᵀ rhs‖`** | **0.0** (machine precision) | **0.013953** (max component 0.013353) |
| least-squares residual of `M logρ = rhs` | 0.0 | 0.013953 (system inconsistent) |

**Meaning**: at the high-value combination's angles there is **no assignment of the 20 local
radii that reconciles the 21 shared side lengths** — the two independent holonomy
(cycle) conditions of the side-matching system fail by 1.4e-2 in log-units (≈1.4 % relative
side-length error), while they are satisfied exactly by the genuine candidate. This is the
strictest form of "the high-value combination cannot be glued".

The two conditions are (a) necessary for every genuine cover (calibrated above), (b) **not
among the constraints the 29-factor dualisation imposes** — the dualisation adds one multiplier
per row, and a per-row Lagrange form does not impose the solvability (integrability) condition
of the linear system, even though the condition is *implied* by "all 21 rows hold", and
(c) the **smallest possible addition**: two scalars on the 42 angles, no new variables.
They coincide with the "2 cycle constraints" already identified by the lead
(`lead/ANGLE-ONLY-EXACT-MODEL.md` cycle rank `21−20+1 = 2`, `lead/NONLINEAR-STRESS-PLAN.md`
"2 cycle and 6 circle equality residuals"), now quantified at the relaxation's own argmax.

## 6c. Result 5 — the holonomy coupling is ALSO nearly free (hypothesis falsified at z*)

Bounded decisive test (`r20_holonomy_test.py`, ≤3 constrained local starts, corrected
parameterisation): maximise the face+switch part of the frozen dual (31 angles: 11 face pairs
`(a,b)` with `c = π−a−b` determined, 9 switch half-angles) subject to the two holonomy
conditions:

| quantity | value |
|---|---|
| holonomy defect at the unconstrained argmax (2 components) | 0.004049, 0.013353 (norm 0.013953) |
| unconstrained face+switch maximum | 8.292486687 |
| holonomy-feasible value (all 3 starts agree) | 8.292453176 (defect 6e-15) |
| **upper bound on the gain of imposing the holonomy alone** | **3.4e-5** |

⇒ the two holonomy conditions *are* violated at the argmax, but restoring them costs only
3.4e-5 of the 4.72e-2 gap: the angles can move within the factors' flat directions.

**Implementation correction (recorded).** The first version of this test left the third face
angle of each triangle as a free variable in the constraint while the objective computed it as
`π−a−b`; the solver then satisfied the holonomy at zero cost (defect 1e-13 at unchanged value).
That reading is withdrawn; the corrected version ties `c = π−a−b` in both objective and
constraint and is the one reported above.

## 6d. Summary of the four mechanism tests — no single missing coupling at z*

| single added coupling (all at the saved z*, R=19/50) | upper bound on its gain | verdict |
|---|---|---|
| exact cyclic **radius sharing** of the sector chain (cycle DP) | 1.8e-5 | empty |
| exact **cyclic closure** `b_i = b_i^cl` (ring argmax held) | 4.2e-4 | empty |
| **holonomy** of the shared-side system (2 conditions) | 3.4e-5 | empty |
| **11 site angle sums** = fan angular resource (`α_i` determined by the neighbours) | 5.3e-3 (11 % of the gap) | weak |
| total gap `V(z*) − π` | 4.72e-2 | diffuse (§6) |

The angle-sum test (`r20_anglesum_test.py`) is the sharpest of the four: the argmax violates the
site angle sums by up to **0.271 rad**, yet pinning `α_i = π − Σθ + b_{i−1} + b_i` and
re-optimising `(u,v)` costs only 0.00532 (rings are flat in `α`). This is the "crucial
correlation discarded by independent-angle duals" flagged by
`lead/FAN-DEFICIT-COORDINATES.md` — measured here as worth ≤ 11 % of the gap at this solution.

Interpretation (structural, not a theorem): at this saved solution the high-value combination
fails to be geometrically realisable **not** through one identifiable missing equality, but
through a *uniform* excess of every one of the 29 factors over its value at the genuine candidate
(1e-3 … 6e-3 each; §6). The relaxation gap is therefore a nonconvexity/Lagrangian-gap phenomenon
of the factor family, not a missing-constraint phenomenon: no single coupling tested recovers
more than 12 % of the gap. Route implication: closing the sharp bound from this family requires
the **inverse problem** (§7) — find `z` for which the candidate's configuration is simultaneously
maximal in all 29 factors — or a different representation; repeatedly adding couplings is
exhausted at this solution.

## 7. Proposal on the table (status after the three tests) and next obligation

**P-R20-1 (measured at the saved solution, not proved).** At the saved pure 29-factor solution z*
(C825 coefficients, R = 19/50) the duality gap is +0.047188 and satisfies:
 (i) the sector-chain **radius-sharing** coupling gains ≤ 1.8e-5 (mechanism test, cycle DP);
 (ii) the individual **cyclic-closure** coupling gains ≤ 4.2e-4 (mechanism test, `b = b^cl`);
 (iii) the gap is **diffuse** over the 29 factors (faces 0.0263, rings 0.0158, switches 0.0051;
 no factor above 14 %);
 (iv) the two **holonomy** conditions of the shared-side system are genuinely violated at the
 argmax (0.013953 vs 0.0 at the candidate) yet imposing them gains ≤ 3.4e-5 (mechanism test,
 corrected parameterisation), i.e. **no single coupling tested recovers ≥ 1 % of the gap**.
*Falsifier of the "no single missing coupling" reading*: exhibit a coupling C and a value
`V_C(z*) ≤ V(z*) − 1e-2`, or exhibit `z` in the same 121-column family with `V(z) − π < 1e-3`
at R = 19/50 (a near-tight dual would show the frame is adequate after all).

**P-R20-2 (still open, now with a measured cost).** The two holonomy conditions
`u_jᵀ·rhs(angles) = 0` (`j = 1,2`, `u_j` a basis of the left null space of the 21×20 side-matching
incidence) hold for every genuine inward q0(6,7) configuration, are two scalars in the 42 angles,
and are not imposed by the current per-row dualisation. Alone they are worth ≤ 3.4e-5 at z*, but
they remain the *minimal* valid addition; their value can only be assessed **jointly** with a
re-optimised `z`.

**Next obligation (the inverse problem; 1 analytic dimension reduction + 1 bounded optimisation).**
1. *Cheap leg (do first).* On the tightened family (holonomy conditions imposed; 20 log-radii
   eliminated along a spanning tree of the 20-node face/switch graph with root `γ_0 = 1`,
   cf. `lead/ANGLE-ONLY-EXACT-MODEL.md`), re-optimise `z` (121 columns, the LP/separation
   proposal machinery of `lead/q0_closure_dual.py` can be reused) and compare with
   `V(z*) = 3.18878` at R = 19/50. Gain ≥ 0.02 ⇒ the side-matching/holonomy frame is the missing
   coupling; gain ≤ 1e-3 ⇒ this frame is exhausted at this solution.
2. *Structural leg.* Solve the **inverse problem**: find `z` (121 unknowns) for which the saved
   candidate's variable tuple is simultaneously maximal in all 29 factors — ≈70 stationarity
   rows (the factors are piecewise linear in `z` through the atoms) plus the global-maximality
   conditions, i.e. the question whether the factor family can be tight at all. This is the only
   route by which the 29-factor family can deliver the sharp value: at `R = r*` a genuine cover
   exists, so every valid relaxation has `V(z) ≥ π`, and sharpness requires `V(z) = π` exactly.
   If the stationarity system is *inconsistent*, the family is structurally incapable of the
   sharp bound and the work must switch representation (the C839 62-variable shape model with the
   2 cycle + 6 circle rows, or the n=14 route) rather than add couplings.

## 8. Scope guards / what is NOT claimed

* Nothing here is a proof of any bound; §1–§6 are calibrated numerics (grid + pattern search,
  identity checks at 1e-15). No claim is registered.
* The statement "the position/closure couplings are empty" is **at the saved z***; it is not a
  statement about all duals, and not a disproof of the C820 route (which C824 uses successfully
  at R=19/50 for the (5,8) class).
* `joint_nested_frozen.json` must not be treated as a pure 29-factor dual (measured factor-side
  total 57.64 at R=19/50); its 7-atom block is joint by construction.
* The candidate radius `r* = 0.3799838531198388 < 19/50`; the frontier leg is evaluated at
  `R = 19/50`, where **no** relaxation can go below π (a genuine cover exists), so the numbers
  below π are not expected at that R for *any* z.
* Grid maxima are not bounds; directions of the reported gains (≤) are stated explicitly where
  they matter.

## 9. Files / repro

```
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_factor_probe.py        # §1, r20_factor_probe.json
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_candidate_calibration.py  # §2
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_residuals.py           # residual table, r20_residuals.json
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_mechanism.py           # §3,§4,§5a, r20_mechanism.json
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_closure_coupling.py    # §5b, r20_closure_coupling.json
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_gap_decomposition.py   # §6
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_holonomy.py            # §6b
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_holonomy_test.py       # §6c
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_anglesum_test.py       # §6d
```
Read-only inputs: `lead/q0_lower375_dual_0_4.json`,
`lead/q0_lower375_dual_certificate_0_4.json`, `lead/q0_exact_closure_radius.json`,
`lead/joint_nested_frozen.json`, `lead/certify_q0_closure.py` (structure reference).
