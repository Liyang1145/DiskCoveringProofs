# cline2-candidate-rigidity — STATUS (2026-09-24, round 4; §3 renamed and corrected after the lead's C249/C529/C830 resolution)

Write scope: this directory only. No delegation used. **All findings below are numeric /
calibration unless explicitly marked proved.** No new theorem is registered here; the lead
owns registration. Sections marked *(corrected)* supersede my first report of this round.

Object of study (read-only inputs):
* `n11/upper/certified_object.json` — the saved 22 integers / 10^17 (rational witness) plus
  the published certified interval.
* `research-2026/team-current/lead/q0_graphs.json`, `q0_exact_closure_radius.py/json`,
  `q0_closure_tangent.json` — the q0(6,7) (= k=4 two-fan) graph and the closure system.
* `research-2026/team-current/lead/TEAM-ROUND4.md`, `PAUSED-2026-09-24.md`, flash-compute /
  flash-geometry STATUS + DEAD (read before exploring).

---

## 1. Coordinate calibration (done first, as instructed)

Caliber: D = closed unit disk, equal disks of radius R, centres in units of D's radius,
angles in radians, exact rational centre data = the 22 integers of the certified object.
Internal check re-derived from scratch in this round:

| check | value | source |
|---|---|---|
| ring sites / hubs | `{1,3,4,5,6,7,8,9,10}` / `{0,2}` | `|c_i| > 1-R` |
| angular order of ring sites | `[5,7,1,8,6,4,9,10,3]` | `tools/active_set.py` |
| boundary capacity | all 9 consecutive pairs satisfy `w_i + w_{i+1} = t_{i+1} - t_i` to `<= 6.7e-16` | `tools/boundary_cond.py` |
| total boundary | `sum_i 2 w_i = 2*pi` (spoke equations sum to `2*pi`) | same |
| Voronoi vertex count inside D | 138 triples, 9 distinct with `R_v` within `8e-17` of R | `tools/active_set_mp.py` |
| next critical level | `0.378831171761...` (2 vertices `(0,3,10)`, `(0,4,9)`) — gap `1.15e-3` | same |

**R_cov of the saved witness = the published interval to 30 significant digits** (see §3).
The two objects (integers vs `toFixed(17)` strings) coincide: `0/11` centres differ.

## 2. THE ACTIVE SET — exactly 18 equalities, 9 + 9 (numeric, calibrated)

`gamma(x) = max over the full critical set of the nearest-site distance` is the covering
radius. The critical set of `gamma` = (a) all triple Voronoi vertices inside D, (b) all
perpendicular-bisector intersections of pairs of sites with bd D *at which the pair really
are the two nearest sites*. At the saved object exactly **18** critical points attain the
maximum, and they split cleanly:

**(i) 9 tight Voronoi vertices** — each a 3-site equidistance point at distance R:
`(0,9,10) (0,2,5) (0,3,5) (2,6,8) (2,5,7) (0,4,6) (0,2,6) (1,2,8) (1,2,7)`.
7 contain one hub and two ring sites; 2 contain both hubs and one ring site.
Residuals against `R = C529` (60 dps): `-9.3e-19 … -7.9e-17` (`tools/tcert_audit.py`).

**(ii) 9 tight boundary points** — perpendicular-bisector intersections with bd D at which
the pair really are the two nearest sites (`tools/active_verified.py`, one parametrisation,
no branch ambiguity):
`(5,7)`, `(7,1)`, `(1,8)`, `(6,8)`, `(4,6)`, `(4,9)`, `(9,10)`, `(3,10)`, `(3,5)` — exactly
the consecutive pairs of the induced order. All 9 have `d - R` in
`[-3.4e-17, +6.7e-52]`; the maximum over bd D is attained at `(7,1)` at `th = 67.69442 deg`
and **equals `C529` to 60 digits** (hence `C529` = lo + 2.14e-60). Independent form: the
arc-capacity equations
`w_i + w_{i+1} = t_{i+1} - t_i` all hold to `<= 6.7e-16` (`tools/boundary_cond.py`); the two
forms have gradients with `cos = -0.971` (same tangent hyperplane, opposite orientation).

Everything below the top is separated by `>= 1.15e-3` (next level `0.378831171761`: the two
vertices `(0,3,10)`, `(0,4,9)` — the "opposite" side of the configuration).

### Necessary-conditions lemma (rigorous, elementary — but *not* new)
If 11 radius-R disks cover D then for every critical point as in (a)/(b) the nearest-site
distance is `<= R`; hence each equality above is a **necessary** condition on any covering
with `R = R*`, and `gamma(x) = R*` at any optimum. No symmetry, no WLOG, no overlap
assumption is used anywhere in this file.

### Rank / tangent space (numeric)
19 rows (9 boundary-capacity + 9 vertex-tightness + 1 rotation gauge) against the 22 centre
coordinates, R held at the certified value (`tools/final_active.py`, `out/J19.npy`):

* singular values `2.678, …, 5.90e-2, 3.08e-9` → **rank 18, nullity 4**; the gap between the
  last significant value (`5.90e-2`) and the noise (`3.1e-9`) is `7` orders of magnitude,
  so the rank is numerically unambiguous.
* `gamma` along each of the 4 null directions (R fixed, gauge fixed): **+9.4e-9, +1.9e-9,
  +1.7e-9, +2.3e-9 at t=1e-4**, and exactly `-1.1e-41` at t=0 → pure quadratic growth,
  **no descent direction**. So the candidate is a strict local minimum of the covering
  radius inside its active family, and no cheaper direction exists to first *and* second
  order at this radius.
* With only the 18 tight-point rows (no gauge) the nullity is 5 — one extra flat direction
  which is the rotation gauge plus a genuine flat direction of the point-conditions alone.
  (The lead's 43-row closure system has nullity 4 and positive multipliers; that system is
  strictly stronger than the 18-point system.)

## 3. Radii and naming (corrected 2026-09-24, after lead's C249/C529/C830 resolution)

**Naming rule (mandatory).** The radius of the saved `n11/upper/certified_object.json` is
**`C529 = 0.3799838531198387090485182…`**. It must **not** be called `T_cert` and must **not**
be called `R_stru`. The registered `T_cert` upper bound belongs to a *different* object — the
1e−60 symmetric KKT witness `research-2026/session2/n11alg/cert_sym60.json` (C249, revised to
C830) — whose literal differs from `C529` at `~2e-17`. Keep them separate; never compare
their digits.

| quantity | value | meaning |
|---|---|---|
| saved-object radius `C529` = γ(22 integers/1e17) | `0.379983853119838709048518179573…` | covering radius of the saved rational witness |
| published interval `[lo,hi]` for the saved object | `0.379983853119838709048518179573…` ± `2e-60` | exact-arith certificate for that same object |
| `C529 − lo` | `+2.14e-60` (attained at the boundary point `(7,1)`, θ = 67.69442°) | witness sits inside its own interval |
| `T_cert` (C249/C830, `cert_sym60.json`) | `0.379983853119838689722261606136093214308718957…` | a **different object**; registered, unchanged |
| `R_stru` | reserved for an algebraic radius of the equality system; not identified by this round | — |

**Interface evidence (2026-09-24, exact code + exact data).** The team's own registered
verifier run on the saved object reproduces my 60-dps number bit-for-bit:

```
py -3 -B -X utf8 research-2026/session2/lead/verify_config.py n11/upper/certified_object.json
  config: n11\upper\certified_object.json  n=11
  R_D upper bound (lead 独立候选集, 60 dps) = 0.379983853119838709048518179573
  attribution: V2b
```

Its candidate set (all V3 circumcircles ∩ D, all V2b perpendicular-bisector points on ∂D, plus
a 20000-point ∂D scan with 200 refinement steps) also attributes the argmax to the boundary,
consistent with γ being attained at the `(7,1)` bisector point (`tools/tcert_audit.py`).

**Retraction of my earlier report.** I had quoted the object's radius as `0.37998385311983868…`
(taken from the KKT-witness literal) and flagged a `+7.9e-17` anomaly against the certified
interval. With the C249/C830 vs C529 separation that flag is **void**: I had conflated two
different objects. There is **no discrepancy** — registered interval, registered verifier and
my 60-dps computation all agree on `C529`. Also, `float64` solves have been superseded by
`cert_sym60.json` (1e−60 precision), so the "8e−17 implementation flag" from the KKT run is
not an implementation bottleneck either; investigation closed by the lead.

## 4. Equality mechanism (the answer to "saturation/equality propagation")

Two independent 9-tuples saturate simultaneously, and they alternate between the two hubs:

* **Boundary capacity (9 equalities).** For each consecutive ring pair in the induced order
  the half-widths of the two covered arcs must *sum exactly* to the angular gap:
  `w_i + w_{i+1} = t_{i+1} - t_i`, i.e. `sum_i w_i = pi`. This is forced by
  `sum_i w_i >= pi` (the arcs must cover bd D) together with `sum_i w_i <= pi` from the
  tightness of the 9 boundary bisector points; any strict inequality in one gap forces
  another gap to be under-covered.
* **Voronoi tightness (9 equalities).** Every Voronoi vertex of the 11-site diagram inside D
  must be at distance `<= R`; at the optimum the 9 extremal ones are exactly `= R`.
  7 of them are `{hub, ring, ring}` vertices and 2 are `{hub, hub, ring}` vertices, so both
  hubs enter the equality set and the two tuples are coupled through the hub–hub bisector.
  **Corrected geometry:** `|c0 − c2| = 0.4224059653 < 2R = 0.7599677062` — the two hub disks
  **overlap** (`|c0−c2| − 2R = −0.33756174`), so the hub Voronoi edge length is **not**
  `|c0−c2| − 2R` and my earlier phrase "segment of that length" was wrong. The correct
  statement, verified numerically (`tools/tcert_audit.py`): the two hub sites *do* share a
  Voronoi edge inside D — its perpendicular bisector contributes 505 of 801 sampled points
  with `{0,2}` the two nearest sites — and each of the two hub-containing tight vertices is
  an endpoint of that shared edge.
* The two tuples interact only through the common ring sites; the ring supplies 9 free arc
  parameters, the hubs 4, plus R = 14; 18 equalities leave a 4-dimensional tangent space
  (after the rotation gauge), whose quadratic growth is verified numerically.
* Consequence for a **global** proof: the 18-point system alone is *necessary but not
  sufficient* — its solution set is of dimension 4 (rotation included), so it does not by
  itself isolate the optimum. Conversely, refuting the candidate requires exhibiting a
  configuration with `gamma < C529`; the 18-point tangent analysis shows this cannot be done
  by a first/second-order perturbation *at fixed active set*.
* **Corrected inference (my earlier text was wrong).** "The 18 equations admit other
  solutions" does **not** imply that no dual certificate can exist on the tight points. The
  obstruction to a dual certificate is the **rank deficit** — rank 18 in 23 variables
  (nullity 5, i.e. codimension 4) — which is a linear-algebra fact at the candidate point and
  is consistent with the lead's independent tangent dimension 4 in the 63-variable system
  (rank 59). Non-uniqueness elsewhere in configuration space is logically independent of that.

## 5. Files / repro (all read-only inputs; outputs in this directory)

```
# VERIFIED path (single bisector parametrisation, no branch ambiguity) -- use these
py -3 -B -X utf8 tools/active_verified.py   # 9 Voronoi vertices + 9 boundary points, levels
py -3 -B -X utf8 tools/tcert_audit.py       # saved-object gamma at 60 dps + hub-edge audit
py -3 -B -X utf8 tools/final_active.py      # rank 18 / nullity 4, gamma along the null space
py -3 -B -X utf8 tools/boundary_crit2.py    # bisector points via the A cos th + B sin th = C form
py -3 -B -X utf8 tools/boundary_final.py    # all branches of every pair + two-nearest test
# cross-check with the team's own registered verifier (exact code, exact data):
py -3 -B -X utf8 research-2026/session2/lead/verify_config.py n11/upper/certified_object.json
#   -> 0.379983853119838709048518179573  attribution V2b
# auxiliaries: tools/boundary_cond.py (9 arc-capacity rows), tools/active_set.py,
#              tools/active_set_mp.py (ring order, angle table)
```
Do **not** use the void scripts listed in `DEAD.md` §A for tight-point values. Scripts whose
only purpose was the (now-closed) tangent/T_cert side line — `tools/solve_rstru*.py`,
`tools/three_radii.py`, `tools/tcert_vs_rstru.py`, `tools/extract_rstru.py`,
`tools/second_order*.py`, `tools/jac*.py`, `tools/flat_family.py`,
`tools/nullspace_probe.py`, `tools/grad_danskin*.py`, `tools/kkt_probe.py` — are **frozen
exploration only**; the lead stopped that line.

## 6. Method limits / dead ends (this round)

* **Grid scans are not evidence** (consistent with flash-geometry DEAD). One dense 200k
  scan gave `0.37998356089092689`, 3e-7 below the true max, purely from sampling — never
  use sampled maxima as bounds. (The registered verifier's own ∂D scan is only used as a
  locator; the value it certifies comes from the closed-form V2b/V3 candidate set.)
* **Rank deficit, not non-uniqueness, is the certificate obstruction** (see §4).
* Double-precision evaluations of 17-decimal vertices have noise `~1e-16` on distances near
  R; any "exact" separation below `1e-15` requires the 60-dps path.

## 7. RETRACTED LINE: sector height / degeneracy (INVALID — see INVALID.md)

**SECTOR-HEIGHT-OBSTRUCTION.md is INVALID and rejected by the lead (2026-09-24).** Five
concrete false statements (wrong ring-centre norm 
 instead of sqrt(1-r^2); wrong
full-width value; Sigma alpha = 2 pi instead of the lead's 2 pi + 2 Sigma b; the false
identity lpha = w/2 for the isosceles sector; and the false obligation (EX) plus the false
hub criterion). Nothing on this line may be cited, and (EX) must **not** be encoded anywhere.
The line is STOPPED. Only the lead's exact norm sandwich and 1D factor route are to be used.

What remains valid in this directory: the calibration table of the saved object (STATUS §2,
	ools/active_verified.py, 	ools/tcert_audit.py), the arc-capacity identity
Sigma w_i = pi, and the naming rule (C529 vs T_cert) in §3. Repro of the corrected
reference numbers: py -3 -B -X utf8 tools/correct_facts_check.py.

## 8. Superseded planning text (kept for the audit trail)


**Obligation answered in `SECTOR-HEIGHT-OBSTRUCTION.md`.** Summary of the verdict:

* **No uniform positive lower bound on the sector height is derivable from local sector
  geometry.** Exact reason: the identity `cot α = k/h − (1−|c|²)/(2hH)` makes height and wedge
  angle the *same* datum, so the lead's bound `α ≥ 2atan(h/(k+√(1−R²)))` and the arc budget
  `α ≥ 2w ≥ g/2` both degrade exactly as `h → 0`. The arc budget has slack
  `9 asin r − π = 0.3664` at `r = 0.38`, so widths are not pinned near `asin r`.
* **The α→π corner is one configuration, not a family** (proved): pinned disk at `|c_0| = r`
  (origin on its boundary), and in the lead's fixed-`R0` normalisation `u = v = t ∈ [75/76,1]`.
  Hence the restricted 1D ring-factor segment is the right target.
* **Exact residual obligation (EX):** ten radius-`r` disks must cover `D \ {origin}`.
  This is global — the hub-only route is provably insufficient (exact criterion
  `h_1h_2 ≤ 2rε` is slack on the admissible range, and `h_j ≤ r−ε` is weaker than the ring
  bound).
* **Rigorous exclusion obtained only at `r = s = 19/50`** (otherwise `C840` yields a 10-disk
  cover at `s`). Numerically the corner appears infeasible over the whole allowance, but
  **no `r*` is claimed** — that run was killed by the shell budget and is not a certificate.
* **Interface note for the certification:** excluding the corner at the single allowance
  `r = 0.38` does not cover `r < 0.38`; the fixed-`R0` dual must be run over the whole segment
  `t ∈ [75/76,1]` *and* encode the origin-avoiding constraint (EX).

**Superseded plan (kept for the audit trail):** adding closure rows to the geometric Jacobian
is moot — the witness already satisfies the closure identically (lead). The earlier L-A/L-B/L-C
sketch below remains a valid description of the *local* sublemma but is not sufficient for
global optimality.

* **L-A (boundary).** `sum_i 2w_i >= 2 pi` with `w_i = arccos((1+s_i^2-R^2)/(2 s_i))` and
  the cyclic gap structure ⟹ every consecutive gap satisfies `w_i + w_{i+1} = t_{i+1}-t_i`
  at any optimum, hence `sum_i w_i = pi` exactly. (Elementary; verified to `6.7e-16` on the
  witness.)
* **L-B (interior).** Every Voronoi vertex of the 11-site diagram inside D is a local max of
  the nearest-site distance on its cell; hence 9 of them are pinned at `= R` and the two
  hub-containing ones are endpoints of the shared hub–hub edge (verified: 505/801 samples,
  `tools/tcert_audit.py`).
* **L-C (gap).** Combining L-A + L-B with the closure identity to show the pinned system has a
  unique solution up to rotation at `R = C529`, with the lower critical points enclosed below
  by `>= 1.1e-3`.
