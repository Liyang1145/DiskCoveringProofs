# Equality mechanism for the sharp q0(6,7) candidate (n=11, nine rings + two hubs)

**Scope.** Established 9-ring + 2-hub reduction (C450/C451, C464, C801/C809) at the saved
upper candidate `n11/upper/certified_object.json`; the q0(6,7) two-fan graph = `q0_graphs.json`
entry `span=4` (hub degrees 7 and 6). Everything below is **numeric/calibration** unless the
line says *proved*. No symmetry, no zero-overlap, no ear hypothesis is used. Radii in units of
the unit-disk radius; D = closed unit disk.

---

## 1. Calibration data (all re-derived this round)

Ring sites `R9 = {1,3,4,5,6,7,8,9,10}`, hubs `{0,2}`. Induced cyclic order

```
[5, 7, 1, 8, 6, 4, 9, 10, 3]      (angles 7.71°, 45.75°, 89.94°, 134.13°, 172.16°,
                                   207.78°, 248.62°, 291.25°, 332.10°)
```

| quantity | value |
|---|---|
| hub moduli | `|c0| = 0.14942849894640000685`, `|c2| = 0.27297746635709790874` |
| hub separation | `|c0-c2| = 0.42240596530349794335` **< 2R = 0.7599677062** (hub disks overlap; they still share a Voronoi edge inside D, see §3) |
| `1-2R` | `0.24003229376032259035` |
| `R` (= certified interval endpoint) | `0.379983853119838709048518179573…` |

## 2. The critical set of the covering radius

For equal disks,

```
gamma(x) = max_{p in D} min_i |p - x_i| = max over the FINITE critical set
```

where the critical set is

* **(a)** all triple points of the 11-site Voronoi diagram that lie in D, and
* **(b)** for each pair of sites, the two intersections of the perpendicular bisector with
  bd D — kept only when the pair really are the two nearest sites there.

The bisector parametrisation (used consistently here) is

```
p . (c_i - c_j) = (|c_i|^2 - |c_j|^2)/2 ,
p = A +- s * n ,  A = C * (c_i-c_j)/|c_i-c_j|^2 ,  C = (|c_i|^2-|c_j|^2)/2 ,
n = (-(c_i-c_j)_y, (c_i-c_j)_x)/|c_i-c_j| ,  s = sqrt(1 - |A|^2)  (empty if |A|>1).
```
*(The sign in `C` is the one thing that is easy to get wrong; the wrong sign reproduces the
antipodal branch and hides the tight points. This bug was made and fixed in this round —
see `DEAD.md`.)*

At the saved witness **exactly 18 points attain the maximum**, and they are exactly two
9-tuples:

### (i) 9 tight Voronoi vertices (each at distance R from its three sites)

| triple | type | point | `d-R` |
|---|---|---|---|
| (0,9,10) | hub-hub-ring | (-0.000574102353, -0.529412040784) | -9.3e-19 |
| (0,2,5) | hub-hub-ring | ( 0.315948155771, 0.061431900196) | -1.0e-18 |
| (0,3,5) | hub-ring-ring | ( 0.378416356737, -0.116776858375) | -1.1e-17 |
| (2,6,8) | hub-ring-ring | (-0.378210672199, 0.306449855600) | -2.0e-17 |
| (2,5,7) | hub-ring-ring | ( 0.378874421053, 0.305628858562) | -3.2e-17 |
| (0,4,6) | hub-ring-ring | (-0.378668736514, -0.115955861337) | -3.3e-17 |
| (0,2,6) | hub-ring-ring | (-0.315814177428, 0.062116994571) | -3.9e-17 |
| (1,2,8) | hub-ring-ring | (-0.219433723710, 0.582987898859) | -4.7e-17 |
| (1,2,7) | hub-ring-ring | ( 0.220697611495, 0.582510612112) | -7.9e-17 |

Both hubs appear in the list (hub 0 in 6 vertices, hub 2 in 5, and 2 vertices contain both
hubs), so the equality system **couples the two hubs** through the two vertices that lie on
their shared Voronoi edge.

### (ii) 9 tight boundary points (arc-capacity saturation)

The 9 consecutive pairs of the induced order; at each pair the two disks' boundary arcs meet
exactly at the bisector point on bd D:

| pair | half-width identity | residual |
|---|---|---|
| (5,7),(7,1),(1,8),(8,6),(6,4),(4,9),(9,10),(10,3),(3,5) | `w_i + w_{i+1} = t_{i+1} - t_i` | `<= 6.7e-16` |

with `w_i = arccos((1+|c_i|^2-R^2)/(2|c_i|))`. Summing the 9 identities gives the global
boundary identity `sum_i w_i = pi` (equivalently `sum_i 2w_i = 2 pi`): the arcs exactly
cover bd D with no slack anywhere.

### Slack points

The next critical level is `0.378831171761…` at the two vertices `(0,3,10)` and `(0,4,9)`,
slack `1.1527e-3`; then `0.3298832…`, `0.3233000…`. So the top-18 cluster is separated from
the rest by a factor-`1.15e-3` gap in radius — any perturbation must move all 18 together.

## 3. Why exactly 9 + 9 (the propagation)

* **Boundary half.** `bd D` must be covered by the 9 ring disks (hubs cannot reach `bd D`
  when `|h| < 1-R`). Each ring disk covers an arc of angular half-width `w_i` around the
  point of `bd D` nearest its centre. Hence `sum_i w_i >= pi`. Tightness of the 9 boundary
  bisector points gives `w_i + w_{i+1} = t_{i+1}-t_i` for every consecutive pair; any gap
  with strict inequality would have to be compensated elsewhere, but the *cyclic* system
  `w_i + w_{i+1} >= t_{i+1}-t_i` with `sum w_i = pi` forces **all nine to be equalities**.
  This is the saturation-propagation statement on the boundary: one active gap forces the
  next, and around the cycle all 9 saturate. *(The inequality form is proved elementary; the
  claim that the candidate realises it is calibration.)*
* **Interior half.** Every Voronoi vertex inside D is a local maximum of the nearest-site
  distance on its cell boundary; covering requires `<= R`. At the optimum 9 of them sit
  exactly at R: 7 of type `{hub, ring, ring}`, 2 of type `{hub, hub, ring}`. **Corrected:** the
  two hub disks **overlap** (`|c0-c2| = 0.4224059653 < 2R = 0.7599677062`, difference
  `-0.33756174`), so the hub Voronoi edge length is **not** `|c0-c2| - 2R`; my earlier phrase
  "extremes of the hub-hub bisector segment of that length" was wrong. What is verified
  (`tools/tcert_audit.py`): the two hub sites **do** share a Voronoi edge inside D — 505 of
  801 sampled points on their bisector line have `{0,2}` as the two nearest sites — and the
  two hub-containing tight vertices `(0,9,10)`, `(0,2,5)` are endpoints of it.
* **Coupling.** The boundary equalities fix the 9 ring arc parameters (1 each, after
  `sum w_i = pi`); the 9 vertex equalities then over-determine the 4 hub degrees of freedom
  plus R. Numerically the combined 19-row system has **rank 18, nullity 4** at the candidate
  (`tools/final_active.py`), i.e. codimension 4 — equal to the lead's independent tangent
  dimension 4 in the 63-variable closure system (rank 59). The equality set is *not*
  isolating: 4 tangent directions remain and `gamma` grows quadratically along all of them.
  A dual certificate at the candidate is obstructed by this **rank deficit**, not by the
  existence of other solutions of the same equations elsewhere.

## 4. Radii and naming (corrected 2026-09-24)

**Mandatory naming:** the saved object's radius is **`C529 = 0.3799838531198387090485182…`**;
never `T_cert`, never `R_stru`.

| object | value | status |
|---|---|---|
| saved witness radius `C529` | `0.379983853119838709048518179573…` | equals the registered interval endpoint; reproduced by the registered verifier (`research-2026/session2/lead/verify_config.py n11/upper/certified_object.json` → `0.379983853119838709048518179573`, attribution V2b) and by my 60-dps critical-set computation (`tools/tcert_audit.py`) |
| registered interval for the saved object | `[lo,hi]`, width `4e-60` | `C529 − lo = +2.14e-60`, attained at the boundary point `(7,1)` (67.69442°) |
| `T_cert` (C249 ⇒ C830; `research-2026/session2/n11alg/cert_sym60.json`) | `0.379983853119838689722261606136093214308718957…` | a **different** 1e−60 object; registered, unchanged; differs from `C529` at `~2e-17` |
| `R_stru` | reserved for an algebraic radius of the equality system; not identified this round | — |

My earlier report's `+7.9e-17` "anomaly" came from conflating these two objects and is
**void**. `float64` local solves are superseded by `cert_sym60.json` (1e−60); the
double-precision gap is not an implementation bottleneck. Line closed by the lead.

## 5. What is missing for a global bound (honest gap)

1. The 18-point equality system is **necessary, not isolating** (codimension 4). Adding the
   global closure rows to the *geometric* Jacobian cannot raise the rank — the witness
   coordinates already satisfy the closure identically, as the lead noted; the closure system
   in its own variables already realises the same codimension 4. The isolating object must be
   the closure system in its own (angle/switch/radius) variables.
2. Even then, one needs a *quantitative* statement
   `gamma(x) >= C529 - c * dist(x, X)^2` off the solution manifold (positive-definiteness of
   the tangent Hessian) — the lead's numeric eigenvalues are the input, but no enclosure
   exists yet.
3. All non-tight critical points must be enclosed strictly below the solution radius
   (`<= R - 1.1e-3` numerically) with interval arithmetic, otherwise a branch switch can
   lower `gamma` outside the analysed chart.
4. No symmetry should be assumed: the 9 ring moduli are distinct
   (`0.7009 … 0.8925`) and the two hubs are not symmetric with respect to the ring order
   (the vertex sets of hubs 0 and 2 overlap only in the single vertex `(0,2,6)`).

## 6. Exact algebraic characterisation (statement to be proved)

Let `x = (c_0..c_10) in R^22`, `R > 0`. The candidate chart is the solution set of

```
(S)   w_i(x,R) + w_{i+1}(x,R) = theta_{i+1}(x) - theta_i(x)        i = 0..8   (cyclic)
(V)   |u_T(x) - x_s| = R  for all s in T, for T in T_9 (the 9 tight triples)
(G)   sum over triples of (Voronoi cell areas of the 11-site diagram) = pi
```

where `theta_i` is the polar angle of `c_i`, `u_T` the circumcentre (or the hub-hub tangent
point) of the triple `T`, and `(G)` is the global closure (11 face angle sums + 21
edge matchings + 9 boundary closures in the lead's angle/switch variables, or equivalently
the area identity). Numerically `(S)+(V)` alone have a 4-parameter solution manifold
(rotation gauge included) with `gamma` strictly increasing in every direction. Note the
consistency with the lead's system: the closure system in its own variables has rank 59/63,
i.e. the *same* codimension 4; adding the closure rows to the geometric Jacobian therefore
cannot raise its rank (the witness already satisfies the closure identically).

**Falsifier for this chart.** A configuration satisfying `(S)+(V)` with
`gamma < C529` (none found; and none to first/second order at the candidate), or a covering
with `R < C529 - 1.15e-3` whose critical set lies outside the chart (a branch switch) —
neither was found.
