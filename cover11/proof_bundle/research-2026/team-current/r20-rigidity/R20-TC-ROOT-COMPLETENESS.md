# Independent geometric assembly for the repaired TC root: completeness of the critical set

Scope: `research-2026/team-current/r20-rigidity/` only. Read-only input:
`lead/repaired_tc_krawczyk.json` (the Krawczyk box for the 12D symmetric system; centre = exact
binary64 rationals, radius `1e-9`). Reproducer: `r20_tc_root_independent.py` ->
`r20_tc_root_independent.json` (+ `.log`). No SciPy, no new optimisation.

**Claim proved here (conditional on the read-only Krawczyk certificate of the lead):** for the
configuration defined by the unique root of the symmetric system inside the box, the 11-face list
built below is the complete Delaunay triangulation, its 11 circumcentres are the complete list of
Voronoi vertices, all of them lie strictly inside `D`, and the covering radius of that
configuration is exactly `R` (the root's `R` coordinate). This gives `r_D(11) <= R` (an upper
bound), not the global lower bound.

---

## 1. Independent derivation of the 7 fan + 2 central equations

Configuration reconstructed from the box (interval arithmetic, `dps = 60`), exactly as in the
interface note:
```
a4 = pi - 2(a0+a1+a2+a3),   a = (a0,a1,a2,a3,a4,a3,a2,a1,a0)  =>  sum a = pi  (identity)
theta4 = 0,  theta[k+1]-theta[k] = a[k]+a[k+1]  cyclically
rho[k] = cos a[k] - sqrt(R^2 - sin^2 a[k])       (positive-sqrt branch)
C_k = rho[k](cos theta_k, sin theta_k),  H0 = (y0,0), H1 = (y1,0),  H0 != H1
B_k = (cos(theta_k + a_k), sin(theta_k + a_k))   (unit-circle tie)
U_k = C_k + C_{k+1} - B_k                        (the other intersection of the two R-circles)
```
**Exact identities (no root equation needed).**
1. `|B_k - C_k| = |B_k - C_{k+1}| = R`: this is precisely the defining equation of `rho[k]`
   (`1 - 2 rho cos a + rho^2 = R^2` solved with the inner branch). Interval check:
   `|B_k - C_k|^2 - R^2 <= 2.4e-8` on the whole box.
2. `|U_k - C_k| = |U_k - C_{k+1}| = R`: `U_k` is by construction the reflection of `B_k` in the
   midpoint of `C_k C_{k+1}`, i.e. the second intersection of the two radius-`R` circles.
   Interval check: `<= 1.4e-7` on the box.
3. The ties tile the boundary: the ring disk `k` covers exactly the arc
   `[theta_k - a_k, theta_k + a_k]` at distance `<= R` (the squared distance to `C_k` is increasing
   in `|phi - theta_k|`), and `sum_k 2a_k = 2 pi` **identically** because `sum a = pi` is built in.
4. Two hubs are exactly `R` from `(m, +/- h)`, `m = (y0+y1)/2`, `d = (y1-y0)/2`,
   `h = sqrt(R^2 - d^2)`: `(m - y_i)^2 + h^2 = d^2 + R^2 - d^2 = R^2` (algebraic identity;
   interval check on the box: the identity interval is `[-2.8e-9, +2.8e-9]`, containing 0).

**Consequence (the fan reduction).** For `k` and a hub `H`, the points `C_k, C_{k+1}, H` have
`U_k` as circumcentre **iff** `|U_k - H| = R` (the other two distances are `R` identically), and
then the circumradius is exactly `R`. So each fan equality "the triangle `(C_k, C_{k+1}, H)` has
circumradius `R`" is exactly the res5 equation `|U_k - H|^2 = R^2`. The root system supplies this
for `k = 1 (H1), 2 (H0), 3 (H0), 8 (H1)`; the four reflection images are
`k = 6 (H1), 5 (H0), 4 (H0), 8 (H1)` (self). Hence **7 active fan equalities** with no additional
assumption. For the two central faces, the "circumradius `R`" condition for `(C_6, H0, H1)` and
`(C_2, H0, H1)` is the fifth res5 equation together with its reflection; both central centres are
exactly `R` from both hubs by identity (4). Hence **2 active central equalities**. The remaining
two fan triangles `(C_0,C_1,H1)` and `(C_7,C_8,H1)` are **not** assumed: they are verified slack.

**Reflection (verified on the box).** `theta_{8-k} = -theta_k`, `rho_{8-k} = rho_k`,
`y`-axis orthogonal: `C_k` mirrors to `C_{8-k}` (error `2.0e-7`), `U_k` mirrors to `U_{7-k}`
(`2.3e-7`), ties `B_k -> B_{k-1}`. The hubs lie on the axis and are fixed.

## 2. Face list, combinatorial incidence, Euler count (structure-assembled, no hull algorithm)

Sites `0..8 = C_0..C_8`, `9 = H0`, `10 = H1`. The list is assembled from the fan/central/reflection
structure (not from a triangulation algorithm):
```
fan active   : (1,2,10) (2,3,9) (3,4,9) (4,5,9) (5,6,9) (6,7,10) (8,0,10)      [7, circumcentres U_k]
central      : (2,9,10) (6,9,10)                                              [2, centres (m,-h),(m,h)]
fan slack    : (0,1,10) (7,8,10)                                              [2, verified slack]
```
Counts (machine-checked):
```
V = 11,  E = 21,  F = 11      V - E + F = 1        (planar triangulation of a disk)
hull edges (k,k+1), k=0..8 : each in exactly 1 face                 [9 edges]
interior edges             : each in exactly 2 faces                [12 edges]
all 11 sites used          : yes
3F = 33 = 2E - h = 2*21 - 9                                         [degree count]
```
The hull is the ring nonagon: strict orientation margin `5.4e-2` (every other site strictly left of
every oriented hull edge), and both hubs are strictly inside it (same test). Since
`F = 2V - 2 - h = 2*11 - 2 - 9 = 11` this is the complete triangulation of the 11 sites, not a
sub-complex.

## 3. Delaunay criterion (this is what makes the list the *Delaunay* triangulation)

For each face the circumcentre is recomputed **from the three sites** (my own 2x2 Cramer solve; a
bug in the first version — adding the base point twice — was found by comparing with the pin and
fixed, see the log), and the squared radius is compared with all other sites:
```
min over faces of min_{j not in face} ( |cc - C_j|^2 - r_face^2 )  =  +1.504954e-01   (>0)
min over faces of (1 - |cc|)                                       =  +6.119735e-01   (>0)
min triangle area margin                                           =  +1.467e-01
```
* Strict emptiness for all 11 faces (margin `>= 0.1505`) => by Delaunay's criterion the list is a
  Delaunay triangulation of the 11 sites.
* **CORRECTED 2026-09-25 (audit, see `R20-TC-ROOT-AUDIT.md` §2):** the sentence that used to follow
  here — "since no margin is zero, there are no four cocircular sites, so the Delaunay triangulation
  is unique" — is invalid and false. The empty-circle margin only excludes *empty* cocircular
  quadruples, and in this configuration 6 quadruples **are** exactly cocircular (the mirror-symmetric
  ones `{C0,C1,C7,C8}`, `{C0,C2,C6,C8}`, `{C0,C3,C5,C8}`, `{C1,C2,C6,C7}`, `{C1,C3,C5,C7}`,
  `{C2,C3,C5,C6}`, by the exact reflection); the other 324 quadruples are non-cocircular on the box
  (`|det| >= 5.6e-8`). What is established instead (`r20_tc_delaunay_completeness.py` [G]) is that
  each of the 6 has a site strictly inside its circle (`>= 0.6107`), i.e. **no empty cocircular
  quadruple** — which is exactly what makes the Delaunay subdivision a triangulation. Uniqueness
  therefore rests on "no empty cocircular quadruple + strict emptiness of the 11 faces", not on
  "no 4 cocircular".
* All 11 circumcentres satisfy `|cc| < 1` with `>= 0.61` margin, so **every Voronoi vertex lies
  strictly inside `D`** (no boundary degeneracy).
* Completeness of the face list is certified in `r20_tc_delaunay_completeness.py` (F1-F5): the 21
  edges are pairwise non-crossing, no site lies in another face, no site lies in an edge interior,
  all 55 face pairs have certified disjoint interiors, and the counts
  `V=11, E=21, F=11, Euler=1, 2E-9 = 33 = 3F` force all 11 bounded faces to be exactly these
  triangles. The combinatorial counts alone (as used before) do not exclude an overlapping cover.
* Cross-check of the active identification: the circumcentre recomputed from the three sites
  coincides with the pin `U_k` to `<= 5e-7` (the residual scale of the root box), and the root
  residual intervals `|U_k - H|^2 - R^2` and `|(m,+/-h) - C_ring|^2 - R^2` all contain `0`
  (as they must, since the exact root lies in the box; equality itself is the root equation, not an
  interval containment).
* Slack: for the two remaining fan faces, `circumradius^2 - R^2 in [-8.747e-4, -8.746e-4]`, i.e.
  `circumradius = R - 1.15e-3 * (1 + O(1e-9))` — strictly below `R`, consistent with the known
  `1.1527e-3` slack level of the symmetric candidate. Nothing is assumed saturated there.

## 4. Why the critical set is complete (boundary + vertex argument)

* **Interior.** `d(x) = min_i |x - C_i|` (with the two hubs among the sites) is real analytic
  except on bisectors. In the interior of a Voronoi cell, `grad |x-C_i|^2 = 2(x - C_i) != 0`, so no
  positive local maximum. On the relative interior of a Voronoi edge (two nearest sites), `d`
  restricted to the bisector line is a strictly convex quadratic, which has no relative-interior
  local maximum. Higher-order ties are Voronoi vertices. Hence every local maximum of `d` in
  `int D` is a Voronoi vertex.
* **Boundary.** On `del D` the ring disk `k` covers the arc `[theta_k - a_k, theta_k + a_k]`, and
  on that arc `|e^{i phi} - C_k|^2 = 1 - 2 rho_k cos(phi - theta_k) + rho_k^2` is maximal at the
  endpoints, where it equals `R^2` (identity 1). Since the nine arcs tile the circle
  (`sum 2a_k = 2 pi`, identity 3), every boundary point has `d <= R`, with equality exactly at the
  nine ties `B_k`.
* **Combination.** Every local maximum of `d` on `D` is either a Voronoi vertex (all 11 of them are
  strictly inside `D`, values `R` for the nine active and `< R` for the two slack) or a boundary
  point (max `= R`). Hence `R_D <= R` for the root configuration, and since the nine ties lie in
  `D` at distance exactly `R`, `R_D = R`.

## 5. Branch legality (all verified on the whole box, so they hold at the exact root)

| branch | margin |
|---|---|
| `a_k > 0` (positive arc half-widths) | `min a_k = 2.8082e-1` |
| `R^2 - sin^2 a_k > 0` (positive-sqrt for `rho`) | `1.0931e-3` |
| `0 < rho_k < 1` (ring disks properly inside `D`) | `[0.700870, 0.892522]` |
| `R^2 - d^2 > 0` (central `h` real) | `9.9781e-2` |
| hubs strictly inside `D`: `(1-R)^2 - |H_i|^2 > 0` | `3.0990e-1` |
| `theta` strictly increasing: `a_k + a_{k+1} > 0` | `6.2167e-1` |
| pins strictly inside `D`: `1 - |U_k|^2 > 0` | `6.1197e-1` |
| hull orientation margin | `5.4020e-2` |
| empty-circle margin | `1.5050e-1` |
| slack face margin (`circumradius < R`) | `8.746e-4` |

All margins are `10^6` times larger than the box radius `1e-9`, so no branch flips inside the box.

## 6. What this does and does not establish

**Does.** Independent (no SciPy) assembly of the 11 faces from the res5 reflection structure;
derivation of the 7 fan + 2 central active equalities and of the 9 boundary ties; combinatorial
completeness (`V,E,F`, Euler, edge multiplicities, site coverage) **plus** the geometric
completeness certificate F1-F5 of `r20_tc_delaunay_completeness.py` (non-crossing edges, no site in
another face, no site in an edge interior, certified disjoint interiors, face count) and the
no-empty-cocircular-quadruple certificate G; Delaunay criterion with strict margins; completeness of
the Voronoi vertex list; branch legality; and the boundary/vertex argument giving
`R_D(configuration at the root) = R` — hence `r_D(11) <= R` with `R` the root's radius.

**Does not.** (i) It does not reprove existence/uniqueness of the 12D root: that is the read-only
Krawczyk certificate (radius `1e-9`, contraction `4.37e-3`), and the "active" equalities are its
equations, not interval statements that a residual contains zero. (ii) It does not bound `r_D(11)`
from below; the local/global and moving-witness obligations of the program are untouched.
(iii) The two slack faces are *verified* slack; no saturation assumption is used anywhere.
(iv) The identification of the root's `R` as an allowed covering radius uses the same configuration
data; the hub labels `H0 = (y0,0)`, `H1 = (y1,0)` have `y0 = +0.27298`, `y1 = -0.14943`, i.e. the
larger-modulus hub sits on the positive axis (this differs from the saved `certified_object.json`
labelling — do not mix the two files). (v) It does not claim that no four sites are cocircular (see
the correction in §3); the six mirror quadruples are cocircular and non-empty.

## 7. Repro

```
py -3 -B -X utf8 r20_tc_root_independent.py
# reads ../lead/repaired_tc_krawczyk.json (read-only), writes r20_tc_root_independent.json
```

**2026-09-25 box fix (audit `R20-TC-ROOT-AUDIT.md` §1).** Line 50 originally built the box as
`mp.iv.mpf([CH[i]-RAD, CH[i]+RAD])`; the binary64 endpoint rounding can move an endpoint inward by
up to `2.723e-17`, so the interval did not provably contain the certified box. The script now uses
`mp.iv.mpf(CH[i]) + mp.iv.mpf([-RAD, RAD])` (the same construction as the lead's kernel) and decides
the two central positivity claims on the exact interval endpoints
(`empty >= 0.1504954350807983567`, `1-|cc| >= 0.61197353225160098382`, conservative `0.15`, `0.61`).
The re-run reproduces the same readings. Companion audit scripts: `r20_tc_box_audit.py` (box defect,
330 circle determinants, exact-endpoint decisions) and `r20_tc_delaunay_completeness.py`
(F1-F5 triangulation certificate + G non-empty cocircular quadruples).

Audit-trail note: a first circumcentre routine added the base site `r` twice; fixed earlier (see the
log). The audit-trail lesson for this round is the two items above — rounded float endpoints, and the
invalid inference from the empty-circle margin to the absence of cocircular quadruples.
