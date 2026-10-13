# Local boundary cyclic closure — final independent audit (repair 2)

Author: cline2-closure-geometry. Scope: this directory only.
This file **replaces** both `AUDIT-CLOSURE.md` (false 4-cell/hub argument) and my
first repair attempt in it. Cross-refs: `lead/CLOSURE-LOCAL-HALFPLANE-PROOF.md`
(lead's halfplane proof), `lead/BOUNDARY-CYCLIC-CLOSURE.md`.

Object / caliber: unit closed disk `D`; a genuine configuration is a cover of `D`
by 11 equal closed disks of radius `r <= R = 19/50`, reduced to the established
inward-root 9-ring + 2-hub nearest-site model with the cyclic 9 owned arcs.
Covering radius = max over `D` of distance to nearest site; genuine means `<= r`.

## 0. Verdict

```
  T_i + L_(i+1) + 2 b_i + (w_i + w_(i+1))/2 = pi                     (CL)
```

is a **necessary equation for every genuine configuration and every `i`**, hence
`h_i * ((CL) residual)` may be added to the certificate dual for arbitrary real
`h_i`. Proof: §2–§4 below (the lead's halfplane proof, independently re-derived
and checked). No hubs, no tiling, no perturbation, no trivalence.

Verified numerically on the saved certified candidate to `<= 8.9e-16`
(`verify_halfplane_proof.py`), and every *inference step* of the proof was checked
as an inequality/order fact (not a residual) at all 9 switches:
`ALL CONE-ORDER + DOMINANCE FACTS VERIFIED: True`.

## 1. Notation and setup

For `i mod 9`: `c_i` ring sites, `c_9, c_10` hubs; `P_i` the switch between the
cells of `c_i` and `c_(i+1)` = the point of `bd D` where ownership changes;
`w_i = ` angular width of the owned arc of `c_i` (= arc from `P_(i-1)` to `P_i`);
`K` = the convex polygon with vertices `P_0..P_8` in cyclic order.

Two elementary facts about a genuine configuration:

* (F1) each owned arc is minor and `w_i = 2 asin(d_i/2)` with
  `d_i = |P_(i-1)P_i| <= 2r`; hence `w_i <= 2 asin r < pi` and
  `sum_i w_i = 2 pi`; moreover `w_i >= 2 pi - 16 asin R > 0` (§5).
* (F2) every site `c` of the reduced model satisfies `|c| <= sqrt(1-r^2)`
  (inward-root condition). Justification: in the reduced model each site is an
  *inward root* — this is the C464/C465 inward-root replacement (the outer root
  of the same boundary arc is dominated by the inner one, so existence of a cover
  may be assumed with inner roots). Concretely, for `r <= 1/2` a site with
  `B(c,r) ⊆ D` has `|c| <= 1-r` and therefore
  `|c|^2 <= (1-r)^2 <= 1-2r+2r^2 < 1-r^2`; the sharp form `|c|^2 <= 1-r^2` is the
  inward-root inequality. (A surface fact "`B(c,r)` meets `bd D`" alone does NOT
  give this and is not used.) Hubs satisfy the stronger `|h_j| <= 1-r`.

## 2. The cone at a switch and the ray order (proof)

Fix `i`, write `P = P_i`, `a = P_(i-1)`, `b = P_(i+1)`, `c = c_i`, `d = c_(i+1)`,
`n = d - c`.

**(2.1) All four rays `a-P, c-P, d-P, b-P` lie in the closed cone at `P`.**
The cone `C_P` at the vertex `P` of a convex polygon with aperture
`theta = pi - (w_i + w_(i+1))/2 in (0,pi)` (strict positivity from (F1)) is
`{P + t v : t >= 0, v in the angular sector spanned by a-P and b-P}`.
`a-P` and `b-P` are its boundary rays. For `c`: every ring site lies in the
inward closed halfplane of every chord of `K` — for the chord `P_(j-1)P_j` with
outward unit normal `m_j` and supporting distance `cos(w_j/2) >= sqrt(1-r^2)`,
Cauchy-Schwarz and (F2) give
`m_j · c <= |c| <= sqrt(1-r^2) <= cos(w_j/2)`, so `c` is in the inward halfplane
of every chord; `K` is the intersection of those halfplanes, hence `c in K`; and
for any point of `K` its direction from `P` lies in the sector at `P` (convexity).
Same for `d`. (This is the lead's Cauchy-Schwarz step; it is correct and is
verified numerically: each ring and hub lies in all 9 inward halfplanes.)

**(2.2) The separating line `n · v = 0` crosses the cone exactly once.**
Because `P` is equidistant from `c` and `d`, `|P-c|^2 = |P-d|^2` gives
`2 P·(d-c) = |d|^2 - |c|^2`, hence

```
   n·(c-P) = n·c - P·n = n·c - (|d|^2-|c|^2)/2 = -|n|^2/2 < 0 ,
   n·(d-P) = +|n|^2/2 > 0
```

(using `2 c·(d-c) = |c|^2 - |d|^2 + |n|^2`). So `c` and `d` lie strictly on
opposite sides of the line through `P` with normal `n`; `c != d` because distinct
ring sites do not share an owned arc.
For `a`: `a` lies in the closed Voronoi cell of `c` (the switch `P_(i-1)` between
`c_(i-1)` and `c_i` is in the closure of both cells, and the open arc owned by
`c_i` has `c_i` as its nearest site), so `|a-c| <= |a-d|`. Squaring and using
`|P-c| = |P-d|`:
`|a-c|^2 - |a-d|^2 = |c|^2 - |d|^2 + 2a·(d-c) = 2 (a-P)·(d-c)`, hence
`n·(a-P) <= 0`; symmetrically `n·(b-P) >= 0`.
A line through the vertex of a cone of aperture `< pi` meets the cone in at most
one ray; since `n·(a-P) <= 0 <= n·(b-P)` and `a-P, b-P` are the extreme rays,
that single ray is strictly between them, and `c` (negative side) and `d`
(positive side) lie on opposite sides of it. Therefore the four rays occur in the
cyclic order `a-P, c-P, d-P, b-P` inside the cone.

**(2.3) Numeric confirmation of the order fact** (independent of any residual):
on the saved candidate the three directed angles
`angle(a-P, c-P)`, `angle(c-P, d-P)`, `angle(d-P, b-P)` all have the *same* sign
and their absolute values sum to `theta = pi - (w_i+w_(i+1))/2` to `4.5e-16`, for
all nine switches; and the dominance inequalities
`(d-c)·(a-P) <= 0 <= (d-c)·(b-P)`, `|a-c| <= |a-d|`, `|b-d| <= |b-c|` hold as
computed (`verify_halfplane_proof.py`).

## 3. The identity (exact; conventions frozen)

Sector triangle `i` = `(A=P_(i-1), C=c_i, B=P_i)`; `alpha_i` = angle at `C`;
`w_i` = arc width from `P_(i-1)` to `P_i`. Define, by the kernel's `atan2`
formulas (independently cross-checked against the geometric angles to `<=2e-16`):

```
  L_i := base angle at A = atan2(v_i sin alpha_i, u_i - v_i cos alpha_i)
  T_i := base angle at B = atan2(u_i sin alpha_i, v_i - u_i cos alpha_i)
         = pi - alpha_i - L_i          (u_i = |CA|, v_i = |CB|)
```

Then for every `i`, with `2 b_i` = the angle at `P_i` between the rays to `c_i`
and `c_(i+1)`:

```
   T_i + L_(i+1) + 2 b_i + (w_i + w_(i+1))/2 = pi                 (CL)
   equivalently   L_i + T_(i+1) + 2 b_i + (w_(i-1) + w_i)/2 = pi
```

Key convention point (this is where an earlier draft of this audit and two of my
own messages went wrong): **`L_(i+1)` is a base angle of the NEXT sector triangle
but is measured AT the CURRENT switch `P_i`** (its vertex `A = P_i`). Attaching
it to `P_(i+1)` produces artifacts up to `0.11` rad which must not be cited.

**Verification (`FINAL_IDENTITY.py`, console output `FINAL_IDENTITY.log`):**
`|sum - pi| <= 4.4e-16` at 9/9 switches on the saved certified candidate, and the
same on regular 9-gons at ring radius `0.86` and `0.90` (the `0.94` case is not a
cover geometry and shows a 3.6e-3 residual — consistent with the hypotheses
failing, not with the identity failing). Also verified: cone order
`a -> c_i -> c_(i+1) -> b` at all nine switches with the three directed angles of
one sign summing to `theta_i = pi - (w_(i-1)+w_i)/2`; the interior angle of `K`
equals that value; widths all positive with `sum w = 2 pi`, `max w =
0.776442795 <= 2 asin r = 0.779557680`, `min w = 0.561643842`.

## 4. Robustness / degeneracies

* **Positive widths.** `w_i > 0` by (F1) (in fact `w_i >= 2pi-16asin R > 0`), so
  no coincident switches and no zero-aperture cone; `theta in (0,pi)`.
* **Tangency** (`|P - c| = r`): the halfplane estimate in (2.1) becomes
  non-strict, the cone stays closed, `(CL)` holds as a limit; interval enclosures
  that keep the closed boundary are sound.
* **Extra equidistant site at `P`.** (2.2) uses only the *pairwise* inequalities
  with `c, d` and the closure of the Voronoi cells, so a third/fourth equidistant
  site changes nothing.
* **Collinear sector triangles** (`alpha = 0` or `pi`): the angles `T, L` are ray
  angles `0` or `pi`; `(CL)` holds by continuity, and the ring factor's closed
  domain covers it.
* **No hubs, no tiling, no perturbation.** The proof never uses hub cells, hub
  positions, the hub-hub bisector, or any covering-preserving perturbation; it
  also never needs a triangulation of `K` into fan triangles (that was the false
  step of my withdrawn draft).
* **Rank/redundancy.** Summing `(CL)` over `i` and using `sum_i w_i = 2pi`
  telescopes; the 9 equations are not independent as equations on the widths
  alone. This does not weaken the dual: arbitrary real `h_i` are allowed, and the
  bound uses the whole real span of the equations.

## 5. The owned-arc lower bound (asked explicitly)

`w_i >= 2 pi - 16 asin R > 0`. Proof: by (F1), `w_j <= 2 asin r <= 2 asin R` for
every `j`, and `sum_j w_j = 2 pi`, so
`w_i = 2 pi - sum_(j != i) w_j >= 2 pi - 8 * (2 asin R) = 2 pi - 16 asin R`.
Numeric: `2 pi - 16 asin(19/50) = 0.046444563591417459 > 0`
(`8 asin(19/50) = 3.1183703717940846 < pi`; `pi - 8 asin(19/50) = 0.0232222817957087`).
The certificate filter `q.b < qmin.a` with `qmin = 4 sin^2(pi-8asin R)/R^2` is
exactly the relaxation of this bound at the largest scale `s = R`
(`q >= 4 sin^2((2pi-16asin R)/2)/R^2`), because
`w = 2 asin(s sqrt(q)/2)` increases with `s` and `w = 2pi-16asin R` at `s = R`
gives `q = 4 sin^2(pi-8asin R)/R^2`. Numerically
`qmin = 0.014935663152905878`, and on the saved candidate the minimum width is
`0.561643842 >= 0.0464445636` and the maximum width `0.776442795 <= 2 asin r =
0.779557680`. The filter discards only infeasible boxes, and every retained box
keeps its interval enclosure, so it is sound.

## 6. Answer to the lead's sector-norm constraint question (corrected)

Geometry (all in the normalization where the two switches are on the unit circle
and the site distances are scaled): with `u, v` the two site-switch distances,
`alpha` the site angle, `q = u^2+v^2-2uv cos alpha`, chord length `d = R sqrt q`,
midpoint `M` with `|M| = kappa = sqrt(1-R^2 q/4)`, and `H = R u v sin alpha /
sqrt(q)` the distance from the site to the chord line, one has for the site `c_P`
that

```
   |c_P|^2 = kappa^2 + (l_P - H)^2 ,
   l_P = (1 - u v cos alpha)/sqrt(q)  = the chord-axis coordinate of the
         unit-circle point at distance R sin(alpha) from both endpoints ,
   2 kappa H = 2 |l_P|  at a symmetric pair (u=v) .
```

Consequences (verified in `lead_inequality.py`):

* the site-norm condition `|c_P| <= sqrt(1-R^2)` is **equivalent** to
  `(H - l_P)^2 <= R^2(1+uv cos alpha)` — an identity-level restatement, not a new
  inequality;
* the lead's literal form `R^2(1+uv cos alpha) <= 2 kappa H` therefore holds only
  on one side of the apex `H = l_P`; it fails (worst slack `-0.288`) on parts of
  the relaxed kernel box (e.g. `alpha -> 0`, `u ~ v ~ 1`, `H -> 0`), which are
  precisely outside the feasible region. It may be used only together with the
  feasibility cut that produced it.
* whether the constraint is *available* in the certificate therefore depends on
  whether the kernel's box already carries the site-norm cut; on its own the
  literal inequality is not a universally valid consequence.

## 7. Caliber caveats (not defects of the identity)

* The identity holds at the **actual** `r`; the certificate evaluates the
  geometry at `R`. Since the kernel's factor domains are boxes in the
  scale-normalized quantities containing the `s = R` slice, the dual bound is for
  the relaxed (larger) primal set and hence valid a fortiori for every `r <= R`.
  What must not be done is to use `|c|^2 <= 1 - R^2` as if it were *sharper* than
  the actual `1 - r^2` (this was the lead's radius-caliber warning; accepted).
* `(CL)` is a necessary local equation. It does not by itself produce any lower
  bound; the numerical value of the bound depends on the full factor assembly,
  whose independent verification is outside this audit.

## 8. Evidence files (this directory)

| file | role |
|---|---|
| `resolve_conv.py`, `decide.py` | final convention resolved: `T_i + L_(i+1) + 2b_i = theta_i` at the current switch, verified 9/9 |
| `final_convention.py`, `lead_convention.py` | the same identity under the lead's sector-triangle notation, with `atan2` formulas cross-checked against the geometric angles (<=2e-16) |
| `verify_halfplane_proof.py` | Voronoi dominance inequalities `(d-c)·(a-P)<=0<=(d-c)·(b-P)`, `|a-c|<=|a-d|`, `|b-d|<=|b-c|`; same-sign directed-angle checks |
| `interior_resolve.py` | interior angle `= pi-(w+w)/2` on saved candidate and regular nonagon |
| `wedge_check.py`, `switch_table.py` | signed ray-order table; switch pairs/angles/radii/widths/owners |
| `verify_saved_cover.py` | covering radius `0.379983853120 = T_cert`, Voronoi degrees 7/6 |
| `lead_inequality.py` | sector-norm constraint audit (§6) |
| `DEAD-LOCAL.md` | withdrawn arguments and failed instruments (incl. the two wrong conventions of `AUDIT-CLOSURE.md` and my first repair) |
| `AUDIT-CLOSURE.md` | withdrawn false draft (history only, rejected by the lead) |

## 9. Status of C820

The lead confirmed C820 already uses `L_i` at `P_(i-1)`, `T_i` at `P_i`, the
actual triangle branches, and the C464 citation, so no amendment was needed.
On that basis I appended an independent `claim_review` for C820 with verdict
`reviewed`: evidence this note §2–§3 plus `resolve_conv.py`,
`verify_halfplane_proof.py`, `interior_resolve.py`, `lead_convention.py`,
`final_convention.py`, `verify_saved_cover.py`; control = coordinate-only
re-derivation of the three analytic steps (Cauchy-Schwarz containment, Voronoi
sign separation, cone order and closure) including negative controls against my
two withdrawn wrong conventions.

Scope of that review: the *local* closure identity and its inference from the
covering hypotheses. It does **not** certify the certificate kernel's factor
assembly, box coverage or interval arithmetic, which remain the producer
teammate's obligation.
