# Audit of the repaired-TC-root geometric assembly (`R20-TC-ROOT-COMPLETENESS.md`)

Scope: `research-2026/team-current/r20-rigidity/` only. Read-only inputs: `../lead/repaired_tc_krawczyk.json`
(Krawczyk box), `../lead/REPAIRED-TC-ROOT-INTERFACE.md`, `../session2/n11tc/py/tc_s33_kkt.py`,
`../session2/n11tc/py/tc_s32_kraw.py` (the `res5` definition). No claim registered (lead owns
registration). Instruments: `r20_tc_box_audit.py` -> `r20_tc_box_audit.json` (+ log) and
`r20_tc_delaunay_completeness.py` -> `r20_tc_delaunay_completeness.json` (+ log); the original
`r20_tc_root_independent.py` was re-run after the box fix (log regenerated).

Verdict in one line: the geometric assembly is repairable and now repaired — two defects were
found (box endpoints; the cocircularity inference) and both are fixed, and the two missing
completeness obligations are now discharged by different instruments, so the chain
`root box -> Delaunay list = triangulation -> Voronoi vertices = 11 circumcentres -> R_D = R`
holds as an *upper bound* argument, conditional only on the read-only Krawczyk certificate.

---

## 1. Defect A (fixed): interval box built with rounded float endpoints

`r20_tc_root_independent.py` line 50 used `mp.iv.mpf([CH[i]-RAD, CH[i]+RAD])`. Both
`CH[i]-RAD` and `CH[i]+RAD` are binary64 operations that round to nearest, so the resulting
interval does **not** necessarily contain the certified box `[c-rad, c+rad]`.

* measured defect (exact binary64 rationals, all 12 coordinates): the true endpoint lies
  outside the old interval by at most `2.723e-17`; both directions occur.
* fix: `iv(CH[i]) + iv([-RAD, RAD])`, i.e. the exact centre plus the exact displacement
  interval (this is what `lead/repair_tc_krawczyk.py certify()` itself does on line 42).
  With the fix the certified box is contained with `0` defect (outward rounding only).
* size check: the defect is 14 orders below the smallest branch margin (`1.093e-3`), so all
  readings are unchanged (re-run reproduces the same numbers), but the *claim* "interval over
  the whole root box" is only valid after the fix. Same defect class as the withdrawn C408
  (point radius / rounded endpoint), hence recorded explicitly.
* positivity decisions: the re-run script now also decides the two central positivity claims on
  the exact interval endpoints (`min_empty_margin_exact = 0.1504954350807983567`,
  `min_inside_D_margin_exact = 0.61197353225160098382`) and prints conservative rational
  thresholds (`0.15`, `0.61`). Float margins remain as summary readings only.

## 2. Defect B (fixed): `empty circle` does not imply `no 4 cocircular`

`R20-TC-ROOT-COMPLETENESS.md` §3 inferred "since no margin is zero, there are no four cocircular
sites". That inference is invalid **and false here**:

* the empty-circle check only excludes cocircular quadruples whose circle is a *listed face's*
  circumcircle and *empty*; a cocircular quadruple with a non-empty circle is invisible to it;
* `r20_tc_box_audit.py` [C] tests all 330 quadruples with the translated circle determinant
  `det[xj-xi, yj-yi, |pj|^2-|pi|^2]`; 324 of them are certified non-cocircular on the whole box
  (`|det| >= 5.6e-8`); the remaining **6 are exactly cocircular**:
  `{C0,C1,C7,C8}, {C0,C2,C6,C8}, {C0,C3,C5,C8}, {C1,C2,C6,C7}, {C1,C3,C5,C7}, {C2,C3,C5,C6}`.
* these 6 are precisely the mirror-symmetric quadruples: two mirror pairs always have their
  common centre on the axis of reflection (their perpendicular bisectors coincide with that
  axis), so they are cyclic *exactly*, not approximately. "No 4 sites cocircular" is therefore
  **false** and must not be claimed.
* what is true and sufficient: **no empty cocircular quadruple**. `r20_tc_delaunay_completeness.py`
  [G] rebuilds each of the 6 circles from the symmetry (centre on the axis, radius from two
  sites) and exhibits a site strictly inside it on the whole box, with margin
  `>= 0.61070938122121436004` (witnesses: H1 for five of them, H0 for `{C1,C3,C5,C7}` and
  `{C2,C3,C5,C6}`). Non-empty cocircular quadruples are exactly those that do not create a
  degenerate Delaunay cell, so the Delaunay subdivision is a triangulation.

This is exactly the distinction the lead flagged: absence of *empty* cocircular quadruples is
enough for a unique Delaunay triangulation; the empty-circle margin alone decides neither
direction of the general cocircularity question.

## 3. Two further findings (not defects, but they change what has to be checked)

1. **`(C4,H0,H1)` is exactly collinear** (`theta_4 = 0` identically, all three on the x-axis).
   The collinear triple is harmless: it has no circumcircle, so it produces no Voronoi vertex,
   and it is not a supporting line (sites on both sides), so no degenerate `infinite-radius`
   Delaunay cell. It does mean "no 3 collinear" must not be quoted as a hypothesis; the count
   argument (F5 below) does not need it.
2. **The reflection symmetry is exact, not merely "verified to 2e-7".** The parameterisation
   `a = (a0,a1,a2,a3,a4,a3,a2,a1,a0)`, `a4 = pi-2(a0+..+a3)`, `theta_4 = 0` gives
   `theta_{8-k} = -theta_k` and `rho_{8-k} = rho_k` as *identities* at the parameter level, so
   `C_k -> C_{8-k}`, `U_k -> U_{7-k}`, hubs fixed. The `1.986e-07` / `2.319e-07` residuals in the
   log are interval-evaluation slack of the box (width `2e-9`), not model error. This is what
   promotes the 4 fan equations `k=1,2,3,8` and the single central equation `k=6` to the
   full 9 active circumcentre ties (plus the 9 boundary ties) exactly.

## 4. Completeness: what was missing and what now closes it

The original text checked combinatorial incidence (V, E, F, Euler, edge multiplicities, site
coverage) but combinatorial counts plus positive areas do **not** by themselves exclude an
overlapping or crossing face list. `r20_tc_delaunay_completeness.py` adds, all on the corrected
box and with decisions on exact interval endpoints:

| id | statement | reading |
|---|---|---|
| F1 | 210 edge pairs: no two edges meet except in a common endpoint (no proper crossing, no collinear overlap) | 0 violations, 0 undecided |
| F2 | 88 (face, other site) pairs: no site lies in the closed triangle of another face | 0 violations |
| F2b | 231 (edge, other site) pairs: no site lies in the interior of an edge | 0 violations |
| F3 | 55 face pairs: interiors disjoint (12 adjacent by opposite-side orientation; the rest by F1 + F2 restricted to non-shared vertices) | 55/55 certified |
| F4 | hull = the ring nonagon, both hubs strictly inside | min orientation margin `5.402e-2` |
| F5 | V=11, E=21, F=11, Euler=1, outer boundary = 9 hull edges | `2E-9 = 33 = 3F` |

Consequence (F5 is the counting step): the 21 edges form a connected plane straight-line graph;
`F_total = E-V+2 = 12`, so 11 bounded faces, and the sum of their side counts is `2E-9 = 33 = 3*11`,
so every bounded face is a triangle. By F1+F2+F2b+F3 each listed triangle is one of those
bounded faces and the list has exactly 11 members, so the listed triangles **are** the bounded
faces: a genuine triangulation, not a sub-complex and not an overlapping cover.

Consequence (G): with no empty cocircular quadruple, the Delaunay subdivision has no cell with
`>= 4` vertices; combined with the strict empty-circle margins (`>= 0.1505`) the subdivision is a
triangulation and equals the listed face list. Hence the Voronoi vertices of the configuration are
exactly the 11 circumcentres, and all 11 are strictly inside `D` (`>= 0.61197`).

## 5. Independent controls actually run

* **Circumcentre recomputation vs structure prediction**: every active fan face's Cramer
  circumcentre lies within `<= 4.7e-7` of its pin `U_k`; the central faces within `<= 1.3e-8` of
  `(m,+/-h)`; the two slack faces differ from their pins by `1.690e-3`, consistent with their
  circumradius `R - 1.151e-3` (`circumradius^2 - R^2 in [-8.747e-4,-8.746e-4]`, and
  `(r-R)(r+R) = -8.75e-4` gives `r-R = -1.151e-3`). So the "active/slack" split is reproduced by
  an instrument that does not use the pins to compute the circumcentre.
* **Incircle determinant control**: for every (face, other site) pair the polynomial incircle
  determinant is computed (translated 3x3 form, no division) with the correct orientation sign;
  the largest signed value is `-0.0463 < 0`, i.e. it agrees with the distance-based empty-circle
  test for all 88 pairs. Two different expressions of the same predicate, same verdict.
* **Angle sums and area sum** (completeness consistency, interval containment): at each ring site
  the sum of face angles equals the nonagon interior angle and at each hub it equals `2*pi`, each
  difference interval of half-width `<= 9.2e-7` containing `0`; `sum(face areas) - hull area` is
  `0` to `+/-2.8e-7`. These are consistency checks (containment, not exactness) — they are
  *not* used as the proof of completeness; F1-F5 are.

## 6. What this audit does and does not establish

**Establishes (conditional on the read-only Krawczyk certificate).** For the exact root of the
12D symmetric system in the box: branch legality; the 9 active faces have circumradius exactly `R`
(by the root equations `f5 = 0` plus the exact pin/quadratic/hub identities); the 2 slack faces
are strictly below `R`; the listed faces are the complete Delaunay triangulation of the 11 sites
with strict empties; every Voronoi vertex of the configuration is one of the 11 circumcentres and
lies strictly inside `D`; the boundary `dD` is covered within `R` by the ring disks (arcs tile by
`sum a = pi`, exact by construction). Hence `R_D(root configuration) = R`, i.e.
`r_D(11) <= R` — an **upper bound** only.

**Does not establish.** (i) existence/uniqueness of the root (read-only input, 12D symmetric
system; audited separately in `r20-geometry/AUDIT-REPAIR-TC-KRAWCZYK.md`); (ii) anything below `R`
for `n = 11` (global lower bound untouched); (iii) that no four sites are cocircular — that
statement is false here and is not used; (iv) interval-kernel independence from `mpmath.iv` (both
audit scripts use the same backend at the same precision; no second backend was built, per the
lead's instruction that none is needed); (v) the active equations are used analytically (the root
system *is* those equations), not by finding an interval containing zero.

## 7. Repro

```
py -3 -B -X utf8 r20_tc_root_independent.py          # re-run after the box fix
py -3 -B -X utf8 r20_tc_box_audit.py                 # box defect + exact-endpoint decisions + 330 determinants
py -3 -B -X utf8 r20_tc_delaunay_completeness.py     # F1-F5 triangulation certificate + G non-empty cocircular quadruples
```
