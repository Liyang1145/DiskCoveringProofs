# AUDIT RESULT — topology-audit-cc2 (one full-interface audit, closed)

Route commandcode2/deepseek/deepseek-v4-flash. Write scope: this directory.
Evidence: `evidence/`. Repro commands at the bottom, all runnable from this directory.

## Two reliable results (the deliverable)

### R1. Full-cell lemma (used by §2–§3 of OWNER-COUNT-UNIFICATION.md)
Claim C1170, proof in `SECTION2-FULL-CELL-LEMMA.md` §1.
* If the closed convex Voronoi cell W_i of an interior site c_i meets S^1 at a point of int W_i,
  the intersection contains a positive-length arc.
* If W_i ∩ S^1 is empty then W_i is compact inside the OPEN disk, so the outward clip
  (domain D_(1+ε), radius r+ε) assigns the site no boundary ownership for small ε>0 — this is
  what §3 line 17 asserts.
* The genuinely degenerate case (W_i meeting S^1 in a tangential singleton) is possible only as
  an ownership TIE under non-strict nearest ownership, which is exactly why the ε-clip is
  necessary; it is not removed by any strictness lemma.

### R2. Independent enumeration / set equality (interfaces I4/I5 of K10-CATALOGUE-AUDIT)
Claim C1168, evidence `evidence/compare-stored.json`.
From-scratch pipeline (imports nothing from any generator): all connected hub graphs by brute
force, forced hub-only triangle count h = e − m + 1, hub multigraph multiplicity 2 − h_e, all
Euler circuits, all weak compositions, faces built from the walk, validity by an independent
simplicial-disk test, classes by minimisation over the full group D_N × S_m (invariance tested).

| object | raw valid | classes | stored | stored classes | set equality |
|---|---|---|---|---|---|
| n12 N=9 m=3 (calibration) | 262 | 51 | 51 | 51 | YES |
| n14 N=10 m=3 | 348 | 68 | 93 | 68 | YES |
| n14 N=10 m=4 | 21084 | 932 | 1442 | 932 | YES |
| lead corrected 10/3, 10/4 | — | 68, 932 | 68, 932 | 68, 932 | YES |

Also: the CURRENT generator's canonicalisation (`lead/gen_k10_fixed_copy.py`, reflection
v ↦ sh − v) is a genuine group invariant (0 violations / 3240 transformed paths) and gives the
same 68 classes; the old file's v ↦ 2sh − v is the source of the 1535 overcount.

## Interface coverage and verdicts
| # | interface | verdict |
|---|---|---|
| I1 | same-arc inner-root -> coverage survives | PASS (inner-root containment 1674/1674, 0 violations; projection direction verified analytically after an early reversed probe) |
| I2 | bisector / connected ownership / 10 arcs + 10 switches | PASS for the strict inequality refinement (equal norms ⇒ d=0; unequal ⇒ d < (|ci|+|cj|)/2 < s); singleton ownership is a legitimate TIE case, not excluded — the clip handles it |
| I3 | collar / hub cells inside gamma | my F3 counterexample withdrawn (illegal); no legal counterexample found |
| I4 | Euler-walk enumeration completeness | PASS (raw counts and class sets reproduced exactly) |
| I5 | canonicalisation / count 1000 | PASS (1535 reps carry exactly 68+932 classes) |

## Withdrawn items (kept in FINDINGS.md for the record, do not reuse)
* F3 hub-facet-midpoint counterexample — placed hubs on S^1, illegal.
* probe Z2/Z3 ownership-jump counterexample — the tangent configuration is not a cover
  (covering radius ≈0.735 >> U).
* "no singleton owner" and "3-ring dual face impossible" corollaries — FALSE; claim C1169
  retracted.
* "current full_canon is not invariant" — applies to the old file only.
* probe_owners.py T1a/T1b direction error; probe_hidden2.py random sweep killed by budget.

## Residual risk (outside this audit's scope)
The 1000-graph reduction remains conditional on (K1)–(K4) (k10 ownership, no-chord, C1142,
coverage). This audit certifies the finite list and the full-cell/clip interface, NOT that every
k10 cover maps into the list. k11 has no established hypotheses: the 85-graph catalogue is not
a global statement.

## Repro
```
py -3 -B enum_indep.py 10 4          # independent raw enumeration (21084 valid, 932 classes)
py -3 -B canon_check.py 10 3         # invariance test
py -3 -B compare_stored.py           # set equality vs stored and corrected catalogues
py -3 -B geo_check.py                # inner-root dominance + §4 constants + clip guard
```
