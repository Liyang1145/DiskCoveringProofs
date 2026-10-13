# n=14 lead identities: VERIFIED (with three corrections)

Object: exact `th` expansion (`verify_c407_lead.py` L185–195) of
`session2/type14/out/hprec_sol.json`, sha256 `7689e60b…b9448a`, R from the file.
Reproduce: `py -3 -B members/candidate/n14_relations_final.py` →
`evidence/n14_relations_final.txt|json`; raw checks in `evidence/lead_identities.txt`.

All parameters are exact rationals read from `th`; no floats enter the decisions below.

## Status of the five proposed relations

| # | relation | residual at the data point | verdict |
|---|---|---|---|
| E0 | `A = (s+z)/2` | **0 (exact rational zero)** | holds exactly on the literals |
| E1 | `s² + r² = 1` | ~2.3e-71 | satisfied |
| E2 | `(A−z)² + (B−r)² = r²` | ~2.1e-71 (5e-62 at dps 60) | satisfied |
| E3 | `z² + t² = 2 t r` | ~2.0e-71 | satisfied |
| E4 | `C² + (1−D)² = r²` | ~−1.2e-71 | satisfied |

E0 is an exact rational equality on the literals; E1–E4 are satisfied to ~1e-71, i.e. at
the level of the 70-digit literals. **They are relations satisfied by this data point, not
identities of the parameters**, and none is proved.

## Corrections to my own checking

1. **Hole at `(0, t−r)` is a quadruple in the same-sign y-pair, not a triple.** The correct
   statement is that `(0, t−r)` is at distance `r` from `c10=(z,0)`, `c11=(−z,0)` and
   `c13=(0,t)` — the point `c12=(0,−t)` is at 0.11377, *not* `r`. My first check used the
   wrong y-pair member and printed a spurious `FAILS`; the corrected check gives residual
   ~2.0e-71 against `c13`. Symmetrically `(0, −(t−r))` pairs with `c12`.
2. `E1–E4` are **not** algebraic identities: they are nonlinear and only hold at the root.
   Only E0 is a literal identity. Treating them as "identities" would be wrong.
3. My earlier "the circle through (A,r) is trivially true" remark was vacuous (every
   `(x,0)` is at distance ≥ r from `(A,r)`); it carries no information and is withdrawn.

## Elimination and dimension

The five relations are **independent**: the Jacobian of `(E0..E4)` in
`(A,B,C,D,s,z,t,r)` has rank **5** (singular values 2.18, 1.42, 1.31, 0.62, 0.49), so the
solution set has dimension **8 − 5 = 3**.

Explicit elimination, with the branches that the data selects (**no sign ambiguity left**):

```
s = 2A − z                                    (from E0, linear)
A from   (2A − z)² = 1 − r²
t = r + sqrt(r² − z²)          [data: t − r = +0.0568866638683 = sqrt(r² − z²)]
B = r − sqrt(r² − (A − z)²)    [data: B − r = +0.122519158042]
D = 1 − sqrt(r² − C²)          [data: 1 − D = +0.157532616572]
```

Free coordinates: **(z, C, r)** — three of them, matching the Lead's "3 vars" target.
`A, s, t, B, D` are then determined by the three branch-fixed formulas, so the Lead's
"3 eqs" is realised as: *three relations among the seven magnitudes after eliminating
`A, s, t, B, D`*, plus the branch choices (which are equations, not free signs, here).

Adding one stationarity or stress condition cuts 3 → 2.

## Geometry of the holes (for the record)

Centres: `0..7 = (±A,±B),(±C,±D)`; `8,9 = (∓s,0)`; `10,11 = (±z,0)`; `12,13 = (0,∓t)`.
Deepest holes: `q = (z, r)` is at distance `r` from `c0, c10, c13`, and the relation
`|q − c0|² = r²` **is** E2, while `|q − c10|² = r²` is trivial (`= r²` identically) and
`|q − c13|² = r²` **is** E3. So the two-hole picture the Lead described is exactly the
pair (E2, E3); E0 and E1 come from the hub/tangency structure and E4 from the C,D rectangle.
