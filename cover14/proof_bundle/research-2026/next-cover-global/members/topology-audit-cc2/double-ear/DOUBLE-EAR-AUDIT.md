# Independent audit — q11 double-all-ring-face exclusion (lead/Q11-DOUBLE-EAR-EXCLUSION.md)

Scope: `members/topology-audit-cc2/double-ear/`. Route commandcode2/deepseek/deepseek-v4-flash.
Evidence: `double-ear-audit.json`; repro `py -3 -B audit_double_ear.py`.

## Verdict

**The measure argument is CORRECT and the margin is independently certified exactly. The
catalogue reduction 5277 → 1273 is reproduced exactly (retained set and by-chord histogram
identical to the lead's).** Two statements of my first version (claim C1174, retracted) were
wrong: the "2618 fan-plane artifacts" (they are wrap-around ears that my sorted-gap test
rejected) and "every row carries a genuine all-ring face" (the 85 chord-0 rows have none).
Corrected below.

## 1. Arc-measure bookkeeping (independently re-derived)

For an all-ring (3-ring) dual face with common witness p: each of its three ring sites c_i is at
distance ≤ r from p, and every point x ∈ J_i satisfies |x−c_i| ≤ r. Triangle inequality gives
|x−p| ≤ 2r. With 2r < 1 the set S¹ ∩ B(p,2r) is a single arc of length ≤ 2·asin(2r), and the
three owned arcs have pairwise disjoint interiors, so

    |J_i| + |J_j| + |J_k| ≤ 2·asin(2r).

For a PAIR of VERTEX-DISJOINT all-ring faces the six arcs are distinct (six different owner
sites) and lie in two arcs of length ≤ 2·asin(2r); the remaining q−6 = 5 owner arcs each have
length ≤ 2·asin(r) (owner centre norm ≤ √(1−r²) after inner-root normalisation). Since the owner
arcs partition S¹ up to finitely many tie points,

    2π ≤ 4·asin(2r) + 10·asin(r).                                        (★)

**Ear identification, corrected.** An all-ring face is a triangle of the complex whose three
vertices all belong to the ring part; its three vertices are therefore pairwise adjacent in the
11-cycle, i.e. it is a consecutive triple {i−1,i,i+1}. Correct test:
`any(set(f) == {(i-1)%11, i, (i+1)%11} for i in range(11))`. My first test compared sorted
successive gaps to 1 and rejected every wrap-around triple ({10,0,1}, {9,10,0}, ...); that was
the only source of the alleged artifacts. With the wrap-aware test **all 13212 all-ring faces in
the 5277 stored face-lists pass and 0 fail**. So there are no fan artifacts: fanning a larger
dual face always adds triangles containing the fanning hub, never an all-ring face.

**Soundness of the pruning rule, corrected.** In a realizing metric cover, every all-ring face F
of a q11 complex has a common witness (its dual vertex), so (★) applies to every F. Hence a
complex containing two VERTEX-DISJOINT all-ring faces cannot be realized, and dropping such
complexes is sound. The earlier "at least one genuine face per row" justification is not needed
(and was false for the 85 chord-0 rows, all of which are retained).

## 2. Exact rational certificate (independently recomputed in Fractions)

* asin positive series with explicit positive tail x^(2N+1)/(1−x²) (coefficients
  C(2n,n)/(4^n(2n+1)) ≤ 1) as upper bound; Machin π = 16 atan(1/5) − 4 atan(1/239) with
  alternating-series two-sided bounds as lower bound for π.
* At r = U: rhs_upper = 6.28314636831364, 2π_lower = 6.28318530717959,
  **margin_lower = 3.8938865943428866e−05 > 0** (lead display 3.8938865969777676e−05; the
  2.6e−12 difference is float-display noise).
* Control: at r = 1/3 the same computation gives ≈ −3.409e−02 < 0, so the certificate is
  sensitive and the r < 1/3 threshold is genuine.
* Monotonicity: d/dr[4 asin(2r)+10 asin(r)] = 8/√(1−4r²) + 10/√(1−r²) > 0 on [0,1/2), so
  positivity at U gives positivity for every r ≤ U.

## 3. Catalogue reduction 5277 → 1273 (wrap-aware re-derivation)

* retained = 1273, removed = 4004; retained index set equals the lead's; by total chord count
  kept/removed = (85/0, 557/0, 520/1080, 105/1832, 6/957, 0/135) for chords 0..5; totals
  1273 and 4004 ✓; all 5-chord rows removed.
* per-row all-ring-face counts: 0:116, 1:698, 2:1791, 3:1838, 4:752, 5:82; 9 of the 11
  possible ears actually occur in the catalogue.

## 4. Conditions and one q10 caveat

1. "All-ring face" = consecutive triple {i−1,i,i+1}; the wrap-aware test identifies them (all
   13212 pass, 0 artifacts).
2. The pair must be VERTEX-DISJOINT; overlapping ears would double-count owned arcs and are not
   covered (as the lead's note already states).
3. q11-only; 1273 necessary graphs remain.
4. **This exclusion does NOT transfer to q10 unchanged.** For q10 (4 interior sites) the
   one-face analogue gives only 2π ≤ 2·asin(2r) + 14·asin(r) = 7.06 > 2π at U, and for two
   disjoint ears the remaining six arcs would have to cover ≈ 2π − 4·asin(2r) = 4.70 rad while
   six arcs of length ≤ 2asin r give 4.06 rad — a genuine but much thinner margin (4.06 vs
   4.70 leaves the middle segments), so the clean contradiction is specific to the q11 count
   (q−6 = 5 remaining arcs). Any q10 analogue needs its own margin computation.

## 5. What is NOT established here

Metric realizability of the 1273 survivors, the q10 family, the final q11 exclusion, and the
k10/k11 optimum. This note certifies: (a) (★) is false at r ≤ U with the certified margin,
(b) the wrap-aware ear identification leaves no artifacts, (c) the 5277 → 1273 reduction is
reproduced exactly, (d) the rule is sound for q11.
