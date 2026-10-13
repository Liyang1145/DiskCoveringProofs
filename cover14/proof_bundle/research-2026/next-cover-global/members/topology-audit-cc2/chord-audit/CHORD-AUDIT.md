# Audit — q11 double-chord exclusion (lead/Q11-DOUBLE-CHORD-EXCLUSION.md, C1177) — corrected

Scope `members/topology-audit-cc2/chord-audit/`. Route commandcode2/deepseek/deepseek-v4-flash.
Evidence `chord-audit.json`; repro `py -3 -B audit_double_chord.py`.

## Corrections of my own earlier text (both errors were mine)

1. **`3L > B` is NOT a valid exclusion and I withdraw it.** Each owned arc is bounded ABOVE by
   L = 2·asin(ρ); a bound of the form 3L > B (B = 2·asin(2ρ)) says nothing about three SHORTER
   arcs. My earlier claim "at most two whole arcs fit in an arc of length ≤ B" reversed the
   direction of the inequality. C1177 does not need it and my "free stronger consequence" (one
   ear already impossible) is withdrawn.
2. **`S¹ ∩ B(p,a)` is never two complementary arcs.** Correct shape (verified numerically):
   with A = (1 + |p|² − a²)/(2|p|), the set is
     * empty iff A > 1 (equivalently |p| < 1 − a),
     * a single point / a single arc of measure 2·acos(A) for |A| ≤ 1,
     * the whole S¹ for A ≤ −1 (equivalently a ≥ 1 + |p|).
   In no case two components. My "two arcs, each of length ≤ B" paragraph is deleted.
3. Correct size statement: the bound |S¹ ∩ B(p,a)| ≤ 2·asin(a) holds only **with the restriction
   |p| ≥ 1 − a**; without it the measure can be 2π. In this problem the witness satisfies
   |p| ≥ 1 − 2ρ (every owner site has |c| ≥ 1 − ρ and the witness is within ρ of three such
   sites), which is exactly the restriction 1 − a = 1 − 2ρ. So "K is a single arc of length
   ≤ B = 2·asin(2ρ)" is correct as the lead wrote it, and my correction (i) was wrong.

## What the audit positively checks

* **Constants at ρ = U**: B = 2·asin(2U) = 1.450878, L = 2·asin(U) = 0.676278,
  2B + 5L = 6.283146 < 2π ✓ (and it FAILS at ρ = 1/3 − 1e-9: 6.317280 > 2π), so U is inside the
  range where the two-disjoint-triple bound bites.
* **Cap formula**: measure(S¹ ∩ B(p,a)) = 2·acos((1+|p|²−a²)/(2|p|)) with the empty/single/whole
  cases above; verified against direct sampling at (a,|p|) = (0.4,0.5), (0.8,0.5), (0.2,0.5),
  (0.9,0.3), (0.6635,0.5), (1.5,0.6).
* **Distance-exactly-2 graph on C11**: 0 triangles, maximum matching 5 ⇒ three middles pairwise
  at distance 2 do not exist, so at most 2 chords. The lead's "not C11²" warning is correct and
  checked.
* **Catalogue reproduced**: kept 1042, removed 4235, retained-index set equal to
  `lead/q11-double-chord-pruning.json`, by-chord kept/removed (85/0, 557/0, 400/1200, 0/1937,
  0/963, 0/135), newly removed beyond double-ear 231, no structural violation (all 2-chord
  survivors have middle distance in {2,9}).

## Status of the three-arc bound

`|J_{i−1}| + |J_i| + |J_{i+1}| ≤ B` for the three consecutive owner arcs of one all-ring face is
what C1177 uses. I did not prove it and I do not claim it. What is established: each arc is ≤ L,
so the sum is ≤ 3L = 2.0288 > B, and a direct search over witness-plus-three-sites
configurations at ρ = U gives maximum sum 1.437 (ratio 0.990 of B) with all three arcs positive —
consistent with the bound and numerically tight, but a numeric search is not a proof. The missing
argument, if the bound is to be load-bearing: the three arcs lie in one connected subset
K_j ⊆ S¹ ∩ B(p,2ρ) with |K_j| ≤ B and COVER it up to negligible sets (partition argument), so
Σ ≥ |K_j|; together with pairwise-disjointness of the arcs inside K_j (Σ ≤ |K_j|) this gives
Σ = |K_j| ≤ B. Neither "3L > B" nor containment alone supplies that.

## Correction to C1176's q10 caveat (recorded, per lead's instruction no new claim)

2·asin(2U) + 14·asin(U) = 6.184824 < 2π, NOT > 2π. My earlier caveat on C1176 is wrong; read
that sentence as amended.

## Not established

Metric realizability of the 1042 survivors; the q10 family; any optimum. The area-relaxation
route is withdrawn by the lead (owned-subarc wedge inequality false at r = U). No area claim is
audited or made here.
