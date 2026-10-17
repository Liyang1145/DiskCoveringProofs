import N11Formalization.SourceExactRoot
import N11Formalization.FlashTenBoundaryTwoCircle
import N11Formalization.FlashTenBoundarySeg1
import N11Formalization.Interval.ArcsinBracket

/-!
# DSH-TOPO-C1 probe: real signatures consumed by the ten-boundary exclusion

Interface probe only — **no theorem, no proof, no claim**. Purpose (handoff §4 / task-1):
print the *actual* types of every object the ten-boundary exclusion consumes, so that the
argument skeleton in `evidence/dsh/topology/ten-boundary/NOTES.md` is tied to signatures
rather than to names. Everything here is `#check` / `#print axioms`; the output is the
evidence, kept verbatim in the gate log.

Write scope: `lean/N11Formalization/DSHTenBoundaryProbe.lean` (new file, DSH-TOPO prefix).
-/

open N11Formalization

/-! ## 1. The cover object and the boundary predicate (the full domain) -/

#check @N11Formalization.Covers
#check @N11Formalization.unitDisk
#check @N11Formalization.Covers.mono
#check @N11Formalization.Covers.nonneg
#check @N11Formalization.MeetsCircle
#check @N11Formalization.BoundaryIdx
#check @N11Formalization.boundaryIdxFintype
#check @N11Formalization.MeetsCircle.mono
#check @N11Formalization.one_sub_le_norm_of_meetsCircle
#check @N11Formalization.not_meetsCircle_of_norm_le
#check @N11Formalization.nine_le_card_boundary
#check @N11Formalization.card_boundaryIdx_le_ten
#check @N11Formalization.card_boundaryIdx_eq_nine_or_ten

/-! ## 2. The existing ten-boundary interface and its unpaid atom -/

#check @N11Formalization.hub_offset_le
#check @N11Formalization.C450Atom
#check @N11Formalization.C450AtomOffset
#check @N11Formalization.c450_of_c450_offset
#check @N11Formalization.not_card_boundaryIdx_eq_ten
#check @N11Formalization.card_boundaryIdx_eq_nine_of_c450

/-! ## 3. The analytic spine (kernel-proved reduction of the atom to arc integrals) -/

#check @N11Formalization.angPt
#check @N11Formalization.continuous_angPt
#check @N11Formalization.circle_integral_le_sum_arc_integrals
#check @N11Formalization.circle_covered_by_others
#check @N11Formalization.TrigDensity
#check @N11Formalization.TrigDensity.toFun
#check @N11Formalization.TrigDensity.nonneg_toFun
#check @N11Formalization.two_pi_mul_le_sum_arc_integrals
#check @N11Formalization.two_circle_capacity
#check @N11Formalization.c450_capacity_contradiction

/-! ## 4. The exact per-disk certificate quantity (source variables t, v=cos φ, e, root sign) -/

#check @N11Formalization.c450Q
#check @N11Formalization.C450Seg1Data
#check @N11Formalization.cos_two_mul_of_cos
#check @N11Formalization.cos_three_mul_of_cos

/-! ## 5. The paid source-root interval (what the exclusion is actually consumed at) -/

#check @N11Formalization.SourceExactRoot.sourceRadius
#check @N11Formalization.SourceExactRoot.sourceRoot
#check @N11Formalization.SourceExactRoot.sourceRadius_eq_Rstar
#check @N11Formalization.SourceExactRoot.sourceRadius_mem_box
#check @N11Formalization.SourceExactRoot.sourceRadius_pos
#check @N11Formalization.SourceExactRoot.sourceRadius_lt_threshold
#check @N11Formalization.boxLoCert
#check @N11Formalization.boxHiCert
#check @N11Formalization.boxHiCert_six_lt_R0
#check @N11Formalization.boxHiCert_six_lt_R0_real
#check @N11Formalization.Rstar_lt_R0_of_krawczyk

/-! ## 6. The interval / arc-function kernel available for eliminating the gap -/

#check @N11Formalization.ArcsinBracket.arcsin_19_50_mem
#check @N11Formalization.ArcsinBracket.arcsin_bracket_of_kernel
#check @N11Formalization.ArcsinBracket.arc_L_mem
#check @N11Formalization.sinLoNLag
#check @N11Formalization.sinLoNLag_le_sin
#check @N11Formalization.sin_le_sinHiNLag
#check @N11Formalization.sqrtLo_le_sqrt
#check @N11Formalization.sqrt_le_sqrtHi
#check @N11Formalization.sinI_mem
#check @N11Formalization.cosI_mem

/-! ## 7. The counting-side control input (why counting alone cannot exclude ten) -/

#check @N11Formalization.card_mul_two_arcsin_ge_two_pi
#check @N11Formalization.card_mul_two_arcsin_ge_two_pi_of_covers_disk
#check @N11Formalization.not_eight_ball_covers_disk_of_lt_R0

/-! ## 8. Axiom profile of every input the exclusion relies on -/

#print axioms N11Formalization.hub_offset_le
#print axioms N11Formalization.not_card_boundaryIdx_eq_ten
#print axioms N11Formalization.card_boundaryIdx_eq_nine_or_ten
#print axioms N11Formalization.two_circle_capacity
#print axioms N11Formalization.c450_capacity_contradiction
#print axioms N11Formalization.SourceExactRoot.sourceRadius_mem_box
#print axioms N11Formalization.boxHiCert_six_lt_R0
#print axioms N11Formalization.ArcsinBracket.arcsin_19_50_mem
