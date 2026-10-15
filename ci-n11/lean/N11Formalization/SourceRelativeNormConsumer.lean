import N11Formalization.SourceRelativeNormPacket
import N11Formalization.FlashLocalFrobeniusEnclosure
import N11Formalization.SourceBoundaryStressPositive

/-! Real relative-row-norm consumer. The transformed columns use
the EXACT proposed9R/10 metric, not the old metric's spectral properties.
Actual45 stress and exact source/canonical geometry remain unchanged.
No G/flux norm, augmented coercivity or global optimality is inferred. -/
set_option autoImplicit false
namespace N11Formalization.SourceRelativeNormConsumer
open N11Formalization RatInterval ResumeNetwork ResumeLocalIncidence
open SourceRelativeMetric SourceRelativeNormPacket SourceCompactStressIntervals
noncomputable section

theorem NB_mem (e : Fin 45) (a : Fin 4) : (NB e a).Mem (sourceN e a) :=
  mem_of_contains (NB_contains e a) (metricBox_mem e a)

private theorem magnitude_scale (e : Fin 45) (a : Fin 4) :
    ((NB e a).abs.hi : ℝ) = (mag e a : ℝ)/1000000000 := by
  simp only [NB,intv,RatInterval.abs,Rat.cast_max,Rat.cast_neg,Rat.cast_div,
    Rat.cast_intCast,Rat.cast_ofNat,mag,Int.cast_max,Int.cast_neg]
  rw [← neg_div,max_div_div_right (by norm_num : (0 : ℝ) ≤ 1000000000)]

theorem box_square_scale (e : Fin 45) :
    ((∑ a : Fin 4,(NB e a).abs.hi^2 : ℚ) : ℝ) =
      (∑ a : Fin 4,(mag e a : ℝ)^2)/1000000000000000000 := by
  simp only [Rat.cast_sum,Rat.cast_pow,magnitude_scale]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem scaled_row_inequality (S L : ℝ)
    (h : 40000*S ≤ 980100*L^2) :
    S/1000000000000000000 ≤
      ((99/200 : ℝ)*(L/100000000))^2 := by
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000000000000)).mpr
  nlinarith only [h]

/-- ALL45 carrying transformed-N rows bounded by actual source stress.
Both entry membership and finite readout are kernel-paid, not premises. -/
theorem source_row_bound (s : SourceEdge) :
    Real.sqrt (∑ a : Fin 4,(sourceN (HarmonicSourceTransport.srcFlat s) a)^2) ≤
      (99/200 : ℝ)*SourceSignedStressAssembly.stress s := by
  let e : Fin 45 := HarmonicSourceTransport.srcFlat s
  have hs := FlashLocal.sum_sq_le_of_boxes (fun a : Fin 4 => sourceN e a)
    (fun a : Fin 4 => NB e a) (NB_mem e)
  rw [box_square_scale] at hs
  have hnum := all_rows e
  change (40000 : ℤ)*(∑ a : Fin 4,(mag e a)^2) ≤
    980100*(loN e)^2 at hnum
  have hc : (40000 : ℝ)*(∑ a : Fin 4,(mag e a : ℝ)^2) ≤
      980100*(loN e : ℝ)^2 := by exact_mod_cast hnum
  have hp : (0 : ℝ) ≤ (loN e : ℝ)/100000000 :=
    div_nonneg (by exact_mod_cast loN_nonneg e) (by norm_num)
  have hroot :
      Real.sqrt (∑ a : Fin 4,(sourceN e a)^2) ≤
        (99/200 : ℝ)*((loN e : ℝ)/100000000) := by
    rw [Real.sqrt_le_left (mul_nonneg (by norm_num) hp)]
    exact hs.trans (scaled_row_inequality _ _ hc)
  have ha := (compact_mem s).1
  have hlo : (loN e : ℝ)/100000000 ≤ SourceSignedStressAssembly.stress s := by
    simpa only [compact,intv,e,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] using ha
  exact hroot.trans (mul_le_mul_of_nonneg_left hlo (by norm_num))

/-- The actual canonical51 adaptive hrow input, including slack edges.
No relative norm sign/membership/readout premise remains. -/
theorem canonical_row_bound (e : Edge) :
    Real.sqrt (∑ a : Fin 4,(canonicalN e a)^2) ≤
      (99/200 : ℝ)*SourceCentreB2Readout.canonicalStress e := by
  classical
  by_cases he : ∃ s : SourceEdge,edgeMap s=e
  · obtain ⟨s,rfl⟩ := he
    simp_rw [canonical_source]
    rw [SourceCentreB2Readout.canonicalStress,SourceAlphaOf.alphaEdge_edgeMap]
    exact source_row_bound s
  · have hz (a : Fin 4) : canonicalN e a=0 := canonical_zero_off e he a
    have hs : (∑ a : Fin 4,(canonicalN e a)^2)=0 := by simp [hz]
    rw [hs,Real.sqrt_zero]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 99/200)
      (SourceBoundaryStressPositive.canonical_nonneg e)

def canonicalNB (e : Edge) (a : Fin 4) : RatInterval :=
  if h : ∃ s : SourceEdge,edgeMap s=e then
    NB (HarmonicSourceTransport.srcFlat (Classical.choose h)) a
  else ofRat 0

/-- The same transformed N's actual204 canonical entry memberships. -/
theorem canonicalNB_mem (e : Edge) (a : Fin 4) :
    (canonicalNB e a).Mem (canonicalN e a) := by
  unfold canonicalNB
  split_ifs with h
  · have hc := canonical_source (Classical.choose h) a
    rw [Classical.choose_spec h] at hc
    rw [hc]
    exact NB_mem _ _
  · rw [canonical_zero_off e h a]
    simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)

end
end N11Formalization.SourceRelativeNormConsumer
#check @N11Formalization.SourceRelativeNormConsumer.source_row_bound
#check @N11Formalization.SourceRelativeNormConsumer.canonical_row_bound
#check @N11Formalization.SourceRelativeNormConsumer.canonicalNB_mem
#print axioms N11Formalization.SourceRelativeNormConsumer.canonical_row_bound
#print axioms N11Formalization.SourceRelativeNormConsumer.canonicalNB_mem
