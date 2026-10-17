import N11Formalization.SourceFineResponseIntervals
import N11Formalization.SourceFineBPointPacket

/-! Actual raw two-spoke scalar response identity. Canonical columns remain
siteMap(raw), H20 uses true Fin11 source slots, source stress remains LENGTH.
Finer scalar boxes are inputs, not augmented coercivity certificates. -/
set_option autoImplicit false
namespace N11Formalization.SourceRawResponseIntervals
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceActiveLaplacian SourceActiveHarmonicSolve SourceActiveFiniteSystem
open SourceResponseFluxIdentity SourceHarmonicMaximumPrinciple
open SourceFineCompactStressIntervals SourceFineResponseIntervals
noncomputable section

def rawResponse (k l : Fin 9) : ℝ := sourceResponse (siteMap k) (siteMap l)
def rawH0 (k l : Fin 9) : ℝ := SourceResponseKernelConsumer.H0 (siteMap k) (siteMap l)

theorem siteMap_injective : Function.Injective siteMap := by decide
theorem activeH_site (i : Fin 11) (j : Fin 9) :
    activeH (.inl i) j=H20 j (Fin.castAdd 9 i) := by
  change _=activeH (nodeEquiv.symm (nodeEquiv (.inl i))) j
  rw [Equiv.symm_apply_apply]

/-- No flux/response/H/geometry premise; delta is subtracted before summing. -/
theorem rawResponse_two_spokes (k l : Fin 9) :
    rawResponse k l=
      ∑ s : Fin 2,SourceSignedStressAssembly.stress (.inl (k,s))*
        ((if k=l then 1 else 0)-H20 (siteMap l) (Fin.castAdd 9 (spokeSite k s))) := by
  unfold rawResponse
  rw [actual_response_anchor_flux,Fintype.sum_sum_type]
  have hf (p : Fin 9 × Fin 3) :
      anchorRow (.inr p) (siteMap k)=0 := rfl
  simp only [hf,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
  rw [Fintype.sum_prod_type]
  simp_rw [anchorRow_spoke,K_spoke]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro s _
    rw [activeH_site]
    have he : siteMap k=siteMap l ↔ k=l := siteMap_injective.eq_iff
    simp only [he]
    split_ifs <;> ring
  · intro n _ hn
    have he : siteMap n≠siteMap k := fun h => hn (siteMap_injective h)
    simp only [if_neg he,mul_zero,zero_mul,Finset.sum_const_zero]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

def responseBox (k l : Fin 9) : RatInterval :=
  SourceActiveMatrixIntervals.sumI (fun s : Fin 2 =>
    mul (compact (.inl (k,s)))
      (sub (ofRat (if k=l then 1 else 0))
        (clippedHBox (Fin.castAdd 9 (spokeSite k s)) (siteMap l))))

theorem responseBox_mem (k l : Fin 9) : (responseBox k l).Mem (rawResponse k l) := by
  rw [rawResponse_two_spokes]
  have hd : (ofRat (if k=l then 1 else 0)).Mem (if k=l then (1 : ℝ) else 0) := by
    by_cases h : k=l
    · simp only [if_pos h]
      simpa only [Rat.cast_one] using ofRat_mem (1 : ℚ)
    · simp only [if_neg h]
      simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)
  exact SourceActiveMatrixIntervals.sumI_mem (fun s =>
    mul_mem (compact_mem (.inl (k,s))) (sub_mem hd (clippedHBox_mem _ _)))

theorem rawResponse_symmetric (k l : Fin 9) : rawResponse k l=rawResponse l k :=
  ResumeResponseProperties.response_symm SourceCentreB2Readout.canonicalStress
    (ResumeHarmonic.coeff SourcePositiveHarmonicConsumer.sourceH) _ _

def symmetricResponseBox (k l : Fin 9) : RatInterval :=
  SourceResponseLinearIntervals.intersectBox (responseBox k l) (responseBox l k)
theorem symmetricResponseBox_mem (k l : Fin 9) :
    (symmetricResponseBox k l).Mem (rawResponse k l) :=
  SourceResponseLinearIntervals.intersectBox_mem _ _ _ (responseBox_mem k l)
    (by rw [rawResponse_symmetric]; exact responseBox_mem l k)

def anchorNode (k : Fin 9) : Fin 29 := ⟨k.val,by omega⟩
def anchorBox (k : Fin 9) (q : Fin 2) := SourceFineBPointPacket.pointI (anchorNode k) q
theorem anchorBox_mem (k : Fin 9) (q : Fin 2) :
    (anchorBox k q).Mem ((arcEnd SourceExactRoot.sourceRoot k).ofLp q) := by
  have h := SourceFineBPointPacket.pointI_mem (anchorNode k) q
  dsimp only [anchorNode] at h
  rw [SourceN2.srcX2_anchor] at h
  exact h

def innerBox (k l : Fin 9) : RatInterval :=
  add (mul (anchorBox k 0) (anchorBox l 0)) (mul (anchorBox k 1) (anchorBox l 1))
theorem innerBox_mem (k l : Fin 9) :
    (innerBox k l).Mem (inner ℝ
      (FlashLocal.circleTangent (sourceAngle (siteMap k)))
      (FlashLocal.circleTangent (sourceAngle (siteMap l)))) := by
  rw [FlashResponseHessianFlux.circleTangent_inner_eq_circleMap,
    ← sourceAnchors_circle,← sourceAnchors_circle]
  change (innerBox k l).Mem (inner ℝ
    (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot (siteMap k))
    (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot (siteMap l)))
  rw [FlashRootNetwork.hU_siteMap,FlashRootNetwork.hU_siteMap,PinTangentGeometry.inner_coords]
  exact add_mem (mul_mem (anchorBox_mem k 0) (anchorBox_mem l 0))
    (mul_mem (anchorBox_mem k 1) (anchorBox_mem l 1))

def offBox (k l : Fin 9) := mul (mul (ofRat 2) (symmetricResponseBox k l)) (innerBox k l)
theorem rawH0_off (k l : Fin 9) (hkl : k≠l) :
    rawH0 k l=2*rawResponse k l*inner ℝ
      (FlashLocal.circleTangent (sourceAngle (siteMap k)))
      (FlashLocal.circleTangent (sourceAngle (siteMap l))) := by
  rw [rawH0,SourceResponseKernelConsumer.H0_eq_hsrc]
  exact FlashResponseHessian.hsrc_off (fun h => hkl (siteMap_injective h.symm))

theorem offBox_mem (k l : Fin 9) (hkl : k≠l) : (offBox k l).Mem (rawH0 k l) := by
  rw [rawH0_off k l hkl]
  exact mul_mem (mul_mem (ofRat_mem 2) (symmetricResponseBox_mem k l)) (innerBox_mem k l)

theorem rawH0_symmetric (k l : Fin 9) : rawH0 k l=rawH0 l k :=
  SourceResponseKernelConsumer.H0_symmetric _ _
theorem rawH0_rowsum (k : Fin 9) : ∑ l : Fin 9,rawH0 k l=0 := by
  have hbij : Function.Bijective siteMap := by decide
  let e : Fin 9 ≃ Fin 9 := Equiv.ofBijective siteMap hbij
  have h := e.sum_comp (fun j => SourceResponseKernelConsumer.H0 (siteMap k) j)
  rw [← SourceResponseKernelConsumer.H0_rowsum (siteMap k)]
  exact h

end
end N11Formalization.SourceRawResponseIntervals
#check @N11Formalization.SourceRawResponseIntervals.rawResponse_two_spokes
#check @N11Formalization.SourceRawResponseIntervals.responseBox_mem
#check @N11Formalization.SourceRawResponseIntervals.offBox_mem
#check @N11Formalization.SourceRawResponseIntervals.rawH0_rowsum
#print axioms N11Formalization.SourceRawResponseIntervals.rawResponse_two_spokes
#print axioms N11Formalization.SourceRawResponseIntervals.offBox_mem
