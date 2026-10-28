import N11Formalization.SourceStressIntervals
import N11Formalization.SourceActiveFiniteSystem

/-! Unconditional entrywise enclosure of the ACTUAL Fin20 free Laplacian and
its9 actual harmonic right-hand sides. Uses all45 exact source stress boxes and
integer incidence, including the two REAL hub sites9/10. No midpoint matrix
or supplied membership assumption. A residual contraction/solution error
certificate remains separate before any response/coercivity enclosure. -/
set_option autoImplicit false
namespace N11Formalization.SourceActiveMatrixIntervals
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceActiveLaplacian SourceActiveHarmonicSolve SourceActiveFiniteSystem
open SourceStressIntervals
noncomputable section

def sumI {ι : Type*} [Fintype ι] (I : ι → RatInterval) : RatInterval :=
  ⟨∑ i,(I i).lo,∑ i,(I i).hi⟩

theorem sumI_mem {ι : Type*} [Fintype ι] {I : ι → RatInterval} {x : ι → ℝ}
    (h : ∀ i,(I i).Mem (x i)) : (sumI I).Mem (∑ i,x i) := by
  constructor
  · change ((∑ i,(I i).lo : ℚ) : ℝ)≤∑ i,x i
    push_cast
    exact Finset.sum_le_sum (fun i _ => (h i).1)
  · change (∑ i,x i)≤((∑ i,(I i).hi : ℚ) : ℝ)
    push_cast
    exact Finset.sum_le_sum (fun i _ => (h i).2)

def incidenceI (e : SourceEdge) (v : SrcFree) : RatInterval :=
  ofRat (incidenceZ e v : ℚ)

theorem incidenceI_mem (e : SourceEdge) (v : SrcFree) :
    (incidenceI e v).Mem (B e v) := by
  simpa only [incidenceI,B,Rat.cast_intCast] using ofRat_mem (incidenceZ e v : ℚ)

def anchorI (e : SourceEdge) (j : Fin 9) : RatInterval :=
  match e with
  | .inl (k,_) => ofRat (if j=ResumeLocalIncidence.siteMap k then -1 else 0)
  | .inr _ => ofRat 0

theorem anchorI_mem (e : SourceEdge) (j : Fin 9) :
    (anchorI e j).Mem (anchorRow e j) := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · have h := SourceRadialFluxConsumer.incidence_source_spoke
      (FlashRootNetwork.rawOfRing j) k s
    rw [SourceRadialFluxConsumer.siteMap_rawOfRing] at h
    have hij : k=FlashRootNetwork.rawOfRing j ↔ j=ResumeLocalIncidence.siteMap k := by
      constructor
      · intro hk
        rw [hk,SourceRadialFluxConsumer.siteMap_rawOfRing]
      · intro hj
        apply SourceRadialFluxConsumer.siteMap_injective
        rw [SourceRadialFluxConsumer.siteMap_rawOfRing,← hj]
    change (ofRat (if j=ResumeLocalIncidence.siteMap k then (-1 : ℚ) else 0)).Mem
      (ResumeAnchorFlux.anchorIncidence (edgeMap (.inl (k,s))) j)
    rw [h]
    simp only [hij]
    split_ifs <;> norm_num [RatInterval.Mem,RatInterval.toSet,ofRat]
  · simpa only [anchorI,anchorRow,edgeMap,ResumeAnchorFlux.anchorIncidence,Rat.cast_zero]
      using ofRat_mem (0 : ℚ)

def ABox (i k : Fin 20) : RatInterval :=
  sumI (fun e : SourceEdge =>
    mul (mul (stressI e) (incidenceI e (nodeEquiv.symm i)))
      (incidenceI e (nodeEquiv.symm k)))

theorem ABox_mem (i k : Fin 20) : (ABox i k).Mem (matrix20 i k) :=
  sumI_mem (fun e => mul_mem
    (mul_mem (stressI_mem e) (incidenceI_mem e (nodeEquiv.symm i)))
      (incidenceI_mem e (nodeEquiv.symm k)))

def rhsBox (j : Fin 9) (i : Fin 20) : RatInterval :=
  neg (sumI (fun e : SourceEdge =>
    mul (mul (stressI e) (incidenceI e (nodeEquiv.symm i))) (anchorI e j)))

theorem rhsBox_mem (j : Fin 9) (i : Fin 20) :
    (rhsBox j i).Mem (rhs20 j i) :=
  neg_mem (sumI_mem (fun e =>
    mul_mem (mul_mem (stressI_mem e) (incidenceI_mem e (nodeEquiv.symm i)))
      (anchorI_mem e j)))

end
end N11Formalization.SourceActiveMatrixIntervals
#check @N11Formalization.SourceActiveMatrixIntervals.ABox_mem
#check @N11Formalization.SourceActiveMatrixIntervals.rhsBox_mem
#print axioms N11Formalization.SourceActiveMatrixIntervals.ABox_mem
#print axioms N11Formalization.SourceActiveMatrixIntervals.rhsBox_mem
