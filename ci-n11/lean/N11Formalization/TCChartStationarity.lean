import Mathlib
import N11Formalization.TCSystem
import N11Formalization.SourceExactRoot
set_option autoImplicit false
namespace N11Formalization.TCChartStationarity
noncomputable section

def objective (u : Fin 12 → ℝ) (z : Fin 7 → ℝ) : ℝ :=
  z 6 - ∑ k : Fin 5, last5 u k * residualFun z k

def objectiveDeriv (u : Fin 12 → ℝ) : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (6 : Fin 7) -
    ∑ k : Fin 5, (last5 u k) •
      (ContinuousLinearMap.proj k).comp (fderiv ℝ residualFun (first7 u))

theorem objectiveDeriv_single (u : Fin 12 → ℝ) (i : Fin 7) :
    objectiveDeriv u (Pi.single i 1) =
      (if i = 6 then 1 else 0) - adjointBlock (first7 u) (last5 u) i := by
  simp [objectiveDeriv, adjointBlock, Pi.single_apply, eq_comm]

theorem objectiveDeriv_zero_of_TC (u : Fin 12 → ℝ) (hTC : TCSystem u = 0) :
    objectiveDeriv u = 0 := by
  have hs : ∀ i : Fin 7, objectiveDeriv u (Pi.single i 1) = 0 := by
    intro i
    have h := congrFun hTC (⟨5 + i.val, by omega⟩ : Fin 12)
    have hi : (⟨5 + i.val - 5, by omega⟩ : Fin 7) = i := by apply Fin.ext; simp
    rw [objectiveDeriv_single]
    simp only [TCSystem, dif_neg (by omega : ¬ 5 + i.val < 5), hi] at h
    have h6 : ((5 + i.val : ℕ) = 11) ↔ i = 6 := by simp only [Fin.ext_iff]; omega
    simpa [Fin.ext_iff, h6] using h
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = ∑ i : Fin 7, z i • (Pi.single i (1 : ℝ)) := by
    funext j
    simp [Pi.single_apply]
  rw [hz, map_sum]
  simp [map_smul, hs]

theorem hasFDerivAt_objective (u : Fin 12 → ℝ)
    (hd : DifferentiableAt ℝ residualFun (first7 u)) :
    HasFDerivAt (objective u) (objectiveDeriv u) (first7 u) := by
  have hsum' := HasFDerivAt.sum (u := (Finset.univ : Finset (Fin 5))) (fun k _ =>
    ((ContinuousLinearMap.proj k).hasFDerivAt.comp _ hd.hasFDerivAt).const_smul (last5 u k))
  have hsum : HasFDerivAt
      (fun z : Fin 7 → ℝ => ∑ k : Fin 5, last5 u k * residualFun z k)
      (∑ k : Fin 5, last5 u k •
        (ContinuousLinearMap.proj k).comp (fderiv ℝ residualFun (first7 u))) (first7 u) := by
    convert hsum' using 1 <;> ext z <;> simp [Finset.sum_apply]
  exact (ContinuousLinearMap.proj (6 : Fin 7)).hasFDerivAt.sub hsum

theorem fderiv_objective_zero (u : Fin 12 → ℝ)
    (hTC : TCSystem u = 0) (hd : DifferentiableAt ℝ residualFun (first7 u)) :
    fderiv ℝ (objective u) (first7 u) = 0 :=
  (hasFDerivAt_objective u hd).fderiv.trans (objectiveDeriv_zero_of_TC u hTC)

theorem sourceRoot_stationarity
    (hd : DifferentiableAt ℝ residualFun (first7 SourceExactRoot.sourceRoot)) :
    fderiv ℝ (objective SourceExactRoot.sourceRoot) (first7 SourceExactRoot.sourceRoot) = 0 :=
  fderiv_objective_zero _ SourceExactRoot.sourceRoot_mem.2 hd

end
end N11Formalization.TCChartStationarity
#print axioms N11Formalization.TCChartStationarity.objectiveDeriv_zero_of_TC
#print axioms N11Formalization.TCChartStationarity.sourceRoot_stationarity
#check @N11Formalization.TCChartStationarity.sourceRoot_stationarity
