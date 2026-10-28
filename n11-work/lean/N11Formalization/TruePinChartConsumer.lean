import N11Formalization.TrueCirclePinSmooth
import N11Formalization.RootPinCurveSmooth
set_option autoImplicit false
namespace N11Formalization.TruePinChartConsumer
open N11Formalization TrueCirclePinSmooth RootPinCurveSmooth
noncomputable section

def dataOf (k : Fin 9) (u : TCPoint) : Data :=
  ![(ringCenter u k) 0, (ringCenter u k) 1,
    (ringCenter u (k+1)) 0, (ringCenter u (k+1)) 1, u 6]

def truePin (k : Fin 9) (u : TCPoint) : Point := pinData (sourceSeed k) (dataOf k u)

@[simp] theorem dataOf_source (k : Fin 9) : dataOf k SourceExactRoot.sourceRoot = sourceData k := rfl
@[simp] theorem left_dataOf (k : Fin 9) (u : TCPoint) : left (dataOf k u) = ringCenter u k := by
  ext i; fin_cases i <;> rfl
@[simp] theorem right_dataOf (k : Fin 9) (u : TCPoint) : right (dataOf k u) = ringCenter u (k+1) := by
  ext i; fin_cases i <;> rfl
@[simp] theorem radius_dataOf (k : Fin 9) (u : TCPoint) : dataOf k u 4 = u 6 := rfl

theorem dataOf_source_smooth (k : Fin 9) : ContDiffAt ℝ 1 (dataOf k) SourceExactRoot.sourceRoot := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact ((contDiffAt_piLp 2).mp (source_ringCenter_smooth k)) 0
  · exact ((contDiffAt_piLp 2).mp (source_ringCenter_smooth k)) 1
  · exact ((contDiffAt_piLp 2).mp (source_ringCenter_smooth (k+1))) 0
  · exact ((contDiffAt_piLp 2).mp (source_ringCenter_smooth (k+1))) 1
  · exact contDiffAt_coord 6 _

theorem truePin_source (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    truePin k SourceExactRoot.sourceRoot = Uvec SourceExactRoot.sourceRoot k :=
  source_pinData_eq k hk

theorem truePin_source_smooth (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (truePin k) SourceExactRoot.sourceRoot := by
  exact ContDiffAt.comp (f := dataOf k) (g := pinData (sourceSeed k))
    SourceExactRoot.sourceRoot (source_pinData_smooth k hk) (dataOf_source_smooth k)

/-- The constructed independent-Cartesian pin, pulled back to the TC chart, has the SAME
Frechet derivative as the reflected Uvec construction. No true-pin existence/equation
premise remains: they are supplied by the actual smooth construction. -/
theorem truePin_source_fderiv (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    fderiv ℝ (truePin k) SourceExactRoot.sourceRoot =
      fderiv ℝ (fun u : TCPoint => Uvec u k) SourceExactRoot.sourceRoot := by
  apply ContinuousLinearMap.ext
  intro du
  let u : ℝ → TCPoint := fun s => SourceExactRoot.sourceRoot + s • du
  have hu : HasDerivAt u du 0 := by
    have h := (hasDerivAt_id (0:ℝ)).smul_const du |>.const_add SourceExactRoot.sourceRoot
    change HasDerivAt (fun s : ℝ => SourceExactRoot.sourceRoot + s • du) (1 • du) 0 at h
    rw [one_smul] at h
    exact h
  have hroot : u 0 = SourceExactRoot.sourceRoot := by simp [u]
  have ht := ((truePin_source_smooth k hk).differentiableAt (by norm_num)).hasFDerivAt
  have hv := ht.comp_hasDerivAt_of_eq 0 hu hroot.symm
  have hd : ContinuousAt (fun s => dataOf k (u s)) 0 := by
    have hh : ContinuousAt (dataOf k) (u 0) := by rw [hroot]; exact (dataOf_source_smooth k).continuousAt
    exact hh.comp hu.continuousAt
  have he : ∀ᶠ s in nhds (0:ℝ),
      ‖truePin k (u s)-ringCenter (u s) k‖^2 = (u s 6)^2 ∧
      ‖truePin k (u s)-ringCenter (u s) (k+1)‖^2 = (u s 6)^2 := by
    have hdata : dataOf k (u 0) = sourceData k := by rw [hroot]; rfl
    have he' := source_pinData_equations_eventually k hk
    rw [← hdata] at he'
    have hh := hd.eventually he'
    simpa only [truePin, left_dataOf, right_dataOf, radius_dataOf] using hh
  exact source_true_pin_velocity k hk hu hroot hv (by
    change truePin k (u 0) = _
    rw [hroot]; exact truePin_source k hk) (he.mono fun s hs => hs.1) (he.mono fun s hs => hs.2)

end
end N11Formalization.TruePinChartConsumer
#check @N11Formalization.TruePinChartConsumer.truePin_source_fderiv
#print axioms N11Formalization.TruePinChartConsumer.truePin_source_fderiv
