import N11Formalization.RootPinNormalConsumer
import N11Formalization.PinCircleDifferential
set_option autoImplicit false
namespace N11Formalization.RootPinDifferentialConsumer
open N11Formalization PinTangentGeometry PinCircleDifferential
noncomputable section

/-- Source strict radicands and radius positivity persist on every continuous source curve. -/
theorem source_curve_legal {u : ℝ → Fin 12 → ℝ} {t : ℝ}
    (hroot : u t = SourceExactRoot.sourceRoot) (hc : ContinuousAt u t) :
    ∀ᶠ s in nhds t, 0 ≤ u s 6 ∧
      ∀ j : Fin 9, Real.sin (angleVec (u s) j)^2 ≤ (u s 6)^2 := by
  have hR : ContinuousAt (fun s => u s 6) t := (continuous_apply 6).continuousAt.comp hc
  have hRp : 0 < u t 6 := by rw [hroot]; exact SourceExactRoot.sourceRadius_pos
  have heR := hR.eventually (eventually_gt_nhds hRp)
  have herad : ∀ j : Fin 9, ∀ᶠ s in nhds t,
      0 < (u s 6)^2 - Real.sin (angleVec (u s) j)^2 := by
    intro j
    have ha : ContinuousAt (fun s => angleVec (u s) j) t :=
      (contDiffAt_angleVec (n := 1) j (u t)).continuousAt.comp hc
    have hsin : ContinuousAt (fun s => Real.sin (angleVec (u s) j)) t :=
      Real.continuous_sin.continuousAt.comp ha
    have hrad := (hR.pow 2).sub (hsin.pow 2)
    have hp : 0 < (u t 6)^2 - Real.sin (angleVec (u t) j)^2 := by
      rw [hroot]
      exact SourceWidthNondegenerate.source_radicand_pos j
    exact hrad.eventually (eventually_gt_nhds hp)
  have heall : ∀ᶠ s in nhds t, ∀ j : Fin 9,
      0 < (u s 6)^2 - Real.sin (angleVec (u s) j)^2 := by
    rw [Filter.eventually_all]
    exact herad
  filter_upwards [heR, heall] with s hs hj
  exact ⟨le_of_lt hs, fun j => by linarith [hj j]⟩

/-- Actual TC-chart reflected pin versus any true equal-circle pin following the same
centers/radius. All normal-rank/branch premises are discharged at SAME sourceRoot.
This remains a chart-curve theorem, not an off-boundary independent-frame identity. -/
theorem source_reflected_curve_derivative_eq
    (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8)
    {u : ℝ → Fin 12 → ℝ} {V : ℝ → Point}
    {w v p q : Point} {r t : ℝ}
    (hroot : u t = SourceExactRoot.sourceRoot)
    (hV : V t = Uvec SourceExactRoot.sourceRoot k)
    (hw : HasDerivAt (fun s => Uvec (u s) k) w t)
    (hv : HasDerivAt V v t)
    (hp : HasDerivAt (fun s => ringCenter (u s) k) p t)
    (hq : HasDerivAt (fun s => ringCenter (u s) (k+1)) q t)
    (hr : HasDerivAt (fun s => u s 6) r t)
    (hc : ContinuousAt u t)
    (hvP : ∀ᶠ s in nhds t, ‖V s - ringCenter (u s) k‖^2 = (u s 6)^2)
    (hvQ : ∀ᶠ s in nhds t, ‖V s - ringCenter (u s) (k+1)‖^2 = (u s 6)^2) : w=v := by
  have hlegal := source_curve_legal hroot hc
  have huP : ∀ᶠ s in nhds t, ‖Uvec (u s) k - ringCenter (u s) k‖^2 = (u s 6)^2 := by
    filter_upwards [hlegal] with s hs
    have hd := dist_Uvec_ringCenter_self (u s) hs.2 hs.1 k
    rw [dist_eq_norm] at hd
    rw [hd]
  have huQ : ∀ᶠ s in nhds t, ‖Uvec (u s) k - ringCenter (u s) (k+1)‖^2 = (u s 6)^2 := by
    filter_upwards [hlegal] with s hs
    have hd := dist_Uvec_ringCenter_succ (u s) hs.2 hs.1 k
    rw [dist_eq_norm] at hd
    rw [hd]
  apply two_pin_curves_derivative_eq hw hv hp hq hr
  · rw [hroot, hV]
  · rw [hroot]
    exact RootPinNormalConsumer.source_contact_normals_independent k hk
  · exact huP
  · exact huQ
  · exact hvP
  · exact hvQ

end
end N11Formalization.RootPinDifferentialConsumer
#check @N11Formalization.RootPinDifferentialConsumer.source_reflected_curve_derivative_eq
#print axioms N11Formalization.RootPinDifferentialConsumer.source_reflected_curve_derivative_eq
