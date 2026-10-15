import N11Formalization.SourceStructuredCoercivityPacket
import N11Formalization.SourceRelativeFluxNorms

/-! SAME9R/10 actualmu9/5000 quadratic coercivity, explicitly transported
raw8->canonical6. Only x6=0 is the pin domain. No H/G/box/coercivity premise.
No mixed/remainder/local gain/full patch/global covering bound is asserted. -/
set_option autoImplicit false
namespace N11Formalization.SourceActualCoercivity
open N11Formalization ResumeLocalIncidence SourceRawResponseIntervals
open SourceStructuredIntervals SourceRelativeFluxGeometry SourceResponseKernelConsumer
noncomputable section

private theorem raw_sum (f : Fin 9 → ℝ) :
    (∑ k : Fin 9,f (siteMap k))=∑ j : Fin 9,f j :=
  canonRawEquiv.symm.sum_comp f
private theorem succAbove8 (i : Fin 8) : (8 : Fin 9).succAbove i=i.castSucc := by
  fin_cases i <;> decide

/-- Canonical6-pinned actual H0/G coercivity with no quantitative inputs. -/
theorem canonical_coercivity (x : Fin 9 → ℝ) (hp : x 6=0) :
    (9/5000 : ℝ)*(∑ j : Fin 9,x j^2)≤
      (∑ i : Fin 9,∑ j : Fin 9,H0 i j*x i*x j)+
        1468*(∑ a : Fin 4,(∑ j : Fin 9,G j a*x j)^2) := by
  let y : Fin 9 → ℝ := fun k => x (siteMap k)
  have hpin : y 8=0 := hp
  have hn : (∑ k : Fin 8,y k.castSucc^2)=∑ j : Fin 9,x j^2 := by
    have h := ResumePinnedCoercivity.sum_delete_pin (8 : Fin 9)
      (fun k => y k^2) (by simp [hpin])
    simp only [succAbove8] at h
    rw [← h]
    exact raw_sum (fun j => x j^2)
  have hquad :
      (∑ k : Fin 8,∑ l : Fin 8,rawH0 k.castSucc l.castSucc*y k.castSucc*y l.castSucc)=
        ∑ i : Fin 9,∑ j : Fin 9,H0 i j*x i*x j := by
    have h := ResumePinnedCoercivity.quadratic_delete_pin (8 : Fin 9) rawH0 y hpin
    simp only [succAbove8] at h
    rw [← h]
    have hr (k : Fin 9) :
        (∑ l : Fin 9,H0 (siteMap k) (siteMap l)*x (siteMap k)*x (siteMap l))=
          ∑ j : Fin 9,H0 (siteMap k) j*x (siteMap k)*x j :=
      raw_sum (fun j => H0 (siteMap k) j*x (siteMap k)*x j)
    change (∑ k : Fin 9,∑ l : Fin 9,H0 (siteMap k) (siteMap l)*
      x (siteMap k)*x (siteMap l))=_
    simp_rw [hr]
    exact raw_sum (fun i => ∑ j : Fin 9,H0 i j*x i*x j)
  have hg (a : Fin 4) :
      (∑ k : Fin 8,rawG k.castSucc a*y k.castSucc)=∑ j : Fin 9,G j a*x j := by
    have h := ResumePinnedCoercivity.sum_delete_pin (8 : Fin 9)
      (fun k => rawG k a*y k) (by simp [hpin])
    simp only [succAbove8] at h
    rw [← h]
    exact raw_sum (fun j => G j a*x j)
  have h := SourceStructuredCoercivityPacket.actual_coercivity (fun k => y k.castSucc)
  rw [hn,hquad] at h
  simp_rw [hg] at h
  exact h

/-- Direct scalar interface for the SAME Qx1468 update's actual power. -/
theorem adaptive_coercivity (x : Fin 9 → ℝ) (hp : x 6=0) :
    (9/5000 : ℝ)*(∑ j : Fin 9,x j^2)≤
      (∑ i : Fin 9,∑ j : Fin 9,H0 i j*x i*x j)+
        1468*(SourceRelativeAdaptiveConsumer.power x)^2 := by
  have h := canonical_coercivity x hp
  have hg (a : Fin 4) :
      (∑ j : Fin 9,G j a*x j)=
        FlashLocal.GtX ResumeAnchorFlux.anchorIncidence SourceRelativeAdaptiveConsumer.D
          SourceRelativeAdaptiveConsumer.tangent SourceRelativeMetric.canonicalN x a := rfl
  rw [SourceRelativeAdaptiveConsumer.power_sq]
  simpa only [hg] using h

/-- Actual scalar consumer removes the coercivity premise only. The SAME
directional/mixed/remainder estimate remains EXPLICIT and is not claimed paid. -/
theorem gain_of_directional (E : ℝ) (x : Fin 9 → ℝ) (hp : x 6=0)
    (hr : Real.sqrt (∑ j : Fin 9,x j^2)≤(729/50000 : ℝ))
    (hdir :
      (∑ i : Fin 9,∑ j : Fin 9,H0 i j*x i*x j)/2+
        1468*(SourceRelativeAdaptiveConsumer.power x)^2-
        (179/5000)*(Real.sqrt (∑ j : Fin 9,x j^2))^3-
        ((2/25)/3)*(Real.sqrt (∑ j : Fin 9,x j^2))^4-
        1468*((99/200)*(2/25)+429/50000)*SourceRelativeAdaptiveConsumer.power x*
          (Real.sqrt (∑ j : Fin 9,x j^2))^2 ≤ E) :
    (∑ j : Fin 9,x j^2)/100000≤E := by
  have hsum : (0 : ℝ)≤∑ j : Fin 9,x j^2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hc :
      (9/5000 : ℝ)*(Real.sqrt (∑ j : Fin 9,x j^2))^2≤
        (∑ i : Fin 9,∑ j : Fin 9,H0 i j*x i*x j)+
          1468*(SourceRelativeAdaptiveConsumer.power x)^2 := by
    rw [Real.sq_sqrt hsum]
    exact adaptive_coercivity x hp
  have h := ResumeCoercivityCertificate.directional_to_local_gain E
    (∑ i : Fin 9,∑ j : Fin 9,H0 i j*x i*x j)
    (Real.sqrt (∑ j : Fin 9,x j^2)) (SourceRelativeAdaptiveConsumer.power x)
    (Real.sqrt_nonneg _) hr hc hdir
  rw [Real.sq_sqrt hsum] at h
  exact h

end
end N11Formalization.SourceActualCoercivity
#check @N11Formalization.SourceActualCoercivity.canonical_coercivity
#check @N11Formalization.SourceActualCoercivity.adaptive_coercivity
#check @N11Formalization.SourceActualCoercivity.gain_of_directional
#print axioms N11Formalization.SourceActualCoercivity.adaptive_coercivity
