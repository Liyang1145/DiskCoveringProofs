import N11Formalization.ResumeRootRefine2

noncomputable section
namespace N11Formalization.ResumeNewton
open Metric

/-- Directed Newton estimate; unlike a symmetric norm bound, retains the
signed correction in the selected coordinate. -/
theorem coord_le_newton {n : ℕ} {g : (Fin n → ℝ) → (Fin n → ℝ)}
    {s : Set (Fin n → ℝ)} {K : NNReal} (hK : (K : ℝ) < 1)
    (hg : LipschitzOnWith K g s) {x c : Fin n → ℝ} (hx : x ∈ s) (hc : c ∈ s)
    (hfix : g x = x) (i : Fin n) {η : ℝ} (hη : ‖g c - c‖ ≤ η) :
    x i ≤ g c i + K * (η / (1 - K)) := by
  have hd := ResumeRootRefine.fixed_point_near_center hK hg hx hc hfix
  have hd' : ‖x - c‖ ≤ η / (1 - K) := hd.trans
    (div_le_div_of_nonneg_right hη (by linarith))
  have hl := hg.norm_sub_le hx hc
  have hi : |g x i - g c i| ≤ ‖g x - g c‖ := by
    simpa using norm_le_pi_norm (g x - g c) i
  have hm := mul_le_mul_of_nonneg_left hd' K.coe_nonneg
  rw [hfix] at hi hl
  linarith [le_abs_self (x i - g c i)]

/-- Same isolated root, concrete certified Jacobian; only the original-center
residual norm and signed sixth coordinate are needed. -/
theorem Rstar_le_newton6
    (S : C891RootSpec) (hsys : S.sys = TCSystem) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6)
    {η δ : ℝ}
    (hη : ‖ratMatCLM HsumPayload.certReal.Yof (TCSystem certCR)‖ ≤ η)
    (hδ : -(ratMatCLM HsumPayload.certReal.Yof (TCSystem certCR)) 6 ≤ δ) :
    Rstar S ≤ certCR 6 + δ +
      ((HsumPayloadB.numK_B : ℝ) / (HsumPayload.Ez : ℝ)) *
      (η / (1 - (HsumPayloadB.numK_B : ℝ) / (HsumPayload.Ez : ℝ))) := by
  let Y := HsumPayload.certReal.Yof
  let K : ℝ := (HsumPayloadB.numK_B : ℝ) / (HsumPayload.Ez : ℝ)
  have hK0 : 0 ≤ K := HsumPayloadB.hK0_B
  have hK1 : K < 1 := HsumPayloadB.hK1_B
  have hdiff : ∀ x ∈ closedBall certCR rhoCertR, DifferentiableAt ℝ TCSystem x :=
    fun x hx => differentiableAt_TCSystem_of_conditions x (nd_hndRho x hx) (nd_hndW x hx)
      (nd_hndU1 x hx) (nd_hndU2 x hx) (nd_hndU3 x hx) (nd_hndU8 x hx) (nd_hndWp x hx)
  have hbound : ∀ x ∈ closedBall certCR rhoCertR,
      ‖ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - (ratMatCLM Y).comp (fderiv ℝ TCSystem x)‖ ≤ K := by
    intro x hx
    exact opNorm_le_of_entry_bounds _ hK0
      (fun i j => ((krawczykMat Y NdBox.JtBox i j).lo : ℝ))
      (fun i j => ((krawczykMat Y NdBox.JtBox i j).hi : ℝ))
      (fun i j => ⟨RatInterval.mem_lo_le
        (mem_krawczykMat (Y := Y) (A := fderiv ℝ TCSystem x) (J := NdBox.JtBox)
          (fun k j => HJBoxInstant.hJ_box x hx k j) i j),
        RatInterval.mem_le_hi
        (mem_krawczykMat (Y := Y) (A := fderiv ℝ TCSystem x) (J := NdBox.JtBox)
          (fun k j => HJBoxInstant.hJ_box x hx k j) i j)⟩)
      GridBridge.hsum_Jt
  let g : (Fin 12 → ℝ) → (Fin 12 → ℝ) := fun x => x - ratMatCLM Y (TCSystem x)
  have hlip : LipschitzOnWith ⟨K, hK0⟩ g (closedBall certCR rhoCertR) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    exact lipschitzOn_ball_of_deriv_bound TCSystem (ratMatCLM Y) certCR rhoCertR K
      hdiff hbound hx hy
  obtain ⟨hbox, hzero⟩ := S.root_mem
  have hroot : S.root ∈ closedBall certCR rhoCertR := by
    rw [mem_closedBall_cert_iff]
    intro i; have := hbox i; rw [hlo, hhi] at this; exact this
  have hc : certCR ∈ closedBall certCR rhoCertR := by
    simp only [mem_closedBall, dist_self]
    norm_num [rhoCertR, rhoCert]
  have hz : TCSystem S.root = 0 := by rw [← hsys]; exact hzero
  have hfix : g S.root = S.root := by simp [g, hz]
  have hgc : ‖g certCR - certCR‖ ≤ η := by
    simpa [g, Y] using hη
  have hn := coord_le_newton (K := ⟨K, hK0⟩) hK1 hlip hroot hc hfix 6 hgc
  have e : Rstar S = S.root 6 := by simp only [Rstar, hidx]
  rw [e]
  change S.root 6 ≤ certCR 6 + δ + K * (η / (1 - K))
  change S.root 6 ≤ certCR 6 - (ratMatCLM Y (TCSystem certCR)) 6 +
    K * (η / (1 - K)) at hn
  change -(ratMatCLM Y (TCSystem certCR)) 6 ≤ δ at hδ
  linarith

#check @Rstar_le_newton6
#print axioms Rstar_le_newton6
end N11Formalization.ResumeNewton
