import N11Formalization.GridBridge

/-! # ResumeRootRefine2 — TCSystem consumer of the a-posteriori bound (C922 step 2)
g x = x - Y·TCSystem x on the certificate ball; K from fixed Jt row sums.
Remaining input: a residual bound η at an arbitrary center c in the ball. -/

noncomputable section
namespace N11Formalization.ResumeRootRefine

/-- A posteriori: fixed point x* of a K-Lipschitz map on s, any c ∈ s ⇒
`‖x* - c‖ ≤ ‖g c - c‖ / (1 - K)`. -/
theorem fixed_point_near_center {E : Type*} [NormedAddCommGroup E]
    {g : E → E} {s : Set E} {K : NNReal} (hK : (K : ℝ) < 1)
    (hg : LipschitzOnWith K g s) {x c : E} (hx : x ∈ s) (hc : c ∈ s)
    (hfix : g x = x) : ‖x - c‖ ≤ ‖g c - c‖ / (1 - K) := by
  have h1 : ‖x - c‖ ≤ K * ‖x - c‖ + ‖g c - c‖ := by
    have hl := hg.norm_sub_le hx hc
    calc ‖x - c‖ = ‖(g x - g c) + (g c - c)‖ := by rw [hfix]; congr 1; abel
      _ ≤ ‖g x - g c‖ + ‖g c - c‖ := norm_add_le _ _
      _ ≤ K * ‖x - c‖ + ‖g c - c‖ := by linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- Coordinate form on `Fin n → ℝ` (sup norm): radius coordinate pinned. -/
theorem coord_le_of_fixed_point {n : ℕ} {g : (Fin n → ℝ) → (Fin n → ℝ)}
    {s : Set (Fin n → ℝ)} {K : NNReal} (hK : (K : ℝ) < 1)
    (hg : LipschitzOnWith K g s) {x c : Fin n → ℝ} (hx : x ∈ s) (hc : c ∈ s)
    (hfix : g x = x) (i : Fin n) {η : ℝ} (hη : ‖g c - c‖ ≤ η) :
    x i ≤ c i + η / (1 - K) := by
  have h := fixed_point_near_center hK hg hx hc hfix
  have hi : |x i - c i| ≤ ‖x - c‖ := by
    simpa using norm_le_pi_norm (x - c) i
  have : ‖g c - c‖ / (1 - K) ≤ η / (1 - K) :=
    div_le_div_of_nonneg_right hη (by linarith)
  linarith [le_abs_self (x i - c i)]




end N11Formalization.ResumeRootRefine

namespace N11Formalization.ResumeRootRefine2
open N11Formalization Metric

/-- Generic: fixed Jt enclosure + row sum ≤ K < 1 ⇒ for any center c in the ball,
`Rstar S ≤ c 6 + η/(1-K)` where η bounds `‖Y·TCSystem c‖`. -/
theorem Rstar_le_center_add
    (Y : Fin 12 → Fin 12 → ℚ) (Jt : Fin 12 → Fin 12 → RatInterval) {K : ℝ}
    (hK0 : 0 ≤ K) (hK1 : K < 1)
    (hdiff : ∀ x ∈ closedBall certCR rhoCertR, DifferentiableAt ℝ TCSystem x)
    (hJ : ∀ x ∈ closedBall certCR rhoCertR, ∀ k j : Fin 12,
      (Jt k j).Mem ((fderiv ℝ TCSystem x) (Pi.single j 1) k))
    (hsum : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat Y Jt i j).lo : ℝ)| |((krawczykMat Y Jt i j).hi : ℝ)| ≤ K)
    (S : C891RootSpec) (hsys : S.sys = TCSystem) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6)
    (c : Fin 12 → ℝ) (hc : c ∈ closedBall certCR rhoCertR)
    {η : ℝ} (hη : ‖ratMatCLM Y (TCSystem c)‖ ≤ η) :
    Rstar S ≤ c 6 + η / (1 - K) := by
  have hbound : ∀ x ∈ closedBall certCR rhoCertR,
      ‖ContinuousLinearMap.id ℝ (Fin 12 → ℝ) - (ratMatCLM Y).comp (fderiv ℝ TCSystem x)‖ ≤ K :=
    fun x hx => opNorm_le_of_entry_bounds _ hK0
      (fun i j => ((krawczykMat Y Jt i j).lo : ℝ)) (fun i j => ((krawczykMat Y Jt i j).hi : ℝ))
      (fun i j => ⟨RatInterval.mem_lo_le
          (mem_krawczykMat (Y := Y) (A := fderiv ℝ TCSystem x) (J := Jt) (fun k j => hJ x hx k j) i j),
        RatInterval.mem_le_hi
          (mem_krawczykMat (Y := Y) (A := fderiv ℝ TCSystem x) (J := Jt) (fun k j => hJ x hx k j) i j)⟩)
      hsum
  let g : (Fin 12 → ℝ) → (Fin 12 → ℝ) := fun x => x - ratMatCLM Y (TCSystem x)
  have hlip : LipschitzOnWith ⟨K, hK0⟩ g (closedBall certCR rhoCertR) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    exact lipschitzOn_ball_of_deriv_bound TCSystem (ratMatCLM Y) certCR rhoCertR K
      hdiff hbound hx hy
  obtain ⟨hbox, hzero⟩ := S.root_mem
  have hroot : S.root ∈ closedBall certCR rhoCertR := by
    rw [mem_closedBall_cert_iff]
    intro i; have := hbox i; rw [hlo, hhi] at this; exact this
  have hz : TCSystem S.root = 0 := by rw [← hsys]; exact hzero
  have hfix : g S.root = S.root := by simp [g, hz]
  have hgc : ‖g c - c‖ ≤ η := by
    have : g c - c = -(ratMatCLM Y (TCSystem c)) := by simp [g]
    rw [this, norm_neg]; exact hη
  have h := ResumeRootRefine.coord_le_of_fixed_point (K := ⟨K, hK0⟩) hK1 hlip hroot hc hfix 6 hgc
  have e : Rstar S = S.root 6 := by simp only [Rstar, hidx]
  rw [e]
  exact h

/-- Concrete GridBridge instance: only the center `c` and residual bound `η` remain. -/
theorem Rstar_le_center_cert
    (S : C891RootSpec) (hsys : S.sys = TCSystem) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6)
    (c : Fin 12 → ℝ) (hc : c ∈ closedBall certCR rhoCertR)
    {η : ℝ} (hη : ‖ratMatCLM HsumPayload.certReal.Yof (TCSystem c)‖ ≤ η) :
    Rstar S ≤ c 6 + η / (1 - (HsumPayloadB.numK_B : ℝ) / (HsumPayload.Ez : ℝ)) :=
  Rstar_le_center_add HsumPayload.certReal.Yof NdBox.JtBox HsumPayloadB.hK0_B HsumPayloadB.hK1_B
    (fun x hx => differentiableAt_TCSystem_of_conditions x (nd_hndRho x hx) (nd_hndW x hx)
      (nd_hndU1 x hx) (nd_hndU2 x hx) (nd_hndU3 x hx) (nd_hndU8 x hx) (nd_hndWp x hx))
    HJBoxInstant.hJ_box GridBridge.hsum_Jt S hsys hlo hhi hidx c hc hη

end N11Formalization.ResumeRootRefine2

#print axioms N11Formalization.ResumeRootRefine2.Rstar_le_center_add
#check @N11Formalization.ResumeRootRefine2.Rstar_le_center_cert
#print axioms N11Formalization.ResumeRootRefine2.Rstar_le_center_cert
