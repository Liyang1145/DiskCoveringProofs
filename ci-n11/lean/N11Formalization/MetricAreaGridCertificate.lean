import N11Formalization.MetricAreaEnvelopeRegularity

/-! Uniform-grid certificates for the entire closed angle domain.
The grid covers the interval by a proved floor construction. The error is
an analytic Lipschitz margin; no optimizer or sampled maximum is trusted.
Concrete node bounds and final strict sums are deliberately left unpaid. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricAreaGridCertificate

open ActualSectorAreaEnvelope MetricAreaEnvelopeRegularity

def gridPoint (U : ℝ) (N : ℕ) (k : Fin (N+1)) : ℝ :=
  U*(k.val : ℝ)/(N : ℝ)

theorem uniform_grid_cover {U x : ℝ} {N : ℕ}
    (hU : 0 < U) (hN : 0 < N) (hx : x ∈ Set.Icc (0 : ℝ) U) :
    ∃ k : Fin (N+1), |x-gridPoint U N k| ≤ U/(N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let q : ℝ := x*(N : ℝ)/U
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hx.1 hNr.le) hU.le
  have hqN : q ≤ (N : ℝ) := by
    dsimp [q]
    apply (div_le_iff₀ hU).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hx.2 hNr.le]
  let k : ℕ := Nat.floor q
  have hk : k ≤ N := Nat.floor_le_of_le hqN
  let K : Fin (N+1) := ⟨k,by omega⟩
  have hb : |q-(k : ℝ)| ≤ 1 := Nat.abs_sub_floor_le hq0
  have he : x-gridPoint U N K = U/(N : ℝ)*(q-(k : ℝ)) := by
    change x-U*(k : ℝ)/(N : ℝ) = U/(N : ℝ)*(q-(k : ℝ))
    dsimp [q]
    field_simp [hU.ne',hNr.ne']
  refine ⟨K,?_⟩
  rw [he,abs_mul,abs_of_nonneg (div_nonneg hU.le hNr.le)]
  exact (mul_le_mul_of_nonneg_left hb (div_nonneg hU.le hNr.le)).trans_eq (mul_one _)

theorem full_interval_upper_of_grid {f : ℝ → ℝ} {L U M : ℝ} {N : ℕ}
    (hN : 0 < N) (hU : Real.pi ≤ U) (hL : 0 ≤ L)
    (hlip : ∀ a b : ℝ, |f a-f b| ≤ L*|a-b|)
    (hnodes : ∀ k : Fin (N+1), f (gridPoint U N k) ≤ M) :
    ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi → f t ≤ M+L*U/(N : ℝ) := by
  intro t ht0 htpi
  obtain ⟨k,hk⟩ := uniform_grid_cover (Real.pi_pos.trans_le hU) hN
    (show t ∈ Set.Icc (0 : ℝ) U from ⟨ht0,htpi.trans hU⟩)
  have hs : f t-f (gridPoint U N k) ≤ L*(U/(N : ℝ)) :=
    (le_abs_self _).trans ((hlip t (gridPoint U N k)).trans
      (mul_le_mul_of_nonneg_left hk hL))
  have hn := hnodes k
  rw [← mul_div_assoc] at hs
  linarith only [hs,hn]

def edgeResidual (c t : ℝ) : ℝ := (19/50 : ℝ)^2*Real.sin t-c*t
def sectorResidual (mu lam t : ℝ) : ℝ :=
  areaEnvelope t+lam*widthEnvelope t-mu*t

theorem edgeResidual_difference (c a b : ℝ) :
    |edgeResidual c a-edgeResidual c b| ≤ ((19/50 : ℝ)^2+|c|)*|a-b| := by
  have he : edgeResidual c a-edgeResidual c b =
      (19/50 : ℝ)^2*(Real.sin a-Real.sin b)-c*(a-b) := by
    unfold edgeResidual
    ring
  have ht : |(19/50 : ℝ)^2*(Real.sin a-Real.sin b)-c*(a-b)| ≤
      |(19/50 : ℝ)^2*(Real.sin a-Real.sin b)|+|c*(a-b)| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      abs_sub_le ((19/50 : ℝ)^2*(Real.sin a-Real.sin b)) 0 (c*(a-b))
  have hs := Real.abs_sin_sub_sin_le a b
  rw [abs_mul,abs_mul] at ht
  norm_num at ht
  rw [he]
  nlinarith only [ht,hs]

theorem sectorResidual_difference {lam : ℝ} (hlam : 0 ≤ lam) (mu a b : ℝ) :
    |sectorResidual mu lam a-sectorResidual mu lam b| ≤
      (1+lam+|mu|)*|a-b| := by
  have he : sectorResidual mu lam a-sectorResidual mu lam b =
      (areaEnvelope a-areaEnvelope b)+lam*(widthEnvelope a-widthEnvelope b)-mu*(a-b) := by
    unfold sectorResidual
    ring
  have ht : |(areaEnvelope a-areaEnvelope b)+lam*(widthEnvelope a-widthEnvelope b)-mu*(a-b)| ≤
      |(areaEnvelope a-areaEnvelope b)+lam*(widthEnvelope a-widthEnvelope b)|+|mu*(a-b)| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      abs_sub_le ((areaEnvelope a-areaEnvelope b)+lam*(widthEnvelope a-widthEnvelope b)) 0 (mu*(a-b))
  have ha := abs_add_le (areaEnvelope a-areaEnvelope b) (lam*(widthEnvelope a-widthEnvelope b))
  have hf := areaEnvelope_difference a b
  have hw := mul_le_mul_of_nonneg_left (widthEnvelope_one_lipschitz a b) hlam
  rw [abs_mul,abs_of_nonneg hlam] at ha
  rw [abs_mul] at ht
  rw [he]
  nlinarith only [ht,ha,hf,hw]

theorem edge_full_domain_upper_of_grid {U M : ℝ} {N : ℕ}
    (hN : 0 < N) (hU : Real.pi ≤ U) (c : ℝ)
    (hnodes : ∀ k : Fin (N+1), edgeResidual c (gridPoint U N k) ≤ M) :
    ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi → edgeResidual c t ≤
      M+((19/50 : ℝ)^2+|c|)*U/(N : ℝ) :=
  full_interval_upper_of_grid hN hU (by positivity) (edgeResidual_difference c) hnodes

theorem sector_full_domain_upper_of_grid {U M lam : ℝ} {N : ℕ}
    (hN : 0 < N) (hU : Real.pi ≤ U) (hlam : 0 ≤ lam) (mu : ℝ)
    (hnodes : ∀ k : Fin (N+1), sectorResidual mu lam (gridPoint U N k) ≤ M) :
    ∀ t : ℝ, 0 ≤ t → t ≤ Real.pi → sectorResidual mu lam t ≤
      M+(1+lam+|mu|)*U/(N : ℝ) :=
  full_interval_upper_of_grid hN hU (by positivity) (sectorResidual_difference hlam mu) hnodes

end N11Formalization.MetricAreaGridCertificate
#check @N11Formalization.MetricAreaGridCertificate.uniform_grid_cover
#check @N11Formalization.MetricAreaGridCertificate.edge_full_domain_upper_of_grid
#check @N11Formalization.MetricAreaGridCertificate.sector_full_domain_upper_of_grid
#print axioms N11Formalization.MetricAreaGridCertificate.uniform_grid_cover
#print axioms N11Formalization.MetricAreaGridCertificate.edge_full_domain_upper_of_grid
#print axioms N11Formalization.MetricAreaGridCertificate.sector_full_domain_upper_of_grid
