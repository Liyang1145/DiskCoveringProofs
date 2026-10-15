import N11Formalization.CompactQuadraticMomentMaximum
import N11Formalization.CompactSimplexGridCertificate
import N11Formalization.ActualSharedMomentMaskedDual

/-! Exact radius maximization and full closed angular grids for signed
face and switch factors. Face grids retain the simplex equation; only
the tiny certified replacement of pi by a rational upper endpoint is
enlarged. Zero-radius and all angular boundaries remain in the domains. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFactorGridCertificate
open CompactQuadraticMomentMaximum CompactSimplexGridCertificate MetricAreaGridCertificate
open ActualSharedMomentDual ActualSharedMomentData ActualEdgeFlagSums
open ActualRingLinkBoundaryData ActualFiniteNearestRefinement

def faceQuadratic (q : Fin 3 → ℝ) (a : Fin 3 → ℝ) : ℝ :=
  2*(19/50 : ℝ)^2*Real.sin (a 0)*Real.sin (a 1)*Real.sin (a 2)+
    ∑ s : Fin 3, q s*Real.sin (a s)^2
def faceLinear (b : Fin 3 → ℝ) (a : Fin 3 → ℝ) : ℝ :=
  ∑ s : Fin 3, b s*Real.sin (a s)
def faceObjective (p q b a : Fin 3 → ℝ) (y : ℝ) : ℝ :=
  (∑ s : Fin 3, p s*a s)+quad (faceQuadratic q a) (faceLinear b a) y
def faceEnvelope (p q b a : Fin 3 → ℝ) : ℝ :=
  (∑ s : Fin 3, p s*a s)+maximum (faceQuadratic q a) (faceLinear b a)
def faceLipschitz (p q b : Fin 3 → ℝ) (s : Fin 3) : ℝ :=
  2*(19/50 : ℝ)^2+|p s|+2*|q s|+|b s|

def switchQuadratic (q d2 t : ℝ) : ℝ := (19/50 : ℝ)^2*Real.sin (2*t)/2+q*Real.sin t^2+d2
def switchLinear (b d1 t : ℝ) : ℝ := b*Real.sin t+d1
def switchObjective (p q b d2 d1 t y : ℝ) : ℝ := p*t+quad (switchQuadratic q d2 t) (switchLinear b d1 t) y
def switchEnvelope (p q b d2 d1 t : ℝ) : ℝ := p*t+maximum (switchQuadratic q d2 t) (switchLinear b d1 t)
def switchLipschitz (p q b : ℝ) : ℝ := (19/50 : ℝ)^2+|p|+2*|q|+|b|

theorem faceObjective_le_envelope (p q b a : Fin 3 → ℝ) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : faceObjective p q b a y ≤ faceEnvelope p q b a := by
  unfold faceObjective faceEnvelope
  exact add_le_add le_rfl (quad_le_maximum hy)
theorem switchObjective_le_envelope (p q b d2 d1 t : ℝ) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    switchObjective p q b d2 d1 t y ≤ switchEnvelope p q b d2 d1 t := by
  unfold switchObjective switchEnvelope
  exact add_le_add le_rfl (quad_le_maximum hy)

theorem unit_product_difference {x y x' y' : ℝ}
    (hy : |y| ≤ 1) (hx' : |x'| ≤ 1) :
    |x*y-x'*y'| ≤ |x-x'|+|y-y'| := by
  have he : x*y-x'*y'=(x-x')*y+x'*(y-y') := by ring
  have ht := abs_add_le ((x-x')*y) (x'*(y-y'))
  simp only [abs_mul] at ht
  have h1 := mul_le_mul_of_nonneg_left hy (abs_nonneg (x-x'))
  have h2 := mul_le_mul_of_nonneg_right hx' (abs_nonneg (y-y'))
  rw [he]
  linarith only [ht,h1,h2]

theorem sine_square_difference (a b : ℝ) : |Real.sin a^2-Real.sin b^2| ≤ 2*|a-b| := by
  have hh := unit_product_difference (x := Real.sin a) (y' := Real.sin b)
    (Real.abs_sin_le_one a) (Real.abs_sin_le_one b)
  have hs := Real.abs_sin_sub_sin_le a b
  simpa only [← pow_two] using hh.trans (show |Real.sin a-Real.sin b|+|Real.sin a-Real.sin b| ≤ 2*|a-b| by linarith)

theorem sine_product_three_difference (a b : Fin 3 → ℝ) :
    |Real.sin (a 0)*Real.sin (a 1)*Real.sin (a 2)-
      Real.sin (b 0)*Real.sin (b 1)*Real.sin (b 2)| ≤ ∑ s : Fin 3, |a s-b s| := by
  have hprod : |Real.sin (b 0)*Real.sin (b 1)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (b 0))
      (abs_nonneg (Real.sin (b 1)))).trans (by simpa using Real.abs_sin_le_one (b 1))
  have h1 := unit_product_difference (x := Real.sin (a 0)) (y' := Real.sin (b 1))
    (Real.abs_sin_le_one (a 1)) (Real.abs_sin_le_one (b 0))
  have h2 := unit_product_difference (x := Real.sin (a 0)*Real.sin (a 1)) (y' := Real.sin (b 2))
    (Real.abs_sin_le_one (a 2)) hprod
  have hs0 := Real.abs_sin_sub_sin_le (a 0) (b 0)
  have hs1 := Real.abs_sin_sub_sin_le (a 1) (b 1)
  have hs2 := Real.abs_sin_sub_sin_le (a 2) (b 2)
  rw [Fin.sum_univ_three]
  linarith only [h1,h2,hs0,hs1,hs2]

theorem weighted_sum_difference {I : Type*} [Fintype I]
    (p f g L : I → ℝ) (hfg : ∀ i, |f i-g i| ≤ L i) :
    |(∑ i : I, p i*f i)-(∑ i : I, p i*g i)| ≤ ∑ i : I, |p i| * L i := by
  rw [← Finset.sum_sub_distrib]
  have hh := Finset.abs_sum_le_sum_abs (fun i => p i*f i-p i*g i) Finset.univ
  apply hh.trans
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left (hfg i) (abs_nonneg (p i))

theorem faceQuadratic_difference (q a b : Fin 3 → ℝ) :
    |faceQuadratic q a-faceQuadratic q b| ≤
      ∑ s : Fin 3, (2*(19/50 : ℝ)^2+2*|q s|)*|a s-b s| := by
  have hp := sine_product_three_difference a b
  have hs := weighted_sum_difference q (fun s => Real.sin (a s)^2)
    (fun s => Real.sin (b s)^2) (fun s => 2*|a s-b s|) (fun s => sine_square_difference (a s) (b s))
  have he : faceQuadratic q a-faceQuadratic q b =
      2*(19/50 : ℝ)^2*(Real.sin (a 0)*Real.sin (a 1)*Real.sin (a 2)-
        Real.sin (b 0)*Real.sin (b 1)*Real.sin (b 2))+
      ((∑ s : Fin 3, q s*Real.sin (a s)^2)-(∑ s : Fin 3, q s*Real.sin (b s)^2)) := by
    unfold faceQuadratic
    ring
  have ht := abs_add_le (2*(19/50 : ℝ)^2*(Real.sin (a 0)*Real.sin (a 1)*Real.sin (a 2)-
      Real.sin (b 0)*Real.sin (b 1)*Real.sin (b 2)))
    ((∑ s : Fin 3, q s*Real.sin (a s)^2)-(∑ s : Fin 3, q s*Real.sin (b s)^2))
  rw [abs_mul] at ht
  norm_num at ht
  have hp' := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2*(19/50)^2 by norm_num)
  rw [he]
  simp only [Fin.sum_univ_three] at hs hp' ht ⊢
  nlinarith only [ht,hs,hp']

theorem faceEnvelope_difference (p q b a a' : Fin 3 → ℝ) :
    |faceEnvelope p q b a-faceEnvelope p q b a'| ≤
      ∑ s : Fin 3, faceLipschitz p q b s*|a s-a' s| := by
  have hp := weighted_sum_difference p a a' (fun s => |a s-a' s|) (fun _ => le_rfl)
  have hq := faceQuadratic_difference q a a'
  have hb := weighted_sum_difference b (fun s => Real.sin (a s)) (fun s => Real.sin (a' s))
    (fun s => |a s-a' s|) (fun s => Real.abs_sin_sub_sin_le (a s) (a' s))
  have hm := maximum_lipschitz (faceQuadratic q a) (faceLinear b a)
    (faceQuadratic q a') (faceLinear b a')
  have he : faceEnvelope p q b a-faceEnvelope p q b a' =
      ((∑ s : Fin 3, p s*a s)-(∑ s : Fin 3, p s*a' s))+
      (maximum (faceQuadratic q a) (faceLinear b a)-maximum (faceQuadratic q a') (faceLinear b a')) := by
    unfold faceEnvelope
    ring
  have ht := abs_add_le ((∑ s : Fin 3, p s*a s)-(∑ s : Fin 3, p s*a' s))
    (maximum (faceQuadratic q a) (faceLinear b a)-maximum (faceQuadratic q a') (faceLinear b a'))
  rw [he]
  unfold faceLinear at hm
  simp only [Fin.sum_univ_three,faceLipschitz,faceLinear] at hp hq hb hm ht ⊢
  nlinarith only [hp,hq,hb,hm,ht]

theorem switchEnvelope_difference (p q b d2 d1 t t' : ℝ) :
    |switchEnvelope p q b d2 d1 t-switchEnvelope p q b d2 d1 t'| ≤ switchLipschitz p q b*|t-t'| := by
  have hs := Real.abs_sin_sub_sin_le t t'
  have hs2 := Real.abs_sin_sub_sin_le (2*t) (2*t')
  rw [show 2*t-2*t'=2*(t-t') by ring,abs_mul] at hs2
  norm_num at hs2
  have hsq := sine_square_difference t t'
  have hqe : switchQuadratic q d2 t-switchQuadratic q d2 t' =
      ((19/50 : ℝ)^2/2)*(Real.sin (2*t)-Real.sin (2*t'))+q*(Real.sin t^2-Real.sin t'^2) := by
    unfold switchQuadratic
    ring
  have hqt := abs_add_le (((19/50 : ℝ)^2/2)*(Real.sin (2*t)-Real.sin (2*t')))
    (q*(Real.sin t^2-Real.sin t'^2))
  simp only [abs_mul] at hqt
  norm_num at hqt
  have hqp := mul_le_mul_of_nonneg_left hsq (abs_nonneg q)
  have hbp := mul_le_mul_of_nonneg_left hs (abs_nonneg b)
  have hm := maximum_lipschitz (switchQuadratic q d2 t) (switchLinear b d1 t)
    (switchQuadratic q d2 t') (switchLinear b d1 t')
  have hbe : switchLinear b d1 t-switchLinear b d1 t'=b*(Real.sin t-Real.sin t') := by
    unfold switchLinear
    ring
  rw [hbe,abs_mul,hqe] at hm
  have he : switchEnvelope p q b d2 d1 t-switchEnvelope p q b d2 d1 t' =
      p*(t-t')+(maximum (switchQuadratic q d2 t) (switchLinear b d1 t)-
        maximum (switchQuadratic q d2 t') (switchLinear b d1 t')) := by
    unfold switchEnvelope
    ring
  have ht := abs_add_le (p*(t-t')) (maximum (switchQuadratic q d2 t) (switchLinear b d1 t)-
    maximum (switchQuadratic q d2 t') (switchLinear b d1 t'))
  rw [abs_mul] at ht
  rw [he]
  unfold switchLipschitz
  nlinarith only [hs2,hqt,hqp,hbp,hm,ht]

def faceGridError (p q b : Fin 3 → ℝ) (U P : ℝ) (N : ℕ) : ℝ :=
  (faceLipschitz p q b 0+faceLipschitz p q b 1+2*faceLipschitz p q b 2)*U/(N : ℝ)+
    faceLipschitz p q b 2*(U-P)

theorem face_full_domain_upper_of_grid (p q b : Fin 3 → ℝ) {U P M : ℝ} {N : ℕ}
    (hU : Real.pi ≤ U) (hP : P ≤ Real.pi) (hN : 0 < N)
    (hnodes : ∀ k : Index N, faceEnvelope p q b (node U N k) ≤ M) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective p q b a y ≤ M+faceGridError p q b U P N := by
  intro a ha hsum y hy
  have hh := pi_simplex_upper_of_grid hU hP hN (faceLipschitz p q b)
    (fun s => by unfold faceLipschitz; positivity) (faceEnvelope p q b)
    (faceEnvelope_difference p q b) hnodes a ⟨fun s => (ha s).1,hsum⟩
  unfold faceGridError
  have he : M+(faceLipschitz p q b 0+faceLipschitz p q b 1+2*faceLipschitz p q b 2)*U/(N : ℝ)+
      faceLipschitz p q b 2*(U-P) =
      M+((faceLipschitz p q b 0+faceLipschitz p q b 1+2*faceLipschitz p q b 2)*U/(N : ℝ)+
      faceLipschitz p q b 2*(U-P)) := by ring
  rw [he] at hh
  exact (faceObjective_le_envelope p q b a hy).trans hh

theorem switch_full_domain_upper_of_grid (p q b d2 d1 : ℝ) {U M : ℝ} {N : ℕ}
    (hU : Real.pi/2 ≤ U) (hN : 0 < N)
    (hnodes : ∀ k : Fin (N+1), switchEnvelope p q b d2 d1 (gridPoint U N k) ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi/2), ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ M+switchLipschitz p q b*U/(N : ℝ) := by
  intro t ht y hy
  obtain ⟨k,hk⟩ := uniform_grid_cover (by linarith [Real.pi_pos] : 0 < U) hN ⟨ht.1,ht.2.trans hU⟩
  have hh := switchEnvelope_difference p q b d2 d1 t (gridPoint U N k)
  have hL : 0 ≤ switchLipschitz p q b := by unfold switchLipschitz; positivity
  have hm := mul_le_mul_of_nonneg_left hk hL
  rw [← mul_div_assoc] at hm
  have hd := le_abs_self (switchEnvelope p q b d2 d1 t-switchEnvelope p q b d2 d1 (gridPoint U N k))
  have ho := switchObjective_le_envelope p q b d2 d1 t hy
  linarith only [hh,hm,hd,ho,hnodes k]

end N11Formalization.SharedMomentFactorGridCertificate
#check @N11Formalization.SharedMomentFactorGridCertificate.face_full_domain_upper_of_grid
#check @N11Formalization.SharedMomentFactorGridCertificate.switch_full_domain_upper_of_grid
#print axioms N11Formalization.SharedMomentFactorGridCertificate.faceEnvelope_difference
#print axioms N11Formalization.SharedMomentFactorGridCertificate.switchEnvelope_difference
#print axioms N11Formalization.SharedMomentFactorGridCertificate.face_full_domain_upper_of_grid
#print axioms N11Formalization.SharedMomentFactorGridCertificate.switch_full_domain_upper_of_grid
