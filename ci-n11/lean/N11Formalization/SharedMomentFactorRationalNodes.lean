import N11Formalization.SharedMomentFactorGridCertificate
import N11Formalization.MetricAreaRationalCertificate

/-! Signed rational Taylor/interval production for every face and switch
envelope node. Exact quadratic radius maximization is performed after
sound outward coefficient enclosures, not after sampling radii. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFactorRationalNodes
open SharedMomentFactorGridCertificate CompactQuadraticMomentMaximum
open CompactSimplexGridCertificate MetricAreaRationalCertificate

def sinInterval (a : ℚ) : RatInterval := ⟨sinLoNLag a,sinHiNLag a⟩
def sinSquaredInterval (a : ℚ) : RatInterval := (sinInterval a).mul (sinInterval a)
def sumThreeInterval (p : Fin 3 → ℚ) (I : Fin 3 → RatInterval) : RatInterval :=
  (((RatInterval.ofRat (p 0)).mul (I 0)).add ((RatInterval.ofRat (p 1)).mul (I 1))).add
    ((RatInterval.ofRat (p 2)).mul (I 2))

theorem sin_mem (a : ℚ) : (sinInterval a).Mem (Real.sin (a : ℝ)) :=
  ⟨sinLoNLag_le_sin a,sin_le_sinHiNLag a⟩
theorem sin_squared_mem (a : ℚ) : (sinSquaredInterval a).Mem (Real.sin (a : ℝ)^2) := by
  simpa only [sinSquaredInterval,pow_two] using RatInterval.mul_mem (sin_mem a) (sin_mem a)
theorem sum_three_mem (p : Fin 3 → ℚ) (I : Fin 3 → RatInterval) (x : Fin 3 → ℝ)
    (hx : ∀ s, (I s).Mem (x s)) :
    (sumThreeInterval p I).Mem (∑ s : Fin 3, (p s : ℝ)*x s) := by
  simpa only [sumThreeInterval,Fin.sum_univ_three] using
    RatInterval.add_mem (RatInterval.add_mem
      (RatInterval.mul_mem (RatInterval.ofRat_mem (p 0)) (hx 0))
      (RatInterval.mul_mem (RatInterval.ofRat_mem (p 1)) (hx 1)))
      (RatInterval.mul_mem (RatInterval.ofRat_mem (p 2)) (hx 2))

def faceQuadraticInterval (q a : Fin 3 → ℚ) : RatInterval :=
  ((((RatInterval.ofRat (2*(19/50 : ℚ)^2)).mul (sinInterval (a 0))).mul
    (sinInterval (a 1))).mul (sinInterval (a 2))).add
    (sumThreeInterval q (fun s => sinSquaredInterval (a s)))
def faceLinearInterval (b a : Fin 3 → ℚ) : RatInterval := sumThreeInterval b (fun s => sinInterval (a s))
def faceUpperQ (p q b a : Fin 3 → ℚ) : ℚ :=
  (∑ s : Fin 3, p s*a s)+maximumQ (faceQuadraticInterval q a).hi (faceLinearInterval b a).hi

theorem face_quadratic_mem (q a : Fin 3 → ℚ) :
    (faceQuadraticInterval q a).Mem (faceQuadratic (fun s => (q s : ℝ)) (fun s => (a s : ℝ))) := by
  have hc : (RatInterval.ofRat (2*(19/50 : ℚ)^2)).Mem (2*(19/50 : ℝ)^2) := by
    convert RatInterval.ofRat_mem (2*(19/50 : ℚ)^2) using 1 <;> norm_num
  exact RatInterval.add_mem (RatInterval.mul_mem (RatInterval.mul_mem
    (RatInterval.mul_mem hc (sin_mem (a 0))) (sin_mem (a 1))) (sin_mem (a 2)))
    (sum_three_mem q (fun s => sinSquaredInterval (a s)) (fun s => Real.sin (a s : ℝ)^2)
      (fun s => sin_squared_mem (a s)))

theorem face_linear_mem (b a : Fin 3 → ℚ) :
    (faceLinearInterval b a).Mem (faceLinear (fun s => (b s : ℝ)) (fun s => (a s : ℝ))) :=
  sum_three_mem b (fun s => sinInterval (a s)) (fun s => Real.sin (a s : ℝ)) (fun s => sin_mem (a s))

theorem face_upper_of_node (p q b a : Fin 3 → ℚ) :
    faceEnvelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ)) (fun s => (b s : ℝ))
      (fun s => (a s : ℝ)) ≤ (faceUpperQ p q b a : ℝ) := by
  have hA := face_quadratic_mem q a
  have hB := face_linear_mem b a
  have hm := (maximum_rational_enclosure hA.1 hA.2 hB.1 hB.2).2
  unfold faceEnvelope faceUpperQ
  push_cast
  exact add_le_add le_rfl hm

def faceNodeQ (U : ℚ) (N : ℕ) (k : Index N) : Fin 3 → ℚ :=
  ![nodeQ U N k.val.1,nodeQ U N k.val.2,U-nodeQ U N k.val.1-nodeQ U N k.val.2]
theorem faceNodeQ_cast (U : ℚ) (N : ℕ) (k : Index N) :
    (fun s => (faceNodeQ U N k s : ℝ)) = node (U : ℝ) N k := by
  funext s
  fin_cases s <;> simp [faceNodeQ,node,nodeQ_cast]

def faceLipschitzQ (p q b : Fin 3 → ℚ) (s : Fin 3) : ℚ :=
  2*(19/50 : ℚ)^2+|p s|+2*|q s|+|b s|
def faceGridErrorQ (p q b : Fin 3 → ℚ) (U P : ℚ) (N : ℕ) : ℚ :=
  (faceLipschitzQ p q b 0+faceLipschitzQ p q b 1+2*faceLipschitzQ p q b 2)*U/N+
    faceLipschitzQ p q b 2*(U-P)
theorem faceGridErrorQ_cast (p q b : Fin 3 → ℚ) (U P : ℚ) (N : ℕ) :
    (faceGridErrorQ p q b U P N : ℝ)=faceGridError
      (fun s => (p s : ℝ)) (fun s => (q s : ℝ)) (fun s => (b s : ℝ)) U P N := by
  simp only [faceGridErrorQ,faceLipschitzQ,faceGridError,faceLipschitz]
  push_cast
  rfl

theorem face_full_domain_upper_of_rational_certificate (p q b : Fin 3 → ℚ)
    (U M : ℚ) (hU : RatInterval.piHi ≤ U) (N : ℕ) (hN : 0 < N)
    (hnodes : ∀ k : Index N, faceUpperQ p q b (faceNodeQ U N k) ≤ M) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) →
      (∑ s : Fin 3, a s)=Real.pi → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ)) (fun s => (b s : ℝ)) a y ≤
        (M+faceGridErrorQ p q b U RatInterval.piLo N : ℚ) := by
  push_cast
  rw [faceGridErrorQ_cast]
  apply face_full_domain_upper_of_grid _ _ _
    (RatInterval.pi_lt_piHi.le.trans (by exact_mod_cast hU)) RatInterval.piLo_lt_pi.le hN
  intro k
  rw [← faceNodeQ_cast]
  exact (face_upper_of_node p q b (faceNodeQ U N k)).trans (by exact_mod_cast hnodes k)

def switchQuadraticInterval (q d2 t : ℚ) : RatInterval :=
  (((RatInterval.ofRat ((19/50 : ℚ)^2/2)).mul (sinInterval (2*t))).add
    ((RatInterval.ofRat q).mul (sinSquaredInterval t))).add (RatInterval.ofRat d2)
def switchLinearInterval (b d1 t : ℚ) : RatInterval :=
  ((RatInterval.ofRat b).mul (sinInterval t)).add (RatInterval.ofRat d1)
def switchUpperQ (p q b d2 d1 t : ℚ) : ℚ :=
  p*t+maximumQ (switchQuadraticInterval q d2 t).hi (switchLinearInterval b d1 t).hi
def switchGridErrorQ (p q b U : ℚ) (N : ℕ) : ℚ :=
  ((19/50 : ℚ)^2+|p|+2*|q|+|b|)*U/N

theorem switch_quadratic_mem (q d2 t : ℚ) :
    (switchQuadraticInterval q d2 t).Mem (switchQuadratic q d2 t) := by
  have hc : (RatInterval.ofRat ((19/50 : ℚ)^2/2)).Mem ((19/50 : ℝ)^2/2) := by
    convert RatInterval.ofRat_mem ((19/50 : ℚ)^2/2) using 1 <;> norm_num
  have hh := RatInterval.add_mem (RatInterval.add_mem (RatInterval.mul_mem hc (sin_mem (2*t)))
    (RatInterval.mul_mem (RatInterval.ofRat_mem q) (sin_squared_mem t))) (RatInterval.ofRat_mem d2)
  convert hh using 1
  · rfl
  · unfold switchQuadratic
    push_cast
    ring
theorem switch_linear_mem (b d1 t : ℚ) :
    (switchLinearInterval b d1 t).Mem (switchLinear b d1 t) :=
  RatInterval.add_mem (RatInterval.mul_mem (RatInterval.ofRat_mem b) (sin_mem t)) (RatInterval.ofRat_mem d1)
theorem switch_upper_of_node (p q b d2 d1 t : ℚ) :
    switchEnvelope p q b d2 d1 t ≤ (switchUpperQ p q b d2 d1 t : ℝ) := by
  have hA := switch_quadratic_mem q d2 t
  have hB := switch_linear_mem b d1 t
  have hm := (maximum_rational_enclosure hA.1 hA.2 hB.1 hB.2).2
  unfold switchEnvelope switchUpperQ
  push_cast
  exact add_le_add le_rfl hm

theorem switch_full_domain_upper_of_rational_certificate (p q b d2 d1 U M : ℚ)
    (hU : RatInterval.piHi/2 ≤ U) (N : ℕ) (hN : 0 < N)
    (hnodes : ∀ k : Fin (N+1), switchUpperQ p q b d2 d1 (nodeQ U N k) ≤ M) :
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi/2), ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ (M+switchGridErrorQ p q b U N : ℚ) := by
  have hUr : Real.pi/2 ≤ (U : ℝ) := by
    have hh : ((RatInterval.piHi : ℚ) : ℝ)/2 ≤ U := by exact_mod_cast hU
    linarith [RatInterval.pi_lt_piHi.le]
  unfold switchGridErrorQ
  push_cast
  apply switch_full_domain_upper_of_grid p q b d2 d1 hUr hN
  intro k
  rw [← nodeQ_cast]
  exact (switch_upper_of_node p q b d2 d1 (nodeQ U N k)).trans (by exact_mod_cast hnodes k)

end N11Formalization.SharedMomentFactorRationalNodes
#check @N11Formalization.SharedMomentFactorRationalNodes.face_full_domain_upper_of_rational_certificate
#check @N11Formalization.SharedMomentFactorRationalNodes.switch_full_domain_upper_of_rational_certificate
#print axioms N11Formalization.SharedMomentFactorRationalNodes.face_upper_of_node
#print axioms N11Formalization.SharedMomentFactorRationalNodes.switch_upper_of_node
#print axioms N11Formalization.SharedMomentFactorRationalNodes.face_full_domain_upper_of_rational_certificate
#print axioms N11Formalization.SharedMomentFactorRationalNodes.switch_full_domain_upper_of_rational_certificate
