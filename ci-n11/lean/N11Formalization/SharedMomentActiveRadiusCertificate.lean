import N11Formalization.CompactQuadraticArgmaxRange
import N11Formalization.SharedMomentFactorIntervalCertificate
import N11Formalization.SharedMomentFactorLocalCertificate

/-! Whole-cell centered factor bounds using certified radii of maximizing
points. The maximizing radius is selected at the target point and kept fixed
when comparing with the midpoint; no differentiation of a maximum or
uniqueness of its maximizer is assumed. All ties and zero radii remain. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentActiveRadiusCertificate
open CompactQuadraticMomentMaximum CompactQuadraticArgmaxRange
open SharedMomentFactorGridCertificate SharedMomentFactorRationalNodes
open SharedMomentFactorIntervalCertificate RationalBoxSubdivision

theorem scaled_change_le {P A B LP LA LB y Y : ℝ}
    (hP : P ≤ LP) (hA : A ≤ LA) (hB : B ≤ LB)
    (hLA : 0 ≤ LA) (hLB : 0 ≤ LB) (hy : 0 ≤ y) (hyY : y ≤ Y) :
    P+A*y^2+B*y ≤ LP+LA*Y^2+LB*Y := by
  have hY : 0 ≤ Y := hy.trans hyY
  have hysq : y^2 ≤ Y^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hyY) (add_nonneg hY hy)]
  exact (add_le_add (add_le_add hP (mul_le_mul_of_nonneg_right hA (sq_nonneg y)))
    (mul_le_mul_of_nonneg_right hB hy)).trans
    (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hysq hLA))
      (mul_le_mul_of_nonneg_left hyY hLB))

def faceActiveLipschitz (p q b : Fin 3 → ℝ) (Y : ℝ) (s : Fin 3) : ℝ :=
  (2*(19/50 : ℝ)^2+2*|q s|)*Y^2+|b s| *Y+|p s|

theorem face_objective_change_le_active (p q b a a' : Fin 3 → ℝ)
    {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    faceObjective p q b a y-faceObjective p q b a' y ≤
      ∑ s : Fin 3, faceActiveLipschitz p q b Y s*|a s-a' s| := by
  have hp := weighted_sum_difference p a a' (fun s => |a s-a' s|) (fun _ => le_rfl)
  have hq := faceQuadratic_difference q a a'
  have hb := weighted_sum_difference b (fun s => Real.sin (a s))
    (fun s => Real.sin (a' s)) (fun s => |a s-a' s|)
    (fun s => Real.abs_sin_sub_sin_le (a s) (a' s))
  have hb' : faceLinear b a-faceLinear b a' ≤ ∑ s : Fin 3, |b s| * |a s-a' s| := by
    exact (le_abs_self _).trans (by simpa only [faceLinear] using hb)
  have hLA : 0 ≤ ∑ s : Fin 3, (2*(19/50 : ℝ)^2+2*|q s|)*|a s-a' s| :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (by positivity) (abs_nonneg _))
  have hLB : 0 ≤ ∑ s : Fin 3, |b s| * |a s-a' s| :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hbound := scaled_change_le ((le_abs_self _).trans hp)
    ((le_abs_self _).trans hq) hb' hLA hLB hy hyY
  have he : faceObjective p q b a y-faceObjective p q b a' y =
      ((∑ s : Fin 3, p s*a s)-(∑ s : Fin 3, p s*a' s))+
      (faceQuadratic q a-faceQuadratic q a')*y^2+(faceLinear b a-faceLinear b a')*y := by
    unfold faceObjective quad
    ring
  have htotal : (∑ s : Fin 3, |p s| * |a s-a' s|)+
      (∑ s : Fin 3, (2*(19/50 : ℝ)^2+2*|q s|)*|a s-a' s|)*Y^2+
      (∑ s : Fin 3, |b s| * |a s-a' s|)*Y =
      ∑ s : Fin 3, faceActiveLipschitz p q b Y s*|a s-a' s| := by
    simp only [Fin.sum_univ_three,faceActiveLipschitz]
    ring
  rw [he,← htotal]
  exact hbound

def faceRadiusUpperQ (q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : ℚ :=
  upperArgQ (faceQuadraticCell q B).hi (faceLinearCell b B).hi
def faceActiveLipschitzQ (p q b : Fin 3 → ℚ) (Y : ℚ) (s : Fin 3) : ℚ :=
  (2*(19/50 : ℚ)^2+2*|q s|)*Y^2+|b s| *Y+|p s|
def faceActiveErrorQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : ℚ :=
  ∑ s : Fin 3, faceActiveLipschitzQ p q b (faceRadiusUpperQ q b B) s*halfWidth B s
def faceActiveUpperQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : ℚ :=
  faceUpperQ p q b (midpoint B)+faceActiveErrorQ p q b B

theorem faceActiveLipschitzQ_cast (p q b : Fin 3 → ℚ) (Y : ℚ) (s : Fin 3) :
    (faceActiveLipschitzQ p q b Y s : ℝ)=
      faceActiveLipschitz (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
        (fun i => (b i : ℝ)) Y s := by
  unfold faceActiveLipschitzQ faceActiveLipschitz
  push_cast
  rfl

theorem face_envelope_le_active_upper (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 3)} {a : Fin 3 → ℝ} (ha : Mem B a) :
    faceEnvelope (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
      (fun i => (b i : ℝ)) a ≤ (faceActiveUpperQ p q b B : ℝ) := by
  have hA := SharedMomentFactorIntervalCertificate.face_quadratic_mem q ha
  have hB := SharedMomentFactorIntervalCertificate.face_linear_mem b ha
  obtain ⟨y,hy,heq,hyY⟩ := maximum_attained_with_rational_upper _ _
    (faceQuadraticCell q B).lo (faceQuadraticCell q B).hi
    (faceLinearCell b B).lo (faceLinearCell b B).hi hA.1 hA.2 hB.1 hB.2
  have hY : (0 : ℝ) ≤ (faceRadiusUpperQ q b B : ℝ) := by
    exact_mod_cast upperArgQ_nonneg (faceQuadraticCell q B).hi (faceLinearCell b B).hi
  have he : faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
      (fun i => (b i : ℝ)) a y =
      faceEnvelope (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a := by
    unfold faceObjective faceEnvelope
    rw [heq]
  have hd := face_objective_change_le_active (fun i => (p i : ℝ))
    (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a (fun i => (midpoint B i : ℝ))
    hy.1 (show y ≤ (faceRadiusUpperQ q b B : ℝ) from hyY)
  have herr : (∑ s : Fin 3, faceActiveLipschitz (fun i => (p i : ℝ))
      (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) (faceRadiusUpperQ q b B) s*
        |a s-(midpoint B s : ℝ)|) ≤ (faceActiveErrorQ p q b B : ℝ) := by
    unfold faceActiveErrorQ
    push_cast
    apply Finset.sum_le_sum
    intro s _
    rw [faceActiveLipschitzQ_cast]
    exact mul_le_mul_of_nonneg_left (distance_le_halfWidth ha s)
      (by unfold faceActiveLipschitz; positivity)
  have hmid := faceObjective_le_envelope (fun i => (p i : ℝ))
    (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) (fun i => (midpoint B i : ℝ)) hy
  have hn := face_upper_of_node p q b (midpoint B)
  rw [he] at hd
  unfold faceActiveUpperQ
  push_cast
  linarith only [hd,herr,hmid,hn]

theorem face_upper_of_active_certificate (p q b : Fin 3 → ℚ) (B : Cell (Fin 3))
    (M : ℚ) (hbound : faceActiveUpperQ p q b B ≤ M) :
    ∀ a, Mem B a → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
        (fun i => (b i : ℝ)) a y ≤ (M : ℝ) := by
  intro a ha y hy
  exact ((faceObjective_le_envelope _ _ _ a hy).trans
    (face_envelope_le_active_upper p q b ha)).trans (by exact_mod_cast hbound)

theorem switch_quadratic_difference (q d2 t t' : ℝ) :
    |switchQuadratic q d2 t-switchQuadratic q d2 t'| ≤
      ((19/50 : ℝ)^2+2*|q|)*|t-t'| := by
  have hs := Real.abs_sin_sub_sin_le (2*t) (2*t')
  rw [show 2*t-2*t'=2*(t-t') by ring,abs_mul] at hs
  norm_num at hs
  have hsq := sine_square_difference t t'
  have he : switchQuadratic q d2 t-switchQuadratic q d2 t' =
      ((19/50 : ℝ)^2/2)*(Real.sin (2*t)-Real.sin (2*t'))+q*(Real.sin t^2-Real.sin t'^2) := by
    unfold switchQuadratic
    ring
  have ht := abs_add_le (((19/50 : ℝ)^2/2)*(Real.sin (2*t)-Real.sin (2*t')))
    (q*(Real.sin t^2-Real.sin t'^2))
  simp only [abs_mul] at ht
  norm_num at ht
  have hp := mul_le_mul_of_nonneg_left hsq (abs_nonneg q)
  rw [he]
  nlinarith only [hs,ht,hp]

def switchActiveLipschitz (p q b Y : ℝ) : ℝ :=
  ((19/50 : ℝ)^2+2*|q|)*Y^2+|b| *Y+|p|

theorem switch_objective_change_le_active (p q b d2 d1 t t' : ℝ)
    {y Y : ℝ} (hy : 0 ≤ y) (hyY : y ≤ Y) :
    switchObjective p q b d2 d1 t y-switchObjective p q b d2 d1 t' y ≤
      switchActiveLipschitz p q b Y*|t-t'| := by
  have hq := switch_quadratic_difference q d2 t t'
  have hs := Real.abs_sin_sub_sin_le t t'
  have hp : p*(t-t') ≤ |p| * |t-t'| := by simpa only [abs_mul] using le_abs_self (p*(t-t'))
  have hb : switchLinear b d1 t-switchLinear b d1 t' ≤ |b| * |t-t'| := by
    have he : switchLinear b d1 t-switchLinear b d1 t'=b*(Real.sin t-Real.sin t') := by
      unfold switchLinear
      ring
    rw [he]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hs (abs_nonneg b))
  have hd := scaled_change_le hp ((le_abs_self _).trans hq) hb
    (show 0 ≤ ((19/50 : ℝ)^2+2*|q|)*|t-t'| by positivity)
    (show 0 ≤ |b| * |t-t'| by positivity) hy hyY
  have he : switchObjective p q b d2 d1 t y-switchObjective p q b d2 d1 t' y =
      p*(t-t')+(switchQuadratic q d2 t-switchQuadratic q d2 t')*y^2+
      (switchLinear b d1 t-switchLinear b d1 t')*y := by
    unfold switchObjective quad
    ring
  rw [he]
  convert hd using 1 <;> unfold switchActiveLipschitz <;> ring

def switchRadiusUpperQ (q b d2 d1 : ℚ) (B : Cell (Fin 1)) : ℚ :=
  upperArgQ (switchQuadraticCell q d2 B).hi (switchLinearCell b d1 B).hi
def switchActiveLipschitzQ (p q b Y : ℚ) : ℚ :=
  ((19/50 : ℚ)^2+2*|q|)*Y^2+|b| *Y+|p|
def switchActiveUpperQ (p q b d2 d1 : ℚ) (B : Cell (Fin 1)) : ℚ :=
  switchUpperQ p q b d2 d1 (midpoint B 0)+
    switchActiveLipschitzQ p q b (switchRadiusUpperQ q b d2 d1 B)*halfWidth B 0

theorem switchActiveLipschitzQ_cast (p q b Y : ℚ) :
    (switchActiveLipschitzQ p q b Y : ℝ)=switchActiveLipschitz p q b Y := by
  unfold switchActiveLipschitzQ switchActiveLipschitz
  push_cast
  rfl

theorem switch_envelope_le_active_upper (p q b d2 d1 : ℚ)
    {B : Cell (Fin 1)} {t : ℝ} (ht : (B 0).Mem t) :
    switchEnvelope p q b d2 d1 t ≤ (switchActiveUpperQ p q b d2 d1 B : ℝ) := by
  have hA := SharedMomentFactorIntervalCertificate.switch_quadratic_mem q d2 ht
  have hB := SharedMomentFactorIntervalCertificate.switch_linear_mem b d1 ht
  obtain ⟨y,hy,heq,hyY⟩ := maximum_attained_with_rational_upper _ _
    (switchQuadraticCell q d2 B).lo (switchQuadraticCell q d2 B).hi
    (switchLinearCell b d1 B).lo (switchLinearCell b d1 B).hi hA.1 hA.2 hB.1 hB.2
  have hY : (0 : ℝ) ≤ (switchRadiusUpperQ q b d2 d1 B : ℝ) := by
    exact_mod_cast upperArgQ_nonneg (switchQuadraticCell q d2 B).hi (switchLinearCell b d1 B).hi
  have hx : Mem B (fun _ => t) := by
    intro i
    fin_cases i
    exact ht
  have he : switchObjective p q b d2 d1 t y=switchEnvelope p q b d2 d1 t := by
    unfold switchObjective switchEnvelope
    rw [heq]
  have hd := switch_objective_change_le_active p q b d2 d1 t (midpoint B 0)
    hy.1 (show y ≤ (switchRadiusUpperQ q b d2 d1 B : ℝ) from hyY)
  have herr := mul_le_mul_of_nonneg_left (distance_le_halfWidth hx 0)
    (show 0 ≤ switchActiveLipschitz p q b (switchRadiusUpperQ q b d2 d1 B) by
      unfold switchActiveLipschitz
      positivity)
  have hmid := switchObjective_le_envelope p q b d2 d1 (midpoint B 0) hy
  have hn := switch_upper_of_node p q b d2 d1 (midpoint B 0)
  rw [he] at hd
  unfold switchActiveUpperQ
  push_cast
  rw [switchActiveLipschitzQ_cast]
  linarith only [hd,herr,hmid,hn]

theorem switch_upper_of_active_certificate (p q b d2 d1 : ℚ) (B : Cell (Fin 1))
    (M : ℚ) (hbound : switchActiveUpperQ p q b d2 d1 B ≤ M) :
    ∀ t, (B 0).Mem t → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ (M : ℝ) := by
  intro t ht y hy
  exact ((switchObjective_le_envelope p q b d2 d1 t hy).trans
    (switch_envelope_le_active_upper p q b d2 d1 ht)).trans (by exact_mod_cast hbound)

end N11Formalization.SharedMomentActiveRadiusCertificate
#check @N11Formalization.SharedMomentActiveRadiusCertificate.face_upper_of_active_certificate
#check @N11Formalization.SharedMomentActiveRadiusCertificate.switch_upper_of_active_certificate
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.face_objective_change_le_active
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.face_envelope_le_active_upper
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.face_upper_of_active_certificate
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.switch_objective_change_le_active
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.switch_envelope_le_active_upper
#print axioms N11Formalization.SharedMomentActiveRadiusCertificate.switch_upper_of_active_certificate
