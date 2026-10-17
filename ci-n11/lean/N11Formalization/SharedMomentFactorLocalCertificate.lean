import N11Formalization.SharedMomentFactorRationalNodes
import N11Formalization.RationalBoxSubdivision

/-! Local rational upper certificates for face and switch factors.
The radius variable is maximized exactly on its entire closed unit interval;
only angular variables are subdivided. The midpoint node uses the certified
signed rational Taylor enclosure, and the Lipschitz remainder pays for the
entire closed angular box, including its boundary. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFactorLocalCertificate
open SharedMomentFactorGridCertificate SharedMomentFactorRationalNodes
open RationalBoxSubdivision MetricAreaRationalCertificate

def faceLocalErrorQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : ℚ :=
  ∑ s : Fin 3, faceLipschitzQ p q b s * halfWidth B s

def faceLocalUpperQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : ℚ :=
  faceUpperQ p q b (midpoint B) + faceLocalErrorQ p q b B

theorem faceLipschitzQ_cast (p q b : Fin 3 → ℚ) (s : Fin 3) :
    (faceLipschitzQ p q b s : ℝ) =
      faceLipschitz (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
        (fun i => (b i : ℝ)) s := by
  unfold faceLipschitzQ faceLipschitz
  push_cast
  rfl

theorem face_local_error_bound (p q b : Fin 3 → ℚ) {B : Cell (Fin 3)}
    {a : Fin 3 → ℝ} (ha : Mem B a) :
    (∑ s : Fin 3,
      faceLipschitz (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
        (fun i => (b i : ℝ)) s * |a s - (midpoint B s : ℝ)|) ≤
      (faceLocalErrorQ p q b B : ℝ) := by
  unfold faceLocalErrorQ
  push_cast
  apply Finset.sum_le_sum
  intro s _
  rw [faceLipschitzQ_cast]
  exact mul_le_mul_of_nonneg_left (distance_le_halfWidth ha s)
    (by unfold faceLipschitz; positivity)

theorem face_envelope_le_local_upper (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 3)} {a : Fin 3 → ℝ} (ha : Mem B a) :
    faceEnvelope (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
      (fun i => (b i : ℝ)) a ≤ (faceLocalUpperQ p q b B : ℝ) := by
  have hd := faceEnvelope_difference (fun i => (p i : ℝ))
    (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a
    (fun i => (midpoint B i : ℝ))
  have hle := le_abs_self
    (faceEnvelope (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
      (fun i => (b i : ℝ)) a -
     faceEnvelope (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
      (fun i => (b i : ℝ)) (fun i => (midpoint B i : ℝ)))
  have hm := face_upper_of_node p q b (midpoint B)
  have he := face_local_error_bound p q b ha
  unfold faceLocalUpperQ
  push_cast
  linarith only [hd,hle,hm,he]

theorem face_objective_le_local_upper (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 3)} {a : Fin 3 → ℝ} (ha : Mem B a)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
      (fun i => (b i : ℝ)) a y ≤ (faceLocalUpperQ p q b B : ℝ) :=
  (faceObjective_le_envelope _ _ _ a hy).trans (face_envelope_le_local_upper p q b ha)

theorem face_upper_of_local_certificate (p q b : Fin 3 → ℚ)
    (B : Cell (Fin 3)) (M : ℚ) (hM : faceLocalUpperQ p q b B ≤ M) :
    ∀ a : Fin 3 → ℝ, Mem B a → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
        (fun i => (b i : ℝ)) a y ≤ (M : ℝ) := by
  intro a ha y hy
  exact (face_objective_le_local_upper p q b ha hy).trans (by exact_mod_cast hM)

def switchLipschitzQ (p q b : ℚ) : ℚ :=
  (19/50 : ℚ)^2 + |p| + 2*|q| + |b|

def switchLocalUpperQ (p q b d2 d1 : ℚ) (B : Cell (Fin 1)) : ℚ :=
  switchUpperQ p q b d2 d1 (midpoint B 0) +
    switchLipschitzQ p q b * halfWidth B 0

theorem switchLipschitzQ_cast (p q b : ℚ) :
    (switchLipschitzQ p q b : ℝ) = switchLipschitz p q b := by
  unfold switchLipschitzQ switchLipschitz
  push_cast
  rfl

theorem switch_envelope_le_local_upper (p q b d2 d1 : ℚ)
    {B : Cell (Fin 1)} {t : ℝ} (ht : (B 0).Mem t) :
    switchEnvelope p q b d2 d1 t ≤ (switchLocalUpperQ p q b d2 d1 B : ℝ) := by
  have hx : Mem B (fun _ => t) := by
    intro i
    fin_cases i
    exact ht
  have hd := switchEnvelope_difference p q b d2 d1 t (midpoint B 0)
  have hle := le_abs_self
    (switchEnvelope p q b d2 d1 t - switchEnvelope p q b d2 d1 (midpoint B 0))
  have hm := switch_upper_of_node p q b d2 d1 (midpoint B 0)
  have he := mul_le_mul_of_nonneg_left (distance_le_halfWidth hx 0)
    (show 0 ≤ switchLipschitz p q b by unfold switchLipschitz; positivity)
  unfold switchLocalUpperQ
  push_cast
  rw [switchLipschitzQ_cast]
  linarith only [hd,hle,hm,he]

theorem switch_objective_le_local_upper (p q b d2 d1 : ℚ)
    {B : Cell (Fin 1)} {t : ℝ} (ht : (B 0).Mem t)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    switchObjective p q b d2 d1 t y ≤ (switchLocalUpperQ p q b d2 d1 B : ℝ) :=
  (switchObjective_le_envelope p q b d2 d1 t hy).trans
    (switch_envelope_le_local_upper p q b d2 d1 ht)

theorem switch_upper_of_local_certificate (p q b d2 d1 : ℚ)
    (B : Cell (Fin 1)) (M : ℚ) (hM : switchLocalUpperQ p q b d2 d1 B ≤ M) :
    ∀ t : ℝ, (B 0).Mem t → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ (M : ℝ) := by
  intro t ht y hy
  exact (switch_objective_le_local_upper p q b d2 d1 ht hy).trans (by exact_mod_cast hM)

end N11Formalization.SharedMomentFactorLocalCertificate
#check @N11Formalization.SharedMomentFactorLocalCertificate.face_upper_of_local_certificate
#check @N11Formalization.SharedMomentFactorLocalCertificate.switch_upper_of_local_certificate
#print axioms N11Formalization.SharedMomentFactorLocalCertificate.face_envelope_le_local_upper
#print axioms N11Formalization.SharedMomentFactorLocalCertificate.face_objective_le_local_upper
#print axioms N11Formalization.SharedMomentFactorLocalCertificate.face_upper_of_local_certificate
#print axioms N11Formalization.SharedMomentFactorLocalCertificate.switch_envelope_le_local_upper
#print axioms N11Formalization.SharedMomentFactorLocalCertificate.switch_objective_le_local_upper
#print axioms N11Formalization.SharedMomentFactorLocalCertificate.switch_upper_of_local_certificate
