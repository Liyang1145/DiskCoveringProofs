import N11Formalization.SharedMomentFactorRationalNodes
import N11Formalization.RationalTrigCellBounds

/-! Direct signed factor bounds on complete closed rational angular cells.
All real angles are enclosed by the rational trigonometric cell operators.
Interval arithmetic preserves signed coefficients; exact quadratic radius
maximization covers every normalized radius, including zero and one. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFactorIntervalCertificate

open RationalBoxSubdivision RationalTrigCellBounds
open SharedMomentFactorGridCertificate SharedMomentFactorRationalNodes
open CompactQuadraticMomentMaximum

def faceQuadraticCell (q : Fin 3 → ℚ) (B : Cell (Fin 3)) : RatInterval :=
  ((((RatInterval.ofRat (2*(19/50 : ℚ)^2)).mul (sinCell (B 0))).mul
    (sinCell (B 1))).mul (sinCell (B 2))).add
    (sumThreeInterval q (fun s => squareCell (sinCell (B s))))

def faceLinearCell (b : Fin 3 → ℚ) (B : Cell (Fin 3)) : RatInterval :=
  sumThreeInterval b (fun s => sinCell (B s))

def faceAngleLinearCell (p : Fin 3 → ℚ) (B : Cell (Fin 3)) : RatInterval :=
  sumThreeInterval p B

def faceDirectUpperQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : ℚ :=
  (faceAngleLinearCell p B).hi+
    maximumQ (faceQuadraticCell q B).hi (faceLinearCell b B).hi

theorem face_quadratic_mem (q : Fin 3 → ℚ) {B : Cell (Fin 3)} {a : Fin 3 → ℝ}
    (ha : RationalBoxSubdivision.Mem B a) :
    (faceQuadraticCell q B).Mem (faceQuadratic (fun s => (q s : ℝ)) a) := by
  have hc : (RatInterval.ofRat (2*(19/50 : ℚ)^2)).Mem (2*(19/50 : ℝ)^2) := by
    convert RatInterval.ofRat_mem (2*(19/50 : ℚ)^2) using 1 <;> norm_num
  exact RatInterval.add_mem (RatInterval.mul_mem (RatInterval.mul_mem
    (RatInterval.mul_mem hc (sinCell_mem (ha 0))) (sinCell_mem (ha 1))) (sinCell_mem (ha 2)))
    (sum_three_mem q (fun s => squareCell (sinCell (B s))) (fun s => Real.sin (a s)^2)
      (fun s => squareCell_mem (sinCell_mem (ha s))))

theorem face_linear_mem (b : Fin 3 → ℚ) {B : Cell (Fin 3)} {a : Fin 3 → ℝ}
    (ha : RationalBoxSubdivision.Mem B a) :
    (faceLinearCell b B).Mem (faceLinear (fun s => (b s : ℝ)) a) :=
  sum_three_mem b (fun s => sinCell (B s)) (fun s => Real.sin (a s))
    (fun s => sinCell_mem (ha s))

theorem face_angle_linear_mem (p : Fin 3 → ℚ) {B : Cell (Fin 3)} {a : Fin 3 → ℝ}
    (ha : RationalBoxSubdivision.Mem B a) :
    (faceAngleLinearCell p B).Mem (∑ s : Fin 3, (p s : ℝ)*a s) :=
  sum_three_mem p B a ha

theorem face_envelope_le_direct_upper (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 3)} {a : Fin 3 → ℝ} (ha : RationalBoxSubdivision.Mem B a) :
    faceEnvelope (fun s => (p s : ℝ)) (fun s => (q s : ℝ)) (fun s => (b s : ℝ)) a ≤
      (faceDirectUpperQ p q b B : ℝ) := by
  have hP := face_angle_linear_mem p ha
  have hA := face_quadratic_mem q ha
  have hL := face_linear_mem b ha
  have hm := (maximum_rational_enclosure hA.1 hA.2 hL.1 hL.2).2
  unfold faceEnvelope faceDirectUpperQ
  rw [Rat.cast_add]
  exact add_le_add hP.2 hm

theorem face_upper_of_direct_certificate (p q b : Fin 3 → ℚ) (B : Cell (Fin 3))
    (M : ℚ) (hbound : faceDirectUpperQ p q b B ≤ M) :
    ∀ a, RationalBoxSubdivision.Mem B a → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun s => (p s : ℝ)) (fun s => (q s : ℝ)) (fun s => (b s : ℝ)) a y ≤
        (M : ℝ) := by
  intro a ha y hy
  exact (faceObjective_le_envelope _ _ _ _ hy).trans
    ((face_envelope_le_direct_upper p q b ha).trans (by exact_mod_cast hbound))

def switchQuadraticCell (q d2 : ℚ) (B : Cell (Fin 1)) : RatInterval :=
  (((RatInterval.ofRat ((19/50 : ℚ)^2/2)).mul
    (sinCell ((RatInterval.ofRat 2).mul (B 0)))).add
    ((RatInterval.ofRat q).mul (squareCell (sinCell (B 0))))).add (RatInterval.ofRat d2)

def switchLinearCell (b d1 : ℚ) (B : Cell (Fin 1)) : RatInterval :=
  ((RatInterval.ofRat b).mul (sinCell (B 0))).add (RatInterval.ofRat d1)

def switchDirectUpperQ (p q b d2 d1 : ℚ) (B : Cell (Fin 1)) : ℚ :=
  ((RatInterval.ofRat p).mul (B 0)).hi+
    maximumQ (switchQuadraticCell q d2 B).hi (switchLinearCell b d1 B).hi

theorem switch_quadratic_mem (q d2 : ℚ) {B : Cell (Fin 1)} {t : ℝ} (ht : (B 0).Mem t) :
    (switchQuadraticCell q d2 B).Mem (switchQuadratic q d2 t) := by
  have hc : (RatInterval.ofRat ((19/50 : ℚ)^2/2)).Mem ((19/50 : ℝ)^2/2) := by
    convert RatInterval.ofRat_mem ((19/50 : ℚ)^2/2) using 1 <;> norm_num
  have htwice : ((RatInterval.ofRat 2).mul (B 0)).Mem (2*t) :=
    RatInterval.mul_mem (by simpa using RatInterval.ofRat_mem (2 : ℚ)) ht
  have hh := RatInterval.add_mem (RatInterval.add_mem
    (RatInterval.mul_mem hc (sinCell_mem htwice))
    (RatInterval.mul_mem (RatInterval.ofRat_mem q) (squareCell_mem (sinCell_mem ht))))
    (RatInterval.ofRat_mem d2)
  convert hh using 1
  · rfl
  · unfold switchQuadratic
    ring

theorem switch_linear_mem (b d1 : ℚ) {B : Cell (Fin 1)} {t : ℝ} (ht : (B 0).Mem t) :
    (switchLinearCell b d1 B).Mem (switchLinear b d1 t) :=
  RatInterval.add_mem (RatInterval.mul_mem (RatInterval.ofRat_mem b) (sinCell_mem ht))
    (RatInterval.ofRat_mem d1)

theorem switch_envelope_le_direct_upper (p q b d2 d1 : ℚ)
    {B : Cell (Fin 1)} {t : ℝ} (ht : (B 0).Mem t) :
    switchEnvelope p q b d2 d1 t ≤ (switchDirectUpperQ p q b d2 d1 B : ℝ) := by
  have hP := RatInterval.mul_mem (RatInterval.ofRat_mem p) ht
  have hA := switch_quadratic_mem q d2 ht
  have hL := switch_linear_mem b d1 ht
  have hm := (maximum_rational_enclosure hA.1 hA.2 hL.1 hL.2).2
  unfold switchEnvelope switchDirectUpperQ
  rw [Rat.cast_add]
  exact add_le_add hP.2 hm

theorem switch_upper_of_direct_certificate (p q b d2 d1 : ℚ) (B : Cell (Fin 1))
    (M : ℚ) (hbound : switchDirectUpperQ p q b d2 d1 B ≤ M) :
    ∀ t, (B 0).Mem t → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ (M : ℝ) := by
  intro t ht y hy
  exact (switchObjective_le_envelope _ _ _ _ _ _ hy).trans
    ((switch_envelope_le_direct_upper p q b d2 d1 ht).trans (by exact_mod_cast hbound))

end N11Formalization.SharedMomentFactorIntervalCertificate
#check @N11Formalization.SharedMomentFactorIntervalCertificate.face_upper_of_direct_certificate
#check @N11Formalization.SharedMomentFactorIntervalCertificate.switch_upper_of_direct_certificate
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_quadratic_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_linear_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_angle_linear_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_envelope_le_direct_upper
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.face_upper_of_direct_certificate
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.switch_quadratic_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.switch_linear_mem
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.switch_envelope_le_direct_upper
#print axioms N11Formalization.SharedMomentFactorIntervalCertificate.switch_upper_of_direct_certificate
