import N11Formalization.FlashLocalFrobeniusSourceN
import N11Formalization.PinTangentGeometry

/-! Exact properties of the EXISTING source circumcenter formula. No face
table from the legacy SourceN module is used; only its frozen Cramer formula.
Noncollinearity is explicit in generic results and must be paid by consumers. -/
set_option autoImplicit false
namespace N11Formalization.CircumcenterGeometry
open N11Formalization PinTangentGeometry
noncomputable section

def triangleDet (A B C : Point) : ℝ := det (B-A) (C-A)

theorem circumcenter_rows (A B C : Point) (hdet : triangleDet A B C ≠ 0) :
    inner ℝ (circumcenter A B C) (B-A) = (‖B‖^2-‖A‖^2)/2 ∧
    inner ℝ (circumcenter A B C) (C-A) = (‖C‖^2-‖A‖^2)/2 := by
  change det (B-A) (C-A) ≠ 0 at hdet
  unfold det at hdet
  have hden : (C-A) 1 * (B-A) 0 - (B-A) 1 * (C-A) 0 ≠ 0 := by
    convert hdet using 1 <;> ring
  constructor <;> rw [inner_coords]
  all_goals
    simp only [circumcenter, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hdet, hden]
    ring

theorem equidistant_rows (A B C U : Point)
    (hAB : ‖U-A‖ = ‖U-B‖) (hAC : ‖U-A‖ = ‖U-C‖) :
    inner ℝ U (B-A) = (‖B‖^2-‖A‖^2)/2 ∧
    inner ℝ U (C-A) = (‖C‖^2-‖A‖^2)/2 := by
  have hab : ‖U-A‖^2 = ‖U-B‖^2 := congrArg (fun r : ℝ => r^2) hAB
  have hac : ‖U-A‖^2 = ‖U-C‖^2 := congrArg (fun r : ℝ => r^2) hAC
  rw [norm_sub_sq_real, norm_sub_sq_real] at hab hac
  constructor <;> rw [inner_sub_right] <;> linarith

/-- The existing source formula is the unique point equidistant to the triple. -/
theorem circumcenter_eq_of_equidistant (A B C U : Point)
    (hdet : triangleDet A B C ≠ 0)
    (hAB : ‖U-A‖ = ‖U-B‖) (hAC : ‖U-A‖ = ‖U-C‖) :
    circumcenter A B C = U := by
  obtain ⟨hzB,hzC⟩ := circumcenter_rows A B C hdet
  obtain ⟨huB,huC⟩ := equidistant_rows A B C U hAB hAC
  have hb : inner ℝ (B-A) (circumcenter A B C) = inner ℝ (B-A) U := by
    rw [real_inner_comm, hzB, real_inner_comm U (B-A), huB]
  have hc : inner ℝ (C-A) (circumcenter A B C) = inner ℝ (C-A) U := by
    rw [real_inner_comm, hzC, real_inner_comm U (C-A), huC]
  apply tangent_unique (P := -(B-A)) (Q := -(C-A)) (U := 0)
  · simpa only [sub_neg_eq_add, zero_add, triangleDet] using hdet
  · simpa only [sub_neg_eq_add, zero_add] using hb
  · simpa only [sub_neg_eq_add, zero_add] using hc

theorem circumcenter_equidistant (A B C : Point) (hdet : triangleDet A B C ≠ 0) :
    ‖circumcenter A B C-A‖ = ‖circumcenter A B C-B‖ ∧
    ‖circumcenter A B C-A‖ = ‖circumcenter A B C-C‖ := by
  obtain ⟨hb,hc⟩ := circumcenter_rows A B C hdet
  have hab : ‖circumcenter A B C-A‖^2 = ‖circumcenter A B C-B‖^2 := by
    rw [inner_sub_right] at hb
    rw [norm_sub_sq_real, norm_sub_sq_real]
    linarith
  have hac : ‖circumcenter A B C-A‖^2 = ‖circumcenter A B C-C‖^2 := by
    rw [inner_sub_right] at hc
    rw [norm_sub_sq_real, norm_sub_sq_real]
    linarith
  constructor <;> nlinarith [norm_nonneg (circumcenter A B C-A),
    norm_nonneg (circumcenter A B C-B), norm_nonneg (circumcenter A B C-C)]

def radius (A B C : Point) : ℝ := ‖circumcenter A B C-A‖

theorem triangleDet_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C : E → Point} {x : E}
    (hA : ContDiffAt ℝ 1 A x) (hB : ContDiffAt ℝ 1 B x) (hC : ContDiffAt ℝ 1 C x) :
    ContDiffAt ℝ 1 (fun y => triangleDet (A y) (B y) (C y)) x := by
  have hv := hB.sub hA
  have hw := hC.sub hA
  exact (((contDiffAt_piLp 2).mp hv 0).mul ((contDiffAt_piLp 2).mp hw 1)).sub
    (((contDiffAt_piLp 2).mp hv 1).mul ((contDiffAt_piLp 2).mp hw 0))

/-- C1 for genuinely moving triples, no constant-centre derivative shortcut. -/
theorem circumcenter_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B C : E → Point} {x : E}
    (hA : ContDiffAt ℝ 1 A x) (hB : ContDiffAt ℝ 1 B x) (hC : ContDiffAt ℝ 1 C x)
    (hdet : triangleDet (A x) (B x) (C x) ≠ 0) :
    ContDiffAt ℝ 1 (fun y => circumcenter (A y) (B y) (C y)) x := by
  have hv := hB.sub hA
  have hw := hC.sub hA
  have v0 := (contDiffAt_piLp 2).mp hv 0
  have v1 := (contDiffAt_piLp 2).mp hv 1
  have w0 := (contDiffAt_piLp 2).mp hw 0
  have w1 := (contDiffAt_piLp 2).mp hw 1
  have hd := ((hB.norm_sq ℝ).sub (hA.norm_sq ℝ)).div_const 2
  have he := ((hC.norm_sq ℝ).sub (hA.norm_sq ℝ)).div_const 2
  have hD := (v0.mul w1).sub (v1.mul w0)
  rw [contDiffAt_piLp 2]
  intro i
  fin_cases i
  · exact ((hd.mul w1).sub (he.mul v1)).div hD hdet
  · exact ((v0.mul he).sub (w0.mul hd)).div hD hdet

end
end N11Formalization.CircumcenterGeometry
#check @N11Formalization.CircumcenterGeometry.circumcenter_eq_of_equidistant
#check @N11Formalization.CircumcenterGeometry.circumcenter_smooth
#print axioms N11Formalization.CircumcenterGeometry.circumcenter_eq_of_equidistant
