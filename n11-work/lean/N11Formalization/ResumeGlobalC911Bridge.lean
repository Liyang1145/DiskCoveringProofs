import N11Formalization.ResumeGlobalC911Int

/-! C911 ℤ→ℝ cast bridge: α = aZ/A, H = HZ/D_j; coeff H = bZ/D_j (bZ defined from HZ);
integer bal_all ⇒ real hbal; hα, hs, hH (row sums 1); instantiate harmonic_energy_le_oracle. -/
namespace N11Formalization.ResumeGlobal.C911Int
open N11Formalization.ResumeNetwork N11Formalization.ResumeDirichlet

def L : ℤ := 6322732090178144674316372123670830585772150341828669606347484418
def M : Fin 9 → ℤ := ![1, 1, 1, 1, 1, 11, 1, 22, 2]

set_option maxRecDepth 100000 in
theorem DM : ∀ j, D j * M j = L := by decide +kernel
set_option maxRecDepth 100000 in
theorem D_pos : ∀ j, 0 < D j := by decide +kernel
set_option maxRecDepth 100000 in
theorem a_pos : ∀ e, 0 < aZ e := by decide +kernel
set_option maxRecDepth 100000 in
theorem a_sum : ∑ e, aZ e = A := by decide +kernel
set_option maxRecDepth 100000 in
theorem H_row : ∀ v, ∑ j, HZ v j * M j = L := by decide +kernel

noncomputable def αR (e : Edge) : ℝ := (aZ e : ℝ) / (A : ℝ)
noncomputable def HR (v : Free) (j : Fin 9) : ℝ := (HZ v j : ℝ) / (D j : ℝ)

theorem A_ne : (A : ℝ) ≠ 0 := by unfold A; norm_num
theorem L_ne : (L : ℝ) ≠ 0 := by unfold L; norm_num

theorem inc_cast (e : Edge) (v : Free) : ((incZ e v : ℤ) : ℝ) = incidence e v := by
  rcases e with ⟨i, s⟩ | ⟨f, j⟩ <;> simp [incZ, incidence] <;> split_ifs <;> simp

theorem coeff_eq (e : Edge) (j : Fin 9) :
    ResumeHarmonic.coeff HR e j = (bZ e j : ℝ) / (D j : ℝ) := by
  have hD : (D j : ℝ) ≠ 0 := by exact_mod_cast (D_pos j).ne'
  rcases e with ⟨i, side⟩ | ⟨f, k⟩
  · simp only [ResumeHarmonic.coeff, bZ, HR]
    split_ifs
    all_goals (push_cast; field_simp)
    all_goals ring
  · simp only [ResumeHarmonic.coeff, bZ, HR]
    push_cast
    field_simp

theorem hα : ∀ e, 0 ≤ αR e := fun e =>
  div_nonneg (by exact_mod_cast (a_pos e).le) (by unfold A; norm_num)

theorem hs : ∑ e, αR e = 1 := by
  simp only [αR]
  rw [← Finset.sum_div]
  have h : (∑ e, (aZ e : ℝ)) = A := by exact_mod_cast a_sum
  rw [h, div_self A_ne]

theorem hbal : ∀ v j, ∑ e, (αR e * incidence e v) * ResumeHarmonic.coeff HR e j = 0 := by
  intro v j
  have hc : ((∑ e, aZ e * incZ e v * bZ e j : ℤ) : ℝ) = 0 := by exact_mod_cast bal_all v j
  push_cast at hc
  have hr : ∀ e, (αR e * incidence e v) * ResumeHarmonic.coeff HR e j =
      ((aZ e : ℝ) * (incZ e v : ℝ) * (bZ e j : ℝ)) / ((A : ℝ) * (D j : ℝ)) := by
    intro e; rw [coeff_eq, ← inc_cast, αR]; ring
  simp_rw [hr, ← Finset.sum_div, hc, zero_div]

theorem HR_eq (v : Free) (j : Fin 9) : HR v j = (HZ v j : ℝ) * (M j : ℝ) / (L : ℝ) := by
  have hD : (D j : ℝ) ≠ 0 := by exact_mod_cast (D_pos j).ne'
  have h : (D j : ℝ) * M j = L := by exact_mod_cast DM j
  unfold HR
  rw [div_eq_div_iff hD L_ne, ← h]
  ring

/-- Row sums of the harmonic extension are 1 (needed for Gram row 0). -/
theorem hH : ∀ v, ∑ j, HR v j = 1 := by
  intro v
  simp_rw [HR_eq, ← Finset.sum_div]
  have h : (∑ j, (HZ v j : ℝ) * (M j : ℝ)) = L := by exact_mod_cast H_row v
  rw [h, div_self L_ne]

/-- Actual consumer instance: C911 lower bound for every unit-bounded anchor tuple. -/
theorem c911_energy_le_oracle (U : Fin 9 → Point) (hU : ∀ j, ‖U j‖ ≤ 1) :
    (∑ e, αR e * ‖∑ j, ResumeHarmonic.coeff HR e j • U j‖ ^ 2) ≤ V2 U :=
  ResumeHarmonic.harmonic_energy_le_oracle αR HR hα hs hbal U hU

end N11Formalization.ResumeGlobal.C911Int

#check @N11Formalization.ResumeGlobal.C911Int.c911_energy_le_oracle
#print axioms N11Formalization.ResumeGlobal.C911Int.c911_energy_le_oracle
#print axioms N11Formalization.ResumeGlobal.C911Int.hH
