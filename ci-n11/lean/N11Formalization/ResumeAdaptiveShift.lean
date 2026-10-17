import N11Formalization.ResumeDirichletShift
import N11Formalization.ResumeAdaptiveRoot
import N11Formalization.ResumeStressComparison

noncomputable section
namespace N11Formalization.ResumeAdaptiveShift
open ResumeNetwork ResumeDirichlet ResumeDirichletShift ResumeAdaptiveRoot ResumeStressComparison

/-- Base flux is linear in weights at fixed root coordinates. No claim about
linearity of the displaced response matrix is involved. -/
theorem baseCross_add (α δ : Edge → ℝ) (U V : Fin 9 → Point) (C Z : Fin 11 → Point) :
    baseCross (fun e => α e + δ e) U C Z V =
      baseCross α U C Z V + baseCross δ U C Z V := by
  simp only [baseCross, add_mul, Finset.sum_add_distrib]

/-- Actual 51-edge oracle lower bound under a supported, balanced stress
perturbation. All geometric source identities are explicit; no response-matrix
identification or displaced-minimizer assumption occurs in this theorem. -/
theorem oracle_shift_lower {α δ : Edge → ℝ} {U V : Fin 9 → Point}
    {C Z : Fin 11 → Point} {R ε : ℝ}
    (hα : ∀ e, 0 ≤ α e) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hδ : ∀ e, |δ e| ≤ ε * α e)
    (hs : ∑ e, α e = 1) (hds : ∑ e, δ e = 0)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hd : ∀ v : Free, ∑ e, (δ e * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = R ^ 2)
    (hU : ∀ i, ‖(U+V) i‖ ≤ 1) :
    2 * (baseCross α U C Z V + baseCross δ U C Z V) +
      (1-ε) * dirichletEnergy α V ≤ V2 (U+V) - R^2 := by
  have hpos : ∀ e, 0 ≤ α e + δ e := by
    intro e
    have hh := (abs_le.mp (hδ e)).1
    have hn := mul_nonneg (show 0 ≤ 1-ε by linarith) (hα e)
    nlinarith
  have hsupport : ∀ e, α e = 0 → δ e = 0 := by
    intro e he
    have hh := hδ e
    rw [he, mul_zero] at hh
    exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  have hroot := adaptive_root_value hpos hs hds ha hd hsupport hl
  have hbase := dirichlet_eq_of_node_balance C Z hpos (balance_add ha hd)
  have hshift := dirichlet_shift hpos (balance_add ha hd) V
  rw [← hbase, hroot, baseCross_add] at hshift
  have hcmp := (dirichlet_of_abs_perturbation hα hε hε1 hδ V).1
  have hsum : ∑ e, (α e + δ e) = 1 := by
    rw [Finset.sum_add_distrib, hs, hds, add_zero]
  have horacle := dirichlet_le_oracle hU hpos hsum
  rw [hshift] at horacle
  linarith

/-- Only the boundary diagonal bounds the variational loss. This upper bound
uses a zero-free trial; it is NOT used as a lower bound for minimized energy. -/
theorem oracle_shift_diagonal_lower {α δ : Edge → ℝ} {U V : Fin 9 → Point}
    {C Z : Fin 11 → Point} {R ε d q : ℝ}
    (hα : ∀ e, 0 ≤ α e) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hδ : ∀ e, |δ e| ≤ ε * α e)
    (hs : ∑ e, α e = 1) (hds : ∑ e, δ e = 0)
    (ha : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C Z e = 0)
    (hd : ∀ v : Free, ∑ e, (δ e * incidence e v) • edgeVector U C Z e = 0)
    (hl : ∀ e, α e ≠ 0 → edgeLength U C Z e ^ 2 = R ^ 2)
    (hU : ∀ i, ‖(U+V) i‖ ≤ 1)
    (hdiag : ∀ j, anchorWeight α j ≤ d) (hd0 : 0 ≤ d)
    (hV : ∑ j, ‖V j‖^2 ≤ q^2) :
    2 * (baseCross α U C Z V + baseCross δ U C Z V) +
      dirichletEnergy α V - ε*d*q^2 ≤ V2 (U+V) - R^2 := by
  have hlo := oracle_shift_lower hα hε hε1 hδ hs hds ha hd hl hU
  have hb := (dirichlet_le_diagonal hα hdiag V).trans
    (mul_le_mul_of_nonneg_left hV hd0)
  have hm := mul_le_mul_of_nonneg_left hb hε
  nlinarith

#check @oracle_shift_diagonal_lower
#print axioms oracle_shift_lower
#print axioms oracle_shift_diagonal_lower
end N11Formalization.ResumeAdaptiveShift
