import N11Formalization.IntervalsHighLag

/-!
# DSH-TOPO-C1 — the missing interval brick: `arccos` at a rational point

Route (a) of the ten-boundary certificate needs one evaluator the tree does not have: an outward
rational bracket for `arccos` at a **rational** point.  Grep confirms `arccos`/`acos` occurs
nowhere in `N11Formalization` outside the `FlashTenBoundary*` C450 files, and `Interval/*` has
`arcsin` (`Interval/ArcsinBracket.lean`) but no `arccos`.

Construction is pure antitonicity, using only in-tree bricks:

* `N11Formalization.cosLoNLag_le_cos`, `N11Formalization.cos_le_cosHiNLag` — order-28 rational
  `cos` bounds at a rational point, valid for **all** `q` (`IntervalsHighLag.lean`);
* `Real.cos_le_cos_of_nonneg_of_le_pi`, `Real.cos_lt_cos_of_nonneg_of_le_pi` — `cos` antitone /
  strictly antitone on `[0,π]`.

`arccos` is antitone with values in `[0,π]`, so `cos hi ≤ q = cos (arccos q)` forces
`arccos q ≤ hi`, and `q ≤ cos lo` forces `lo ≤ arccos q`.  Both directions are proved by
contradiction against strict antitonicity, so no `arccos`-specific order lemma is needed.

**Scope label: module/standalone** (infrastructure brick, not root-integrated).  Negative control
in `DSHTenBoundaryAcosControl` (see NOTES §10.4).
-/

set_option autoImplicit false

namespace N11Formalization

/-- **`arccos` bracket from `cos` brackets.**  If the rational `cos` bounds sandwich `q` between
`cos lo` and `cos hi`, then `arccos q ∈ [lo, hi]`.  Both sides hold for **arbitrary** rationals
`lo hi` in `[0,π]`; the caller supplies the validated bracket, so the statement carries no
domain machinery beyond `lo, hi ∈ [0,π]` and `q ∈ [-1,1]`. -/
theorem arccos_bracket_of_cos {q lo hi : ℚ}
    (hlo0 : 0 ≤ (lo : ℝ)) (hloπ : (lo : ℝ) ≤ Real.pi)
    (hhi0 : 0 ≤ (hi : ℝ)) (hhiπ : (hi : ℝ) ≤ Real.pi)
    (hq : (q : ℝ) ∈ Set.Icc (-1) 1)
    (h1 : ((cosHiNLag hi : ℚ) : ℝ) ≤ (q : ℝ))
    (h2 : (q : ℝ) ≤ ((cosLoNLag lo : ℚ) : ℝ)) :
    Real.arccos (q : ℝ) ∈ Set.Icc (lo : ℝ) (hi : ℝ) := by
  have hcosq : Real.cos (Real.arccos (q : ℝ)) = (q : ℝ) := Real.cos_arccos hq.1 hq.2
  have ha0 : 0 ≤ Real.arccos (q : ℝ) := Real.arccos_nonneg (q : ℝ)
  have haπ : Real.arccos (q : ℝ) ≤ Real.pi := Real.arccos_le_pi (q : ℝ)
  -- upper side: `cos hi ≤ q`; lower side: `q ≤ cos lo`
  have hU : Real.cos (hi : ℝ) ≤ (q : ℝ) := le_trans (cos_le_cosHiNLag hi) h1
  have hL : (q : ℝ) ≤ Real.cos (lo : ℝ) := le_trans h2 (cosLoNLag_le_cos lo)
  constructor
  · -- `lo ≤ arccos q`: else strict antitonicity gives `cos lo < cos (arccos q) = q`
    by_contra hcon
    push Not at hcon
    have hstrict := Real.cos_lt_cos_of_nonneg_of_le_pi ha0 hloπ hcon
    rw [hcosq] at hstrict
    linarith
  · -- `arccos q ≤ hi`: else strict antitonicity gives `q = cos (arccos q) < cos hi`
    by_contra hcon
    push Not at hcon
    have hstrict := Real.cos_lt_cos_of_nonneg_of_le_pi hhi0 haπ hcon
    rw [hcosq] at hstrict
    linarith

/-- A validated bracket for `arccos` on a rational **interval**: if `q ∈ [qlo, qhi]` then
`arccos q ∈ [arccos qhi, arccos qlo]` (antitone).  Stated with explicit rational brackets so the
consumer never handles `arccos` of a non-rational. -/
theorem arccos_mem_of_mem {q qlo qhi blo bhi : ℚ}
    (hb0 : 0 ≤ (bhi : ℝ)) (hbπ : (bhi : ℝ) ≤ Real.pi)
    (hb0' : 0 ≤ (blo : ℝ)) (hbπ' : (blo : ℝ) ≤ Real.pi)
    (h1 : ((cosHiNLag bhi : ℚ) : ℝ) ≤ (qlo : ℝ))   -- cos bhi ≤ qlo
    (h2 : (qhi : ℝ) ≤ ((cosLoNLag blo : ℚ) : ℝ))   -- qhi ≤ cos blo
    {q : ℚ} (hqq : (q : ℝ) ∈ Set.Icc (qlo : ℝ) (qhi : ℝ))
    (hq1 : (q : ℝ) ∈ Set.Icc (-1) 1) :
    Real.arccos (q : ℝ) ∈ Set.Icc ((blo : ℝ)) ((bhi : ℝ)) := by
  exact arccos_bracket_of_cos hb0' hbπ' hb0 hbπ hq1
    (le_trans h1 hqq.1) (le_trans hqq.2 h2)

end N11Formalization

namespace N11Formalization

-- Negative control: the output bracket is *necessary*, not vacuous.

/-- `19/50 < cos 1` (so the point `1` is strictly below `arccos (19/50)`). -/
theorem lt_cos_one : (19 : ℝ) / 50 < Real.cos 1 := by
  have h : (19 : ℚ) / 50 < cosLoNLag 1 := by decide +kernel
  have h' : ((19 : ℚ) / 50 : ℝ) < ((cosLoNLag 1 : ℚ) : ℝ) := by exact_mod_cast h
  have h2 : ((cosLoNLag 1 : ℚ) : ℝ) ≤ Real.cos (1 : ℝ) := by simpa using cosLoNLag_le_cos 1
  linarith

/-- **Negative control.**  The bracket `[0,1]` for `arccos (19/50)` is genuinely too narrow: the
brick's output is not vacuous, and the instrument fails here for the right mathematical reason
(`arccos (19/50) ≈ 1.181 > 1`), not through a parser or elaboration failure. -/
theorem arccos_19_50_not_mem_zero_one :
    ¬ (Real.arccos ((19 : ℚ) / 50 : ℝ) ∈ Set.Icc (0 : ℝ) 1) := by
  intro hmem
  have hq1 : (-1 : ℝ) ≤ ((19 : ℚ) / 50 : ℝ) := by norm_num
  have hq2 : ((19 : ℚ) / 50 : ℝ) ≤ 1 := by norm_num
  rcases lt_or_eq_of_le hmem.2 with hlt | heq
  · have hstrict := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _)
      (by linarith [Real.pi_gt_three]) hlt
    rw [Real.cos_arccos hq1 hq2] at hstrict
    linarith [lt_cos_one]
  · have hcos := Real.cos_arccos hq1 hq2
    rw [heq] at hcos
    linarith [lt_cos_one, hcos]

end N11Formalization

#print axioms N11Formalization.arccos_bracket_of_cos
#print axioms N11Formalization.arccos_mem_of_mem
#print axioms N11Formalization.arccos_19_50_not_mem_zero_one
#check @N11Formalization.arccos_bracket_of_cos
#check @N11Formalization.arccos_mem_of_mem
#check @N11Formalization.arccos_19_50_not_mem_zero_one