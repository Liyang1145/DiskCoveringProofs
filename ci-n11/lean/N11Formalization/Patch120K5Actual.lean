import N11Formalization.Patch120K5Consumer
import N11Formalization.FlashLeafRootChart
import N11Formalization.ResumeRelativeScalar

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace N11Formalization.Patch120K5Actual
open N11Formalization Patch120K5 Patch120K5Consumer
open FlashLeafSplit ResumeGlobal FlashLeafRootChart

noncomputable def L : ℝ := 2 * Real.arcsin (19 / 50)
noncomputable def D : ℝ := 9 * L - 2 * Real.pi

-- Lifted source-root anchor displacement about canonical anchor 6.
noncomputable def delta (u : Fin 12 → ℝ) (i : Fin 9) : ℝ :=
  match i.val with
  | 0 => 2*angleVec u 0 + 2*angleVec u 1 + 2*angleVec u 2 - 2*Real.pi
  | 1 => 2*angleVec u 0 + 2*angleVec u 1 + 2*angleVec u 2 + 2*angleVec u 3 - 2*Real.pi
  | 2 => -(2*angleVec u 0 + 2*angleVec u 1 + 2*angleVec u 2 + 2*angleVec u 3)
  | 3 => -(2*angleVec u 0 + 2*angleVec u 1 + 2*angleVec u 2)
  | 4 => -(2*angleVec u 0 + 2*angleVec u 1)
  | 5 => -(2*angleVec u 0)
  | 7 => 2*angleVec u 0
  | 8 => 2*angleVec u 0 + 2*angleVec u 1
  | _ => 0

noncomputable def h (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  ((i.val : ℝ) - 6) * L - D * (tlift y (f9 i) - tlift y 6) - delta u i

noncomputable def q2 (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) : ℝ :=
  (h u y 0)^2 + (h u y 1)^2 + (h u y 2)^2 + (h u y 3)^2 +
    (h u y 4)^2 + (h u y 5)^2 + (h u y 7)^2 + (h u y 8)^2

noncomputable def q (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) : ℝ := Real.sqrt (q2 u y)

theorem pi_mem : (PILO : ℝ) ≤ Real.pi ∧ Real.pi ≤ (PIHI : ℝ) := by
  exact ⟨RatInterval.piLo_lt_pi.le, RatInterval.pi_lt_piHi.le⟩

theorem q2_le_4935 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u)
    {y : Fin 9 → ℝ} (hc : Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4935) (tlift y)) :
    q2 u y ≤ (729/50000 : ℝ)^2 := by
  have hs := k5_q_of_cell_4935_of_inCertBox hu pi_mem hc
  norm_num [q2, h, delta, L, D]
  norm_num at hs
  convert hs using 1 <;> ring

theorem q2_le_4957 {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u)
    {y : Fin 9 → ℝ} (hc : Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4957) (tlift y)) :
    q2 u y ≤ (729/50000 : ℝ)^2 := by
  have hs := k5_q_of_cell_4957_of_inCertBox hu pi_mem hc
  norm_num [q2, h, delta, L, D]
  norm_num at hs
  convert hs using 1 <;> ring

theorem q_le {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u)
    {y : Fin 9 → ℝ}
    (hc : Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4935) (tlift y) ∨
      Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4957) (tlift y)) :
    q u y ≤ (729/50000 : ℝ) := by
  unfold q
  rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 729/50000)]
  rcases hc with hc | hc
  · exact q2_le_4935 hu hc
  · exact q2_le_4957 hu hc

theorem local_gain_of_geometric_bound {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u)
    {y : Fin 9 → ℝ}
    (hc : Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4935) (tlift y) ∨
      Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4957) (tlift y))
    {E p : ℝ}
    (hg : (9/10000 : ℝ)*(q u y)^2 + 734*p^2 - (179/5000)*(q u y)^3
      - ((2/25)/3)*(q u y)^4 - 1468*((99/200)*(2/25) + 429/50000)*p*(q u y)^2 ≤ E) :
    (q u y)^2/100000 ≤ E :=
  ResumeRelativeScalar.local_gain (Real.sqrt_nonneg _) (q_le hu hc) hg

-- Negative control: reversed pin orientation does not satisfy this hull.
def wrongMember (lo hi : Fin 9 → ℚ) (d : Fin 10 → Fin 10 → ℚ) : Prop :=
  ∀ i : Fin 9, i ≠ 6 → lo i ≤ -d 6 (f9 i) ∧ d (f9 i) 6 ≤ hi i

theorem wrong_orientation_rejected : ¬ wrongMember k5lo k5hi db4935 := by
  unfold wrongMember
  decide +kernel

theorem terminal4935 : (DBMSourceTree.data (4935 : Fin 5011)).terminal = true := by decide +kernel
theorem terminal4957 : (DBMSourceTree.data (4957 : Fin 5011)).terminal = true := by decide +kernel

theorem delta_eq_root_anchor (u : Fin 12 → ℝ) {LL DD : ℝ} (hD : DD ≠ 0) (i : Fin 9) :
    delta u i = anchorAngle LL DD (chartY u LL DD) i.val -
      anchorAngle LL DD (chartY u LL DD) 6 := by
  have step (k : Fin 9) := anchor_succ_sub LL DD (chartY u LL DD) k
  have s0 := step 0; have s1 := step 1; have s2 := step 2; have s3 := step 3
  have s4 := step 4; have s5 := step 5; have s6 := step 6; have s7 := step 7
  rw [width_chartY u hD] at s0 s1 s2 s3 s4 s5 s6 s7
  norm_num [shift3, angleVec] at s0 s1 s2 s3 s4 s5 s6 s7
  fin_cases i <;> simp [delta, angleVec] <;> linarith

theorem anchor_eq_tlift (y : Fin 9 → ℝ) (i : Fin 9) :
    anchorAngle L D y i.val = (i.val : ℝ) * L - D * tlift y (f9 i) := rfl

theorem h_eq_actual_perturbation (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) (i : Fin 9) :
    h u y i = (anchorAngle L D y i.val - anchorAngle L D y 6) -
      (anchorAngle L D (chartY u L D) i.val - anchorAngle L D (chartY u L D) 6) := by
  have hD : D ≠ 0 := (show 0 < D from FlashLeafRootChart.D_pos).ne'
  have h6 : anchorAngle L D y 6 = (6 : ℝ)*L - D*tlift y 6 := by
    simpa [f9] using anchor_eq_tlift y (6 : Fin 9)
  rw [← delta_eq_root_anchor u hD i, anchor_eq_tlift y i, h6]
  norm_num [h]
  ring

theorem q2_eq_pinned_sum (u : Fin 12 → ℝ) (y : Fin 9 → ℝ) :
    q2 u y = ∑ i ∈ Finset.univ.filter (fun i : Fin 9 => i ≠ 6), (h u y i)^2 := by
  have hf : Finset.univ.filter (fun i : Fin 9 => i ≠ 6) = {0,1,2,3,4,5,7,8} := by decide
  rw [hf]
  norm_num [q2, Finset.sum_insert, Finset.sum_singleton, Fin.ext_iff]
  <;> ring

theorem actual_pinned_norm_le {u : Fin 12 → ℝ} (hu : RootRangeBoxFull.InCertBox u)
    {y : Fin 9 → ℝ}
    (hc : Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4935) (tlift y) ∨
      Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 4957) (tlift y)) :
    Real.sqrt (∑ i ∈ Finset.univ.filter (fun i : Fin 9 => i ≠ 6),
      ((anchorAngle L D y i.val - anchorAngle L D y 6) -
        (anchorAngle L D (chartY u L D) i.val - anchorAngle L D (chartY u L D) 6))^2)
      ≤ (729/50000 : ℝ) := by
  have hs : (∑ i ∈ Finset.univ.filter (fun i : Fin 9 => i ≠ 6),
      ((anchorAngle L D y i.val - anchorAngle L D y 6) -
        (anchorAngle L D (chartY u L D) i.val - anchorAngle L D (chartY u L D) 6))^2)
      = q2 u y := by
    rw [q2_eq_pinned_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [h_eq_actual_perturbation]
  rw [hs]
  exact q_le hu hc

end N11Formalization.Patch120K5Actual
#check @N11Formalization.Patch120K5Actual.q_le
#check @N11Formalization.Patch120K5Actual.local_gain_of_geometric_bound
#print axioms N11Formalization.Patch120K5Actual.q_le
#print axioms N11Formalization.Patch120K5Actual.local_gain_of_geometric_bound
#print axioms N11Formalization.Patch120K5Actual.wrong_orientation_rejected

#check @N11Formalization.Patch120K5Actual.h_eq_actual_perturbation
#print axioms N11Formalization.Patch120K5Actual.h_eq_actual_perturbation
#print axioms N11Formalization.Patch120K5Actual.q2_eq_pinned_sum

#check @N11Formalization.Patch120K5Actual.actual_pinned_norm_le
#print axioms N11Formalization.Patch120K5Actual.actual_pinned_norm_le
#print N11Formalization.Patch120K5Actual.L
#print N11Formalization.Patch120K5Actual.D
#print N11Formalization.Patch120K5Actual.q
#print N11Formalization.Patch120K5Actual.q2
#print N11Formalization.Patch120K5Actual.h
#print N11Formalization.Patch120K5Actual.delta
