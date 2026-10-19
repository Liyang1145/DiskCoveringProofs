import N11Formalization.TCSystem

noncomputable section
namespace N11Formalization

/-- Angles of the *unit-circle boundary anchors*, not radial center angles
and not the interior face witnesses called Uvec in TCSystem. -/
def rawAnchorAngle (u : Fin 12 → ℝ) (k : Fin 9) : ℝ :=
  thetaOf (angleVec u) k + angleVec u k

theorem arcEnd_eq_rawAnchorAngle (u : Fin 12 → ℝ) (k : Fin 9) :
    arcEnd u k = !₂[Real.cos (rawAnchorAngle u k), Real.sin (rawAnchorAngle u k)] := rfl

/-- The chart widths for consecutive boundary anchors are 2*a_(k+1).
The center-angle widths a_k+a_(k+1) do not describe this anchor network. -/
theorem rawAnchorAngle_step (u : Fin 12 → ℝ) (k : Fin 8) :
    rawAnchorAngle u ⟨k.val+1, by omega⟩ - rawAnchorAngle u ⟨k.val, by omega⟩ =
      2 * angleVec u ⟨k.val+1, by omega⟩ := by
  unfold rawAnchorAngle
  have h := thetaOf_rec (angleVec u) k
  linarith

theorem rawAnchorAngle_wrap (u : Fin 12 → ℝ) :
    rawAnchorAngle u 0 + 2 * Real.pi - rawAnchorAngle u 8 = 2 * angleVec u 0 := by
  simp [rawAnchorAngle, thetaOf, angleVec]
  ring

/-- Exact diagnostic for the erroneous center-angle chart. -/
theorem anchor_center_gap_difference (u : Fin 12 → ℝ) (k : Fin 8) :
    (rawAnchorAngle u ⟨k.val+1, by omega⟩ - rawAnchorAngle u ⟨k.val, by omega⟩) -
      (angleVec u ⟨k.val, by omega⟩ + angleVec u ⟨k.val+1, by omega⟩) =
      angleVec u ⟨k.val+1, by omega⟩ - angleVec u ⟨k.val, by omega⟩ := by
  rw [rawAnchorAngle_step]
  ring

#print axioms rawAnchorAngle_step
#print axioms rawAnchorAngle_wrap
#print axioms anchor_center_gap_difference
end N11Formalization
