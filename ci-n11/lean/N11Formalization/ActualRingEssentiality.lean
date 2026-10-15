import N11Formalization.ActualHubEssentiality

/-! Every ring disk is essential on the ACTUAL circle, not just in a
measure ledger. This is derived from the eight-disk arc obstruction;
no ownership connectedness or order premise is introduced. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualRingEssentiality
open DSHTopologyInterior ActualHubEssentiality

def PrivateCirclePoint (c : Fin 11 → Point) (r : ℝ) (j : Fin 11) : Prop :=
  ∃ x : Point, ‖x‖ = 1 ∧ dist x (c j) ≤ r ∧
    ∀ i : Fin 11, i ≠ j → r < dist x (c i)

theorem private_circle_point {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) (j : Fin 9) :
    PrivateCirclePoint c r ⟨j.val, by omega⟩ := by
  classical
  let J : Fin 11 := ⟨j.val, by omega⟩
  by_contra hprivate
  have hcover_other (x : Point) (hx : ‖x‖ = 1) :
      ∃ i : Fin 11, i ≠ J ∧ dist x (c i) ≤ r := by
    by_contra hnone
    obtain ⟨i, hi⟩ := hc x (mem_unitDisk.mpr hx.le)
    have heq : i = J := by
      by_contra hne
      exact hnone ⟨i, hne, hi⟩
    apply hprivate
    refine ⟨x, hx, ?_, ?_⟩
    · simpa only [heq] using hi
    · intro k hk
      exact lt_of_not_ge (fun hd => hnone ⟨k, hk, hd⟩)
  let d : Fin 8 → Point := fun k => c ⟨(j.succAbove k).val, by omega⟩
  apply not_eight_ball_covers_circle_of_lt_R0 d (Covers.nonneg hc) hr
  intro x hx
  obtain ⟨i, hi, hd⟩ := hcover_other x hx
  have hir : i.val < 9 := (hR i).mp ⟨x, hx, hd⟩
  let i9 : Fin 9 := ⟨i.val, hir⟩
  have hij : i9 ≠ j := by
    intro he
    apply hi
    exact Fin.ext (congrArg (fun q : Fin 9 => q.val) he)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
  refine ⟨k, ?_⟩
  have he : (⟨(j.succAbove k).val, by omega⟩ : Fin 11) = i := by
    exact Fin.ext (congrArg (fun q : Fin 9 => q.val) hk)
  change dist x (c ⟨(j.succAbove k).val, by omega⟩) ≤ r
  rwa [he]

theorem ring_privatePoint {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r)
    {j : Fin 11} (hj : j.val < 9) : PrivatePoint c r j := by
  have hp := private_circle_point hc hr hR (⟨j.val, hj⟩ : Fin 9)
  obtain ⟨x, hx, hd, ho⟩ := hp
  exact ⟨x, mem_unitDisk.mpr hx.le, hd, ho⟩

/-- All eleven sites are irredundant and distinct; no genericity needed. -/
theorem all_private_and_injective (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) (hr : r < 19/50) (hR : RingLabels c r) :
    (∀ j : Fin 11, PrivatePoint c r j) ∧ Function.Injective c := by
  have hp (j : Fin 11) : PrivatePoint c r j := by
    by_cases hj : j.val < 9
    · exact ring_privatePoint hc hr hR hj
    · exact private_point_of_atom h450 hr.le hc hR (show 9 ≤ j.val by omega)
  refine ⟨hp, ?_⟩
  intro i j heq
  by_contra hij
  exact private_point_ne (hp i) hij heq

end N11Formalization.ActualRingEssentiality
#check @N11Formalization.ActualRingEssentiality.private_circle_point
#check @N11Formalization.ActualRingEssentiality.all_private_and_injective
#print axioms N11Formalization.ActualRingEssentiality.private_circle_point
#print axioms N11Formalization.ActualRingEssentiality.all_private_and_injective
