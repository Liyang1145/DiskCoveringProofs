import N11Formalization.ActualClippedMeshVertices

/-! The open planar unit disk minus ANY finite set is path connected.
Uses the genuine unitBall homeomorphism and the proved rank>1 countable
complement theorem. This is a planar-disk statement, not the false claim
that a circle minus finitely many switch points stays connected. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualPuncturedDiskConnected
open ActualVoronoiIncidence

def OpenDisk : Set Point := Metric.ball (0 : Point) 1

theorem mem_openDisk {x : Point} : x ∈ OpenDisk ↔ ‖x‖ < 1 := by
  simp [OpenDisk,Metric.mem_ball,dist_zero_right]

theorem punctured_disk_pathConnected {S : Set Point} (hS : S.Finite) :
    IsPathConnected (OpenDisk \ S) := by
  let e : Point ≃ₜ Metric.ball (0 : Point) 1 := Homeomorph.unitBall
  let f : Point → Point := fun x => (e x).val
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hfinj : Function.Injective f := by
    intro x y he
    exact e.injective (Subtype.ext he)
  let T := f ⁻¹' S
  have hT : T.Finite := hS.preimage hfinj.injOn
  have hdim : 1 < Module.rank ℝ Point := by
    rw [← Module.finrank_eq_rank]
    have hd : Module.finrank ℝ Point = 2 := finrank_euclideanSpace_fin
    rw [hd]
    norm_num
  have hpath : IsPathConnected Tᶜ :=
    hT.countable.isPathConnected_compl_of_one_lt_rank hdim
  have himage : f '' Tᶜ = OpenDisk \ S := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(e x).property,hx⟩
    · intro hy
      let Y : Metric.ball (0 : Point) 1 := ⟨y,hy.1⟩
      have he : f (e.symm Y) = y := congrArg Subtype.val (e.apply_symm_apply Y)
      refine ⟨e.symm Y,?_,he⟩
      change f (e.symm Y) ∉ S
      rw [he]
      exact hy.2
  rw [← himage]
  exact hpath.image hf

theorem actual_punctured_disk_pathConnected {c : Fin 11 → Point}
    (hc : Function.Injective c) : IsPathConnected (OpenDisk \ ClippedVertices c) :=
  punctured_disk_pathConnected (clippedVertices_finite hc)

end N11Formalization.ActualPuncturedDiskConnected
#check @N11Formalization.ActualPuncturedDiskConnected.punctured_disk_pathConnected
#print axioms N11Formalization.ActualPuncturedDiskConnected.punctured_disk_pathConnected
#print axioms N11Formalization.ActualPuncturedDiskConnected.actual_punctured_disk_pathConnected
