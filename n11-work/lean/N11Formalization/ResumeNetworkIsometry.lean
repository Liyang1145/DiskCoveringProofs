import N11Formalization.ResumeNetwork

/-! Coordinate normalization is harmless for the actual network oracle. The same
map acts on anchors, centers and face witnesses, so all 51 constraints are retained. -/
namespace N11Formalization.ResumeNetworkIsometry
open ResumeNetwork

 theorem feasible_map (f : Point → Point)
    (hf : ∀ x y, dist (f x) (f y) = dist x y)
    (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ) :
    Feasible (f ∘ U) (f ∘ C) (f ∘ Z) r ↔ Feasible U C Z r := by
  have he : ∀ e, edgeLength (f ∘ U) (f ∘ C) (f ∘ Z) e = edgeLength U C Z e := by
    intro e
    rcases e with ⟨i, side⟩ | ⟨k, v⟩ <;> simp [edgeLength, Function.comp_def, hf]
  simp only [Feasible, he]

 theorem feasibleSquares_eq (f : Point ≃ Point)
    (hf : ∀ x y, dist (f x) (f y) = dist x y) (U : Fin 9 → Point) :
    feasibleSquares (f ∘ U) = feasibleSquares U := by
  ext q
  constructor
  · rintro ⟨C, Z, r, hr, hq⟩
    refine ⟨f.symm ∘ C, f.symm ∘ Z, r, ?_, hq⟩
    apply (feasible_map f hf U _ _ r).mp
    simpa [Function.comp_def] using hr
  · rintro ⟨C, Z, r, hr, hq⟩
    exact ⟨f ∘ C, f ∘ Z, r, (feasible_map f hf U C Z r).mpr hr, hq⟩

/-- This also applies to reflection/reversal and translation, not only rotation. -/
 theorem oracle_isometry (f : Point ≃ Point)
    (hf : ∀ x y, dist (f x) (f y) = dist x y) (U : Fin 9 → Point) :
    V2 (f ∘ U) = V2 U := by
  unfold V2
  rw [feasibleSquares_eq f hf U]

#print axioms oracle_isometry
end N11Formalization.ResumeNetworkIsometry
