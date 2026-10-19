import Class33Core.SectorKernel
namespace Class33Core.SectorKernel
theorem splitBox_spec {B BL BR : Box} {d : Nat} {t : Rat} (h : splitBox B d t = some (BL, BR)) :
    (d = 0 ∧ B.a0 ≤ t ∧ t ≤ B.a1 ∧ BL = { B with a1 := t } ∧ BR = { B with a0 := t }) ∨
    (d = 1 ∧ B.u0 ≤ t ∧ t ≤ B.u1 ∧ BL = { B with u1 := t } ∧ BR = { B with u0 := t }) ∨
    (d = 2 ∧ B.v0 ≤ t ∧ t ≤ B.v1 ∧ BL = { B with v1 := t } ∧ BR = { B with v0 := t }) := by
  unfold splitBox at h
  split at h
  · split at h
    · rename_i hc; cases h; exact Or.inl ⟨rfl, hc.1, hc.2, rfl, rfl⟩
    · cases h
  · split at h
    · rename_i hc; cases h; exact Or.inr (Or.inl ⟨rfl, hc.1, hc.2, rfl, rfl⟩)
    · cases h
  · split at h
    · rename_i hc; cases h; exact Or.inr (Or.inr ⟨rfl, hc.1, hc.2, rfl, rfl⟩)
    · cases h
  · cases h
end Class33Core.SectorKernel
