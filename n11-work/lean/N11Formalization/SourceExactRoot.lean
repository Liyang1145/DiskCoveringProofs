import N11Formalization.GridBridge
import N11Formalization.FlashAttainmentRstarConsumer
import N11Formalization.ResumeNewtonData

/-! Freeze the exact source constant after proved root existence. This is not
an optimality theorem. No research hypotheses are added or assumed. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SourceExactRoot
open N11Formalization

/-- The source box predicate, including the actual TC/KKT expression. -/
def RootPredicate (u : Fin 12 → ℝ) : Prop :=
  (∀ i : Fin 12, (boxLoCert i : ℝ) ≤ u i ∧ u i ≤ (boxHiCert i : ℝ)) ∧
    TCSystem u = 0

/-- The proved GridBridge root pays the entire existence-and-uniqueness premise. -/
theorem exists_unique : ∃! u : Fin 12 → ℝ, RootPredicate u := by
  obtain ⟨S, hs, hl, hh, _, _, _⟩ := GridBridge.nd_box_final
  have h := S.exists_unique
  rw [hs, hl, hh] at h
  exact h

/-- System, source box, and radius index are fixed by construction, not parameters. -/
def sourceSpec : C891RootSpec := tcRootSpec boxLoCert boxHiCert exists_unique

def sourceRoot : Fin 12 → ℝ := sourceSpec.root

def sourceRadius : ℝ := sourceRoot 6

theorem sourceSpec_sys : sourceSpec.sys = TCSystem := rfl
theorem sourceSpec_lo : sourceSpec.boxLo = boxLoCert := rfl
theorem sourceSpec_hi : sourceSpec.boxHi = boxHiCert := rfl
theorem sourceSpec_idx : sourceSpec.radiusIndex = 6 := rfl

theorem sourceRadius_eq_Rstar : sourceRadius = Rstar sourceSpec := rfl

theorem sourceRoot_mem : RootPredicate sourceRoot := sourceSpec.root_mem

theorem sourceRoot_unique {u : Fin 12 → ℝ} (hu : RootPredicate u) :
    u = sourceRoot := sourceSpec.root_unique hu

/-- Any same-source spec has exactly this root. -/
theorem root_eq_sourceRoot (S : C891RootSpec) (hs : S.sys = TCSystem)
    (hl : S.boxLo = boxLoCert) (hh : S.boxHi = boxHiCert) : S.root = sourceRoot := by
  apply sourceRoot_unique
  have hm := S.root_mem
  rw [hs, hl, hh] at hm
  exact hm

/-- Any same-source spec with the actual coordinate6 reads the same radius. -/
theorem Rstar_eq_sourceRadius (S : C891RootSpec) (hs : S.sys = TCSystem)
    (hl : S.boxLo = boxLoCert) (hh : S.boxHi = boxHiCert) (hi : S.radiusIndex = 6) :
    Rstar S = sourceRadius := by
  unfold Rstar
  rw [root_eq_sourceRoot S hs hl hh, hi]
  rfl
theorem source_attainment : Covers (centersOfRoot sourceRoot) sourceRadius :=
  FlashAttainmentRstarConsumer.covers_of_specified_root_actual sourceSpec rfl rfl rfl rfl

theorem sourceRadius_pos : 0 < sourceRadius :=
  Rstar_pos_of_krawczyk (S := sourceSpec) rfl ⟨rfl, rfl⟩ rfl

theorem sourceRadius_lt_threshold : sourceRadius < C921Sem.threshR :=
  ResumeNewtonData.root_lt_threshold sourceSpec rfl rfl rfl rfl

theorem sourceRadius_mem_box : (boxLoCert 6 : ℝ) ≤ sourceRadius ∧
    sourceRadius ≤ (boxHiCert 6 : ℝ) := sourceRoot_mem.1 6

/-- End consumer: the only missing half is the unrestricted lower bound;
this theorem itself is explicitly conditional and not counted as completion. -/
theorem main_of_lower_bound
    (hlower : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → sourceRadius ≤ r) :
    N11MainStatement sourceRadius :=
  n11_main_of_strongInterface ⟨⟨centersOfRoot sourceRoot, source_attainment⟩, hlower⟩

end N11Formalization.SourceExactRoot

#print N11Formalization.SourceExactRoot.sourceSpec
#print N11Formalization.SourceExactRoot.sourceRoot
#print N11Formalization.SourceExactRoot.sourceRadius
#print N11Formalization.SourceExactRoot.exists_unique
#print N11Formalization.SourceExactRoot.sourceRoot_mem
#print N11Formalization.SourceExactRoot.root_eq_sourceRoot
#print N11Formalization.SourceExactRoot.source_attainment
#print N11Formalization.SourceExactRoot.sourceRadius_lt_threshold
#print N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.SourceExactRoot.exists_unique
#print axioms N11Formalization.SourceExactRoot.root_eq_sourceRoot
#print axioms N11Formalization.SourceExactRoot.source_attainment
#print axioms N11Formalization.SourceExactRoot.sourceRadius_pos
#print axioms N11Formalization.SourceExactRoot.sourceRadius_lt_threshold
#print axioms N11Formalization.SourceExactRoot.main_of_lower_bound
