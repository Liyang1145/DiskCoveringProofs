import N11Formalization.Definitions

/-! Canonical fixed-switch SOC network: 18 boundary edges and 33 face edges.
Source: FIXED-SWITCH-SOC-REDUCTION.md §§1–3, EXACT-ORACLE-INDEX-MAP.md §7.
This is a relaxation object, not a theorem that arbitrary covers have this graph. -/
noncomputable section
namespace N11Formalization.ResumeNetwork

abbrev Edge := (Fin 9 × Fin 2) ⊕ (Fin 11 × Fin 3)

/-- Nine fan faces followed by the two central faces. Hubs are sites 9 and 10. -/
def face : Fin 11 → Fin 3 → Fin 11 :=
  ![![0, 1, 9], ![1, 2, 9], ![2, 3, 9], ![3, 4, 9],
    ![4, 5, 10], ![5, 6, 10], ![6, 7, 10], ![7, 8, 10], ![8, 0, 10],
    ![0, 9, 10], ![4, 9, 10]]

/-- Boundary switches bounding the arc owned by site i are U_(i-1) and U_i. -/
def anchorIndex (i : Fin 9) (side : Fin 2) : Fin 9 :=
  if side = 0 then i - 1 else i

def edgeLength (U : Fin 9 → Point) (C Z : Fin 11 → Point) : Edge → ℝ
  | .inl (i, side) => dist (C ⟨i.val, by omega⟩) (U (anchorIndex i side))
  | .inr (f, v) => dist (C (face f v)) (Z f)

def Feasible (U : Fin 9 → Point) (C Z : Fin 11 → Point) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ e, edgeLength U C Z e ≤ r

def energy (α : Edge → ℝ) (U : Fin 9 → Point) (C Z : Fin 11 → Point) : ℝ :=
  ∑ e, α e * edgeLength U C Z e ^ 2

def feasibleSquares (U : Fin 9 → Point) : Set ℝ :=
  {q | ∃ (C Z : Fin 11 → Point) (r : ℝ), Feasible U C Z r ∧ q = r ^ 2}

/-- Squared oracle directly defined from the same 51 constraints. -/
def V2 (U : Fin 9 → Point) : ℝ := sInf (feasibleSquares U)

theorem edge_card : Fintype.card Edge = 51 := by decide

theorem weighted_energy_le {α : Edge → ℝ} {U : Fin 9 → Point}
    {C Z : Fin 11 → Point} {r : ℝ}
    (hα : ∀ e, 0 ≤ α e) (hs : ∑ e, α e = 1) (hf : Feasible U C Z r) :
    energy α U C Z ≤ r ^ 2 := by
  calc
    energy α U C Z ≤ ∑ e, α e * r ^ 2 := by
      apply Finset.sum_le_sum
      intro e _
      apply mul_le_mul_of_nonneg_left _ (hα e)
      have he := hf.2 e
      have hn : 0 ≤ edgeLength U C Z e := by cases e <;> exact dist_nonneg
      nlinarith [hf.1]
    _ = r ^ 2 := by rw [← Finset.sum_mul, hs, one_mul]

theorem feasibleSquares_bddBelow (U : Fin 9 → Point) : BddBelow (feasibleSquares U) := by
  refine ⟨0, ?_⟩
  rintro q ⟨C, Z, r, hf, rfl⟩
  positivity

theorem oracle_le_feasible {U : Fin 9 → Point} {C Z : Fin 11 → Point} {r : ℝ}
    (hf : Feasible U C Z r) : V2 U ≤ r ^ 2 :=
  csInf_le (feasibleSquares_bddBelow U) ⟨C, Z, r, hf, rfl⟩

/-- Anchors on or in the unit circle give the trivial feasible assignment at radius 1. -/
theorem feasible_unit {U : Fin 9 → Point} (hU : ∀ i, ‖U i‖ ≤ 1) :
    Feasible U (fun _ => 0) (fun _ => 0) 1 := by
  refine ⟨by norm_num, ?_⟩
  intro e
  rcases e with ⟨i, side⟩ | ⟨f, v⟩
  · simpa [edgeLength, dist_zero_left] using hU (anchorIndex i side)
  · simp [edgeLength]

/-- Any uniform lower bound on a normalized nonnegative stress energy is an oracle
lower bound. No attainment, strong duality, or unique Schur minimizer is assumed. -/
theorem stress_lower_bound {U : Fin 9 → Point} {α : Edge → ℝ} {L : ℝ}
    (hU : ∀ i, ‖U i‖ ≤ 1) (hα : ∀ e, 0 ≤ α e) (hs : ∑ e, α e = 1)
    (hL : ∀ C Z, L ≤ energy α U C Z) : L ≤ V2 U := by
  apply le_csInf
  · exact ⟨1, (fun _ => 0), (fun _ => 0), 1, feasible_unit hU, by norm_num⟩
  · rintro q ⟨C, Z, r, hf, rfl⟩
    exact (hL C Z).trans (weighted_energy_le hα hs hf)

/-- Real consumer of geometric witnesses; the 18+33 assumptions are precisely
those supplied by a canonical covering, whose construction remains unproved. -/
theorem oracle_le_of_geometric_witnesses {U : Fin 9 → Point}
    {C Z : Fin 11 → Point} {r : ℝ} (hr : 0 ≤ r)
    (hboundary : ∀ i : Fin 9, ∀ side : Fin 2,
      dist (C ⟨i.val, by omega⟩) (U (anchorIndex i side)) ≤ r)
    (hfaces : ∀ f : Fin 11, ∀ v : Fin 3, dist (C (face f v)) (Z f) ≤ r) :
    V2 U ≤ r ^ 2 := by
  apply oracle_le_feasible (C := C) (Z := Z)
  refine ⟨hr, ?_⟩
  intro e
  rcases e with ⟨i, side⟩ | ⟨f, v⟩
  · exact hboundary i side
  · exact hfaces f v

/-- Cyclic endpoint calibration, including the wrap at site zero. -/
theorem endpoint_wrap : anchorIndex 0 0 = 8 ∧ anchorIndex 0 1 = 0 ∧
    anchorIndex 8 0 = 7 ∧ anchorIndex 8 1 = 8 := by decide

theorem central_face_calibration : face 9 = ![0, 9, 10] ∧ face 10 = ![4, 9, 10] := by
  constructor <;> rfl

theorem oracle_nonneg {U : Fin 9 → Point} (hU : ∀ i, ‖U i‖ ≤ 1) : 0 ≤ V2 U := by
  apply le_csInf
  · exact ⟨1, (fun _ => 0), (fun _ => 0), 1, feasible_unit hU, by norm_num⟩
  · rintro q ⟨C, Z, r, hf, rfl⟩
    positivity

/-- Known-answer calibration: all anchors coincide at the origin, so value is zero. -/
theorem oracle_zero_anchors : V2 (fun _ => 0) = 0 := by
  apply le_antisymm
  · have h : Feasible (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 := by
      refine ⟨le_rfl, ?_⟩
      intro e
      cases e <;> simp [edgeLength]
    simpa using oracle_le_feasible h
  · exact oracle_nonneg (by intro i; simp)

/-- Dirichlet energy: all 22 free points minimized, including isolated auxiliaries.
No positive-definiteness or invertibility requirement on the full free block. -/
def dirichletEnergy (α : Edge → ℝ) (U : Fin 9 → Point) : ℝ :=
  sInf (Set.range (fun CZ : (Fin 11 → Point) × (Fin 11 → Point) => energy α U CZ.1 CZ.2))

theorem energy_nonneg {α : Edge → ℝ} (hα : ∀ e, 0 ≤ α e)
    (U : Fin 9 → Point) (C Z : Fin 11 → Point) : 0 ≤ energy α U C Z := by
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (hα e) (sq_nonneg _)

theorem dirichlet_le_energy {α : Edge → ℝ} (hα : ∀ e, 0 ≤ α e)
    (U : Fin 9 → Point) (C Z : Fin 11 → Point) : dirichletEnergy α U ≤ energy α U C Z := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro q ⟨⟨C', Z'⟩, rfl⟩
    exact energy_nonneg hα U C' Z'
  · exact ⟨(C, Z), rfl⟩

/-- Actual weak squared SOC duality on the concrete graph, with no unproved
minimization or source-semantic inequality as a hypothesis. -/
theorem dirichlet_le_oracle {U : Fin 9 → Point} {α : Edge → ℝ}
    (hU : ∀ i, ‖U i‖ ≤ 1) (hα : ∀ e, 0 ≤ α e) (hs : ∑ e, α e = 1) :
    dirichletEnergy α U ≤ V2 U :=
  stress_lower_bound hU hα hs (dirichlet_le_energy hα U)

#check @dirichlet_le_oracle
#print axioms dirichlet_le_oracle
#check @stress_lower_bound
#print axioms weighted_energy_le
#print axioms oracle_le_feasible
#print axioms stress_lower_bound
end N11Formalization.ResumeNetwork
