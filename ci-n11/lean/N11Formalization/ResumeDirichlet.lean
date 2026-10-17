import N11Formalization.ResumeNetwork

/-! Completing squares for a possibly singular weighted network. This avoids an
inverse/positive-definiteness premise and supports zero-stress auxiliary nodes. -/
noncomputable section
namespace N11Formalization.ResumeDirichlet
open N11Formalization.ResumeNetwork

/-- Generic vector edge kernel. Orthogonality is the linear stationarity equation;
nonnegative weights suffice for minimality, without strict positivity. -/
theorem sumsq_min_of_stationary {E : Type*} [Fintype E]
    (α : E → ℝ) (a d : E → Point) (hα : ∀ e, 0 ≤ α e)
    (hstat : ∑ e, α e * inner ℝ (a e) (d e) = 0) :
    (∑ e, α e * ‖a e‖ ^ 2) ≤ ∑ e, α e * ‖a e + d e‖ ^ 2 := by
  have he : (∑ e, α e * ‖a e + d e‖ ^ 2) =
      (∑ e, α e * ‖a e‖ ^ 2) +
      2 * (∑ e, α e * inner ℝ (a e) (d e)) + (∑ e, α e * ‖d e‖ ^ 2) := by
    simp only [norm_add_sq_real, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he, hstat]
  have hn : 0 ≤ ∑ e, α e * ‖d e‖ ^ 2 :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hα e) (sq_nonneg _))
  linarith

def edgeVector (U : Fin 9 → Point) (C Z : Fin 11 → Point) : Edge → Point
  | .inl (i, side) => C ⟨i.val, by omega⟩ - U (anchorIndex i side)
  | .inr (f, v) => C (face f v) - Z f

theorem edgeLength_eq_norm (U : Fin 9 → Point) (C Z : Fin 11 → Point) (e : Edge) :
    edgeLength U C Z e = ‖edgeVector U C Z e‖ := by
  cases e <;> exact dist_eq_norm _ _

theorem edgeVector_shift (U : Fin 9 → Point) (C Z dC dZ : Fin 11 → Point) (e : Edge) :
    edgeVector U (C + dC) (Z + dZ) e =
      edgeVector U C Z e + edgeVector (fun _ => 0) dC dZ e := by
  rcases e with ⟨i, side⟩ | ⟨f, v⟩
  · simp only [edgeVector, Pi.add_apply]; abel
  · simp only [edgeVector, Pi.add_apply]; abel

/-- Linear stationarity in all free directions is sufficient for the genuine
Dirichlet minimum. The statement permits a singular free block. -/
theorem energy_min_of_stationarity {α : Edge → ℝ} {U : Fin 9 → Point}
    (C0 Z0 : Fin 11 → Point) (hα : ∀ e, 0 ≤ α e)
    (hstat : ∀ dC dZ : Fin 11 → Point,
      ∑ e, α e * inner ℝ (edgeVector U C0 Z0 e)
        (edgeVector (fun _ => 0) dC dZ e) = 0)
    (C Z : Fin 11 → Point) : energy α U C0 Z0 ≤ energy α U C Z := by
  have h := sumsq_min_of_stationary α (edgeVector U C0 Z0)
    (edgeVector (fun _ => 0) (C - C0) (Z - Z0)) hα (hstat _ _)
  have he : ∀ e, edgeVector U C0 Z0 e + edgeVector (fun _ => 0) (C - C0) (Z - Z0) e =
      edgeVector U C Z e := by
    intro e
    rw [← edgeVector_shift]
    simp
  simp_rw [he] at h
  simpa only [energy, edgeLength_eq_norm] using h

/-- Candidate harmonic extension eliminates the minimization premise. -/
theorem dirichlet_eq_of_stationarity {α : Edge → ℝ} {U : Fin 9 → Point}
    (C0 Z0 : Fin 11 → Point) (hα : ∀ e, 0 ≤ α e)
    (hstat : ∀ dC dZ : Fin 11 → Point,
      ∑ e, α e * inner ℝ (edgeVector U C0 Z0 e)
        (edgeVector (fun _ => 0) dC dZ e) = 0) :
    dirichletEnergy α U = energy α U C0 Z0 := by
  apply le_antisymm (dirichlet_le_energy hα U C0 Z0)
  apply le_csInf
  · exact ⟨energy α U C0 Z0, (C0, Z0), rfl⟩
  · rintro q ⟨⟨C, Z⟩, rfl⟩
    exact energy_min_of_stationarity C0 Z0 hα hstat C Z

/-- Finite force balance kills the cross term for every displacement. `B` may
be any incidence/extension matrix, so entries with zero stress cause no difficulty. -/
theorem cross_term_zero_of_balance {E V : Type*} [Fintype E] [Fintype V]
    (α : E → ℝ) (B : E → V → ℝ) (a : E → Point)
    (hbal : ∀ v, ∑ e, (α e * B e v) • a e = 0) (d : V → Point) :
    (∑ e, α e * inner ℝ (a e) (∑ v, B e v • d v)) = 0 := by
  simp_rw [inner_sum, real_inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hz : ∀ v, (∑ e, α e * (B e v * inner ℝ (a e) (d v))) = 0 := by
    intro v
    calc
      _ = inner ℝ (∑ e, (α e * B e v) • a e) (d v) := by
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro e _
        rw [real_inner_smul_left]
        ring
      _ = 0 := by rw [hbal v]; simp
  simp_rw [hz]
  simp

/-- A finite linear balance certificate yields minimum energy for every free
variation. It needs no matrix inverse and permits a singular Gram matrix. -/
theorem sumsq_min_of_balance {E V : Type*} [Fintype E] [Fintype V]
    (α : E → ℝ) (B : E → V → ℝ) (a : E → Point)
    (hα : ∀ e, 0 ≤ α e) (hbal : ∀ v, ∑ e, (α e * B e v) • a e = 0)
    (d : V → Point) :
    (∑ e, α e * ‖a e‖ ^ 2) ≤ ∑ e, α e * ‖a e + ∑ v, B e v • d v‖ ^ 2 :=
  sumsq_min_of_stationary α a _ hα (cross_term_zero_of_balance α B a hbal d)

/-- The 22 free nodes: eleven sites and eleven face auxiliaries. -/
abbrev Free := (Fin 11) ⊕ (Fin 11)

def incidence : Edge → Free → ℝ
  | .inl (i, _), v => if v = .inl ⟨i.val, by omega⟩ then 1 else 0
  | .inr (f, j), v => (if v = .inl (face f j) then 1 else 0) -
      (if v = .inr f then 1 else 0)

theorem incidence_apply (dC dZ : Fin 11 → Point) (e : Edge) :
    (∑ v : Free, incidence e v • Sum.elim dC dZ v) =
      edgeVector (fun _ => 0) dC dZ e := by
  rcases e with ⟨i, side⟩ | ⟨f, j⟩
  · simp [incidence, edgeVector]
  · simp [incidence, edgeVector, sub_smul, Finset.sum_sub_distrib]

/-- Finite 22-node force balance is enough for the exact Dirichlet value.
This is the concrete consumer for an exported harmonic-extension certificate. -/
theorem dirichlet_eq_of_node_balance {α : Edge → ℝ} {U : Fin 9 → Point}
    (C0 Z0 : Fin 11 → Point) (hα : ∀ e, 0 ≤ α e)
    (hbal : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C0 Z0 e = 0) :
    dirichletEnergy α U = energy α U C0 Z0 := by
  apply dirichlet_eq_of_stationarity C0 Z0 hα
  intro dC dZ
  have h := cross_term_zero_of_balance α incidence (edgeVector U C0 Z0) hbal
    (Sum.elim dC dZ)
  simpa only [incidence_apply] using h

/-- Geometric consumer of a concrete finite balance certificate: its energy
is a valid lower bound on every feasible covering-network radius squared. -/
theorem balanced_energy_le_oracle {α : Edge → ℝ} {U : Fin 9 → Point}
    (C0 Z0 : Fin 11 → Point) (hU : ∀ i, ‖U i‖ ≤ 1)
    (hα : ∀ e, 0 ≤ α e) (hs : ∑ e, α e = 1)
    (hbal : ∀ v : Free, ∑ e, (α e * incidence e v) • edgeVector U C0 Z0 e = 0) :
    energy α U C0 Z0 ≤ V2 U := by
  rw [← dirichlet_eq_of_node_balance C0 Z0 hα hbal]
  exact dirichlet_le_oracle hU hα hs

#check @balanced_energy_le_oracle
#print axioms balanced_energy_le_oracle
#check @dirichlet_eq_of_node_balance
#print axioms dirichlet_eq_of_node_balance
#check @dirichlet_eq_of_stationarity
#print axioms cross_term_zero_of_balance
#print axioms dirichlet_eq_of_stationarity
end N11Formalization.ResumeDirichlet
