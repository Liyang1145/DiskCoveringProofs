import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450SourceQuantityImportedAudit
open C450SourceQuantity

def first : TenSeg := c450Segs[0]'(by decide +kernel)
theorem first_mem : first ∈ c450Segs := by decide +kernel
theorem nn0 : |first.a1|+|first.a2|+|first.a3| ≤ first.a0 :=
  (c450Segs_nonneg first first_mem).1
theorem nn1 : |first.b1|+|first.b2|+|first.b3| ≤ first.b0 :=
  (c450Segs_nonneg first first_mem).2

example : c450Q first.a0 first.a1 first.a2 first.a3
    first.b0 first.b1 first.b2 first.b3 0 1 0 false =
    c450Outer (first.W0 nn0) (hubPt (31/50))+
      c450Inner (first.W1 nn1) (hubPt (31/50)) 0 := by
  apply quantity_eq first nn0 nn1
  · rw [norm_hubPt]; norm_num
  · norm_num
  · norm_num
  · norm_num [hubPt,norm_pair_zero (by norm_num : (0:ℝ) ≤ 31/50)]
  · rw [norm_hubPt]; norm_num [rho]
  · rw [norm_hubPt]; norm_num
example : c450Q first.a0 first.a1 first.a2 first.a3
    first.b0 first.b1 first.b2 first.b3 0 1 0 true =
    c450Outer (first.W0 nn0) (hubPt (69/50))+
      c450Inner (first.W1 nn1) (hubPt (69/50)) 0 := by
  apply quantity_eq first nn0 nn1
  · rw [norm_hubPt]; norm_num
  · norm_num
  · norm_num
  · norm_num [hubPt,norm_pair_zero (by norm_num : (0:ℝ) ≤ 69/50)]
  · rw [norm_hubPt]; norm_num [rho]
  · rw [norm_hubPt]; norm_num

theorem hub_sub (x y : ℝ) : hubPt x-hubPt y = hubPt (x-y) := by
  ext i
  fin_cases i <;> simp [hubPt]
example : c450B (hubPt (9/10)) (7/50) = 0 := by
  change (if ‖hubPt (9/10)-hubPt (7/50)‖ < 2*(19/50:ℝ) then
    Real.arccos (‖hubPt (9/10)-hubPt (7/50)‖/(2*(19/50:ℝ))) else 0) = 0
  rw [hub_sub,norm_hubPt]
  norm_num
example : c450Inner (first.W1 nn1) (hubPt (69/50)) 0 = 0 := by
  have hB : c450B (hubPt (69/50)) 0 = 0 := by
    change (if ‖hubPt (69/50)-hubPt 0‖ < 2*(19/50:ℝ) then
      Real.arccos (‖hubPt (69/50)-hubPt 0‖/(2*(19/50:ℝ))) else 0) = 0
    rw [hub_sub,norm_hubPt]
    norm_num
  simp [c450Inner,hB]

example (hq : SourceQuantityObligation) : C450Atom := atom_of_quantity hq
example (hq : SourceQuantityObligation) (c : Fin 11 → Point) (r : ℝ)
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11), Covers (fun j => c (p j)) r ∧
      DSHTopologyInterior.RingLabels (fun j => c (p j)) r :=
  C450NormalizedInterface.ringLabels_of_source (source_of_quantity hq) hr hc
example : ¬C450PerDiskObligation := C450OrientationControl.not_obligation
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450SourceQuantityImportedAudit
#print N11Formalization.C450SourceQuantity.QuantityBound
#print N11Formalization.C450SourceQuantity.SourceQuantityObligation
#check @N11Formalization.C450SourceQuantity.parameters
#check @N11Formalization.C450SourceQuantity.quantity_eq
#check @N11Formalization.C450SourceQuantity.atom_of_quantity
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450SourceQuantity.legal_sin_sq
#print axioms N11Formalization.C450SourceQuantity.parameters
#print axioms N11Formalization.C450SourceQuantity.direction_bounds
#print axioms N11Formalization.C450SourceQuantity.scalarEll_eq
#print axioms N11Formalization.C450SourceQuantity.quantity_eq
#print axioms N11Formalization.C450SourceQuantity.normalized_of_quantity
#print axioms N11Formalization.C450SourceQuantity.source_of_quantity
#print axioms N11Formalization.C450SourceQuantity.atom_of_quantity
