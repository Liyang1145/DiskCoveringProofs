import N11Formalization
set_option autoImplicit false
namespace N11Formalization.C450NormalizedImportedAudit
open C450NormalizedInterface

example (p : Point) : ∃ a : ℝ,
    SourceChartIsometry.rotate a p = hubPt ‖p‖ := exists_hub_rotation p
example : ∃ a : ℝ, SourceChartIsometry.rotate a (0 : Point) = hubPt 0 := by
  simpa only [norm_zero] using exists_hub_rotation (0 : Point)
example (a : ℝ) (c : Fin 11 → Point) (r : ℝ) (hc : Covers c r) :
    Covers (fun i => SourceChartIsometry.rotate a (c i)) r := covers_rotate a hc
example : Covers
    (fun i => SourceChartIsometry.rotate Real.pi (centersOfRoot SourceExactRoot.sourceRoot i))
    SourceExactRoot.sourceRadius :=
  covers_rotate Real.pi SourceExactRoot.source_attainment
example : ∃ a : ℝ, SourceChartIsometry.rotate a C450OrientationControl.h = hubPt (7/50) := by
  simpa only [C450OrientationControl.norm_h] using
    exists_hub_rotation C450OrientationControl.h
example (hs : SourceObligation) : C450Atom := atom_of_source hs
example (hs : SourceObligation) (c : Fin 11 → Point) (r : ℝ)
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 := nine_of_source hs hr hc
example (hs : SourceObligation) (c : Fin 11 → Point) (r : ℝ)
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11), Covers (fun j => c (p j)) r ∧
      DSHTopologyInterior.RingLabels (fun j => c (p j)) r :=
  ringLabels_of_source hs hr hc
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450NormalizedImportedAudit
#print N11Formalization.C450NormalizedInterface.PerDiskNormalized
#print N11Formalization.C450NormalizedInterface.SourceObligation
#check @N11Formalization.C450NormalizedInterface.exists_hub_rotation
#check @N11Formalization.C450NormalizedInterface.covers_rotate
#check @N11Formalization.C450NormalizedInterface.atom_of_normalized
#check @N11Formalization.C450NormalizedInterface.atom_of_source
#check @N11Formalization.C450NormalizedInterface.nine_of_source
#check @N11Formalization.C450NormalizedInterface.ringLabels_of_source
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450NormalizedInterface.rotate_norm
#print axioms N11Formalization.C450NormalizedInterface.exists_hub_rotation
#print axioms N11Formalization.C450NormalizedInterface.covers_rotate
#print axioms N11Formalization.C450NormalizedInterface.meets_rotate
#print axioms N11Formalization.C450NormalizedInterface.atom_of_normalized
#print axioms N11Formalization.C450NormalizedInterface.normalized_of_certificate
#print axioms N11Formalization.C450NormalizedInterface.atom_of_source
#print axioms N11Formalization.C450NormalizedInterface.nine_of_source
#print axioms N11Formalization.C450NormalizedInterface.ringLabels_of_source
