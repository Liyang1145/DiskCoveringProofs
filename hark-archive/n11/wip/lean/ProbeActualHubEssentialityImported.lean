import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubEssentialityImportedAudit
open ActualHubEssentiality DSHTopologyInterior

theorem original_radius_consumer
    (h25 : C450Source11Segment.RemainingSourceObligation)
    {c : Fin 11 → Point} {r : ℝ} (hr : r < SourceExactRoot.sourceRadius)
    (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11), Covers (fun j => c (p j)) r ∧
      RingLabels (fun j => c (p j)) r ∧ HubStructure (fun j => c (p j)) r :=
  relabeled_structure_of_source (C450Source11Segment.source_of_remaining h25) hr hc

theorem actual_private_point (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hc : Covers c r) (hR : RingLabels c r)
    (j : Fin 11) (hj : 9 ≤ j.val) : PrivatePoint c r j :=
  private_point_of_atom h450 hr hc hR hj

theorem actual_margin (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hc : Covers c r) (hR : RingLabels c r)
    (j : Fin 11) (hj : 9 ≤ j.val) : ‖c j‖ + r < 1 :=
  hub_strict_margin_of_atom h450 hr hc hR hj

theorem actual_whole_closed_disk (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hc : Covers c r) (hR : RingLabels c r)
    (j : Fin 11) (hj : 9 ≤ j.val) :
    ∀ y : Point, dist y (c j) ≤ r → ‖y‖ < 1 :=
  ((structure_of_atom h450 hr hc hR).1 j hj).2.2

theorem actual_ne_every_other_site (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hc : Covers c r) (hR : RingLabels c r)
    (j : Fin 11) (hj : 9 ≤ j.val) : ∀ i : Fin 11, i ≠ j → c j ≠ c i := by
  intro i hij
  exact private_point_ne (private_point_of_atom h450 hr hc hR hj) hij.symm

end N11Formalization.ActualHubEssentialityImportedAudit
#print N11Formalization.ActualHubEssentiality.PrivatePoint
#print N11Formalization.ActualHubEssentiality.HubStructure
#check @N11Formalization.ActualHubEssentialityImportedAudit.original_radius_consumer
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.ActualHubEssentiality.not_deleted_cover
#print axioms N11Formalization.ActualHubEssentiality.private_point_of_atom
#print axioms N11Formalization.ActualHubEssentiality.private_point_ne
#print axioms N11Formalization.ActualHubEssentiality.closed_ball_strict_margin
#print axioms N11Formalization.ActualHubEssentiality.hub_strict_margin_of_atom
#print axioms N11Formalization.ActualHubEssentiality.structure_of_atom
#print axioms N11Formalization.ActualHubEssentiality.relabeled_structure_of_source
#print axioms N11Formalization.ActualHubEssentiality.tangent_margin_control
#print axioms N11Formalization.ActualHubEssentiality.outside_no_circle_control
#print axioms N11Formalization.ActualHubEssentialityImportedAudit.original_radius_consumer
#print axioms N11Formalization.ActualHubEssentialityImportedAudit.actual_private_point
#print axioms N11Formalization.ActualHubEssentialityImportedAudit.actual_margin
#print axioms N11Formalization.ActualHubEssentialityImportedAudit.actual_whole_closed_disk
#print axioms N11Formalization.ActualHubEssentialityImportedAudit.actual_ne_every_other_site
