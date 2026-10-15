import N11Formalization.C450NormalizedInterface
import N11Formalization.FlashCoverReductionLocalization

/-! Genuine arbitrary-cover hub structure, conditional ONLY on actual C450.
No source configuration, distinctness, canonical face or interiority premise.
The final source consumer preserves the original radius and cover under a
finite permutation. SourceObligation remains explicit until all36 are paid.
Draft: actual module/root/import acceptance must be inspected separately. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubEssentiality
open DSHTopologyInterior

def DeletedCover (c : Fin 11 → Point) (r : ℝ) (j : Fin 11) : Prop :=
  ∀ x : Point, x ∈ unitDisk → ∃ i : Fin 11, i ≠ j ∧ dist x (c i) ≤ r

def PrivatePoint (c : Fin 11 → Point) (r : ℝ) (j : Fin 11) : Prop :=
  ∃ x : Point, x ∈ unitDisk ∧ dist x (c j) ≤ r ∧
    ∀ i : Fin 11, i ≠ j → r < dist x (c i)

private theorem other_hub (j : Fin 11) (hj : 9 ≤ j.val) :
    ∃ k : Fin 11, 9 ≤ k.val ∧ j ≠ k ∧
      ∀ i : Fin 11, i ≠ j → i ≠ k → i.val < 9 := by
  have hv : j.val = 9 ∨ j.val = 10 := by omega
  have hs : j = (9 : Fin 11) ∨ j = 10 := by
    rcases hv with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hs with h | h
  · refine ⟨10, by decide, ?_, ?_⟩
    · rw [h]
      decide
    · intro i hij hik
      have hi9 : i.val ≠ 9 := by
        intro hi
        exact hij ((Fin.ext hi).trans h.symm)
      have hi10 : i.val ≠ 10 := by
        intro hi
        exact hik (Fin.ext hi)
      omega
  · refine ⟨9, by decide, ?_, ?_⟩
    · rw [h]
      decide
    · intro i hij hik
      have hi10 : i.val ≠ 10 := by
        intro hi
        exact hij ((Fin.ext hi).trans h.symm)
      have hi9 : i.val ≠ 9 := by
        intro hi
        exact hik (Fin.ext hi)
      omega

/-- A removable hub creates a genuine forbidden ten-boundary cover.
The replacement and all radius enlargement steps are paid in this proof. -/
theorem not_deleted_cover (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hR : RingLabels c r) {j : Fin 11} (hj : 9 ≤ j.val) :
    ¬ DeletedCover c r j := by
  classical
  intro hdel
  obtain ⟨k, hk, hjk, hother⟩ := other_hub j hj
  let d : Fin 11 → Point := fun i => if i = j then angPt 0 else c i
  have hcov : ∀ x : Point, ‖x‖ ≤ 1 →
      ∃ i : Fin 11, dist x (d i) ≤ 19/50 := by
    intro x hx
    obtain ⟨i, hij, hi⟩ := hdel x (mem_unitDisk.mpr hx)
    exact ⟨i, by simpa only [d, if_neg hij] using hi.trans hr⟩
  have htouch : ∀ i : Fin 11, i ≠ k → MeetsCircle d (19/50) i := by
    intro i hik
    by_cases hij : i = j
    · subst i
      refine ⟨angPt 0, norm_angPt 0, ?_⟩
      simp only [d, if_pos rfl, dist_self]
      norm_num
    · obtain ⟨x, hx, hi⟩ := hR.ring_meets (hother i hij hik)
      exact ⟨x, hx, by simpa only [d, if_neg hij] using hi.trans hr⟩
  have harc : ∀ x : Point, ‖x‖ = 1 →
      ∃ i : Fin 11, i ≠ k ∧ dist x (d i) ≤ 19/50 := by
    intro x hx
    obtain ⟨i, hij, hi⟩ := hdel x (mem_unitDisk.mpr hx.le)
    have hik : i ≠ k := by
      intro heq
      subst i
      exact (hR.hub_not_meets hk) ⟨x, hx, hi⟩
    exact ⟨i, hik, by simpa only [d, if_neg hij] using hi.trans hr⟩
  exact h450 d k hcov htouch harc

/-- Every hub has a private covered point; redundancy is not an input. -/
theorem private_point_of_atom (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hc : Covers c r) (hR : RingLabels c r)
    {j : Fin 11} (hj : 9 ≤ j.val) : PrivatePoint c r j := by
  classical
  by_contra hnone
  apply not_deleted_cover h450 hr hR hj
  intro x hx
  by_contra hno
  apply hnone
  obtain ⟨i, hi⟩ := hc x hx
  have hij : i = j := by
    by_contra hij
    exact hno ⟨i, hij, hi⟩
  refine ⟨x, hx, ?_, ?_⟩
  · simpa only [hij] using hi
  · intro k hkj
    exact lt_of_not_ge (fun hk => hno ⟨k, hkj, hk⟩)

/-- No distinct index may coincide with a site having a private point. -/
theorem private_point_ne {c : Fin 11 → Point} {r : ℝ} {j k : Fin 11}
    (hj : PrivatePoint c r j) (hjk : j ≠ k) : c j ≠ c k := by
  intro heq
  obtain ⟨x, hx, hself, hother⟩ := hj
  have hfar := hother k hjk.symm
  rw [← heq] at hfar
  linarith

/-- Generic closed-ball geometry, including the zero centre and zero radius.
Initial contact with D and exclusion of its boundary are explicit inputs,
both discharged by the actual-cover consumer below. -/
theorem closed_ball_strict_margin {p : Point} {r : ℝ} (hr : 0 ≤ r)
    (hx : ∃ x : Point, ‖x‖ ≤ 1 ∧ dist x p ≤ r)
    (hsep : ∀ y : Point, dist y p ≤ r → ‖y‖ ≠ 1) : ‖p‖ + r < 1 := by
  obtain ⟨x, hx1, hxp⟩ := hx
  have hxlt : ‖x‖ < 1 := by
    rcases lt_or_eq_of_le hx1 with h | h
    · exact h
    · exact (hsep x hxp h).elim
  have hall : ∀ y ∈ Metric.closedBall p r, ‖y‖ < 1 :=
    convex_closed_norm_lt_one (convex_closedBall p r)
      (Metric.mem_closedBall.mpr hxp) hxlt
      (fun y hy => hsep y (Metric.mem_closedBall.mp hy))
  by_cases hp : p = 0
  · have hy : r • angPt 0 ∈ Metric.closedBall p r := by
      rw [hp, Metric.mem_closedBall, dist_zero_right, norm_smul, norm_angPt,
        mul_one, Real.norm_eq_abs, abs_of_nonneg hr]
    have hmax := hall (r • angPt 0) hy
    rw [norm_smul, norm_angPt, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hr] at hmax
    simpa only [hp, norm_zero, zero_add] using hmax
  · have hn : 0 < ‖p‖ := norm_pos_iff.mpr hp
    let u : Point := ‖p‖⁻¹ • p
    have hu : ‖u‖ = 1 := by
      change ‖‖p‖⁻¹ • p‖ = 1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn,
        inv_mul_cancel₀ hn.ne']
    have hpu : p = ‖p‖ • u := by
      change p = ‖p‖ • (‖p‖⁻¹ • p)
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    let y : Point := (‖p‖ + r) • u
    have hsub : y - p = r • u := by
      change (‖p‖ + r) • u - p = r • u
      calc
        (‖p‖ + r) • u - p = (‖p‖ + r) • u - ‖p‖ • u :=
          congrArg (fun z : Point => (‖p‖ + r) • u - z) hpu
        _ = r • u := by rw [← sub_smul]; simp
    have hd : dist y p = r := by
      rw [dist_eq_norm, hsub, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hr]
    have hmax := hall y (Metric.mem_closedBall.mpr hd.le)
    change ‖(‖p‖ + r) • u‖ < 1 at hmax
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg p) hr)] at hmax
    exact hmax

/-- Entire closed hub disk is strictly inside D; neither existence nor
interiority is postulated. Original r is kept, not replaced by R0. -/
theorem hub_strict_margin_of_atom (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hc : Covers c r) (hR : RingLabels c r)
    {j : Fin 11} (hj : 9 ≤ j.val) : ‖c j‖ + r < 1 := by
  obtain ⟨x, hx, hself, hother⟩ := private_point_of_atom h450 hr hc hR hj
  exact closed_ball_strict_margin (Covers.nonneg hc)
    ⟨x, mem_unitDisk.mp hx, hself⟩
    (fun y hy hn => (hR.hub_not_meets hj) ⟨y, hn, hy⟩)

def HubStructure (c : Fin 11 → Point) (r : ℝ) : Prop :=
  (∀ j : Fin 11, 9 ≤ j.val → PrivatePoint c r j ∧ ‖c j‖ + r < 1 ∧
    ∀ y : Point, dist y (c j) ≤ r → ‖y‖ < 1) ∧ c 9 ≠ c 10

theorem structure_of_atom (h450 : C450Atom) {c : Fin 11 → Point} {r : ℝ}
    (hr : r ≤ 19/50) (hc : Covers c r) (hR : RingLabels c r) :
    HubStructure c r := by
  constructor
  · intro j hj
    have hp := private_point_of_atom h450 hr hc hR hj
    have hm := hub_strict_margin_of_atom h450 hr hc hR hj
    refine ⟨hp, hm, ?_⟩
    intro y hy
    have hn : ‖y‖ ≤ dist y (c j) + ‖c j‖ := by
      calc
        ‖y‖ = ‖(y - c j) + c j‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - c j‖ + ‖c j‖ := norm_add_le _ _
        _ = dist y (c j) + ‖c j‖ := by rw [dist_eq_norm]
    linarith
  · exact private_point_ne (private_point_of_atom h450 hr hc hR (j := 9) (by decide))
      (by decide : (9 : Fin 11) ≠ 10)

/-- Actual unrestricted cover consumer. Only genuine36 normalized source
inequalities remain explicit; no graph/face/genericity premise is added. -/
theorem relabeled_structure_of_source (hs : C450NormalizedInterface.SourceObligation)
    {c : Fin 11 → Point} {r : ℝ} (hr : r < SourceExactRoot.sourceRadius)
    (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11), Covers (fun j => c (p j)) r ∧
      RingLabels (fun j => c (p j)) r ∧ HubStructure (fun j => c (p j)) r := by
  obtain ⟨p, hcov, hlabels⟩ := C450NormalizedInterface.ringLabels_of_source hs hr hc
  have hroot : SourceExactRoot.sourceRadius < 19/50 :=
    SourceExactRoot.sourceRadius_mem_box.2.trans_lt boxHiCert_six_lt_R0_real
  exact ⟨p, hcov, hlabels, structure_of_atom (C450NormalizedInterface.atom_of_source hs)
    (hr.trans hroot).le hcov hlabels⟩

theorem tangent_margin_control :
    ¬ (‖((3 : ℝ)/4) • angPt 0‖ + (1:ℝ)/4 < 1) := by
  rw [norm_smul, norm_angPt, mul_one, Real.norm_eq_abs]
  norm_num

theorem outside_no_circle_control :
    (∀ x : Point, dist x ((2:ℝ) • angPt 0) ≤ (1:ℝ)/4 → ‖x‖ ≠ 1) ∧
      ¬ (‖(2:ℝ) • angPt 0‖ + (1:ℝ)/4 < 1) := by
  have hp : ‖(2:ℝ) • angPt 0‖ = 2 := by
    rw [norm_smul, norm_angPt, mul_one, Real.norm_eq_abs]
    norm_num
  constructor
  · intro x hx hnorm
    have hle : ‖(2:ℝ) • angPt 0‖ ≤ dist x ((2:ℝ) • angPt 0) + ‖x‖ := by
      calc
        ‖(2:ℝ) • angPt 0‖ = ‖((2:ℝ) • angPt 0 - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖(2:ℝ) • angPt 0 - x‖ + ‖x‖ := norm_add_le _ _
        _ = dist x ((2:ℝ) • angPt 0) + ‖x‖ := by rw [dist_eq_norm, norm_sub_rev]
    rw [hp, hnorm] at hle
    linarith
  · rw [hp]
    norm_num

end N11Formalization.ActualHubEssentiality

#check @N11Formalization.ActualHubEssentiality.not_deleted_cover
#check @N11Formalization.ActualHubEssentiality.private_point_of_atom
#check @N11Formalization.ActualHubEssentiality.closed_ball_strict_margin
#check @N11Formalization.ActualHubEssentiality.hub_strict_margin_of_atom
#check @N11Formalization.ActualHubEssentiality.structure_of_atom
#check @N11Formalization.ActualHubEssentiality.relabeled_structure_of_source
#print axioms N11Formalization.ActualHubEssentiality.not_deleted_cover
#print axioms N11Formalization.ActualHubEssentiality.private_point_of_atom
#print axioms N11Formalization.ActualHubEssentiality.private_point_ne
#print axioms N11Formalization.ActualHubEssentiality.closed_ball_strict_margin
#print axioms N11Formalization.ActualHubEssentiality.hub_strict_margin_of_atom
#print axioms N11Formalization.ActualHubEssentiality.structure_of_atom
#print axioms N11Formalization.ActualHubEssentiality.relabeled_structure_of_source
#print axioms N11Formalization.ActualHubEssentiality.tangent_margin_control
#print axioms N11Formalization.ActualHubEssentiality.outside_no_circle_control
