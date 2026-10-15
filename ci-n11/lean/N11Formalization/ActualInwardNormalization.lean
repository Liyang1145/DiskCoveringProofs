import N11Formalization.ActualVoronoiCells
import N11Formalization.Assembly.InnerRootReplace

/-! Normalize every ACTUAL boundary disk to its inner radial root.
The original radius, cover and actual circle caps are retained. Unlike the
older Assembly interface, outer-root membership is a conclusion, not an input.
Nearest ownership must be rebuilt after replacement; it is not preserved. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualInwardNormalization
open DSHTopologyInterior ActualHubEssentiality ActualVoronoiCells

theorem covers_pos {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r) (hr1 : r < 1) :
    0 < r := by
  have hnonneg := Covers.nonneg hc
  have hcount := card_mul_two_arcsin_ge_two_pi c hnonneg hr1
    (fun x hx => hc x (mem_unitDisk.mpr hx.le))
  rcases hnonneg.eq_or_lt with hzero | hpos
  · rw [← hzero, Real.arcsin_zero, mul_zero] at hcount
    linarith [Real.pi_pos]
  · exact hpos

theorem norm_root_cases {c : Point} {r : ℝ} (hc : c ≠ 0)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmeet : ∃ x : Point, ‖x‖ = 1 ∧ dist x c ≤ r) :
    ‖c‖ = innerRoot (capHalfWidth c r) r ∨
      ‖c‖ = outerRoot (capHalfWidth c r) r := by
  let θ := capHalfWidth c r
  have hs : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hthreshold : -1 ≤ (1 + ‖c‖^2 - r^2)/(2*‖c‖) := by
    rw [le_div_iff₀ (by linarith : 0 < 2*‖c‖)]
    nlinarith
  have hcos : Real.cos θ = (1 + ‖c‖^2 - r^2)/(2*‖c‖) :=
    Real.cos_arccos hthreshold (cap_threshold_le_one_of_meets hc hr0 hmeet)
  have heq : ‖c‖^2 - 2*‖c‖*Real.cos θ + (1-r^2) = 0 := by
    rw [hcos]
    exact diskRoot_relation hs.ne'
  have hsquare : (‖c‖ - Real.cos θ)^2 = r^2 - Real.sin θ^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hroot : Real.sqrt (r^2 - Real.sin θ^2) = |‖c‖ - Real.cos θ| := by
    rw [← hsquare, Real.sqrt_sq_eq_abs]
  by_cases hside : ‖c‖ ≤ Real.cos θ
  · left
    change ‖c‖ = Real.cos θ - Real.sqrt (r^2 - Real.sin θ^2)
    rw [hroot, abs_of_nonpos (sub_nonpos.mpr hside)]
    ring
  · right
    change ‖c‖ = Real.cos θ + Real.sqrt (r^2 - Real.sin θ^2)
    rw [hroot, abs_of_nonneg (by linarith : 0 ≤ ‖c‖ - Real.cos θ)]
    ring

def inward (c : Point) (r : ℝ) : Point :=
  innerRoot (capHalfWidth c r) r • centerDir c

theorem inward_dominates {c x : Point} {r : ℝ} (hc : c ≠ 0)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hmeet : ∃ y : Point, ‖y‖ = 1 ∧ dist y c ≤ r)
    (hx : ‖x‖ ≤ 1) (hd : dist x c ≤ r) : dist x (inward c r) ≤ r := by
  rcases norm_root_cases hc hr0.le hr1 hmeet with hi | ho
  · have he : c = inward c r := by
      calc
        c = ‖c‖ • centerDir c := self_eq_norm_smul_centerDir hc
        _ = innerRoot (capHalfWidth c r) r • centerDir c := by rw [hi]
        _ = inward c r := rfl
    rwa [← he]
  · exact dist_innerRoot_le_of_dist_le hc hr0 hr1 ho hmeet hx hd

theorem inward_cap_iff {c x : Point} {r : ℝ} (hc : c ≠ 0)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmeet : ∃ y : Point, ‖y‖ = 1 ∧ dist y c ≤ r) (hx : ‖x‖ = 1) :
    dist x (inward c r) ≤ r ↔ dist x c ≤ r := by
  exact (cap_innerRoot_iff (centerDir_norm hc) hx hr0 hr1
    (capHalfWidth_nonneg c r) (capHalfWidth_le_arcsin hc hr0 hr1)).trans
      (cap_eq_of_meets hc hr0 hr1 hmeet hx).1.symm

theorem inward_norm_le {c : Point} {r : ℝ} (hc : c ≠ 0)
    (hr0 : 0 ≤ r) (hr1 : r < 1) : ‖inward c r‖ ≤ Real.sqrt (1-r^2) := by
  let θ := capHalfWidth c r
  have hθ0 : 0 ≤ θ := capHalfWidth_nonneg c r
  have hθ : θ ≤ Real.arcsin r := capHalfWidth_le_arcsin hc hr0 hr1
  have hp : 0 < innerRoot θ r := innerRoot_pos hr0 hr1 hθ0 hθ
  have horder := innerRoot_le_outerRoot θ r
  have hprod := innerRoot_mul_outerRoot (sin_sq_le_sq_of_le_arcsin' hr1.le hθ0 hθ)
  have hsq : innerRoot θ r ^ 2 ≤ 1-r^2 := by
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr horder)]
  have hsqrt : Real.sqrt (1-r^2)^2 = 1-r^2 := Real.sq_sqrt (by nlinarith)
  change ‖innerRoot θ r • centerDir c‖ ≤ _
  rw [norm_smul, centerDir_norm hc, mul_one, Real.norm_eq_abs, abs_of_pos hp]
  nlinarith [Real.sqrt_nonneg (1-r^2)]

def normalize (c : Fin 11 → Point) (r : ℝ) : Fin 11 → Point := by
  classical
  exact fun i => if MeetsCircle c r i then inward (c i) r else c i

theorem touching_ne_zero {c : Fin 11 → Point} {r : ℝ} (hr1 : r < 1)
    {i : Fin 11} (hi : MeetsCircle c r i) : c i ≠ 0 := by
  intro hzero
  have h := one_sub_le_norm_of_meetsCircle hi
  rw [hzero, norm_zero] at h
  linarith

theorem normalized_cover {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hr1 : r < 1) : Covers (normalize c r) r := by
  intro x hx
  obtain ⟨i, hi⟩ := hc x hx
  by_cases hm : MeetsCircle c r i
  · refine ⟨i, ?_⟩
    rw [normalize, if_pos hm]
    exact inward_dominates (touching_ne_zero hr1 hm) (covers_pos hc hr1)
      hr1 hm (mem_unitDisk.mp hx) hi
  · exact ⟨i, by simpa only [normalize, if_neg hm] using hi⟩

theorem normalized_circle_caps {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hr1 : r < 1) (i : Fin 11) {x : Point} (hx : ‖x‖ = 1) :
    dist x (normalize c r i) ≤ r ↔ dist x (c i) ≤ r := by
  by_cases hm : MeetsCircle c r i
  · rw [normalize, if_pos hm]
    exact inward_cap_iff (touching_ne_zero hr1 hm) (Covers.nonneg hc) hr1 hm hx
  · simp only [normalize, if_neg hm]

theorem normalized_meets_iff {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hr1 : r < 1) (i : Fin 11) :
    MeetsCircle (normalize c r) r i ↔ MeetsCircle c r i := by
  constructor
  · rintro ⟨x, hx, hd⟩
    exact ⟨x, hx, (normalized_circle_caps hc hr1 i hx).mp hd⟩
  · rintro ⟨x, hx, hd⟩
    exact ⟨x, hx, (normalized_circle_caps hc hr1 i hx).mpr hd⟩

theorem normalized_ringLabels {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hr1 : r < 1) (hR : RingLabels c r) : RingLabels (normalize c r) r :=
  fun i => (normalized_meets_iff hc hr1 i).trans (hR i)

theorem normalized_hub_eq {c : Fin 11 → Point} {r : ℝ} (hR : RingLabels c r)
    {i : Fin 11} (hi : 9 ≤ i.val) : normalize c r i = c i := by
  simp only [normalize, if_neg (hR.hub_not_meets hi)]

theorem normalized_ring_norm {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hr1 : r < 1) (hR : RingLabels c r) {i : Fin 11} (hi : i.val < 9) :
    ‖normalize c r i‖ ≤ Real.sqrt (1-r^2) := by
  have hm := hR.ring_meets hi
  rw [normalize, if_pos hm]
  exact inward_norm_le (touching_ne_zero hr1 hm) (Covers.nonneg hc) hr1

/-- No radius enlargement and no source-configuration substitution.
The remaining C450 source inequalities are the only certificate inputs. -/
theorem normalized_structure_of_source (hs : C450NormalizedInterface.SourceObligation)
    {c : Fin 11 → Point} {r : ℝ} (hr : r < SourceExactRoot.sourceRadius)
    (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11),
      let d := normalize (fun j => c (p j)) r
      Covers d r ∧ RingLabels d r ∧ HubStructure d r ∧ HubCellStructure d r ∧
        (∀ i : Fin 11, i.val < 9 → ‖d i‖ ≤ Real.sqrt (1-r^2)) ∧
        (∀ i : Fin 11, 9 ≤ i.val → d i = c (p i)) := by
  obtain ⟨p, hp, hR⟩ := C450NormalizedInterface.ringLabels_of_source hs hr hc
  have hr0 : r ≤ 19/50 := hr.le.trans
    (SourceExactRoot.sourceRadius_mem_box.2.trans_lt boxHiCert_six_lt_R0_real).le
  have hr1 : r < 1 := by linarith
  have hcov := normalized_cover hp hr1
  have hlabels := normalized_ringLabels hp hr1 hR
  have h450 := C450NormalizedInterface.atom_of_source hs
  refine ⟨p, hcov, hlabels, structure_of_atom h450 hr0 hcov hlabels,
    hubCells_of_atom h450 hr0 hcov hlabels, ?_, ?_⟩
  · intro i hi
    exact normalized_ring_norm hp hr1 hR hi
  · intro i hi
    exact normalized_hub_eq hR hi

end N11Formalization.ActualInwardNormalization
#check @N11Formalization.ActualInwardNormalization.normalized_cover
#check @N11Formalization.ActualInwardNormalization.normalized_structure_of_source
#print axioms N11Formalization.ActualInwardNormalization.normalized_cover
#print axioms N11Formalization.ActualInwardNormalization.normalized_circle_caps
#print axioms N11Formalization.ActualInwardNormalization.normalized_structure_of_source
