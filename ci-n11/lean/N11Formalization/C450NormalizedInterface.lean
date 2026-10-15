import N11Formalization.DSHTenBoundaryData
import N11Formalization.DSHTenBoundaryReduce
import N11Formalization.DSHCanonicalRelabel
import N11Formalization.SourceChartIsometry

/-! Source-aligned C450 interface. The hub is normalized only INSIDE the
certificate; an actual isometric rotation transports every original cover.
The36 continuum inequalities remain explicit and are NOT asserted here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NormalizedInterface
open scoped Interval
open MeasureTheory
open SourceChartIsometry

theorem rotate_zero (a : ℝ) : rotate a (0 : Point) = 0 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [rotate]

theorem rotate_norm (a : ℝ) (p : Point) : ‖rotate a p‖ = ‖p‖ := by
  have hd := rotate_dist a p 0
  simpa only [rotate_zero,dist_zero_right] using hd

/-- Includes the zero hub; no genericity or direction premise remains. -/
theorem exists_hub_rotation (p : Point) :
    ∃ a : ℝ, rotate a p = hubPt ‖p‖ := by
  by_cases hp : p = 0
  · refine ⟨0, ?_⟩
    rw [hp,rotate_zero,norm_zero]
    ext i
    fin_cases i <;> simp [hubPt]
  · obtain ⟨phi,hc,hs⟩ := exists_angle_of_point p hp
    have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    have hsq := PinTangentGeometry.norm_sq_coords p
    refine ⟨-phi, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [rotate,hubPt,Real.cos_neg,Real.sin_neg,hc,hs]
    · field_simp
      nlinarith [hsq]
    · field_simp
      ring

theorem inverse_dist (a : ℝ) (x p : Point) :
    dist x (rotate a p) = dist (rotate (-a) x) p := by
  have hd := rotate_dist a (rotate (-a) x) p
  have hi : rotate a (rotate (-a) x) = x := by
    simpa only [neg_neg] using rotate_inverse (-a) x
  rwa [hi] at hd

theorem covers_rotate (a : ℝ) {c : Fin 11 → Point} {r : ℝ}
    (hc : Covers c r) : Covers (fun i => rotate a (c i)) r := by
  intro x hx
  have hx0 : ‖rotate (-a) x‖ ≤ 1 := by
    rw [rotate_norm]
    exact hx
  obtain ⟨i,hi⟩ := hc (rotate (-a) x) hx0
  exact ⟨i,by rw [inverse_dist]; exact hi⟩

theorem meets_rotate (a : ℝ) {c : Fin 11 → Point} {r : ℝ} {i : Fin 11}
    (hc : MeetsCircle c r i) : MeetsCircle (fun j => rotate a (c j)) r i := by
  obtain ⟨x,hx,hd⟩ := hc
  refine ⟨rotate a x, ?_, ?_⟩
  · rw [rotate_norm,hx]
  · rw [rotate_dist]
    exact hd

/-- C450 only in the source's hub=(e,0) frame. The arbitrary-cover bridge
below pays that normalization, rather than asking fixed densities to work
for all hub directions. -/
def NormalizedAtom : Prop :=
  ∀ (c : Fin 11 → Point) (hub : Fin 11) (e : ℝ),
    0 ≤ e → e ≤ 7/50 → c hub = hubPt e →
    (∀ x : Point, ‖x‖ ≤ 1 → ∃ i : Fin 11, dist x (c i) ≤ 19/50) →
    (∀ i : Fin 11, i ≠ hub → MeetsCircle c (19/50) i) →
    (∀ x : Point, ‖x‖ = 1 → ∃ i : Fin 11, i ≠ hub ∧ dist x (c i) ≤ 19/50) →
    False

theorem atom_of_normalized (hn : NormalizedAtom) : C450Atom := by
  intro c hub hcov htouch harc
  obtain ⟨a,ha⟩ := exists_hub_rotation (c hub)
  let d : Fin 11 → Point := fun i => rotate a (c i)
  have hdcov : ∀ x : Point, ‖x‖ ≤ 1 → ∃ i : Fin 11, dist x (d i) ≤ 19/50 :=
    covers_rotate a hcov
  have hdtouch : ∀ i : Fin 11, i ≠ hub → MeetsCircle d (19/50) i := by
    intro i hi
    exact meets_rotate a (htouch i hi)
  have hdarc : ∀ x : Point, ‖x‖ = 1 →
      ∃ i : Fin 11, i ≠ hub ∧ dist x (d i) ≤ 19/50 := by
    intro x hx
    have hx0 : ‖rotate (-a) x‖ = 1 := by rw [rotate_norm,hx]
    obtain ⟨i,hi,hd⟩ := harc (rotate (-a) x) hx0
    refine ⟨i,hi,?_⟩
    change dist x (rotate a (c i)) ≤ 19/50
    rw [inverse_dist]
    exact hd
  exact hn d hub ‖c hub‖ (norm_nonneg _) (hub_offset_le htouch hcov)
    ha hdcov hdtouch hdarc

def PerDiskNormalized (W0 W1 : TrigDensity) (e0 e1 : ℝ) : Prop :=
  ∀ (c : Point) (e : ℝ),
    1-19/50 ≤ ‖c‖ → ‖c‖ ≤ 1+19/50 → 0 ≤ e → e0 ≤ e → e ≤ e1 →
    (∫ theta in (0)..(2*Real.pi),
      if dist (angPt theta) c ≤ (19/50:ℝ) then W0.toFun theta else 0) +
    (∫ theta in (0)..(2*Real.pi),
      if dist (hubPt e+(19/50:ℝ) • angPt theta) c ≤ (19/50:ℝ)
        then W1.toFun theta else 0) <
      (2*Real.pi*W0.a0+2*Real.pi*W1.a0)/10

def SegmentNormalized (s : TenSeg) : Prop :=
  ∀ (h0 : |s.a1|+|s.a2|+|s.a3| ≤ s.a0)
    (h1 : |s.b1|+|s.b2|+|s.b3| ≤ s.b0),
    PerDiskNormalized (s.W0 h0) (s.W1 h1) (s.eLo:ℝ) (s.eHi:ℝ)

structure Certificate where
  segs : List TenSeg
  chain : Chain 0 segs = some (7/50)
  nonneg : ∀ s ∈ segs,
    |s.a1|+|s.a2|+|s.a3| ≤ s.a0 ∧ |s.b1|+|s.b2|+|s.b3| ≤ s.b0
  bound : ∀ s ∈ segs, SegmentNormalized s

theorem Certificate.segs_ne_nil (hc : Certificate) : hc.segs ≠ [] := by
  intro hnil
  have ht := hc.chain
  rw [hnil] at ht
  simp only [Chain] at ht
  norm_num at ht

theorem normalized_of_certificate (hc : Certificate) : NormalizedAtom := by
  intro c hub e he0 hehi hh hcov htouch harc
  have hehiQ : e ≤ (↑(7/50:ℚ):ℝ) := by
    norm_num
    exact hehi
  obtain ⟨s,hs,hslo,hshi⟩ := exists_seg_of_chain hc.segs 0 (7/50)
    hc.chain hc.segs_ne_nil e (by simpa only [Rat.cast_zero] using he0) hehiQ
  obtain ⟨hn0,hn1⟩ := hc.nonneg s hs
  have hW := hc.bound s hs hn0 hn1
  let ring : Fin 10 → Point := fun j => c (hub.succAbove j)
  have hcovD : ∀ x : Point, ‖x‖ ≤ 1 →
      (∃ j : Fin 10, dist x (ring j) ≤ 19/50) ∨ dist x (c hub) ≤ 19/50 := by
    intro x hx
    obtain ⟨i,hi⟩ := hcov x hx
    by_cases him : i = hub
    · exact Or.inr (by rw [← him]; exact hi)
    · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq him
      exact Or.inl ⟨j,by simpa [ring,hj] using hi⟩
  have harcD : ∀ theta : ℝ, ∃ j : Fin 10, dist (angPt theta) (ring j) ≤ 19/50 := by
    intro theta
    obtain ⟨i,hi,hd⟩ := harc (angPt theta) (norm_angPt theta)
    obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi
    exact ⟨j,by simpa [ring,hj] using hd⟩
  have hper : ∀ j : Fin 10,
      (∫ theta in (0)..(2*Real.pi),
        if dist (angPt theta) (ring j) ≤ (19/50:ℝ) then (s.W0 hn0).toFun theta else 0) +
      (∫ theta in (0)..(2*Real.pi),
        if dist (c hub+(19/50:ℝ) • angPt theta) (ring j) ≤ (19/50:ℝ)
          then (s.W1 hn1).toFun theta else 0) <
        (2*Real.pi*(s.W0 hn0).a0+2*Real.pi*(s.W1 hn1).a0)/10 := by
    intro j
    have hm := htouch (hub.succAbove j) (Fin.succAbove_ne hub j)
    have hlo : 1-19/50 ≤ ‖ring j‖ := by
      simpa only [ring] using one_sub_le_norm_of_meetsCircle hm
    have hhi : ‖ring j‖ ≤ 1+19/50 := by
      simpa only [ring] using norm_le_one_add_of_meetsCircle hm
    rw [hh]
    exact hW (ring j) e hlo hhi he0 hslo hshi
  have hmargin : ‖c hub‖+19/50 < 1 := by
    rw [hh,norm_hubPt,abs_of_nonneg he0]
    linarith
  exact c450_capacity_contradiction (s.W0 hn0) (s.W1 hn1) (by norm_num : 0 < 10)
    (by norm_num) hmargin hcovD harcD hper

theorem atom_of_certificate (hc : Certificate) : C450Atom :=
  atom_of_normalized (normalized_of_certificate hc)

/-- All36 source-normalized continuous inequalities, still EXPLICIT/UNPROVED. -/
def SourceObligation : Prop := ∀ s ∈ c450Segs, SegmentNormalized s

def source_certificate (hs : SourceObligation) : Certificate :=
  ⟨c450Segs,c450Segs_chain,c450Segs_nonneg,hs⟩

theorem atom_of_source (hs : SourceObligation) : C450Atom :=
  atom_of_certificate (source_certificate hs)

theorem nine_of_source (hs : SourceObligation) {c : Fin 11 → Point} {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    Fintype.card (BoundaryIdx c r) = 9 := by
  have hroot : SourceExactRoot.sourceRadius < 19/50 :=
    SourceExactRoot.sourceRadius_mem_box.2.trans_lt boxHiCert_six_lt_R0_real
  exact card_boundaryIdx_eq_nine_of_c450 (atom_of_source hs) (Covers.nonneg hc)
    (hr.trans hroot) hc

theorem ringLabels_of_source (hs : SourceObligation) {c : Fin 11 → Point} {r : ℝ}
    (hr : r < SourceExactRoot.sourceRadius) (hc : Covers c r) :
    ∃ p : Equiv.Perm (Fin 11), Covers (fun j => c (p j)) r ∧
      DSHTopologyInterior.RingLabels (fun j => c (p j)) r :=
  DSHTopologyInterior.exists_covers_ringLabels (nine_of_source hs hr hc) hc

end N11Formalization.C450NormalizedInterface
#check @N11Formalization.C450NormalizedInterface.exists_hub_rotation
#check @N11Formalization.C450NormalizedInterface.covers_rotate
#check @N11Formalization.C450NormalizedInterface.atom_of_source
#check @N11Formalization.C450NormalizedInterface.ringLabels_of_source
#print axioms N11Formalization.C450NormalizedInterface.exists_hub_rotation
#print axioms N11Formalization.C450NormalizedInterface.atom_of_source
#print axioms N11Formalization.C450NormalizedInterface.ringLabels_of_source
