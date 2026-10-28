import N11Formalization.ActualCapClusterLift
import N11Formalization.ActualOwnershipSwitchWidths
import N11Formalization.ActualSectorAreaEnvelope
import N11Formalization.ActualQ1CoreFans

/-! The true three consecutive owned arcs of an actual ear lie in one
radius-2r circle cap. Their total width, rather than the sum of overlapping
complete cap widths, is bounded. Arbitrary cyclic cut and closed endpoints
are retained. No owned-capacity or large-cap lift is supplied as a premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualEarOwnedWidth

open ActualCoverStructuralReduction ActualBoundaryNineTies ActualOwnershipSwitchWidths
open ActualBoundaryArcFrame ActualBoundaryCyclicOrder ActualBoundaryOverlapAdjacency
open ActualBoundaryOwnershipIntervals ActualCapClusterLift ActualRingDirectionOrder
open ActualEarCapacity ActualQ1CoreFans ActualRingLinkBoundaryData
open ActualFiniteNearestRefinement ActualRefinementTriangleUniqueness
open DSHTopologyInterior ActualMetricAngleAtoms ActualSectorAreaEnvelope

def runIndex (i : Fin 9) : ℕ → Fin 9
  | 0 => i
  | n+1 => nextRing (runIndex i n)

def runShift (i : Fin 9) : ℕ → ℤ
  | 0 => 0
  | n+1 => runShift i n+nextShift (runIndex i n)

def runLift {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℕ → ℝ
  | 0 => (v.tie i).angle
  | n+1 => runLift v i n+switchGap v (runIndex i n)

theorem runIndex_succ (i : Fin 9) (n : ℕ) :
    runIndex i (n+1) = nextRing (runIndex i n) := rfl

theorem runLift_eq {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (i : Fin 9) (n : ℕ) :
    runLift v i n = (v.tie (runIndex i n)).angle+(runShift i n : ℝ)*period := by
  induction n with
  | zero => simp [runLift,runIndex,runShift]
  | succ n ih =>
    rw [runLift,ih,runShift,Int.cast_add,runIndex_succ]
    unfold switchGap nextLift
    ring

theorem run_interval_cap {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50)
    (v : NineTies c r) (i : Fin 9) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc (runLift v i n) (runLift v i (n+1))) :
    dist (circleMap t) (c (ringSite (nextRing (runIndex i n)))) ≤ r := by
  let d : ℝ := (runShift i n : ℝ)*period
  have he : runLift v i (n+1) = nextLift v (runIndex i n)+d := by
    rw [runLift,runLift_eq]
    unfold switchGap
    dsimp [d]
    ring
  have hs : t-d ∈ Set.Icc (v.tie (runIndex i n)).angle (nextLift v (runIndex i n)) := by
    rw [runLift_eq,he] at ht
    dsimp [d] at *
    constructor <;> linarith [ht.1,ht.2]
  have hend := switch_endpoints_mem_weak v (runIndex i n)
  have hc := ActualBoundaryOwnershipIntervals.arc_between hend.1.1 hend.2.1 hs
  have hd := (cap_iff_lift h.cover hr h.labels (nextRing (runIndex i n)) (t-d)).mpr
    ⟨nextShift (runIndex i n),hc⟩
  have hp : circleMap t = circleMap (t-d) := by
    convert circleMap_periodic (t-d) (runShift i n) using 1 <;> dsimp [d] <;> ring
  rwa [hp]

/-- A real interval of length at most3 whose whole image is in the true
large disk is contained in one periodic cap copy. Existence and nonzero
center are produced from an actual point of the interval. -/
theorem short_interval_big_width {p : Point} {r a b : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 19/50) (hab : a ≤ b) (hlen : b-a ≤ 3)
    (hcap : ∀ t ∈ Set.Icc a b, dist (circleMap t) p ≤ 2*r) :
    b-a ≤ 2*Real.arcsin (2*r) := by
  have ha := hcap a ⟨le_rfl,hab⟩
  have hp : p ≠ 0 := by
    intro hz
    rw [hz,dist_zero_right,circleMap_norm] at ha
    linarith
  have hm : ∃ y : Point, ‖y‖=1 ∧ dist y p ≤ 2*r :=
    ⟨circleMap a,circleMap_norm a,ha⟩
  obtain ⟨m,hma⟩ := (big_cap_iff hp hr0 hr hm a).mp ha
  have hw := big_halfWidth_lt hp hr0 hr
  have hsame (t : ℝ) (ht : t ∈ Set.Icc a b) : t ∈ BigArc p r m := by
    obtain ⟨k,hkt⟩ := (big_cap_iff hp hr0 hr hm t).mp (hcap t ht)
    have he : k=m := by
      by_contra hne
      have hn : k+1 ≤ m ∨ m+1 ≤ k := by omega
      change bigMidpoint p+(m : ℝ)*period-capHalfWidth p (2*r) ≤ a ∧
        a ≤ bigMidpoint p+(m : ℝ)*period+capHalfWidth p (2*r) at hma
      change bigMidpoint p+(k : ℝ)*period-capHalfWidth p (2*r) ≤ t ∧
        t ≤ bigMidpoint p+(k : ℝ)*period+capHalfWidth p (2*r) at hkt
      dsimp [period] at hma hkt
      rcases hn with hn | hn
      · have hnR : (k : ℝ)+1 ≤ (m : ℝ) := by exact_mod_cast hn
        nlinarith [hma.1,hma.2,hkt.1,hkt.2,ht.1,ht.2,Real.pi_gt_three]
      · have hnR : (m : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast hn
        nlinarith [hma.1,hma.2,hkt.1,hkt.2,ht.1,ht.2,Real.pi_gt_three]
    rwa [he] at hkt
  have hb := hsame b ⟨hab,le_rfl⟩
  change bigMidpoint p+(m : ℝ)*period-capHalfWidth p (2*r) ≤ a ∧
    a ≤ bigMidpoint p+(m : ℝ)*period+capHalfWidth p (2*r) at hma
  change bigMidpoint p+(m : ℝ)*period-capHalfWidth p (2*r) ≤ b ∧
    b ≤ bigMidpoint p+(m : ℝ)*period+capHalfWidth p (2*r) at hb
  have hs := capHalfWidth_le_arcsin hp (by linarith : 0 ≤ 2*r) (by linarith : 2*r < 1)
  linarith [hma.1,hb.2]

def earGaps (e : Fin 9) : Finset (Fin 9) := {e-2,e-1,e}

theorem ear_gap_owners : ∀ e i : Fin 9,
    i ∈ earGaps e ↔ nextRing i ∈ earSet e := by decide +kernel

theorem ear_gap_card : ∀ e : Fin 9, (earGaps e).card=3 := by decide +kernel

theorem three_run_owners : ∀ (e : Fin 9) (n : Fin 3),
    nextRing (runIndex (e-2) n.val) ∈ earSet e := by decide +kernel

theorem three_run_width_sum {c : Fin 11 → Point} {r : ℝ}
    (v : NineTies c r) (e : Fin 9) :
    (∑ i ∈ earGaps e, switchGap v i) = runLift v (e-2) 3-runLift v (e-2) 0 := by
  have hi : runIndex (e-2) 0=e-2 ∧ runIndex (e-2) 1=e-1 ∧ runIndex (e-2) 2=e := by
    fin_cases e <;> decide
  have hn : e-2 ≠ e-1 ∧ e-2 ≠ e ∧ e-1 ≠ e := by fin_cases e <;> decide
  have hnot : e-2 ∉ ({e-1,e} : Finset (Fin 9)) := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using ⟨hn.1,hn.2.1⟩
  have hnot' : e-1 ∉ ({e} : Finset (Fin 9)) := by
    simpa only [Finset.mem_singleton] using hn.2.2
  simp only [earGaps,Finset.sum_insert hnot,
    Finset.sum_insert hnot',Finset.sum_singleton,
    runLift,hi.1,hi.2.1,hi.2.2]
  ring

theorem three_run_cover {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r) (e : Fin 9)
    {t : ℝ} (ht : t ∈ Set.Icc (runLift v (e-2) 0) (runLift v (e-2) 3)) :
    ∃ n : Fin 3,
      dist (circleMap t) (c (ringSite (nextRing (runIndex (e-2) n.val)))) ≤ r := by
  by_cases h1 : t ≤ runLift v (e-2) 1
  · exact ⟨0,run_interval_cap h hr v (e-2) 0 ⟨ht.1,h1⟩⟩
  · by_cases h2 : t ≤ runLift v (e-2) 2
    · exact ⟨1,run_interval_cap h hr v (e-2) 1 ⟨(lt_of_not_ge h1).le,h2⟩⟩
    · exact ⟨2,run_interval_cap h hr v (e-2) 2 ⟨(lt_of_not_ge h2).le,ht.2⟩⟩

/-- An arbitrary actual common-point ear bounds its three real owned widths. -/
theorem actual_ear_owned_width {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r)
    (e : Fin 9) (he : Ear c r e) :
    (∑ i ∈ earGaps e, switchGap v i) ≤ 2*Real.arcsin (2*r) := by
  obtain ⟨p,hp⟩ := he
  have hpos : 0 ≤ ∑ i ∈ earGaps e, switchGap v i :=
    Finset.sum_nonneg (fun i _ => (actual_switch_gap_positive h hr v i).le)
  have hu (i : Fin 9) : switchGap v i < Real.pi/4 := by
    have hg := actual_switch_gap_le_two_halfWidth v i
    have hh := halfWidth_le_small h.cover hr h.labels (nextRing i)
    linarith
  have hsmall : (∑ i ∈ earGaps e, switchGap v i) ≤ 3 := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ earGaps e) => (hu i).le)
    simp only [Finset.sum_const,ear_gap_card,nsmul_eq_mul,Nat.cast_ofNat] at hs
    linarith [Real.pi_lt_four]
  rw [three_run_width_sum] at hpos hsmall ⊢
  apply short_interval_big_width (Covers.nonneg h.cover) hr (by linarith) hsmall
  intro t ht
  obtain ⟨n,hn⟩ := three_run_cover h hr v e ht
  have hc := hp _ (three_run_owners e n)
  have hd := dist_triangle (circleMap t) (c (ringSite (nextRing (runIndex (e-2) n.val)))) p
  rw [dist_comm (c _) p] at hd
  linarith

theorem EarData.actual_common_point {c : Fin 11 → Point} {r : ℝ}
    {R : Refinement c r} (E : EarData R) : Ear c r E.center := by
  refine ⟨R.witness E.index,?_⟩
  intro j hj
  have hm : ringSite j ∈ labelSet R E.index := by
    rw [E.labels]
    simp only [earSet,Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> simp [prevSite,nextSite,nextRing]
  obtain ⟨s,hs⟩ := mem_labelSet.mp hm
  rw [← hs]
  exact (Refinement.real_triangle R E.index).2.1 s |>.2

def outsideGaps (e : Fin 9) : Finset (Fin 9) := Finset.univ \ earGaps e

theorem outside_gap_card : ∀ e : Fin 9, (outsideGaps e).card=6 := by decide +kernel

theorem actual_ear_outside_width {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r)
    (e : Fin 9) (he : Ear c r e) :
    2*Real.pi-2*Real.arcsin (2*r) ≤ ∑ i ∈ outsideGaps e, switchGap v i := by
  have hc := actual_ear_owned_width h hr v e he
  have hs := Finset.sum_sdiff (f := switchGap v) (Finset.subset_univ (earGaps e))
  rw [actual_switch_gap_sum] at hs
  change (∑ i ∈ outsideGaps e, switchGap v i)+(∑ i ∈ earGaps e, switchGap v i)=2*Real.pi at hs
  linarith only [hc,hs]

theorem actual_ear_outside_envelope {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (v : NineTies c r)
    (e : Fin 9) (he : Ear c r e) :
    2*Real.pi-2*Real.arcsin (19/25) ≤
      ∑ i ∈ outsideGaps e, widthEnvelope (sectorAngle v i) := by
  have hc := actual_ear_outside_width h hr v e he
  have hb := Real.arcsin_le_arcsin (show 2*r ≤ (19/25 : ℝ) by linarith)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ outsideGaps e) =>
    actual_sector_width_envelope h hr v i)
  linarith only [hc,hb,hs]

/-- All six outside-owned arcs and their continuous metric envelope budget
come from the actual selected triangle witness; no cluster-width hypothesis. -/
theorem actual_selected_ear_outside_envelope {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) {R : Refinement c r}
    (v : NineTies c r) (E : EarData R) :
    2*Real.pi-2*Real.arcsin (19/25) ≤
      ∑ i ∈ outsideGaps E.center, widthEnvelope (sectorAngle v i) :=
  actual_ear_outside_envelope h hr v E.center (EarData.actual_common_point E)

end N11Formalization.ActualEarOwnedWidth
#check @N11Formalization.ActualEarOwnedWidth.actual_ear_owned_width
#check @N11Formalization.ActualEarOwnedWidth.EarData.actual_common_point
#check @N11Formalization.ActualEarOwnedWidth.actual_selected_ear_outside_envelope
#print axioms N11Formalization.ActualEarOwnedWidth.short_interval_big_width
#print axioms N11Formalization.ActualEarOwnedWidth.actual_ear_owned_width
#print axioms N11Formalization.ActualEarOwnedWidth.EarData.actual_common_point
#print axioms N11Formalization.ActualEarOwnedWidth.actual_selected_ear_outside_envelope
