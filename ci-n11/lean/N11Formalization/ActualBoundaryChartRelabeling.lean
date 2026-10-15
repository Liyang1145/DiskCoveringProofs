import N11Formalization.ActualBoundaryChart

/-! Arbitrary cyclic cut of the genuine boundary chart.
No fixed-cut canonical0/4 assumption is made. A site permutation may act
freely on the2 hubs, provided its9 ring labels have the given cyclic shift.
All anchors, centers and future33 witnesses undergo the SAME isometries. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualBoundaryChartRelabeling
open ActualRingDirectionOrder ActualBoundaryCyclicOrder ActualBoundaryAnchorWidths
open ActualBoundaryChart SourceChartIsometry ResumeGlobal ResumeNetwork

def shiftY (y : Fin 9 → ℝ) (k : Fin 9) : Fin 9 → ℝ := fun i => y (i+k)

theorem shiftY_nonneg {y : Fin 9 → ℝ} (hy : ∀ i, 0 ≤ y i) (k : Fin 9) :
    ∀ i, 0 ≤ shiftY y k i := fun i => hy (i+k)

theorem shiftY_sum {y : Fin 9 → ℝ} (hy : ∑ i, y i = 1) (k : Fin 9) :
    ∑ i, shiftY y k i = 1 := by
  have he := Equiv.sum_comp (Equiv.addRight k) y
  exact he.trans hy

theorem cell_next_circle {y : Fin 9 → ℝ} (hy : ∑ i, y i = 1) (j : Fin 9) :
    circleMap (cellAngles y (nextRing j)) =
      circleMap (cellAngles y j+width Patch120K5Actual.L Patch120K5Actual.D y j) := by
  have hrec := anchor_succ_sub Patch120K5Actual.L Patch120K5Actual.D y j
  by_cases hj : j = 8
  · subst j
    have h9 := anchor_nine Patch120K5Actual.L Patch120K5Actual.D y hy rfl
    have hz := anchor_zero Patch120K5Actual.L Patch120K5Actual.D y
    have hn : nextRing (8 : Fin 9) = 0 := by decide
    rw [hn]
    change circleMap (anchorAngle _ _ y 0) =
      circleMap (anchorAngle _ _ y 8+width _ _ y 8)
    rw [hz]
    change anchorAngle _ _ y 9-anchorAngle _ _ y 8 = width _ _ y 8 at hrec
    have he : anchorAngle Patch120K5Actual.L Patch120K5Actual.D y 8+
        width Patch120K5Actual.L Patch120K5Actual.D y 8 = 2*Real.pi := by linarith
    rw [he]
    simpa using (circleMap_add_two_pi 0).symm
  · apply congrArg circleMap
    dsimp [cellAngles]
    rw [next_val hj]
    linarith

theorem shifted_circle {y : Fin 9 → ℝ} (hy : ∑ i, y i = 1) (k i : Fin 9) :
    circleMap (cellAngles y k+cellAngles (shiftY y k) i) =
      chartAnchors y (i+k) := by
  have hall (n : ℕ) (hn : n < 9) :
      circleMap (cellAngles y k+anchorAngle Patch120K5Actual.L Patch120K5Actual.D
        (shiftY y k) n) = chartAnchors y ((⟨n,hn⟩ : Fin 9)+k) := by
    induction n with
    | zero => simp [anchor_zero,chartAnchors,cellAngles]
    | succ n ih =>
      have hn0 : n < 9 := by omega
      let j : Fin 9 := ⟨n,hn0⟩
      have hj8 : j ≠ 8 := by
        intro he
        have hv := congrArg (fun q : Fin 9 => q.val) he
        change n = 8 at hv
        omega
      have hnxt : nextRing j = (⟨n+1,hn⟩ : Fin 9) := by
        apply Fin.ext
        exact next_val hj8
      have hrec := anchor_succ_sub Patch120K5Actual.L Patch120K5Actual.D (shiftY y k) j
      change anchorAngle _ _ (shiftY y k) (n+1)-anchorAngle _ _ (shiftY y k) n =
        width Patch120K5Actual.L Patch120K5Actual.D y (j+k) at hrec
      have hp := ih hn0
      change circleMap (cellAngles y k+anchorAngle _ _ (shiftY y k) n) =
        circleMap (cellAngles y (j+k)) at hp
      have hr := congrArg (rotate (width Patch120K5Actual.L Patch120K5Actual.D y (j+k))) hp
      rw [rotate_circle,rotate_circle] at hr
      have hidx : nextRing (j+k) = (⟨n+1,hn⟩ : Fin 9)+k := by
        rw [show nextRing (j+k) = nextRing j+k by
          simp [nextRing,add_assoc,add_comm,add_left_comm],hnxt]
      calc
        circleMap (cellAngles y k+anchorAngle _ _ (shiftY y k) (n+1)) =
          circleMap (width Patch120K5Actual.L Patch120K5Actual.D y (j+k)+
            (cellAngles y k+anchorAngle _ _ (shiftY y k) n)) := by congr 1; linarith
        _ = circleMap (width Patch120K5Actual.L Patch120K5Actual.D y (j+k)+
            cellAngles y (j+k)) := hr
        _ = circleMap (cellAngles y (nextRing (j+k))) := by
          rw [add_comm]
          exact (cell_next_circle hy (j+k)).symm
        _ = chartAnchors y ((⟨n+1,hn⟩ : Fin 9)+k) := by rw [hidx]; rfl
  exact hall i.val i.isLt

theorem shifted_anchor {y : Fin 9 → ℝ} (hy : ∑ i, y i = 1) (k i : Fin 9) :
    rotate (-cellAngles y k) (chartAnchors y (i+k)) = chartAnchors (shiftY y k) i := by
  have he : rotate (cellAngles y k) (chartAnchors (shiftY y k) i) =
      chartAnchors y (i+k) := by
    rw [chartAnchors,rotate_circle]
    exact shifted_circle hy k i
  rw [← he,rotate_inverse]

theorem anchorIndex_shift (i k : Fin 9) (side : Fin 2) :
    anchorIndex (i+k) side = anchorIndex i side+k := by
  fin_cases side <;> simp [anchorIndex]
  abel

def gaugeMap {c : Fin 11 → Point} {r : ℝ} (b : BoundaryChart c r) (k : Fin 9) (p : Point) : Point :=
  rotate (-cellAngles b.y k) (rotation (-anchorLift c r 0) p)

theorem gaugeMap_dist {c : Fin 11 → Point} {r : ℝ}
    (b : BoundaryChart c r) (k : Fin 9) (p q : Point) :
    dist (gaugeMap b k p) (gaugeMap b k q) = dist p q := by
  change dist (rotate _ (rotate _ p)) (rotate _ (rotate _ q)) = dist p q
  rw [rotate_dist,rotate_dist]

/-- All18 rows for ANY canonical cut and either hub permutation. -/
theorem BoundaryChart.shifted_boundary {c : Fin 11 → Point} {r : ℝ}
    (b : BoundaryChart c r) (k : Fin 9) (e : Equiv.Perm (Fin 11))
    (he : ∀ i : Fin 9, e (ringSite i) = ringSite (i+k))
    (i : Fin 9) (side : Fin 2) :
    dist (gaugeMap b k (c (e (ringSite i))))
      (chartAnchors (shiftY b.y k) (anchorIndex i side)) ≤ r := by
  rw [← shifted_anchor b.sum_one k (anchorIndex i side),he]
  change dist (rotate _ (rotation _ _)) (rotate _ _) ≤ r
  rw [rotate_dist]
  have hb := b.boundary (i+k) side
  rw [anchorIndex_shift] at hb
  exact hb

/-- Same-map transmission of canonical33 AFTER their actual production. -/
theorem BoundaryChart.shifted_feasible_of_faces {c : Fin 11 → Point} {r : ℝ}
    (b : BoundaryChart c r) (hr : 0 ≤ r) (k : Fin 9) (e : Equiv.Perm (Fin 11))
    (he : ∀ i : Fin 9, e (ringSite i) = ringSite (i+k))
    (Z : Fin 11 → Point)
    (hf : ∀ f : Fin 11, ∀ v : Fin 3, dist (c (e (face f v))) (Z f) ≤ r) :
    Feasible (chartAnchors (shiftY b.y k))
      (fun i => gaugeMap b k (c (e i))) (fun f => gaugeMap b k (Z f)) r := by
  refine ⟨hr,?_⟩
  intro edge
  rcases edge with ⟨i,side⟩ | ⟨f,v⟩
  · exact BoundaryChart.shifted_boundary b k e he i side
  · change dist (gaugeMap b k _) (gaugeMap b k _) ≤ r
    rw [gaugeMap_dist]
    exact hf f v

end N11Formalization.ActualBoundaryChartRelabeling
#check @N11Formalization.ActualBoundaryChartRelabeling.shifted_anchor
#check @N11Formalization.ActualBoundaryChartRelabeling.BoundaryChart.shifted_feasible_of_faces
#print axioms N11Formalization.ActualBoundaryChartRelabeling.shifted_anchor
#print axioms N11Formalization.ActualBoundaryChartRelabeling.BoundaryChart.shifted_feasible_of_faces
