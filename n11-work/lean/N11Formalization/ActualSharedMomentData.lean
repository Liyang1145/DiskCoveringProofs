import N11Formalization.ActualEdgeMetricModel

/-! Genuine first/second shared-side and endpoint-copy moments.
All radii are the original actual circumradii in units `R0=19/50`.
Signed finite masks cancel on true geometry before any compact-box
relaxation. No radius saturation, factor upper bound or numeric class
certificate is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedMomentData

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualFaceCircumradiusAtoms ActualMetricAngleAtoms ActualSharedFactorArea
open ActualSquaredSideMatching ActualEdgeFlagSums ActualEdgeMetricModel
open ActualRefinementDoubleCounting ActualRefinementTriangleUniqueness
open ActualBoundaryNineTies ActualSwitchAtomAggregate ActualBoundarySwitchMetric
open ActualBoundarySwitchAngles ActualSwitchSineAtoms ActualSectorMetricDomain
open ActualRingDirectionOrder ActualRingLinkBoundaryData ActualBoundaryCyclicOrder
open ActualSiteAngleChain ActualOwnershipSwitchWidths
open ActualSwitchBaseAngle ActualOwnedSectorDecomposition

def faceNormalized {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) : ℝ := faceRadius R A / (19 / 50)

def switchNormalized {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) : ℝ :=
  (switchData h hr v k).radius / (19 / 50)

def faceFirst {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : ℝ :=
  faceNormalized R A * Real.sin (faceAngle R A s)

def switchFirst {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) : ℝ :=
  switchNormalized h hr v k * Real.sin (SwitchData.angle (switchData h hr v k))

def faceSecond {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) : ℝ := faceFirst R A s ^ 2

def switchSecond {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) : ℝ :=
  switchFirst h hr v k ^ 2

/-- An orientation-free normalized half-chord on a two-label edge.
The four ordered pairs contribute the distance twice. -/
def sharedFirst (c : Fin 11 → Point) (e : Finset (Fin 11)) : ℝ :=
  (∑ i ∈ e, ∑ j ∈ e, dist (c i) (c j)) / (4 * (19 / 50 : ℝ))

theorem actual_face_normalized_domain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r) (A : R.Index) :
    0 < faceNormalized R A ∧ faceNormalized R A ≤ 1 := by
  have hb := actual_face_radius_bounds h R A
  unfold faceNormalized
  refine ⟨div_pos hb.1 (by norm_num), ?_⟩
  rw [div_le_one₀ (by norm_num : (0 : ℝ) < 19 / 50)]
  exact hb.2.trans hr.le

theorem actual_switch_normalized_domain {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) :
    0 < switchNormalized h hr v k ∧ switchNormalized h hr v k ≤ 1 := by
  exact ⟨div_pos (switchData h hr v k).radius_pos (by norm_num),
    (switchData h hr v k).normalized_radius.2⟩

/-- The paid switch angle is the half-apex at the genuine boundary tie. -/
theorem actual_switch_half_apex {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) :
    SwitchData.angle (switchData h hr v k) =
      EuclideanGeometry.angle (c (nextSite k)) (switchPoint v k) (c (ringSite k)) / 2 := by
  have hn := h.injective.ne (boundary_sites_distinct k).2.1.symm
  have hs := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := c (nextSite k)) (p₂ := c (ringSite k)) (switchPoint v k) hn
  have hb := SwitchData.base_angles (switchData h hr v k) (v.tie k).equidistant
  change EuclideanGeometry.angle (c (nextSite k)) (c (ringSite k)) (switchPoint v k) =
      Real.pi / 2 - SwitchData.angle (switchData h hr v k) ∧
    EuclideanGeometry.angle (c (ringSite k)) (c (nextSite k)) (switchPoint v k) =
      Real.pi / 2 - SwitchData.angle (switchData h hr v k) at hb
  rw [EuclideanGeometry.angle_comm (c (ringSite k)) (switchPoint v k) (c (nextSite k)),
    EuclideanGeometry.angle_comm (switchPoint v k) (c (nextSite k)) (c (ringSite k)),
    hb.1, hb.2] at hs
  linarith

theorem actual_face_normalized_square {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) :
    faceNormalized R A ^ 2 = faceSquaredNormalized R A := rfl

theorem actual_switch_normalized_square {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) :
    switchNormalized h hr v k ^ 2 = switchSquared h hr v k := rfl

theorem actual_face_second_formula {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    faceSecond R A s = faceSquaredNormalized R A * Real.sin (faceAngle R A s) ^ 2 := by
  unfold faceSecond faceFirst
  rw [mul_pow, actual_face_normalized_square]

theorem actual_switch_second_formula {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) :
    switchSecond h hr v k = switchSquared h hr v k *
      Real.sin (SwitchData.angle (switchData h hr v k)) ^ 2 := by
  unfold switchSecond switchFirst
  rw [mul_pow, actual_switch_normalized_square]

theorem shared_first_pair (c : Fin 11 → Point) {i j : Fin 11} (hij : i ≠ j) :
    sharedFirst c {i, j} = halfChord (c i) (c j) / (19 / 50) := by
  unfold sharedFirst halfChord
  simp only [Finset.sum_pair hij, dist_self, dist_comm (c j) (c i), zero_add, add_zero]
  ring

theorem actual_face_first_at_edge {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    faceFirst R A s = sharedFirst c (flagEdge R A s) := by
  have hd : ∀ s : Fin 3, s + 1 ≠ s + 2 := by decide +kernel
  rw [flag_edge_eq_pair, shared_first_pair c ((Refinement.labels_injective R A).ne (hd s))]
  unfold faceFirst faceNormalized halfChord
  rw [actual_face_sine_rule]
  ring

theorem actual_switch_first_at_edge {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) :
    switchFirst h hr v k = sharedFirst c (cycleEdge k) := by
  have hd : ∀ k : Fin 9, ringSite k ≠ nextSite k := by decide +kernel
  rw [cycleEdge, shared_first_pair c (hd k)]
  have hs := SwitchData.chord_sine (switchData h hr v k)
  rw [(switchData h hr v k).chord_exact] at hs
  unfold switchFirst switchNormalized
  calc
    _ = ((switchData h hr v k).radius *
      Real.sin (SwitchData.angle (switchData h hr v k))) / (19 / 50 : ℝ) := by ring
    _ = _ := by rw [hs]

/-- Every true pair of opposite slots shares both moments, even on an
artificial diagonal. No distinct-witness or saturation premise is used. -/
theorem actual_shared_side_moments {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A B : R.Index} {s t : Fin 3} {i j : Fin 11}
    (hs : SideAt R A s i j) (ht : SideAt R B t i j) :
    faceFirst R A s = faceFirst R B t ∧ faceSecond R A s = faceSecond R B t := by
  have hm : faceFirst R A s = faceFirst R B t := by
    rw [actual_face_first_at_edge, actual_face_first_at_edge,
      flag_edge_of_side_at R hs, flag_edge_of_side_at R ht]
  exact ⟨hm, congrArg (fun x : ℝ => x ^ 2) hm⟩

theorem actual_boundary_side_moments {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r)
    (v : NineTies c r) (k : Fin 9) {A : R.Index} {s : Fin 3}
    (hs : SideAt R A s (ringSite k) (nextSite k)) :
    faceFirst R A s = switchFirst h hr v k ∧
      faceSecond R A s = switchSecond h hr v k := by
  have hm : faceFirst R A s = switchFirst h hr v k := by
    rw [actual_face_first_at_edge, actual_switch_first_at_edge, flag_edge_of_side_at R hs]
    rfl
  exact ⟨hm, congrArg (fun x : ℝ => x ^ 2) hm⟩

theorem actual_endpoint_first_copies {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) :
    leftNormalized v k = switchNormalized h hr v k ∧
      rightNormalized v k = switchNormalized h hr v (nextRing k) := by
  have hc := actual_sector_radius_copies h hr v k
  unfold leftNormalized rightNormalized switchNormalized
  rw [hc.1, hc.2]
  exact ⟨rfl, rfl⟩

theorem actual_endpoint_second_copies {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r) (k : Fin 9) :
    leftNormalized v k ^ 2 = switchNormalized h hr v k ^ 2 ∧
      rightNormalized v k ^ 2 = switchNormalized h hr v (nextRing k) ^ 2 := by
  have hc := actual_endpoint_first_copies h hr v k
  exact ⟨congrArg (fun x : ℝ => x ^ 2) hc.1, congrArg (fun x : ℝ => x ^ 2) hc.2⟩

/-- Pure finite incidence condition on signed coefficients. It asserts no
metric identity, field value, energy or factor bound. -/
def MaskBalanced {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (f : R.Index → Fin 3 → ℝ) (g : Fin 9 → ℝ) : Prop :=
  ∀ e ∈ edges R, edgeSum R f e + switchSum g e = 0

theorem edge_sum_common_factor {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (f : R.Index → Fin 3 → ℝ)
    (F : Finset (Fin 11) → ℝ) (e : Finset (Fin 11)) :
    edgeSum R (fun A s => f A s * F (flagEdge R A s)) e = edgeSum R f e * F e := by
  classical
  unfold edgeSum
  calc
    _ = ∑ p ∈ edgeFlags R e, f p.1 p.2 * F e := by
      apply Finset.sum_congr rfl
      intro p hp
      change f p.1 p.2 * F (flagEdge R p.1 p.2) = _
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := by rw [Finset.sum_mul]

theorem switch_sum_common_factor (g : Fin 9 → ℝ)
    (F : Finset (Fin 11) → ℝ) (e : Finset (Fin 11)) :
    switchSum (fun k => g k * F (cycleEdge k)) e = switchSum g e * F e := by
  classical
  unfold switchSum
  calc
    _ = ∑ k : Fin 9, (if cycleEdge k = e then g k else 0) * F e := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : cycleEdge k = e <;> simp [hk]
    _ = _ := by rw [Finset.sum_mul]

/-- A balanced signed mask cancels any common-edge function of the true
first moment. In particular this pays simultaneous first/squared moment
polynomials before decoupling the factors into compact boxes. -/
theorem actual_side_function_cancellation {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r) (v : NineTies c r)
    (f : R.Index → Fin 3 → ℝ) (g : Fin 9 → ℝ) (hm : MaskBalanced R f g)
    (P : Finset (Fin 11) → ℝ → ℝ) :
    (∑ A : R.Index, ∑ s : Fin 3, f A s * P (flagEdge R A s) (faceFirst R A s)) +
      (∑ k : Fin 9, g k * P (cycleEdge k) (switchFirst h hr v k)) = 0 := by
  classical
  simp_rw [actual_face_first_at_edge, actual_switch_first_at_edge]
  rw [← sum_edge_sum R (fun A s => f A s * P (flagEdge R A s) (sharedFirst c (flagEdge R A s))),
    ← sum_switch_sum h hr R (fun k => g k * P (cycleEdge k) (sharedFirst c (cycleEdge k))),
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro e he
  rw [edge_sum_common_factor R f (fun e => P e (sharedFirst c e)) e,
    switch_sum_common_factor g (fun e => P e (sharedFirst c e)) e,
    ← add_mul, hm e he, zero_mul]

theorem actual_side_moment_cancellation {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (R : Refinement c r) (v : NineTies c r)
    (f : R.Index → Fin 3 → ℝ) (g : Fin 9 → ℝ) (hm : MaskBalanced R f g)
    (betaFirst betaSecond : Finset (Fin 11) → ℝ) :
    (∑ A : R.Index, ∑ s : Fin 3, f A s *
      (betaFirst (flagEdge R A s) * faceFirst R A s +
        betaSecond (flagEdge R A s) * faceSecond R A s)) +
      (∑ k : Fin 9, g k * (betaFirst (cycleEdge k) * switchFirst h hr v k +
        betaSecond (cycleEdge k) * switchSecond h hr v k)) = 0 :=
  actual_side_function_cancellation h hr R v f g hm
    (fun e x => betaFirst e * x + betaSecond e * x ^ 2)

theorem actual_copy_function_cancellation {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r)
    (L T : Fin 9 → ℝ → ℝ) :
    (∑ k : Fin 9, (L k (switchNormalized h hr v k) +
      T k (switchNormalized h hr v (nextRing k)))) -
      (∑ k : Fin 9, (L k (leftNormalized v k) + T k (rightNormalized v k))) = 0 := by
  have he (k : Fin 9) : L k (switchNormalized h hr v k) +
      T k (switchNormalized h hr v (nextRing k)) =
        L k (leftNormalized v k) + T k (rightNormalized v k) := by
    rw [(actual_endpoint_first_copies h hr v k).1, (actual_endpoint_first_copies h hr v k).2]
  simp_rw [he]
  exact sub_self _

theorem actual_copy_moment_cancellation {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19 / 50) (v : NineTies c r)
    (leftFirst leftSecond rightFirst rightSecond : Fin 9 → ℝ) :
    (∑ k : Fin 9, (leftFirst k * switchNormalized h hr v k +
      leftSecond k * switchNormalized h hr v k ^ 2 +
      rightFirst k * switchNormalized h hr v (nextRing k) +
      rightSecond k * switchNormalized h hr v (nextRing k) ^ 2)) -
      (∑ k : Fin 9, (leftFirst k * leftNormalized v k + leftSecond k * leftNormalized v k ^ 2 +
        rightFirst k * rightNormalized v k + rightSecond k * rightNormalized v k ^ 2)) = 0 := by
  have hc := actual_copy_function_cancellation h hr v
    (fun k x => leftFirst k * x + leftSecond k * x ^ 2)
    (fun k x => rightFirst k * x + rightSecond k * x ^ 2)
  simpa only [add_assoc] using hc

end N11Formalization.ActualSharedMomentData

#check @N11Formalization.ActualSharedMomentData.actual_shared_side_moments
#check @N11Formalization.ActualSharedMomentData.actual_side_moment_cancellation
#check @N11Formalization.ActualSharedMomentData.actual_copy_moment_cancellation
#print axioms N11Formalization.ActualSharedMomentData.actual_face_first_at_edge
#print axioms N11Formalization.ActualSharedMomentData.actual_switch_half_apex
#print axioms N11Formalization.ActualSharedMomentData.actual_face_normalized_domain
#print axioms N11Formalization.ActualSharedMomentData.actual_switch_normalized_domain
#print axioms N11Formalization.ActualSharedMomentData.actual_switch_first_at_edge
#print axioms N11Formalization.ActualSharedMomentData.actual_shared_side_moments
#print axioms N11Formalization.ActualSharedMomentData.actual_boundary_side_moments
#print axioms N11Formalization.ActualSharedMomentData.actual_endpoint_first_copies
#print axioms N11Formalization.ActualSharedMomentData.actual_endpoint_second_copies
#print axioms N11Formalization.ActualSharedMomentData.actual_side_function_cancellation
#print axioms N11Formalization.ActualSharedMomentData.actual_side_moment_cancellation
#print axioms N11Formalization.ActualSharedMomentData.actual_copy_function_cancellation
#print axioms N11Formalization.ActualSharedMomentData.actual_copy_moment_cancellation
