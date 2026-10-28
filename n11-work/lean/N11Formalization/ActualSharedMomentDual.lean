import N11Formalization.ActualSharedMomentData
import N11Formalization.MetricSectorCompactRegularity

/-! Signed first/second moment weak dual on the genuine three-family
factor model. Station equations, area, shared sides, endpoint copies and
the complete owned width are produced from actual geometry. Only finite
coefficient incidence and full-domain factor upper bounds are inputs. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedMomentDual
open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualSharedMomentData ActualEdgeMetricModel
open ActualEdgeFlagSums ActualRefinementDoubleCounting ActualSiteAngleChain
open ActualRingAngleClosure ActualHubOneTurn ActualMetricAngleAtoms
open ActualRingLinkBoundaryData ActualRingDirectionOrder ActualBoundaryCyclicOrder
open ActualBoundarySwitchAngles ActualSwitchAtomAggregate ActualSharedFactorArea
open ActualSectorMetricDomain ActualOwnershipSwitchWidths ActualFaceCircumradiusAtoms

structure Coefficients {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) where
  mu : Fin 11 → ℝ
  faceMask : R.Index → Fin 3 → ℝ
  switchMask : Fin 9 → ℝ
  sideFirst : Finset (Fin 11) → ℝ
  sideSecond : Finset (Fin 11) → ℝ
  leftFirst : Fin 9 → ℝ
  leftSecond : Fin 9 → ℝ
  rightFirst : Fin 9 → ℝ
  rightSecond : Fin 9 → ℝ
  width : ℝ

def stationConstant (mu : Fin 11 → ℝ) : ℝ :=
  ∑ i : Fin 11, mu i * (if i.val < 9 then Real.pi else 2*Real.pi)

theorem actual_station_row {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (i : Fin 11) :
    siteFaceSum R i + (∑ k : Fin 9, if nextSite k=i then sectorAngle v k else 0) -
      (∑ k : Fin 9, if i ∈ cycleEdge k then SwitchData.angle (switchData h hr v k) else 0) =
        if i.val < 9 then Real.pi else 2*Real.pi := by
  classical
  rcases site_owner_or_hub i with ⟨k,rfl⟩ | hi
  · have hk : (nextSite k).val < 9 := (nextRing k).isLt
    simp only [owner_site_injective.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,if_true,hk]
    rw [ring_switch_row]
    linarith [actual_ring_angle_closure h hr R v k]
  · have hn : ¬ i.val < 9 := by omega
    simp only [owner_not_hub i hi,if_false,Finset.sum_const_zero,add_zero,
      cycle_edge_hub_not_mem i hi,hn,sub_zero]
    exact actual_hub_angle_sum h hr R i hi

theorem actual_weighted_station_balance {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (mu : Fin 11 → ℝ) :
    (∑ A : R.Index, ∑ s : Fin 3, mu (R.labels A s)*faceAngle R A s) +
      (∑ k : Fin 9, mu (nextSite k)*sectorAngle v k) -
      (∑ k : Fin 9, (∑ i ∈ cycleEdge k, mu i)*SwitchData.angle (switchData h hr v k)) =
        stationConstant mu := by
  classical
  have hf : (∑ i : Fin 11, mu i*siteFaceSum R i) =
      ∑ A : R.Index, ∑ s : Fin 3, mu (R.labels A s)*faceAngle R A s := by
    simp only [siteFaceSum,Finset.mul_sum,mul_ite,mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    rw [Finset.sum_comm]
    simp [eq_comm]
  have hs : (∑ i : Fin 11, mu i*(∑ k : Fin 9,
      if nextSite k=i then sectorAngle v k else 0)) =
      ∑ k : Fin 9, mu (nextSite k)*sectorAngle v k := by
    simp only [Finset.mul_sum,mul_ite,mul_zero]
    rw [Finset.sum_comm]
    simp [eq_comm]
  have hb : (∑ i : Fin 11, mu i*(∑ k : Fin 9,
      if i ∈ cycleEdge k then SwitchData.angle (switchData h hr v k) else 0)) =
      ∑ k : Fin 9, (∑ i ∈ cycleEdge k, mu i)*SwitchData.angle (switchData h hr v k) := by
    simp only [Finset.mul_sum,mul_ite,mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_filter]
    simp [Finset.sum_mul]
  have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
    congrArg (fun x : ℝ => mu i*x) (actual_station_row h hr R v i))
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  rw [hf,hs,hb] at hh
  exact hh

theorem right_copy_reindex (d y : Fin 9 → ℝ) :
    (∑ k : Fin 9, d (k-1)*y k) = ∑ k : Fin 9, d k*y (nextRing k) := by
  have hh := Equiv.sum_comp (Equiv.addRight (1 : Fin 9)) (fun k => d (k-1)*y k)
  simpa only [Equiv.coe_addRight,add_sub_cancel_right,nextRing] using hh.symm

def faceFactor {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (A : R.Index) (a : Fin 3 → ℝ) (y : ℝ) : ℝ :=
  2*(19/50 : ℝ)^2*y^2*Real.sin (a 0)*Real.sin (a 1)*Real.sin (a 2) -
    (∑ s : Fin 3, D.mu (R.labels A s)*a s) +
    ∑ s : Fin 3, D.faceMask A s*(D.sideFirst (flagEdge R A s)*(y*Real.sin (a s)) +
      D.sideSecond (flagEdge R A s)*(y*Real.sin (a s))^2)

def switchFactor {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (k : Fin 9) (b y : ℝ) : ℝ :=
  (19/50 : ℝ)^2*y^2*Real.sin (2*b)/2 + (∑ i ∈ cycleEdge k, D.mu i)*b +
    D.switchMask k*(D.sideFirst (cycleEdge k)*(y*Real.sin b) +
      D.sideSecond (cycleEdge k)*(y*Real.sin b)^2) +
    (D.leftFirst k+D.rightFirst (k-1))*y + (D.leftSecond k+D.rightSecond (k-1))*y^2

def sectorFactor {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : Coefficients R) (k : Fin 9) (a u v : ℝ) : ℝ :=
  MetricSectorCompactRegularity.sectorFactor a u v +
    D.width*MetricSectorCompactRegularity.sectorWidth a u v-D.mu (nextSite k)*a -
    D.leftFirst k*u-D.leftSecond k*u^2-D.rightFirst k*v-D.rightSecond k*v^2

theorem actual_moment_factor_sum {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (D : Coefficients R)
    (hm : MaskBalanced R D.faceMask D.switchMask) :
    (∑ A : R.Index, faceFactor D A (faceAngle R A) (faceNormalized R A)) +
      (∑ k : Fin 9, switchFactor D k (SwitchData.angle (switchData h hr v k))
        (switchNormalized h hr v k)) +
      (∑ k : Fin 9, sectorFactor D k (sectorAngle v k) (leftNormalized v k) (rightNormalized v k)) =
      Real.pi-stationConstant D.mu+2*Real.pi*D.width := by
  have ha := actual_shared_factor_area h hr R v
  have hb := actual_weighted_station_balance h hr R v D.mu
  have hmom := actual_side_moment_cancellation h hr R v D.faceMask D.switchMask hm
    D.sideFirst D.sideSecond
  have hc := actual_copy_moment_cancellation h hr v D.leftFirst D.leftSecond D.rightFirst D.rightSecond
  have hw := actual_switch_gap_sum v
  have h1 := right_copy_reindex D.rightFirst (switchNormalized h hr v)
  have h2 := right_copy_reindex D.rightSecond (fun k => switchNormalized h hr v k^2)
  have hf (A : R.Index) : faceFactor D A (faceAngle R A) (faceNormalized R A) =
      faceArea R A-(∑ s : Fin 3, D.mu (R.labels A s)*faceAngle R A s) +
      ∑ s : Fin 3, D.faceMask A s*(D.sideFirst (flagEdge R A s)*faceFirst R A s +
        D.sideSecond (flagEdge R A s)*faceSecond R A s) := rfl
  have hs (k : Fin 9) : switchFactor D k (SwitchData.angle (switchData h hr v k))
      (switchNormalized h hr v k) = switchArea h hr v k +
      (∑ i ∈ cycleEdge k, D.mu i)*SwitchData.angle (switchData h hr v k) +
      D.switchMask k*(D.sideFirst (cycleEdge k)*switchFirst h hr v k +
        D.sideSecond (cycleEdge k)*switchSecond h hr v k) +
      (D.leftFirst k+D.rightFirst (k-1))*switchNormalized h hr v k +
      (D.leftSecond k+D.rightSecond (k-1))*switchNormalized h hr v k^2 := rfl
  have ht (k : Fin 9) : sectorFactor D k (sectorAngle v k) (leftNormalized v k) (rightNormalized v k) =
      sectorArea v k+D.width*switchGap v k-D.mu (nextSite k)*sectorAngle v k -
      D.leftFirst k*leftNormalized v k-D.leftSecond k*leftNormalized v k^2 -
      D.rightFirst k*rightNormalized v k-D.rightSecond k*rightNormalized v k^2 := by
    unfold sectorFactor
    rw [← (MetricSectorCompactRegularity.actual_sector_compact_factors h hr v k).1,
      ← (MetricSectorCompactRegularity.actual_sector_compact_factors h hr v k).2]
  simp_rw [hf,hs,ht]
  simp only [add_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib] at hc ⊢
  rw [h1,h2,← Finset.mul_sum,hw]
  linarith only [ha,hb,hmom,hc]

theorem exclude_of_full_domain_moment_certificate {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (D : Coefficients R)
    (hm : MaskBalanced R D.faceMask D.switchMask)
    (faceMax : R.Index → ℝ) (switchMax sectorMax : Fin 9 → ℝ)
    (hf : ∀ (A : R.Index) (a : Fin 3 → ℝ),
      (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1, faceFactor D A a y ≤ faceMax A)
    (hs : ∀ (k : Fin 9) (b : ℝ), b ∈ Set.Icc (0 : ℝ) (Real.pi/2) →
      ∀ y ∈ Set.Icc (0 : ℝ) 1, switchFactor D k b y ≤ switchMax k)
    (ht : ∀ (k : Fin 9) (a : ℝ), a ∈ Set.Icc (0 : ℝ) Real.pi →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1,
      sectorFactor D k a u w ≤ sectorMax k)
    (hstrict : stationConstant D.mu-2*Real.pi*D.width+
      (∑ A : R.Index, faceMax A)+(∑ k : Fin 9, switchMax k)+(∑ k : Fin 9, sectorMax k) < Real.pi) :
    False := by
  have hsum := actual_moment_factor_sum h hr R v D hm
  have hface := Finset.sum_le_sum (s := Finset.univ) (fun A _ => hf A (faceAngle R A)
    (fun s => ⟨(actual_face_angle_strict R A s).1.le,(actual_face_angle_strict R A s).2.le⟩)
    (actual_face_angle_sum h R A) (faceNormalized R A)
    ⟨(actual_face_normalized_domain h hr R A).1.le,(actual_face_normalized_domain h hr R A).2⟩)
  have hswitch := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hs k
    (SwitchData.angle (switchData h hr v k))
    ⟨(SwitchData.angle_bounds (switchData h hr v k)).1.le,
      (SwitchData.angle_bounds (switchData h hr v k)).2.le⟩
    (switchNormalized h hr v k)
    ⟨(actual_switch_normalized_domain h hr v k).1.le,(actual_switch_normalized_domain h hr v k).2⟩)
  have hsector := Finset.sum_le_sum (s := Finset.univ) (fun k _ => ht k (sectorAngle v k)
    (actual_sector_angle_bounds v k) (leftNormalized v k)
    ⟨(actual_normalized_endpoint_domain h hr v k).1.le,
      (actual_normalized_endpoint_domain h hr v k).2.1⟩ (rightNormalized v k)
    ⟨(actual_normalized_endpoint_domain h hr v k).2.2.1.le,
      (actual_normalized_endpoint_domain h hr v k).2.2.2⟩)
  linarith only [hsum,hface,hswitch,hsector,hstrict]

end N11Formalization.ActualSharedMomentDual
#check @N11Formalization.ActualSharedMomentDual.actual_weighted_station_balance
#check @N11Formalization.ActualSharedMomentDual.actual_moment_factor_sum
#check @N11Formalization.ActualSharedMomentDual.exclude_of_full_domain_moment_certificate
#print axioms N11Formalization.ActualSharedMomentDual.actual_weighted_station_balance
#print axioms N11Formalization.ActualSharedMomentDual.actual_moment_factor_sum
#print axioms N11Formalization.ActualSharedMomentDual.exclude_of_full_domain_moment_certificate
