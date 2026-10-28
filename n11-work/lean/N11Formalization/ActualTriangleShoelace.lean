import N11Formalization.ActualBoundaryChainConservation

/-! Weighted actual integer boundary chain and determinant algebra.
Each genuine positive triangle contributes twice its oriented determinant.
This is the algebraic starting point, not yet a global area identity. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualTriangleShoelace
open ActualTriangleBoundaryChain ActualFiniteNearestRefinement FlashTiling

theorem det2_antisymm (a b : Point) : det2 a b = -det2 b a := by
  unfold det2
  ring

theorem triangle_orient_shoelace (a b k : Point) :
    orient a b k=det2 a b+det2 b k+det2 k a := by
  simp only [orient,det2,PiLp.sub_apply]
  ring

theorem indicator_pair_sum (p q : Fin 11) (w : Fin 11 → Fin 11 → ℝ) :
    (∑ i : Fin 11, ∑ j : Fin 11, (if i=p ∧ j=q then (1 : ℝ) else 0)*w i j)=w p q := by
  simp [ite_and,ite_mul,Finset.sum_ite_irrel]

theorem triangle_boundary_cast (t : Fin 3 → Fin 11) (i j : Fin 11) :
    (triangleBoundary t i j : ℝ) =
      (if i=t 0 ∧ j=t 1 then (1 : ℝ) else 0) +
      (if i=t 1 ∧ j=t 2 then (1 : ℝ) else 0) +
      (if i=t 2 ∧ j=t 0 then (1 : ℝ) else 0) -
      (if j=t 0 ∧ i=t 1 then (1 : ℝ) else 0) -
      (if j=t 1 ∧ i=t 2 then (1 : ℝ) else 0) -
      (if j=t 2 ∧ i=t 0 then (1 : ℝ) else 0) := by
  unfold triangleBoundary
  push_cast
  rfl

theorem triangle_weighted_boundary (t : Fin 3 → Fin 11) (c : Fin 11 → Point) :
    (∑ i : Fin 11, ∑ j : Fin 11,
      (triangleBoundary t i j : ℝ)*det2 (c i) (c j)) =
        2*orient (c (t 0)) (c (t 1)) (c (t 2)) := by
  simp only [triangle_boundary_cast,add_mul,sub_mul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hrev (p q : Fin 11) :
      (∑ i : Fin 11, ∑ j : Fin 11,
        (if j=p ∧ i=q then (1 : ℝ) else 0)*det2 (c i) (c j))=det2 (c q) (c p) := by
    simpa only [and_comm] using indicator_pair_sum q p (fun i j => det2 (c i) (c j))
  rw [indicator_pair_sum,indicator_pair_sum,indicator_pair_sum,hrev,hrev,hrev,
    triangle_orient_shoelace]
  rw [det2_antisymm (c (t 1)) (c (t 0)),det2_antisymm (c (t 2)) (c (t 1)),
    det2_antisymm (c (t 0)) (c (t 2))]
  ring

theorem actual_total_weighted_boundary {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) :
    (∑ i : Fin 11, ∑ j : Fin 11, (total R i j : ℝ)*det2 (c i) (c j)) =
      2*∑ A : R.Index, orient (c (R.labels A 0)) (c (R.labels A 1)) (c (R.labels A 2)) := by
  classical
  unfold total
  simp only [Int.cast_sum,Finset.sum_mul]
  apply Eq.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  simp only [coefficient,triangle_weighted_boundary,Finset.mul_sum]

end N11Formalization.ActualTriangleShoelace
#check @N11Formalization.ActualTriangleShoelace.actual_total_weighted_boundary
#print axioms N11Formalization.ActualTriangleShoelace.triangle_weighted_boundary
#print axioms N11Formalization.ActualTriangleShoelace.actual_total_weighted_boundary
