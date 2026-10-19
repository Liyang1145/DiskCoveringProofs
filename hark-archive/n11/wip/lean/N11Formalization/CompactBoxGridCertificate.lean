import N11Formalization.MetricAreaGridCertificate

/-! Complete anisotropic finite grids on compact boxes of arbitrary finite
dimension. Degenerate zero-width axes and every closed boundary are kept.
Coordinatewise Lipschitz bounds produce a true whole-box upper bound;
no nearest-grid existence or sampled maximum is supplied as a premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.CompactBoxGridCertificate
open MetricAreaGridCertificate

def Box {I : Type*} (U : I → ℝ) : Set (I → ℝ) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) (U i)}

def gridVector {I : Type*} (U : I → ℝ) (N : I → ℕ)
    (k : ∀ i, Fin (N i+1)) : I → ℝ := fun i => gridPoint (U i) (N i) (k i)

theorem gridPoint_mem {U : ℝ} {N : ℕ} (hU : 0 ≤ U) (hN : 0 < N)
    (k : Fin (N+1)) : gridPoint U N k ∈ Set.Icc (0 : ℝ) U := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : k.val ≤ N := by omega
  have hkr : (k.val : ℝ) ≤ N := by exact_mod_cast hk
  unfold gridPoint
  constructor
  · exact div_nonneg (mul_nonneg hU (Nat.cast_nonneg _)) hNr.le
  · apply (div_le_iff₀ hNr).mpr
    exact mul_le_mul_of_nonneg_left hkr hU

theorem gridVector_mem {I : Type*} (U : I → ℝ) (N : I → ℕ)
    (hU : ∀ i, 0 ≤ U i) (hN : ∀ i, 0 < N i)
    (k : ∀ i, Fin (N i+1)) : gridVector U N k ∈ Box U :=
  fun i => gridPoint_mem (hU i) (hN i) (k i)

theorem box_grid_cover {I : Type*} (U : I → ℝ) (N : I → ℕ)
    (hU : ∀ i, 0 ≤ U i) (hN : ∀ i, 0 < N i)
    {x : I → ℝ} (hx : x ∈ Box U) :
    ∃ k : ∀ i, Fin (N i+1), ∀ i, |x i-gridVector U N k i| ≤ U i/(N i : ℝ) := by
  have hc (i : I) : ∃ k : Fin (N i+1),
      |x i-gridPoint (U i) (N i) k| ≤ U i/(N i : ℝ) := by
    by_cases hi : U i=0
    · have hxi : x i=0 := by have hh := hx i; rw [hi] at hh; linarith [hh.1,hh.2]
      refine ⟨⟨0,by omega⟩,?_⟩
      simp [hxi,hi,gridPoint]
    · exact uniform_grid_cover (lt_of_le_of_ne (hU i) (Ne.symm hi)) (hN i) (hx i)
  choose k hk using hc
  exact ⟨k,hk⟩

theorem weighted_box_upper_of_grid {I : Type*} [Fintype I]
    (U L : I → ℝ) (N : I → ℕ)
    (hU : ∀ i, 0 ≤ U i) (hL : ∀ i, 0 ≤ L i) (hN : ∀ i, 0 < N i)
    (f : (I → ℝ) → ℝ) (M : ℝ)
    (hlip : ∀ x ∈ Box U, ∀ y ∈ Box U,
      |f x-f y| ≤ ∑ i : I, L i*|x i-y i|)
    (hnodes : ∀ k : ∀ i, Fin (N i+1), f (gridVector U N k) ≤ M) :
    ∀ x ∈ Box U, f x ≤ M+∑ i : I, L i*U i/(N i : ℝ) := by
  intro x hx
  obtain ⟨k,hk⟩ := box_grid_cover U N hU hN hx
  have hs := hlip x hx (gridVector U N k) (gridVector_mem U N hU hN k)
  have hm : (∑ i : I, L i*|x i-gridVector U N k i|) ≤
      ∑ i : I, L i*U i/(N i : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [← mul_div_assoc] using mul_le_mul_of_nonneg_left (hk i) (hL i)
  have hd := (le_abs_self (f x-f (gridVector U N k))).trans (hs.trans hm)
  linarith only [hd,hnodes k]

end N11Formalization.CompactBoxGridCertificate
#check @N11Formalization.CompactBoxGridCertificate.box_grid_cover
#check @N11Formalization.CompactBoxGridCertificate.weighted_box_upper_of_grid
#print axioms N11Formalization.CompactBoxGridCertificate.box_grid_cover
#print axioms N11Formalization.CompactBoxGridCertificate.weighted_box_upper_of_grid
