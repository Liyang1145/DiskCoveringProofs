import N11Formalization.CoverDensity
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
namespace N11Formalization.PolynomialGeneric
open N11Formalization

/-- A nonzero real polynomial cannot vanish on an entire open rational/real box. -/
theorem exists_nonzero_in_box {σ : Type*} (p : MvPolynomial σ ℝ) (hp : p ≠ 0)
    (a b : σ → ℝ) (hab : ∀ j, a j < b j) :
    ∃ q : σ → ℝ, (∀ j, q j ∈ Set.Ioo (a j) (b j)) ∧ MvPolynomial.eval q p ≠ 0 := by
  classical
  by_contra hn
  apply hp
  apply MvPolynomial.funext_set (fun j => Set.Ioo (a j) (b j))
    (fun j => Set.Ioo_infinite (hab j))
  intro q hq
  have hq' : ∀ j, q j ∈ Set.Ioo (a j) (b j) := fun j => hq j (Set.mem_univ j)
  have hz : MvPolynomial.eval q p = 0 := by
    by_contra h
    exact hn ⟨q, hq', h⟩
  simpa using hz

abbrev Coord := Fin 11 × Fin 2

def coordinates (c : Fin 11 → Point) : Coord → ℝ := fun j => (c j.1).ofLp j.2

def centers (q : Coord → ℝ) : Fin 11 → Point :=
  fun i => WithLp.toLp 2 (fun j => q (i, j))

theorem centers_close {c : Fin 11 → Point} {q : Coord → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hclose : ∀ j, |q j - coordinates c j| < ε / 2) : dist c (centers q) < ε := by
  apply (dist_pi_lt_iff hε).mpr
  intro i
  rw [dist_eq_norm]
  have h0 := hclose (i, 0)
  have h1 := hclose (i, 1)
  have hs0 : ((c i).ofLp 0 - q (i, 0)) ^ 2 < (ε / 2) ^ 2 := by
    have h := (abs_lt.mp h0)
    dsimp [coordinates] at h
    nlinarith
  have hs1 : ((c i).ofLp 1 - q (i, 1)) ^ 2 < (ε / 2) ^ 2 := by
    have h := (abs_lt.mp h1)
    dsimp [coordinates] at h
    nlinarith
  have hn : ‖c i - centers q i‖ ^ 2 =
      ((c i).ofLp 0 - q (i, 0)) ^ 2 + ((c i).ofLp 1 - q (i, 1)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp [centers, Real.norm_eq_abs, sq_abs]
  have hs : ‖c i - centers q i‖ ^ 2 < ε ^ 2 := by
    rw [hn]
    nlinarith [sq_pos_of_pos hε]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hs

/-- One small perturbation avoids every zero-set in a finite nonzero polynomial family.
This is not a presumed 'general position': each actual excluded degeneracy must be
bound to a polynomial and its nonzero premise proved by the caller. -/
theorem exists_centers_avoiding {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial Coord ℝ) (hp : ∀ l, p l ≠ 0)
    (c : Fin 11 → Point) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : Fin 11 → Point, dist c d < ε ∧
      ∀ l, MvPolynomial.eval (coordinates d) (p l) ≠ 0 := by
  classical
  let P : MvPolynomial Coord ℝ := ∏ l, p l
  have hP : P ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun l _ => hp l)
  obtain ⟨q, hq, he⟩ := exists_nonzero_in_box P hP
    (fun j => coordinates c j - ε / 2) (fun j => coordinates c j + ε / 2)
    (fun j => by linarith)
  have hclose : ∀ j, |q j - coordinates c j| < ε / 2 := by
    intro j
    exact abs_lt.mpr ⟨by linarith [(hq j).1], by linarith [(hq j).2]⟩
  refine ⟨centers q, centers_close hε hclose, ?_⟩
  have hcoords : coordinates (centers q) = q := by
    funext j
    rfl
  rw [hcoords]
  have hprod : (∏ l, MvPolynomial.eval q (p l)) ≠ 0 := by
    simpa [P, map_prod] using he
  exact fun l => Finset.prod_ne_zero_iff.mp hprod l (Finset.mem_univ l)

theorem dense_avoiding_polynomials {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial Coord ℝ) (hp : ∀ l, p l ≠ 0) :
    Dense {d : Fin 11 → Point | ∀ l, MvPolynomial.eval (coordinates d) (p l) ≠ 0} := by
  intro c
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨d, hd, hgood⟩ := exists_centers_avoiding p hp c ε hε
  exact ⟨d, hgood, hd⟩

/-- Real lower-bound consumer: zero-length/coincidence/collinear/cocircular classes
can all be removed together once represented by nonzero polynomials. -/
theorem lower_bound_of_polynomial_generic {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial Coord ℝ) (hp : ∀ l, p l ≠ 0) (R r0 : ℝ) (hR0 : R ≤ r0)
    (hgood : ∀ (r : ℝ) (c : Fin 11 → Point),
      (∀ l, MvPolynomial.eval (coordinates c) (p l) ≠ 0) →
      0 ≤ r → r < r0 → Covers c r → R ≤ r)
    (r : ℝ) (c : Fin 11 → Point) (hr : 0 ≤ r) (hc : Covers c r) : R ≤ r :=
  CoverDensity.lower_bound_of_dense_class _ (dense_avoiding_polynomials p hp)
    R r0 hR0 hgood r c hr hc

end N11Formalization.PolynomialGeneric
#print N11Formalization.PolynomialGeneric.exists_nonzero_in_box
#print N11Formalization.PolynomialGeneric.exists_centers_avoiding
#print N11Formalization.PolynomialGeneric.lower_bound_of_polynomial_generic
#print axioms N11Formalization.PolynomialGeneric.exists_nonzero_in_box
#print axioms N11Formalization.PolynomialGeneric.exists_centers_avoiding
#print axioms N11Formalization.PolynomialGeneric.dense_avoiding_polynomials
#print axioms N11Formalization.PolynomialGeneric.lower_bound_of_polynomial_generic
