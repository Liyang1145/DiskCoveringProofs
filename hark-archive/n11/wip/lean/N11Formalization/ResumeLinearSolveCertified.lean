import N11Formalization.ResumeLinearSolveIterate

namespace N11Formalization.ResumeLinearSolveCertified
open RatInterval ResumeLinearSolveEnclosure ResumeLinearSolveIterate

def seedBox (q e : ℚ) : RatInterval := ⟨-(e/(1-q)), e/(1-q)⟩

/-- End-to-end solver interface: geometric entry memberships plus finite rational
bounds suffice for an exact unique solution and every refined error enclosure.
The preconditioner and midpoint may be arbitrary proposals. -/
theorem existsUnique_with_refinements {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℚ) (AB : Fin n → Fin n → RatInterval)
    (bB : Fin n → RatInterval) (b : Fin n → ℝ) (y : Fin n → ℚ)
    (q e : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1) (he : 0 ≤ e)
    (hA : ∀ i j, Mem (AB i j) (A i j)) (hb : ∀ i, Mem (bB i) (b i))
    (hrow : ∀ i, ∑ j, max |(krawczykMat C AB i j).lo|
       |(krawczykMat C AB i j).hi| ≤ q)
    (hmag : ∀ i, max |(residualBox C AB bB y i).lo|
       |(residualBox C AB bB y i).hi| ≤ e) :
    ∃ x, A.mulVec x=b ∧ (∀ z, A.mulVec z=b → z=x) ∧
      ∀ k i, Mem (iterBox C AB bB y (fun _ => seedBox q e) k i)
        (x i-(y i : ℝ)) := by
  have hq0r : (0:ℝ) ≤ q := by exact_mod_cast hq0
  have hq1r : (q:ℝ) < 1 := by exact_mod_cast hq1
  have her : (0:ℝ) ≤ e := by exact_mod_cast he
  have hrowr : ∀ i, ∑ j, max |((krawczykMat C AB i j).lo : ℝ)|
       |((krawczykMat C AB i j).hi : ℝ)| ≤ (q:ℝ) := by
    intro i
    exact_mod_cast hrow i
  have hmagr : ∀ i, max |((residualBox C AB bB y i).lo : ℝ)|
       |((residualBox C AB bB y i).hi : ℝ)| ≤ (e:ℝ) := by
    intro i
    exact_mod_cast hmag i
  obtain ⟨x,hx,huniq⟩ := ResumeLinearSolveInterval.existsUnique_of_intervals
    A C AB q hq0r hq1r hA hrowr b
  refine ⟨x,hx,huniq,?_⟩
  apply iter_mem A C AB bB b x y _ hA hb hx
  intro i
  have hi := solution_coordinates A C AB bB b x y q e hq1r her
    (ResumeLinearSolveInterval.residual_bound A C AB q hq0r hA hrowr)
    hA hb hmagr hx i
  change (-((e/(1-q):ℚ):ℝ) ≤ x i-(y i:ℝ)) ∧
    x i-(y i:ℝ) ≤ ((e/(1-q):ℚ):ℝ)
  push_cast
  constructor <;> linarith [hi.1,hi.2]

#print existsUnique_with_refinements
#print axioms existsUnique_with_refinements
end N11Formalization.ResumeLinearSolveCertified
