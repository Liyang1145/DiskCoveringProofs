import Mathlib

noncomputable section
open Real

abbrev Pt : Type := EuclideanSpace ℝ (Fin 2)

def mkP (x y : ℝ) : Pt := !₂[x, y]

theorem dist_pt (p q : Pt) :
    dist p q = Real.sqrt ((p.ofLp 0 - q.ofLp 0) ^ 2 + (p.ofLp 1 - q.ofLp 1) ^ 2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  have h0 : (p - q).ofLp 0 = p.ofLp 0 - q.ofLp 0 := rfl
  have h1 : (p - q).ofLp 1 = p.ofLp 1 - q.ofLp 1 := rfl
  simp only [Fin.sum_univ_two, h0, h1, Real.norm_eq_abs, sq_abs]

example (p q : Pt) :
    dist p q = Real.sqrt ((p.ofLp 0 - q.ofLp 0) * (p.ofLp 0 - q.ofLp 0)
      + (p.ofLp 1 - q.ofLp 1) * (p.ofLp 1 - q.ofLp 1)) := by
  rw [dist_pt]
  congr 1
  ring

example (x y c : ℝ) :
    Real.sqrt ((x - c) * (x - c) + y * y) = dist (mkP (x - c) y) (mkP 0 0) := by
  rw [dist_pt]
  congr 1
  simp [mkP]
  ring

example (x y c : ℝ) :
    Real.sqrt ((x - c) * (x - c) + y * y) = dist (mkP (x - c) y) (mkP 0 0) := by
  rw [dist_pt]
  have h0 : (mkP (x - c) y : Pt).ofLp 0 = x - c := rfl
  have h1 : (mkP (x - c) y : Pt).ofLp 1 = y := rfl
  have h2 : (mkP (0:ℝ) 0 : Pt).ofLp 0 = 0 := rfl
  have h3 : (mkP (0:ℝ) 0 : Pt).ofLp 1 = 0 := rfl
  rw [h0, h1, h2, h3]
  congr 1
  ring

end
