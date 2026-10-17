import Mathlib

noncomputable section
abbrev Pt : Type := EuclideanSpace ℝ (Fin 2)
def mkP (x y : ℝ) : Pt := !₂[x, y]

theorem dist_pt (p q : Pt) :
    dist p q = Real.sqrt ((p.ofLp 0 - q.ofLp 0) ^ 2 + (p.ofLp 1 - q.ofLp 1) ^ 2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  have h0 : (p - q).ofLp 0 = p.ofLp 0 - q.ofLp 0 := rfl
  have h1 : (p - q).ofLp 1 = p.ofLp 1 - q.ofLp 1 := rfl
  simp only [Fin.sum_univ_two, h0, h1, Real.norm_eq_abs, sq_abs]

-- 关键：mkP 的投影能否在 ring 之前被消掉
example (X Y : ℝ) : dist (mkP X Y) (mkP 0 0) = Real.sqrt (X * X + Y * Y) := by
  rw [dist_pt]
  congr 1
  simp only [mkP]
  ring

example (X Y : ℝ) : dist (mkP X Y) (mkP 0 0) = Real.sqrt (X * X + Y * Y) := by
  rw [dist_pt]
  congr 1
  simp only [mkP, WithLp.ofLp]
  ring

example (X Y : ℝ) : (mkP X Y : Pt).ofLp 0 = X := by simp only [mkP, WithLp.ofLp]
example (X Y : ℝ) : (mkP X Y : Pt).ofLp 1 = Y := by simp only [mkP, WithLp.ofLp]

end
