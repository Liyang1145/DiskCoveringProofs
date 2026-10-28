import Mathlib

noncomputable section
open Real

abbrev Pt : Type := EuclideanSpace ℝ (Fin 2)

def mkP (x y : ℝ) : Pt := !₂[x, y]

def projX (p : Pt) (i : ℕ) : ℝ := if i = 0 then p.ofLp 0 else p.ofLp 1

theorem dist_pt (p q : Pt) :
    dist p q = Real.sqrt ((p.ofLp 0 - q.ofLp 0) ^ 2 + (p.ofLp 1 - q.ofLp 1) ^ 2) := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  have h0 : (p - q).ofLp 0 = p.ofLp 0 - q.ofLp 0 := rfl
  have h1 : (p - q).ofLp 1 = p.ofLp 1 - q.ofLp 1 := rfl
  simp only [Fin.sum_univ_two, h0, h1, Real.norm_eq_abs, sq_abs]

@[simp] theorem projX_zero (p : Pt) : projX p 0 = p.ofLp 0 := rfl
@[simp] theorem projX_one (p : Pt) : projX p 1 = p.ofLp 1 := rfl

-- 目标：projX 版本的桥
example (x y c : ℝ) :
    Real.sqrt ((projX (mkP (x - c) y) 0 - projX (mkP 0 0) 0)
        * (projX (mkP (x - c) y) 0 - projX (mkP 0 0) 0)
      + (projX (mkP (x - c) y) 1 - projX (mkP 0 0) 1)
        * (projX (mkP (x - c) y) 1 - projX (mkP 0 0) 1)) = dist (mkP (x - c) y) (mkP 0 0) := by
  rw [dist_pt]
  congr 1
  simp only [projX_zero, projX_one]
  ring

-- 泛型版本
example (a c d : ℝ) :
    Real.sqrt ((a - c) * (a - c) + d * d) = dist (mkP (a - c) d) (mkP 0 0) := by
  rw [dist_pt]
  have h0 : (mkP (a - c) d : Pt).ofLp 0 = a - c := rfl
  have h1 : (mkP (a - c) d : Pt).ofLp 1 = d := rfl
  have h2 : (mkP (0:ℝ) 0 : Pt).ofLp 0 = 0 := rfl
  have h3 : (mkP (0:ℝ) 0 : Pt).ofLp 1 = 0 := rfl
  rw [h0, h1, h2, h3]
  congr 1
  ring

end
