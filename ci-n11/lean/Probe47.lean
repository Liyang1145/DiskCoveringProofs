import N11Formalization.SourceLoop

open N11Formalization

namespace ProbeIsolate

-- 目标 1：sqrt_eq_dist_axis 的重写链
example (x y c : ℝ) :
    Real.sqrt ((x - c) * (x - c) + y * y) = dist (mkPoint (x - c) y) (mkPoint 0 0) := by
  rw [dist_point_eq_sqrt]
  congr 1
  simp [mkPoint]
  ring

example (x y c : ℝ) :
    Real.sqrt ((x - c) * (x - c) + y * y) = dist (mkPoint (x - c) y) (mkPoint 0 0) := by
  rw [dist_point_eq_sqrt]
  have h : ∀ a b : ℝ, (mkPoint a b : Point).ofLp 0 = a := fun _ _ => rfl
  have h' : ∀ a b : ℝ, (mkPoint a b : Point).ofLp 1 = b := fun _ _ => rfl
  rw [h, h', h, h']
  ring

example (a b : ℝ) : dist (mkPoint a b) (mkPoint 0 0)
    = Real.sqrt (a * a + b * b) := by
  rw [dist_point_eq_sqrt]
  congr 1
  rfl

-- 目标 2：泛型桥（用 mkPoint 的坐标投影）
example (a c d : ℝ) :
    Real.sqrt ((a - c) * (a - c) + d * d) = dist (mkPoint (a - c) d) (mkPoint 0 0) := by
  rw [dist_point_eq_sqrt]
  congr 1
  rfl

end ProbeIsolate
