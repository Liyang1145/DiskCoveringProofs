import Mathlib

noncomputable section
abbrev Pt : Type := EuclideanSpace ℝ (Fin 2)
def mkP (x y : ℝ) : Pt := !₂[x, y]

-- 哪些引理能化简 (mkP X Y).ofLp 0 ？
example (X Y : ℝ) : (mkP X Y : Pt).ofLp 0 = X := rfl
example (X Y : ℝ) : (mkP X Y : Pt).ofLp 1 = Y := rfl
example (X Y : ℝ) : (mkP X Y : Pt).ofLp 0 = X := by simp [mkP]
example (X Y : ℝ) : (mkP X Y : Pt).ofLp 0 = X := by simp only [mkP]; rfl
example (X Y : ℝ) : (mkP X Y : Pt).ofLp 0 = X := by norm_num [mkP]

-- 用 WithLp
#check @WithLp.ofLp
example (X Y : ℝ) : (mkP X Y : Pt).ofLp 0 = X := by simp [mkP, WithLp.ofLp]

-- 关键的 ite 形态
example (p : Pt) (h : p.ofLp 0 = (5:ℝ)) : (if (0:ℕ) = 0 then p.ofLp 0 else p.ofLp 1) = 5 := by
  simp [h]

end
