import N11Formalization.SourceIdentity

noncomputable section
namespace N11Formalization

open Real

-- ============ 目标：Uvec 与 ULoop 的坐标桥（先做 case k=1 的模型） ============

-- 步骤 1：EuclideanSpace 加法/减法的坐标分配（点式，应 rfl）
example (a b : Point) : (a + b).ofLp 0 = a.ofLp 0 + b.ofLp 0 := rfl
example (a b : Point) : (a - b).ofLp 0 = a.ofLp 0 - b.ofLp 0 := rfl
example (a b : Point) : (a + b).ofLp 1 = a.ofLp 1 + b.ofLp 1 := rfl

-- 步骤 2：mkPoint 的投影
def mkProbe (x y : ℝ) : Point := !₂[x, y]
example (x y : ℝ) : (mkProbe x y : Point).ofLp 0 = x := by
  simp only [mkProbe, Matrix.cons_val_zero, Matrix.cons_val_one]
example (x y : ℝ) : (mkProbe x y : Point).ofLp 1 = y := by
  simp only [mkProbe, Matrix.cons_val_zero, Matrix.cons_val_one]

-- 步骤 3：点相等用坐标 + ext
example (a b : Point) (h0 : a.ofLp 0 = b.ofLp 0) (h1 : a.ofLp 1 = b.ofLp 1) : a = b := by
  ext i <;> fin_cases i <;> simp [h0, h1]

end N11Formalization
