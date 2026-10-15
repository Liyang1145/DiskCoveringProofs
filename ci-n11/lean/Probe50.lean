import N11Formalization.SourceIdentity

noncomputable section
namespace ProbeSrc

open N11Formalization

-- 复刻 proj 定义（与 SourceLoop 一致）
def projP (p : Point) (i : ℕ) : ℝ := match i with
  | 0 => p.ofLp 0
  | _ => p.ofLp 1

def mkP (x y : ℝ) : Point := !₂[x, y]

example (x y : ℝ) : projP (mkP x y) 0 = x := rfl
example (x y : ℝ) : projP (mkP x y) 1 = y := rfl
example (a : Point) : projP a 0 = a.ofLp 0 := rfl
example (a : Point) : projP a 1 = a.ofLp 1 := rfl
example (a : Point) : projP a 0 = (if 0 = 0 then a.ofLp 0 else a.ofLp 1) := rfl

-- 关键：dist 的平方和形式能否与 projP 形式对上
example (p q : Point) :
    dist p q = Real.sqrt ((projP p 0 - projP q 0) * (projP p 0 - projP q 0)
      + (projP p 1 - projP q 1) * (projP p 1 - projP q 1)) := by
  rw [N11Formalization.dist_point_eq_sqrt]
  congr 1
  ring

end ProbeSrc
