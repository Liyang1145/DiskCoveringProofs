import Mathlib
import N11Formalization.Definitions

/-!
ResumeAttainmentTriangle —— 精确三角形覆盖引理（无余量，紧等号允许）。
若 a,b,c 与点 O 等距 R（O 为外心），p 为 a,b,c 的凸组合，则 min_v dist p v ≤ R。
证明：Σλ_v‖p−v‖² = R² − ‖p−O‖² ≤ R²（重心恒等式）。
这是 C892 Delaunay 面覆盖路线的承重核：每个活跃面外接半径 = R*，面内点被精确覆盖。
-/

namespace N11Formalization.ResumeAttainment

/-- 标量核：坐标形式。 -/
theorem tri_scalar (a0 a1 b0 b1 c0 c1 o0 o1 R la lb lc : ℝ)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc) (hs : la + lb + lc = 1)
    (ha : (a0 - o0) ^ 2 + (a1 - o1) ^ 2 = R ^ 2)
    (hb : (b0 - o0) ^ 2 + (b1 - o1) ^ 2 = R ^ 2)
    (hc : (c0 - o0) ^ 2 + (c1 - o1) ^ 2 = R ^ 2) :
    let p0 := la * a0 + lb * b0 + lc * c0
    let p1 := la * a1 + lb * b1 + lc * c1
    la * ((p0 - a0) ^ 2 + (p1 - a1) ^ 2) + lb * ((p0 - b0) ^ 2 + (p1 - b1) ^ 2)
      + lc * ((p0 - c0) ^ 2 + (p1 - c1) ^ 2)
      = R ^ 2 - ((p0 - o0) ^ 2 + (p1 - o1) ^ 2) := by
  intro p0 p1
  have hc' : lc = 1 - la - lb := by linarith
  subst hc'
  simp only [p0, p1]
  linear_combination la * ha + lb * hb + (1 - la - lb) * hc

/-- 三者之一 ≤ R（平方形式）。 -/
theorem tri_min_sq (da db dc la lb lc R2 : ℝ)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc) (hs : la + lb + lc = 1)
    (h : la * da + lb * db + lc * dc ≤ R2) : da ≤ R2 ∨ db ≤ R2 ∨ dc ≤ R2 := by
  by_contra hn
  simp only [not_or, not_le] at hn
  obtain ⟨h1, h2, h3⟩ := hn
  have e1 : la * R2 ≤ la * da := mul_le_mul_of_nonneg_left h1.le hla
  have e2 : lb * R2 ≤ lb * db := mul_le_mul_of_nonneg_left h2.le hlb
  have e3 : lc * R2 ≤ lc * dc := mul_le_mul_of_nonneg_left h3.le hlc
  have hR : R2 = la * R2 + lb * R2 + lc * R2 := by
    rw [← add_mul, ← add_mul, hs, one_mul]
  -- 至少一个 λ 严格正，则对应不等式严格
  rcases lt_or_eq_of_le hla with hpa | hza
  · have := mul_lt_mul_of_pos_left h1 hpa; linarith
  rcases lt_or_eq_of_le hlb with hpb | hzb
  · have := mul_lt_mul_of_pos_left h2 hpb; linarith
  have hpc : 0 < lc := by linarith
  have := mul_lt_mul_of_pos_left h3 hpc; linarith

/-- **精确三角形覆盖（坐标版）**：外接圆半径 R 的三角形内每点离某顶点 ≤ R（平方）。 -/
theorem tri_cover_sq (a0 a1 b0 b1 c0 c1 o0 o1 R la lb lc : ℝ)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc) (hs : la + lb + lc = 1)
    (ha : (a0 - o0) ^ 2 + (a1 - o1) ^ 2 = R ^ 2)
    (hb : (b0 - o0) ^ 2 + (b1 - o1) ^ 2 = R ^ 2)
    (hc : (c0 - o0) ^ 2 + (c1 - o1) ^ 2 = R ^ 2) :
    let p0 := la * a0 + lb * b0 + lc * c0
    let p1 := la * a1 + lb * b1 + lc * c1
    (p0 - a0) ^ 2 + (p1 - a1) ^ 2 ≤ R ^ 2 ∨ (p0 - b0) ^ 2 + (p1 - b1) ^ 2 ≤ R ^ 2 ∨
      (p0 - c0) ^ 2 + (p1 - c1) ^ 2 ≤ R ^ 2 := by
  intro p0 p1
  have e := tri_scalar a0 a1 b0 b1 c0 c1 o0 o1 R la lb lc hla hlb hlc hs ha hb hc
  apply tri_min_sq _ _ _ la lb lc _ hla hlb hlc hs
  rw [e]
  nlinarith [sq_nonneg (p0 - o0), sq_nonneg (p1 - o1)]

end N11Formalization.ResumeAttainment

namespace N11Formalization.ResumeAttainment
open N11Formalization

theorem dist_sq_coord (x y : Point) :
    dist x y ^ 2 = (x.ofLp 0 - y.ofLp 0) ^ 2 + (x.ofLp 1 - y.ofLp 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem tri_cover_pt (a b c O p : Point) (R la lb lc : ℝ) (hR : 0 ≤ R)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc) (hs : la + lb + lc = 1)
    (ha : dist a O = R) (hb : dist b O = R) (hc : dist c O = R)
    (hp : p = la • a + lb • b + lc • c) :
    dist p a ≤ R ∨ dist p b ≤ R ∨ dist p c ≤ R := by
  have hsq : ∀ v : Point, dist v O = R →
      (v.ofLp 0 - O.ofLp 0) ^ 2 + (v.ofLp 1 - O.ofLp 1) ^ 2 = R ^ 2 := by
    intro v hv; rw [← dist_sq_coord, hv]
  have h := tri_cover_sq (a.ofLp 0) (a.ofLp 1) (b.ofLp 0) (b.ofLp 1) (c.ofLp 0) (c.ofLp 1)
    (O.ofLp 0) (O.ofLp 1) R la lb lc hla hlb hlc hs (hsq a ha) (hsq b hb) (hsq c hc)
  have e0 : p.ofLp 0 = la * a.ofLp 0 + lb * b.ofLp 0 + lc * c.ofLp 0 := by subst hp; simp
  have e1 : p.ofLp 1 = la * a.ofLp 1 + lb * b.ofLp 1 + lc * c.ofLp 1 := by subst hp; simp
  simp only at h
  rw [← e0, ← e1] at h
  have key : ∀ v : Point, (p.ofLp 0 - v.ofLp 0) ^ 2 + (p.ofLp 1 - v.ofLp 1) ^ 2 ≤ R ^ 2 →
      dist p v ≤ R := by
    intro v hv
    rw [← dist_sq_coord] at hv
    by_contra hc
    push Not at hc
    nlinarith [dist_nonneg (x := p) (y := v)]
  rcases h with h | h | h
  · exact Or.inl (key a h)
  · exact Or.inr (Or.inl (key b h))
  · exact Or.inr (Or.inr (key c h))

end N11Formalization.ResumeAttainment

#print axioms N11Formalization.ResumeAttainment.tri_cover_pt

