import Mathlib
import N11Formalization.Assembly.G2Unified
import N11Formalization.SourceIdentity

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





/-!
ResumeAttainmentAnnulusFace —— (1) 松弛推广：共同 O 到三顶点 ≤ R 即可；
(2) 活跃面 consumer：residual u = 0 ⇒ 四个 U 面三顶点到 U_k 距离 = R ⇒ 面内点被覆盖（精确，无余量）。
-/

namespace N11Formalization.ResumeAttainment
open N11Formalization

/-- 标量核（一般）：Σλ‖p−v‖² = Σλ‖v−O‖² − ‖p−O‖²。 -/
theorem tri_scalar_le (a0 a1 b0 b1 c0 c1 o0 o1 la lb lc : ℝ) (hs : la + lb + lc = 1) :
    let p0 := la * a0 + lb * b0 + lc * c0
    let p1 := la * a1 + lb * b1 + lc * c1
    la * ((p0 - a0) ^ 2 + (p1 - a1) ^ 2) + lb * ((p0 - b0) ^ 2 + (p1 - b1) ^ 2)
      + lc * ((p0 - c0) ^ 2 + (p1 - c1) ^ 2)
      = la * ((a0 - o0) ^ 2 + (a1 - o1) ^ 2) + lb * ((b0 - o0) ^ 2 + (b1 - o1) ^ 2)
        + lc * ((c0 - o0) ^ 2 + (c1 - o1) ^ 2) - ((p0 - o0) ^ 2 + (p1 - o1) ^ 2) := by
  intro p0 p1
  have hc' : lc = 1 - la - lb := by linarith
  subst hc'
  simp only [p0, p1]
  ring

/-- **松弛三角覆盖**：O 到三顶点距离都 ≤ R，p 为凸组合 ⇒ p 离某顶点 ≤ R。 -/
theorem tri_cover_pt_le (a b c O p : Point) (R la lb lc : ℝ) (hR : 0 ≤ R)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc) (hs : la + lb + lc = 1)
    (ha : dist a O ≤ R) (hb : dist b O ≤ R) (hc : dist c O ≤ R)
    (hp : p = la • a + lb • b + lc • c) :
    dist p a ≤ R ∨ dist p b ≤ R ∨ dist p c ≤ R := by
  have e0 : p.ofLp 0 = la * a.ofLp 0 + lb * b.ofLp 0 + lc * c.ofLp 0 := by subst hp; simp
  have e1 : p.ofLp 1 = la * a.ofLp 1 + lb * b.ofLp 1 + lc * c.ofLp 1 := by subst hp; simp
  have E := tri_scalar_le (a.ofLp 0) (a.ofLp 1) (b.ofLp 0) (b.ofLp 1) (c.ofLp 0) (c.ofLp 1)
    (O.ofLp 0) (O.ofLp 1) la lb lc hs
  simp only at E
  rw [← e0, ← e1, ← dist_sq_coord, ← dist_sq_coord, ← dist_sq_coord, ← dist_sq_coord,
    ← dist_sq_coord, ← dist_sq_coord, ← dist_sq_coord] at E
  have sqle : ∀ v : Point, dist v O ≤ R → dist v O ^ 2 ≤ R ^ 2 := fun v hv =>
    pow_le_pow_left₀ dist_nonneg hv 2
  have hsum : la * dist p a ^ 2 + lb * dist p b ^ 2 + lc * dist p c ^ 2 ≤ R ^ 2 := by
    rw [E]
    nlinarith [mul_le_mul_of_nonneg_left (sqle a ha) hla, mul_le_mul_of_nonneg_left (sqle b hb) hlb,
      mul_le_mul_of_nonneg_left (sqle c hc) hlc, sq_nonneg (dist p O)]
  by_contra hn
  push Not at hn
  obtain ⟨h1, h2, h3⟩ := hn
  have q : ∀ v : Point, R < dist p v → R ^ 2 < dist p v ^ 2 := fun v hv =>
    pow_lt_pow_left₀ hv hR (by norm_num)
  have ka := mul_le_mul_of_nonneg_left (q a h1).le hla
  have kb := mul_le_mul_of_nonneg_left (q b h2).le hlb
  have kc := mul_le_mul_of_nonneg_left (q c h3).le hlc
  -- 三个 λ 之一 > 0，给出严格不等
  have hpos : 0 < la ∨ 0 < lb ∨ 0 < lc := by
    by_contra hz; push Not at hz; linarith [hz.1, hz.2.1, hz.2.2]
  rcases hpos with h | h | h
  · have := mul_lt_mul_of_pos_left (q a h1) h; nlinarith
  · have := mul_lt_mul_of_pos_left (q b h2) h; nlinarith
  · have := mul_lt_mul_of_pos_left (q c h3) h; nlinarith

/-! ## 活跃面 consumer（精确等号） -/

theorem dist_U1_hub1 (u : Fin 12 → ℝ) (h : residual u = 0) : dist (Uvec u 1) (hub1 u) = u 6 := by
  have := residual_comp_0 u; rw [h] at this; simp at this; linarith
theorem dist_U2_hub0 (u : Fin 12 → ℝ) (h : residual u = 0) : dist (Uvec u 2) (hub0 u) = u 6 := by
  have := residual_comp_1 u; rw [h] at this; simp at this; linarith
theorem dist_U3_hub0 (u : Fin 12 → ℝ) (h : residual u = 0) : dist (Uvec u 3) (hub0 u) = u 6 := by
  have := residual_comp_2 u; rw [h] at this; simp at this; linarith
theorem dist_U8_hub1 (u : Fin 12 → ℝ) (h : residual u = 0) : dist (Uvec u 8) (hub1 u) = u 6 := by
  have := residual_comp_3 u; rw [h] at this; simp at this; linarith

/-- 活跃面通用形式：面 (C_k, C_{k+1}, hub) 以 U_k 为外心、半径 u 6 ⇒ 面内每点被覆盖。 -/
theorem active_face_cover (u : Fin 12 → ℝ) (H : RootRange u) (k : Fin 9) (hub : Point)
    (hh : dist (Uvec u k) hub = u 6) (p : Point) (la lb lc : ℝ)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc) (hs : la + lb + lc = 1)
    (hp : p = la • ringCenter u k + lb • ringCenter u (k + 1) + lc • hub) :
    dist p (ringCenter u k) ≤ u 6 ∨ dist p (ringCenter u (k + 1)) ≤ u 6 ∨ dist p hub ≤ u 6 := by
  apply tri_cover_pt (ringCenter u k) (ringCenter u (k + 1)) hub (Uvec u k) p (u 6) la lb lc
    H.hR hla hlb hlc hs _ _ _ hp
  · rw [dist_comm]; exact dist_Uvec_ringCenter_self u H.hsin H.hR k
  · rw [dist_comm]; exact dist_Uvec_ringCenter_succ u H.hsin H.hR k
  · rw [dist_comm]; exact hh

/-- 四个 U 活跃面（面 [1,2,H1]、[2,3,H0]、[3,4,H0]、[8,0,H1]），全由 residual u = 0 精确供给。 -/
theorem active_U_faces_cover (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0) :
    (∀ (p : Point) (la lb lc : ℝ), 0 ≤ la → 0 ≤ lb → 0 ≤ lc → la + lb + lc = 1 →
      p = la • ringCenter u 1 + lb • ringCenter u (1 + 1) + lc • hub1 u →
      dist p (ringCenter u 1) ≤ u 6 ∨ dist p (ringCenter u (1 + 1)) ≤ u 6 ∨ dist p (hub1 u) ≤ u 6) ∧
    (∀ (p : Point) (la lb lc : ℝ), 0 ≤ la → 0 ≤ lb → 0 ≤ lc → la + lb + lc = 1 →
      p = la • ringCenter u 2 + lb • ringCenter u (2 + 1) + lc • hub0 u →
      dist p (ringCenter u 2) ≤ u 6 ∨ dist p (ringCenter u (2 + 1)) ≤ u 6 ∨ dist p (hub0 u) ≤ u 6) ∧
    (∀ (p : Point) (la lb lc : ℝ), 0 ≤ la → 0 ≤ lb → 0 ≤ lc → la + lb + lc = 1 →
      p = la • ringCenter u 3 + lb • ringCenter u (3 + 1) + lc • hub0 u →
      dist p (ringCenter u 3) ≤ u 6 ∨ dist p (ringCenter u (3 + 1)) ≤ u 6 ∨ dist p (hub0 u) ≤ u 6) ∧
    (∀ (p : Point) (la lb lc : ℝ), 0 ≤ la → 0 ≤ lb → 0 ≤ lc → la + lb + lc = 1 →
      p = la • ringCenter u 8 + lb • ringCenter u (8 + 1) + lc • hub1 u →
      dist p (ringCenter u 8) ≤ u 6 ∨ dist p (ringCenter u (8 + 1)) ≤ u 6 ∨ dist p (hub1 u) ≤ u 6) :=
  ⟨fun p la lb lc a b c s hp => active_face_cover u H 1 _ (dist_U1_hub1 u hres) p la lb lc a b c s hp,
   fun p la lb lc a b c s hp => active_face_cover u H 2 _ (dist_U2_hub0 u hres) p la lb lc a b c s hp,
   fun p la lb lc a b c s hp => active_face_cover u H 3 _ (dist_U3_hub0 u hres) p la lb lc a b c s hp,
   fun p la lb lc a b c s hp => active_face_cover u H 8 _ (dist_U8_hub1 u hres) p la lb lc a b c s hp⟩

end N11Formalization.ResumeAttainment

#print axioms N11Formalization.ResumeAttainment.tri_cover_pt_le
#print axioms N11Formalization.ResumeAttainment.active_U_faces_cover


