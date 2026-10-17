import N11Formalization.ResumeAttainmentFace2

/-! ResumeAttainmentMirror —— 镜像 U 面：回文角 ⇒ C_{8-k} = refl C_k（y ↦ −y），hub 在 x 轴。
面 [6,7,H1]、[5,6,H0]、[4,5,H0] 分别以 refl U1、refl U2、refl U3 为外心、半径 u 6，精确覆盖。 -/

namespace N11Formalization.ResumeAttainment
open N11Formalization

/-- 关于 x 轴的反射。 -/
noncomputable def refl (p : Point) : Point := !₂[p.ofLp 0, -(p.ofLp 1)]

theorem refl_c0 (p : Point) : (refl p).ofLp 0 = p.ofLp 0 := by simp [refl]
theorem refl_c1 (p : Point) : (refl p).ofLp 1 = -(p.ofLp 1) := by simp [refl]

/-- 若 x 是 x' 的反射坐标，则 dist x (refl y) = dist x' y。 -/
theorem dist_mirror {x x' y : Point} (h0 : x.ofLp 0 = x'.ofLp 0) (h1 : x.ofLp 1 = -(x'.ofLp 1)) :
    dist x (refl y) = dist x' y := by
  apply eq_of_sq_eq_nonneg dist_nonneg dist_nonneg
  rw [dist_sq_coord, dist_sq_coord, refl_c0, refl_c1, h0, h1]; ring

theorem theta_mirror (u : Fin 12 → ℝ) :
    thetaOf (angleVec u) 7 = -thetaOf (angleVec u) 1 ∧
    thetaOf (angleVec u) 6 = -thetaOf (angleVec u) 2 ∧
    thetaOf (angleVec u) 5 = -thetaOf (angleVec u) 3 ∧
    thetaOf (angleVec u) 4 = 0 := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;> simp [thetaOf, angleVec] <;> ring

theorem rc_mirror (u : Fin 12 → ℝ) (k k' : Fin 9) (ha : angleVec u k' = angleVec u k)
    (ht : thetaOf (angleVec u) k' = -thetaOf (angleVec u) k) :
    (ringCenter u k').ofLp 0 = (ringCenter u k).ofLp 0 ∧
    (ringCenter u k').ofLp 1 = -((ringCenter u k).ofLp 1) := by
  simp only [ringCenter, rhoK, ha, ht, Real.cos_neg, Real.sin_neg]
  constructor <;> simp

theorem hub_mirror0 (u : Fin 12 → ℝ) :
    (hub0 u).ofLp 0 = (hub0 u).ofLp 0 ∧ (hub0 u).ofLp 1 = -((hub0 u).ofLp 1) := by
  simp [hub0]
theorem hub_mirror1 (u : Fin 12 → ℝ) :
    (hub1 u).ofLp 0 = (hub1 u).ofLp 0 ∧ (hub1 u).ofLp 1 = -((hub1 u).ofLp 1) := by
  simp [hub1]

theorem rc7 (u : Fin 12 → ℝ) :
    (ringCenter u 7).ofLp 0 = (ringCenter u 1).ofLp 0 ∧
    (ringCenter u 7).ofLp 1 = -((ringCenter u 1).ofLp 1) :=
  rc_mirror u 1 7 (by simp [angleVec]) (theta_mirror u).1
theorem rc6 (u : Fin 12 → ℝ) :
    (ringCenter u 6).ofLp 0 = (ringCenter u 2).ofLp 0 ∧
    (ringCenter u 6).ofLp 1 = -((ringCenter u 2).ofLp 1) :=
  rc_mirror u 2 6 (by simp [angleVec]) (theta_mirror u).2.1
theorem rc5 (u : Fin 12 → ℝ) :
    (ringCenter u 5).ofLp 0 = (ringCenter u 3).ofLp 0 ∧
    (ringCenter u 5).ofLp 1 = -((ringCenter u 3).ofLp 1) :=
  rc_mirror u 3 5 (by simp [angleVec]) (theta_mirror u).2.2.1
theorem rc4 (u : Fin 12 → ℝ) :
    (ringCenter u 4).ofLp 0 = (ringCenter u 4).ofLp 0 ∧
    (ringCenter u 4).ofLp 1 = -((ringCenter u 4).ofLp 1) := by
  refine ⟨rfl, ?_⟩
  have h : Real.sin (thetaOf (angleVec u) 4) = 0 := by rw [(theta_mirror u).2.2.2]; simp
  simp [ringCenter, h]

/-- 通用镜像面：原面 (a',b',c') 以 O 为外心半径 R，镜像顶点 (a,b,c) 以 refl O 为外心。 -/
theorem mirror_face_cover {a b c a' b' c' O p : Point} {R la lb lc : ℝ} (hR : 0 ≤ R)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc) (hs : la + lb + lc = 1)
    (ma : a.ofLp 0 = a'.ofLp 0 ∧ a.ofLp 1 = -(a'.ofLp 1))
    (mb : b.ofLp 0 = b'.ofLp 0 ∧ b.ofLp 1 = -(b'.ofLp 1))
    (mc : c.ofLp 0 = c'.ofLp 0 ∧ c.ofLp 1 = -(c'.ofLp 1))
    (ha : dist a' O = R) (hb : dist b' O = R) (hc : dist c' O = R)
    (hp : p = la • a + lb • b + lc • c) :
    dist p a ≤ R ∨ dist p b ≤ R ∨ dist p c ≤ R :=
  tri_cover_pt a b c (refl O) p R la lb lc hR hla hlb hlc hs
    ((dist_mirror ma.1 ma.2).trans ha) ((dist_mirror mb.1 mb.2).trans hb)
    ((dist_mirror mc.1 mc.2).trans hc) hp

theorem dU1_hub1 (u : Fin 12 → ℝ) (h : residual u = 0) : dist (hub1 u) (Uvec u 1) = u 6 := by
  have := residual_comp_0 u; rw [h] at this; simp at this; rw [dist_comm]; linarith
theorem dU2_hub0 (u : Fin 12 → ℝ) (h : residual u = 0) : dist (hub0 u) (Uvec u 2) = u 6 := by
  have := residual_comp_1 u; rw [h] at this; simp at this; rw [dist_comm]; linarith
theorem dU3_hub0 (u : Fin 12 → ℝ) (h : residual u = 0) : dist (hub0 u) (Uvec u 3) = u 6 := by
  have := residual_comp_2 u; rw [h] at this; simp at this; rw [dist_comm]; linarith

/-- 三个镜像 U 面 [6,7,H1]、[5,6,H0]、[4,5,H0]（外心 refl U1/U2/U3），RootRange + residual = 0。 -/
theorem mirror_U_faces_cover (u : Fin 12 → ℝ) (H : RootRange u) (hres : residual u = 0)
    (p : Point) (la lb lc : ℝ) (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hs : la + lb + lc = 1) :
    (p = la • ringCenter u 7 + lb • ringCenter u 6 + lc • hub1 u →
      dist p (ringCenter u 7) ≤ u 6 ∨ dist p (ringCenter u 6) ≤ u 6 ∨ dist p (hub1 u) ≤ u 6) ∧
    (p = la • ringCenter u 6 + lb • ringCenter u 5 + lc • hub0 u →
      dist p (ringCenter u 6) ≤ u 6 ∨ dist p (ringCenter u 5) ≤ u 6 ∨ dist p (hub0 u) ≤ u 6) ∧
    (p = la • ringCenter u 5 + lb • ringCenter u 4 + lc • hub0 u →
      dist p (ringCenter u 5) ≤ u 6 ∨ dist p (ringCenter u 4) ≤ u 6 ∨ dist p (hub0 u) ≤ u 6) := by
  have s := fun k => dist_Uvec_ringCenter_self u H.hsin H.hR k
  have t := fun k => dist_Uvec_ringCenter_succ u H.hsin H.hR k
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · exact mirror_face_cover H.hR hla hlb hlc hs (rc7 u) (rc6 u) (hub_mirror1 u)
      (by rw [dist_comm]; exact s 1) (by rw [dist_comm]; exact t 1) (dU1_hub1 u hres) hp
  · exact mirror_face_cover H.hR hla hlb hlc hs (rc6 u) (rc5 u) (hub_mirror0 u)
      (by rw [dist_comm]; exact s 2) (by rw [dist_comm]; exact t 2) (dU2_hub0 u hres) hp
  · exact mirror_face_cover H.hR hla hlb hlc hs (rc5 u) (rc4 u) (hub_mirror0 u)
      (by rw [dist_comm]; exact s 3) (by rw [dist_comm]; exact t 3) (dU3_hub0 u hres) hp

end N11Formalization.ResumeAttainment

#print axioms N11Formalization.ResumeAttainment.mirror_U_faces_cover
