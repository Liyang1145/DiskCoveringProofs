import N11Formalization.ResumeAttainmentAnnulusFace

/-! ResumeAttainmentSlack —— 两个非活跃（松弛）面 [0,1,H1]、[7,8,H1]（TC 索引）。
外心候选 U_0 / U_7：到两环中心距离 = u 6 精确（dist_Uvec_ringCenter_*），
到 H1 的距离 ≤ u 6 是**显式前提** hS0/hS7（非活跃 ⇔ 松弛，待盒区间供给）。 -/

namespace N11Formalization.ResumeAttainment
open N11Formalization

theorem slack_face_cover (u : Fin 12 → ℝ) (H : RootRange u) (k : Fin 9)
    (hS : dist (Uvec u k) (hub1 u) ≤ u 6)
    (p : Point) (la lb lc : ℝ) (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hs : la + lb + lc = 1)
    (hp : p = la • ringCenter u k + lb • ringCenter u (k + 1) + lc • hub1 u) :
    dist p (ringCenter u k) ≤ u 6 ∨ dist p (ringCenter u (k + 1)) ≤ u 6 ∨
      dist p (hub1 u) ≤ u 6 := by
  apply tri_cover_pt_le (ringCenter u k) (ringCenter u (k + 1)) (hub1 u) (Uvec u k) p (u 6)
    la lb lc H.hR hla hlb hlc hs _ _ _ hp
  · rw [dist_comm]; exact (dist_Uvec_ringCenter_self u H.hsin H.hR k).le
  · rw [dist_comm]; exact (dist_Uvec_ringCenter_succ u H.hsin H.hR k).le
  · rw [dist_comm]; exact hS

/-- 两松弛面：[0,1,H1]（外心 U_0）与 [7,8,H1]（外心 U_7）。 -/
theorem slack_faces_cover (u : Fin 12 → ℝ) (H : RootRange u)
    (hS0 : dist (Uvec u 0) (hub1 u) ≤ u 6) (hS7 : dist (Uvec u 7) (hub1 u) ≤ u 6)
    (p : Point) (la lb lc : ℝ) (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hs : la + lb + lc = 1) :
    (p = la • ringCenter u 0 + lb • ringCenter u (0 + 1) + lc • hub1 u →
      dist p (ringCenter u 0) ≤ u 6 ∨ dist p (ringCenter u (0 + 1)) ≤ u 6 ∨
        dist p (hub1 u) ≤ u 6) ∧
    (p = la • ringCenter u 7 + lb • ringCenter u (7 + 1) + lc • hub1 u →
      dist p (ringCenter u 7) ≤ u 6 ∨ dist p (ringCenter u (7 + 1)) ≤ u 6 ∨
        dist p (hub1 u) ≤ u 6) :=
  ⟨slack_face_cover u H 0 hS0 p la lb lc hla hlb hlc hs,
   slack_face_cover u H 7 hS7 p la lb lc hla hlb hlc hs⟩

end N11Formalization.ResumeAttainment

#print axioms N11Formalization.ResumeAttainment.slack_faces_cover
