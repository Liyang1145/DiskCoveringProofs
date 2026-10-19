import N11Formalization.ResumeAttainmentTriangle
import N11Formalization.Assembly.G2Unified
import N11Formalization.SourceIdentity

/-!
ResumeAttainmentFace2 —— W 活跃面 [6,9,10]（C_6, H0, H1）以 W 为外心、半径 u 6，精确覆盖。
dist(W,C6)=u6 由 residual 4 = 0；dist(W,H0)=dist(W,H1)=u6 由 W 的构造（需 ((u5-u4)/2)² ≤ u6²，
即 sqrt 实参非负——显式前提，待盒供给）。
-/

namespace N11Formalization.ResumeAttainment
open N11Formalization

theorem eq_of_sq_eq_nonneg {d R : ℝ} (hd : 0 ≤ d) (hR : 0 ≤ R) (h : d ^ 2 = R ^ 2) : d = R := by
  apply le_antisymm <;> nlinarith

theorem dist_W_hub0 (u : Fin 12 → ℝ) (hR : 0 ≤ u 6) (hW : ((u 5 - u 4) / 2) ^ 2 ≤ (u 6) ^ 2) :
    dist (wPoint u) (hub0 u) = u 6 := by
  apply eq_of_sq_eq_nonneg dist_nonneg hR
  rw [dist_sq_coord, wPoint_coord0, wPoint_coord1, hub0_coord0, hub0_coord1,
    sub_zero, Real.sq_sqrt (by linarith)]
  ring

theorem dist_W_hub1 (u : Fin 12 → ℝ) (hR : 0 ≤ u 6) (hW : ((u 5 - u 4) / 2) ^ 2 ≤ (u 6) ^ 2) :
    dist (wPoint u) (hub1 u) = u 6 := by
  apply eq_of_sq_eq_nonneg dist_nonneg hR
  rw [dist_sq_coord, wPoint_coord0, wPoint_coord1, hub1_coord0, hub1_coord1,
    sub_zero, Real.sq_sqrt (by linarith)]
  ring

theorem dist_W_C6 (u : Fin 12 → ℝ) (h : residual u = 0) :
    dist (wPoint u) (ringCenter u 6) = u 6 := by
  have := residual_comp_4 u; rw [h] at this; simp at this; linarith

/-- **W 面精确覆盖**：面 [C_6, H0, H1] 内每点离某顶点 ≤ u 6（紧等号，无余量）。 -/
theorem W_face_cover (u : Fin 12 → ℝ) (hR : 0 ≤ u 6)
    (hW : ((u 5 - u 4) / 2) ^ 2 ≤ (u 6) ^ 2) (hres : residual u = 0)
    (p : Point) (la lb lc : ℝ) (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hs : la + lb + lc = 1) (hp : p = la • ringCenter u 6 + lb • hub0 u + lc • hub1 u) :
    dist p (ringCenter u 6) ≤ u 6 ∨ dist p (hub0 u) ≤ u 6 ∨ dist p (hub1 u) ≤ u 6 := by
  apply tri_cover_pt (ringCenter u 6) (hub0 u) (hub1 u) (wPoint u) p (u 6) la lb lc
    hR hla hlb hlc hs _ _ _ hp
  · rw [dist_comm]; exact dist_W_C6 u hres
  · rw [dist_comm]; exact dist_W_hub0 u hR hW
  · rw [dist_comm]; exact dist_W_hub1 u hR hW

end N11Formalization.ResumeAttainment

#print axioms N11Formalization.ResumeAttainment.W_face_cover
