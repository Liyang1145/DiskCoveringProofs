import N11Formalization.ResumeAttainmentMirror
import N11Formalization.ResumeAttainmentFace3

/-! ResumeAttainmentCentral2 —— 中心面 [C2,H0,H1]（TC 原始索引）= W 面 [C6,H0,H1] 的镜像，
外心 refl wPoint、半径 u 6，精确覆盖。盒版：InCertBox + residual = 0。 -/

namespace N11Formalization.ResumeAttainment
open N11Formalization N11Formalization.RootRangeBoxFull

theorem rc2_of_6 (u : Fin 12 → ℝ) :
    (ringCenter u 2).ofLp 0 = (ringCenter u 6).ofLp 0 ∧
    (ringCenter u 2).ofLp 1 = -((ringCenter u 6).ofLp 1) := by
  obtain ⟨h0, h1⟩ := rc6 u
  exact ⟨h0.symm, by rw [h1]; ring⟩

theorem central2_face_cover_box (u : Fin 12 → ℝ) (hu : InCertBox u) (hres : residual u = 0)
    (p : Point) (la lb lc : ℝ) (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hs : la + lb + lc = 1) (hp : p = la • ringCenter u 2 + lb • hub0 u + lc • hub1 u) :
    dist p (ringCenter u 2) ≤ u 6 ∨ dist p (hub0 u) ≤ u 6 ∨ dist p (hub1 u) ≤ u 6 := by
  have hR := (ha_hapi_of_box u hu).1
  have hW := hW_of_box u hu
  exact mirror_face_cover hR hla hlb hlc hs (rc2_of_6 u) (hub_mirror0 u) (hub_mirror1 u)
    (by rw [dist_comm]; exact dist_W_C6 u hres)
    (by rw [dist_comm]; exact dist_W_hub0 u hR hW)
    (by rw [dist_comm]; exact dist_W_hub1 u hR hW) hp

end N11Formalization.ResumeAttainment

#print axioms N11Formalization.ResumeAttainment.central2_face_cover_box
