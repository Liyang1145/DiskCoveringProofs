import N11Formalization.ResumeAttainmentFace2
import N11Formalization.PremiseBundle
import N11Formalization.RootRangeBoxFull

/-! ResumeAttainmentFace3 —— 消去 W 面前提 hW：由 InCertBox → 闭球 → sqrtArgs_pos（Wpf>0）。 -/

namespace N11Formalization.ResumeAttainment
open N11Formalization N11Formalization.RootRangeBoxFull

theorem hW_of_box (u : Fin 12 → ℝ) (hu : InCertBox u) :
    ((u 5 - u 4) / 2) ^ 2 ≤ (u 6) ^ 2 := by
  have hx : u ∈ Metric.closedBall certCR rhoCertR := mem_closedBall_cert_iff.mpr hu
  have h := PremiseBundle.pb_hWp hx
  have e : Wpf (first7 u) = (u 6) ^ 2 - ((u 5 - u 4) / 2) ^ 2 := rfl
  rw [e] at h; linarith

/-- W 面精确覆盖，盒版：只剩 InCertBox + residual = 0。 -/
theorem W_face_cover_box (u : Fin 12 → ℝ) (hu : InCertBox u) (hres : residual u = 0)
    (p : Point) (la lb lc : ℝ) (hla : 0 ≤ la) (hlb : 0 ≤ lb) (hlc : 0 ≤ lc)
    (hs : la + lb + lc = 1) (hp : p = la • ringCenter u 6 + lb • hub0 u + lc • hub1 u) :
    dist p (ringCenter u 6) ≤ u 6 ∨ dist p (hub0 u) ≤ u 6 ∨ dist p (hub1 u) ≤ u 6 :=
  W_face_cover u (ha_hapi_of_box u hu).1 (hW_of_box u hu) hres p la lb lc hla hlb hlc hs hp

end N11Formalization.ResumeAttainment

#print axioms N11Formalization.ResumeAttainment.W_face_cover_box
