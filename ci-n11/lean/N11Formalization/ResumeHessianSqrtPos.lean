import N11Formalization.PremiseBundle

/-! ResumeHessian: 盒内全部 sqrt 参数正性（TCSystem 中出现的三类 sqrt）打包。
  rhoK 的 R²−sin²a_s（9 槽）→ Wfun；wPoint 的 R²−((y1−y0)/2)² → Wpf；
  dist 的 SRad（5 条残差）→ HessSeam.SRad。唯一前提 hx。 -/

namespace N11Formalization.ResumeHessian

open N11Formalization

theorem sqrtArgs_pos {x : Fin 12 → ℝ} (hx : x ∈ Metric.closedBall certCR rhoCertR) :
    (∀ s : Fin 9, 0 < Wfun s (first7 x)) ∧ 0 < Wpf (first7 x) ∧
      ∀ k : Fin 5, 0 < HessSeam.SRad k (first7 x) :=
  ⟨fun s => PremiseBundle.pb_Wfun_pos hx s, PremiseBundle.pb_hWp hx,
    fun k => PremiseBundle.pb_hpos k hx⟩

end N11Formalization.ResumeHessian

#check @N11Formalization.ResumeHessian.sqrtArgs_pos
#print N11Formalization.Wfun
#print N11Formalization.Wpf
#print axioms N11Formalization.ResumeHessian.sqrtArgs_pos
