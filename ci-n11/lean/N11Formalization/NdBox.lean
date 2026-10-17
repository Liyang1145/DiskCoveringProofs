import N11Formalization.EtaUsage
import N11Formalization.HJBoxInstant
import N11Formalization.KrawczykMono
import N11Formalization.HfmUncond
import N11Formalization.EtaInstance

noncomputable section

namespace N11Formalization.NdBox

open N11Formalization

/-- 承重 Jt。 -/
def JtBox : Fin 12 → Fin 12 → RatInterval :=
  Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)

theorem JtBox_valid : ∀ r c : Fin 12, RatInterval.Valid (JtBox r c) :=
  km_valid_of_mem_all (v := fun k j => (fderiv ℝ TCSystem certCR) (Pi.single j 1) k)
    (HJBoxInstant.hJ_box certCR (Metric.mem_closedBall_self rhoCertR_pos.le))

/-- 路线 1：固定常数 KCons/KConsR（经 nd_via_hyp）。网格行和为显式参数。 -/
theorem nd_box_fixedK
    (hsumB : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat HsumPayload.certReal.Yof (km_gridTable km_gridD JtBox) i j).lo : ℝ)|
        |((krawczykMat HsumPayload.certReal.Yof (km_gridTable km_gridD JtBox) i j).hi : ℝ)| ≤ KCons)
    (hsumRB : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMatR (km_gridTable km_gridD JtBox) HsumPayload.certReal.Yof i j).lo : ℝ)|
        |((krawczykMatR (km_gridTable km_gridD JtBox) HsumPayload.certReal.Yof i j).hi : ℝ)| ≤ KConsR) :
    ∃ S : C891RootSpec, Rstar S < 19 / 50 := by
  obtain ⟨S, -, -, -, -, -, h⟩ := nd_via_hyp D hFm_uncond eta_hηb JtBox HJBoxInstant.hJ_box
    (km_hsum_transfer_grid _ JtBox JtBox_valid hsumB)
    (km_hsumR_transfer_grid _ JtBox JtBox_valid hsumRB)
  exact ⟨S, h⟩

/-- 路线 2：新 K/K' 参数化（直接 nd_end_to_end_right）。 -/
theorem nd_box (K K' : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) (hK'0 : 0 ≤ K') (hK'1 : K' < 1)
    (hres : etaCons + K * rhoCertR < rhoCertR)
    (hsumB : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMat HsumPayload.certReal.Yof (km_gridTable km_gridD JtBox) i j).lo : ℝ)|
        |((krawczykMat HsumPayload.certReal.Yof (km_gridTable km_gridD JtBox) i j).hi : ℝ)| ≤ K)
    (hsumRB : ∀ i : Fin 12, ∑ j : Fin 12,
      max |((krawczykMatR (km_gridTable km_gridD JtBox) HsumPayload.certReal.Yof i j).lo : ℝ)|
        |((krawczykMatR (km_gridTable km_gridD JtBox) HsumPayload.certReal.Yof i j).hi : ℝ)| ≤ K') :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 ∧
        ((boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ)) ∧ Rstar S < 19 / 50 :=
  nd_end_to_end_right HsumPayload.certReal.Yof K etaCons K' hK0 hK1 hη0 hK'0 hK'1
    JtBox HJBoxInstant.hJ_box
    (km_hsum_transfer_grid _ JtBox JtBox_valid hsumB)
    (km_hsumR_transfer_grid _ JtBox JtBox_valid hsumRB)
    (fmCert lamCert D) hFm_uncond eta_hηb hres

end N11Formalization.NdBox
