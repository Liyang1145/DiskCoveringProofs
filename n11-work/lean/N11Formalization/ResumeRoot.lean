import N11Formalization.NdBox
import N11Formalization.HsumPayloadB

/-!
# `ResumeRoot` — G1 consumer-first assembly (draft, NOT compiled; root-consumer)

Consumer: `nd_end_to_end_right` (C891 same root, radiusIndex = 6, no sInf).
Payload: `HsumPayloadB.certB/certBR` (kernel `check`/`checkR` by decide).
Y identity: `certB.Yof = certReal.Yof` — same `Dz`,`numYz` fields ⇒ `rfl`.

Single explicit premise `hC`: the B′ payload table envelopes the ball Jacobian table
`JtBox = Jt'' (HessOfBox d2xBox d2yBox)` cell-wise (144 `Contains` goals;
49 via `Ladder49.B49_jt_*_iv`, 95 via DrowBallBox kernel endpoints). Not proved here.
-/

noncomputable section
namespace N11Formalization.ResumeRoot
open N11Formalization N11Formalization.HsumCert

theorem Y_same : HsumPayloadB.certB.Yof = HsumPayload.certReal.Yof := rfl
theorem Y_sameR : HsumPayloadB.certBR.Yof = HsumPayload.certReal.Yof := rfl
theorem J_sameR : HsumPayloadB.certBR.Jof = HsumPayloadB.certB.Jof := rfl

/-- Root, conditional ONLY on the envelope `hC` (no hH/hJ/hsum/eta/Fm premises). -/
theorem root_of_envelope
    (hC : ∀ r c : Fin 12, RatInterval.Contains (HsumPayloadB.certB.Jof r c) (NdBox.JtBox r c)) :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 ∧
        ((boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ)) ∧ Rstar S < 19 / 50 := by
  have hsum := km_hsum_transfer HsumPayload.certReal.Yof hC NdBox.JtBox_valid
    (by rw [← Y_same]; exact HsumPayloadB.certB_hsum)
  have hsumR := km_hsumR_transfer HsumPayload.certReal.Yof (JtW := HsumPayloadB.certBR.Jof) hC
    NdBox.JtBox_valid (by rw [← Y_sameR]; exact HsumPayloadB.certBR_hsumR)
  exact nd_end_to_end_right HsumPayload.certReal.Yof _ etaCons _
    (HsumPayloadB.hK0_B) HsumPayloadB.hK1_B hη0 HsumPayloadB.hK'0_B HsumPayloadB.hK'1_B
    NdBox.JtBox HJBoxInstant.hJ_box hsum hsumR
    (fmCert lamCert D) hFm_uncond eta_hηb HsumPayloadB.hresCons_B

end N11Formalization.ResumeRoot
