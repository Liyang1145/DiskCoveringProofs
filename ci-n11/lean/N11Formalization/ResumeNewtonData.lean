import N11Formalization.ResumeNewton
import N11Formalization.EtaInstance
import N11Formalization.HfmUncond
import N11Formalization.C921Sem

noncomputable section
namespace N11Formalization.ResumeNewtonData
open RatInterval

/-- Tighter norm bound, reusing the same certified center residual intervals. -/
def tightCert : EtaResCert := { cEta with numEta := 3, denEta := 100000000000000000 }

theorem tight_check : tightCert.etaCheck = true := by decide

/-- Negative control: the same nonzero center residual cannot be certified zero. -/
theorem zero_residual_rejected :
    ({ tightCert with numEta := 0 } : EtaResCert).etaCheck = false := by decide

theorem mem_FmW (k : Fin 12) : (FmW k).Mem (TCSystem certCR k) :=
  mem_of_contains (enc_all k) (hFm_uncond k)

theorem residual_norm : ‖ratMatCLM HsumPayload.certReal.Yof (TCSystem certCR)‖ ≤
    (3 : ℝ) / 100000000000000000 := by
  apply norm_ratMatCLM_le mem_FmW (by norm_num)
  exact (EtaResCert.etaCheck_sound tight_check).1

theorem signed_sixth : -(ratMatCLM HsumPayload.certReal.Yof (TCSystem certCR)) 6 ≤
    (13 : ℝ) / 1000000000000000000 := by
  have hm := mem_incrMatVec (Y := cEta.Yof) mem_FmW (6 : Fin 12)
  have hv := RatInterval.mem_lo_le hm
  have he : (incrMatVec cEta.Yof FmW (6 : Fin 12)).lo =
      (cEta.loV 6 : ℚ) / (cEta.E : ℚ) := by
    change (RatInterval.dot (cEta.Yof 6) cEta.Fof).lo = _
    rw [RatInterval.dot_lo_eq _ _ (fun k => EtaResCert.Fof_valid cEta EtaDcom_pos etaLoF_le_hiF k),
      RatInterval.finRange_map_sum, EtaResCert.sum_loV_eq cEta EtaDcom_pos]
  rw [he] at hv
  have hcross : -(cEta.loV 6) * 1000000000000000000 ≤ 13 * cEta.E := by decide
  have hq : -((cEta.loV 6 : ℚ) / (cEta.E : ℚ)) ≤ (13 : ℚ) / 1000000000000000000 := by
    rw [← neg_div]
    apply (div_le_div_iff₀ (EtaResCert.Epos cEta EtaDcom_pos) (by norm_num)).mpr
    exact_mod_cast hcross
  have hr : -(((cEta.loV 6 : ℚ) / (cEta.E : ℚ)) : ℝ) ≤
      (13 : ℝ) / 1000000000000000000 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hq
    simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using hh
  rw [cEta_Yof] at hv
  push_cast at hv hr
  linarith

/-- C922: strict threshold pin for the original root, no contracted-box inclusion
hypothesis and no Python numerical premise. -/
theorem root_lt_threshold (S : C891RootSpec)
    (hsys : S.sys = TCSystem) (hlo : S.boxLo = boxLoCert)
    (hhi : S.boxHi = boxHiCert) (hidx : S.radiusIndex = 6) :
    Rstar S < C921Sem.threshR := by
  have h := ResumeNewton.Rstar_le_newton6 S hsys hlo hhi hidx residual_norm signed_sixth
  apply lt_of_le_of_lt h
  have hc : certCR 6 = (6845180557269243 : ℝ) / 2 ^ 54 := by
    change ((6845180557269243 / 2 ^ 54 : ℚ) : ℝ) = _
    norm_num
  rw [hc]
  norm_num [HsumPayloadB.numK_B, HsumPayload.Ez,
    C921Sem.threshR, G3ArcConstants.thresh]

/-- Actual root-existence consumer with the original system, box and radius index. -/
theorem exists_root_below_threshold :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧
      S.boxHi = boxHiCert ∧ S.radiusIndex = 6 ∧
      ((boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ)) ∧
      Rstar S < C921Sem.threshR := by
  obtain ⟨S, hs, hl, hh, hi, hb, _⟩ := GridBridge.nd_box_final
  exact ⟨S, hs, hl, hh, hi, hb, root_lt_threshold S hs hl hh hi⟩

#check @exists_root_below_threshold
#print axioms exists_root_below_threshold
#check @root_lt_threshold
#print axioms root_lt_threshold
#print axioms residual_norm
#print axioms signed_sixth
end N11Formalization.ResumeNewtonData
