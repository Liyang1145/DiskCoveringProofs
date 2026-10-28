import N11Formalization.TcRootHook
import N11Formalization.NondegProof
import N11Formalization.DrowBallBox_compIvBoxBox

namespace N11Formalization.RootRangeBoxFull
open N11Formalization RatInterval

def InCertBox (u : Fin 12 → ℝ) : Prop :=
  ∀ i : Fin 12, (boxLoCert i : ℝ) ≤ u i ∧ u i ≤ (boxHiCert i : ℝ)

theorem hQ (u : Fin 12 → ℝ) (hu : InCertBox u) : ∀ i, (ndBox i).Mem (u i) := fun i => hu i

theorem ha_hapi_of_box (u : Fin 12 → ℝ) (hu : InCertBox u) :
    0 ≤ u 6 ∧ (∀ k : Fin 9, 0 ≤ angleVec u k) ∧ (∀ k : Fin 9, angleVec u k ≤ Real.pi) := by
  have l0 := (hu 0).1; have l1 := (hu 1).1; have l2 := (hu 2).1; have l3 := (hu 3).1
  have h0 := (hu 0).2; have h1 := (hu 1).2; have h2 := (hu 2).2; have h3 := (hu 3).2
  have l6 := (hu 6).1
  have e0 : boxLoCert 0 = 1798923298417342433274219 / 2 ^ 82 := rfl
  have e1 : boxLoCert 1 = 1648215922234750999800171 / 2 ^ 82 := rfl
  have e2 : boxLoCert 2 = 1357971481365603998574955 / 2 ^ 82 := rfl
  have e3 : boxLoCert 3 = 1852132483251062452070763 / 2 ^ 82 := rfl
  have e6 : boxLoCert 6 = 1837489159457200081021291 / 2 ^ 82 := rfl
  have f0 : boxHiCert 0 = 1798923308088748990191253 / 2 ^ 82 := rfl
  have f1 : boxHiCert 1 = 1648215931906157556717205 / 2 ^ 82 := rfl
  have f2 : boxHiCert 2 = 1357971491037010555491989 / 2 ^ 82 := rfl
  have f3 : boxHiCert 3 = 1852132492922469008987797 / 2 ^ 82 := rfl
  rw [e0] at l0; rw [e1] at l1; rw [e2] at l2; rw [e3] at l3; rw [e6] at l6
  rw [f0] at h0; rw [f1] at h1; rw [f2] at h2; rw [f3] at h3
  push_cast at l0 l1 l2 l3 l6 h0 h1 h2 h3
  have hp := Real.pi_gt_three
  refine ⟨by linarith, ?_, ?_⟩
  · intro k; fin_cases k <;> simp [angleVec] <;> linarith
  · intro k; fin_cases k <;> simp [angleVec] <;> linarith
theorem hsin_0 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 0) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 0)).lo : ℝ) ≤ Real.sin (angleVec u 0) ∧
      Real.sin (angleVec u 0) ≤ ((sinTotLag (ndAngleBox ndBox 0)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 0))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 0)).lo : ℝ) := by
    rw [DrowBallBox.B_sa0_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 0)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa0_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_0 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 0 := by
  have hm : ((ndRhoBox ndBox 0).lo : ℝ) ≤ rhoK u 0 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 0)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 0).lo : ℝ) := by
    rw [DrowBallBox.B_rho0_lo]; norm_num
  linarith

theorem hsin_1 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 1) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 1)).lo : ℝ) ≤ Real.sin (angleVec u 1) ∧
      Real.sin (angleVec u 1) ≤ ((sinTotLag (ndAngleBox ndBox 1)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 1))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 1)).lo : ℝ) := by
    rw [DrowBallBox.B_sa1_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 1)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa1_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_1 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 1 := by
  have hm : ((ndRhoBox ndBox 1).lo : ℝ) ≤ rhoK u 1 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 1)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 1).lo : ℝ) := by
    rw [DrowBallBox.B_rho1_lo]; norm_num
  linarith

theorem hsin_2 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 2) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 2)).lo : ℝ) ≤ Real.sin (angleVec u 2) ∧
      Real.sin (angleVec u 2) ≤ ((sinTotLag (ndAngleBox ndBox 2)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 2))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 2)).lo : ℝ) := by
    rw [DrowBallBox.B_sa2_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 2)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa2_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_2 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 2 := by
  have hm : ((ndRhoBox ndBox 2).lo : ℝ) ≤ rhoK u 2 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 2)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 2).lo : ℝ) := by
    rw [DrowBallBox.B_rho2_lo]; norm_num
  linarith

theorem hsin_3 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 3) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 3)).lo : ℝ) ≤ Real.sin (angleVec u 3) ∧
      Real.sin (angleVec u 3) ≤ ((sinTotLag (ndAngleBox ndBox 3)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 3))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 3)).lo : ℝ) := by
    rw [DrowBallBox.B_sa3_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 3)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa3_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_3 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 3 := by
  have hm : ((ndRhoBox ndBox 3).lo : ℝ) ≤ rhoK u 3 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 3)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 3).lo : ℝ) := by
    rw [DrowBallBox.B_rho3_lo]; norm_num
  linarith

theorem hsin_4 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 4) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 4)).lo : ℝ) ≤ Real.sin (angleVec u 4) ∧
      Real.sin (angleVec u 4) ≤ ((sinTotLag (ndAngleBox ndBox 4)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 4))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 4)).lo : ℝ) := by
    rw [DrowBallBox.B_sa4_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 4)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa4_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_4 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 4 := by
  have hm : ((ndRhoBox ndBox 4).lo : ℝ) ≤ rhoK u 4 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 4)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 4).lo : ℝ) := by
    rw [DrowBallBox.B_rho4_lo]; norm_num
  linarith

theorem hsin_5 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 5) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 3)).lo : ℝ) ≤ Real.sin (angleVec u 5) ∧
      Real.sin (angleVec u 5) ≤ ((sinTotLag (ndAngleBox ndBox 3)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 5))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 3)).lo : ℝ) := by
    rw [DrowBallBox.B_sa3_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 3)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa3_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_5 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 5 := by
  have hm : ((ndRhoBox ndBox 3).lo : ℝ) ≤ rhoK u 5 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 5)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 3).lo : ℝ) := by
    rw [DrowBallBox.B_rho3_lo]; norm_num
  linarith

theorem hsin_6 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 6) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 6)).lo : ℝ) ≤ Real.sin (angleVec u 6) ∧
      Real.sin (angleVec u 6) ≤ ((sinTotLag (ndAngleBox ndBox 6)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 6))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 6)).lo : ℝ) := by
    rw [DrowBallBox.B_sa6_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 6)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa6_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_6 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 6 := by
  have hm : ((ndRhoBox ndBox 6).lo : ℝ) ≤ rhoK u 6 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 6)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 6).lo : ℝ) := by
    rw [DrowBallBox.B_rho6_lo]; norm_num
  linarith

theorem hsin_7 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 7) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 1)).lo : ℝ) ≤ Real.sin (angleVec u 7) ∧
      Real.sin (angleVec u 7) ≤ ((sinTotLag (ndAngleBox ndBox 1)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 7))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 1)).lo : ℝ) := by
    rw [DrowBallBox.B_sa1_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 1)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa1_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_7 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 7 := by
  have hm : ((ndRhoBox ndBox 1).lo : ℝ) ≤ rhoK u 7 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 7)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 1).lo : ℝ) := by
    rw [DrowBallBox.B_rho1_lo]; norm_num
  linarith

theorem hsin_8 (u : Fin 12 → ℝ) (hu : InCertBox u) :
    Real.sin (angleVec u 8) ^ 2 ≤ (u 6) ^ 2 := by
  have hm : ((sinTotLag (ndAngleBox ndBox 8)).lo : ℝ) ≤ Real.sin (angleVec u 8) ∧
      Real.sin (angleVec u 8) ≤ ((sinTotLag (ndAngleBox ndBox 8)).hi : ℝ) :=
    RatInterval.mem_iff.mp (sinTotLag_mem (ndAngleBox_mem (hQ u hu) 8))
  have c1 : -((boxLoCert 6 : ℚ) : ℝ) ≤ ((sinTotLag (ndAngleBox ndBox 8)).lo : ℝ) := by
    rw [DrowBallBox.B_sa8_lo, TcRootHook.lo6]; norm_num
  have c2 : ((sinTotLag (ndAngleBox ndBox 8)).hi : ℝ) ≤ ((boxLoCert 6 : ℚ) : ℝ) := by
    rw [DrowBallBox.B_sa8_hi, TcRootHook.lo6]; norm_num
  have l6 := (hu 6).1
  exact sq_le_sq' (by linarith [hm.1]) (by linarith [hm.2])

theorem hrho_8 (u : Fin 12 → ℝ) (hu : InCertBox u) : 0 ≤ rhoK u 8 := by
  have hm : ((ndRhoBox ndBox 8).lo : ℝ) ≤ rhoK u 8 :=
    RatInterval.mem_lo_le (ndRhoBox_mem (hQ u hu) 8)
  have c : (0 : ℝ) ≤ ((ndRhoBox ndBox 8).lo : ℝ) := by
    rw [DrowBallBox.B_rho8_lo]; norm_num
  linarith

theorem rootRange_of_box (u : Fin 12 → ℝ) (hu : InCertBox u) : RootRange u := by
  obtain ⟨hR, ha, hapi⟩ := ha_hapi_of_box u hu
  refine ⟨hR, ha, hapi, ?_, ?_⟩
  · intro k; fin_cases k
    exacts [hsin_0 u hu, hsin_1 u hu, hsin_2 u hu, hsin_3 u hu, hsin_4 u hu,
      hsin_5 u hu, hsin_6 u hu, hsin_7 u hu, hsin_8 u hu]
  · intro k; fin_cases k
    exacts [hrho_0 u hu, hrho_1 u hu, hrho_2 u hu, hrho_3 u hu, hrho_4 u hu,
      hrho_5 u hu, hrho_6 u hu, hrho_7 u hu, hrho_8 u hu]

/-- nd_box_final 的根满足 RootRange（无前提）。 -/
theorem nd_box_final_rootRange :
    ∃ S : C891RootSpec, S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧
      S.radiusIndex = 6 ∧ Rstar S < 19 / 50 ∧ RootRange S.root := by
  obtain ⟨S, hs, hlo, hhi, hidx, _, hlt⟩ := GridBridge.nd_box_final
  refine ⟨S, hs, hlo, hhi, hidx, hlt, rootRange_of_box _ ?_⟩
  intro i; have h := S.root_mem.1 i; rw [hlo, hhi] at h; exact h

end N11Formalization.RootRangeBoxFull