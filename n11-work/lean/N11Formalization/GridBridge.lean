import N11Formalization.KrawczykMono
import N11Formalization.HsumPayloadB
import N11Formalization.NdBox
import N11Formalization.BallJtLam
import N11Formalization.DrowBallBox_compIvBoxBox
import N11Formalization.HJBoxInstant
import N11Formalization.Ladder49_jt_kkt_z
import Mathlib.Data.Rat.Floor

set_option maxHeartbeats 0
set_option exponentiation.threshold 400

/-! # GridBridge: `HsumPayloadB.certB.Jof r c = km_gridTable km_gridD (Jt'' …) r c`, 144 cells.
Payload imported from root module N11Formalization.HsumPayloadB. -/

namespace N11Formalization.GridBridge
open N11Formalization.HsumPayloadB

theorem Dz_eq : HsumPayload.Dz = km_gridD := by unfold HsumPayload.Dz km_gridD; norm_num

theorem cell_0_0 : certB.Jof 0 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 0 := by
  show certB.Jof 0 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up7 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_0_0_lo, DrowBallBox.B_comp_0_0_hi]
  have hl : loNum_B 0 0 = 635933387355719457923727501586821671909043866978792160524222117450487790336249701676397422326843 := rfl
  have hh : hiNum_B 0 0 = 635934054750534737471283918525032057550590314380880240685761217703621576332669676333335542385607 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_0_1 : certB.Jof 0 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 1 := by
  show certB.Jof 0 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up7 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_0_1_lo, DrowBallBox.B_comp_0_1_hi]
  have hl : loNum_B 0 1 = 2283321006287451861730544825883400795435965045198637198715477142030015819683296974473799700402615 := rfl
  have hh : hiNum_B 0 1 = 2283322059107186984636407375728412392565067250161503269648537059133531011396501230522181905641540 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_0_2 : certB.Jof 0 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 2 := by
  show certB.Jof 0 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up7 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_0_2_lo, DrowBallBox.B_comp_0_2_hi]
  have hl : loNum_B 0 2 = 1521401277450162745486597649461012200007007786052386998449906854622864969335770407348030677596351 := rfl
  have hh : hiNum_B 0 2 = 1521401921935746153607672843661673705706869025788535621660410226157192579819413108294391498597912 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_0_3 : certB.Jof 0 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 3 := by
  show certB.Jof 0 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up7 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_0_3_lo, DrowBallBox.B_comp_0_3_hi]
  have hl : loNum_B 0 3 = 0 := rfl
  have hh : hiNum_B 0 3 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_0_4 : certB.Jof 0 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 4 := by
  show certB.Jof 0 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up7 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_0_4_lo, DrowBallBox.B_comp_0_4_hi]
  have hl : loNum_B 0 4 = 0 := rfl
  have hh : hiNum_B 0 4 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_0_5 : certB.Jof 0 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 5 := by
  show certB.Jof 0 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up7 5)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_0_5_lo, DrowBallBox.B_comp_0_5_hi]
  have hl : loNum_B 0 5 = -185850605509079638005510722033999226420217284426433756021677639865091021379132570022810020556607 := rfl
  have hh : hiNum_B 0 5 = -185850211415007430479042463801775560460429302847758101741776948074031892819419395139750494653837 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_0_6 : certB.Jof 0 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 6 := by
  show certB.Jof 0 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up7 6)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_0_6_lo, DrowBallBox.B_comp_0_6_hi]
  have hl : loNum_B 0 6 = -9029122596683253373823269305256320403171987278296286874731089181330320021119749342973100170512084 := rfl
  have hh : hiNum_B 0 6 = -9029120805924275987757330138661895801361532424570198447069998465751182751664232844384797984763772 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_0_7 : certB.Jof 0 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 7 := by
  show certB.Jof 0 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 0 7 = 0 := rfl
  have hh : hiNum_B 0 7 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_0_8 : certB.Jof 0 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 8 := by
  show certB.Jof 0 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 0 8 = 0 := rfl
  have hh : hiNum_B 0 8 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_0_9 : certB.Jof 0 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 9 := by
  show certB.Jof 0 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 0 9 = 0 := rfl
  have hh : hiNum_B 0 9 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_0_10 : certB.Jof 0 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 10 := by
  show certB.Jof 0 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 0 10 = 0 := rfl
  have hh : hiNum_B 0 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_0_11 : certB.Jof 0 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 0 11 := by
  show certB.Jof 0 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 0) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 0 11 = 0 := rfl
  have hh : hiNum_B 0 11 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_1_0 : certB.Jof 1 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 0 := by
  show certB.Jof 1 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up7 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_1_0_lo, DrowBallBox.B_comp_1_0_hi]
  have hl : loNum_B 1 0 = -1161730476257958164384985366239773198840291012962645522748988019838315456864194723104099172464315 := rfl
  have hh : hiNum_B 1 0 = -1161729602426921880602112950424492775132732751163589356903922778427971098860870592844599431869695 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_1_1 : certB.Jof 1 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 1 := by
  show certB.Jof 1 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up7 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_1_1_lo, DrowBallBox.B_comp_1_1_hi]
  have hl : loNum_B 1 1 = -1161730476257958164384985366239773198840291012962645522748988019838315456864194723104099172464315 := rfl
  have hh : hiNum_B 1 1 = -1161729602426921880602112950424492775132732751163589356903922778427971098860870592844599431869695 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_1_2 : certB.Jof 1 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 2 := by
  show certB.Jof 1 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up7 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_1_2_lo, DrowBallBox.B_comp_1_2_hi]
  have hl : loNum_B 1 2 = 505156109600004816657444074050595279855477397977457995594550282494432630510182208547764155080886 := rfl
  have hh : hiNum_B 1 2 = 505156615957489768451911358586043432274459206960107429249614949030054247830727515861172972491761 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_1_3 : certB.Jof 1 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 3 := by
  show certB.Jof 1 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up7 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_1_3_lo, DrowBallBox.B_comp_1_3_hi]
  have hl : loNum_B 1 3 = 6348998643497504507586546090945900992698864193568476043687164334424696209985082183509628993015222 := rfl
  have hh : hiNum_B 1 3 = 6349004345492154502619825326565896861900239453898614281180571913998816565936593007754807001962238 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_1_4 : certB.Jof 1 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 4 := by
  show certB.Jof 1 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up7 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_1_4_lo, DrowBallBox.B_comp_1_4_hi]
  have hl : loNum_B 1 4 = -185850607253278002108166717698080132992715178717398707361213262825792588144056875077905130585838 := rfl
  have hh : hiNum_B 1 4 = -185850209670824946672350093718590463728044711543244186893708750082506208314872518312727101226298 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_1_5 : certB.Jof 1 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 5 := by
  show certB.Jof 1 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up7 5)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_1_5_lo, DrowBallBox.B_comp_1_5_hi]
  have hl : loNum_B 1 5 = 0 := rfl
  have hh : hiNum_B 1 5 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_1_6 : certB.Jof 1 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 6 := by
  show certB.Jof 1 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up7 6)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_1_6_lo, DrowBallBox.B_comp_1_6_hi]
  have hl : loNum_B 1 6 = -14190955278263618779071195841414037504365147304428661828390098098629776395353439241641216066782449 := rfl
  have hh : hiNum_B 1 6 = -14190947809981727994261975108427437146109313868133671323138240872716668864134410918392898417448276 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_1_7 : certB.Jof 1 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 7 := by
  show certB.Jof 1 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 1 7 = 0 := rfl
  have hh : hiNum_B 1 7 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_1_8 : certB.Jof 1 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 8 := by
  show certB.Jof 1 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 1 8 = 0 := rfl
  have hh : hiNum_B 1 8 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_1_9 : certB.Jof 1 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 9 := by
  show certB.Jof 1 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 1 9 = 0 := rfl
  have hh : hiNum_B 1 9 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_1_10 : certB.Jof 1 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 10 := by
  show certB.Jof 1 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 1 10 = 0 := rfl
  have hh : hiNum_B 1 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_1_11 : certB.Jof 1 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 1 11 := by
  show certB.Jof 1 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 1) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 1 11 = 0 := rfl
  have hh : hiNum_B 1 11 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_2_0 : certB.Jof 2 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 0 := by
  show certB.Jof 2 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up7 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_2_0_lo, DrowBallBox.B_comp_2_0_hi]
  have hl : loNum_B 2 0 = -34055807460251866854075926103193411995553404399695940615739081994315123011123159225890735184468397 := rfl
  have hh : hiNum_B 2 0 = -34055544541879582414940602683182528325541492629086425245503844477177765768066583936275408757443879 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_2_1 : certB.Jof 2 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 1 := by
  show certB.Jof 2 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up7 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_2_1_lo, DrowBallBox.B_comp_2_1_hi]
  have hl : loNum_B 2 1 = -34055807460251866854075926103193411995553404399695940615739081994315123011123159225890735184468397 := rfl
  have hh : hiNum_B 2 1 = -34055544541879582414940602683182528325541492629086425245503844477177765768066583936275408757443879 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_2_2 : certB.Jof 2 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 2 := by
  show certB.Jof 2 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up7 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_2_2_lo, DrowBallBox.B_comp_2_2_hi]
  have hl : loNum_B 2 2 = -34055807460251866854075926103193411995553404399695940615739081994315123011123159225890735184468397 := rfl
  have hh : hiNum_B 2 2 = -34055544541879582414940602683182528325541492629086425245503844477177765768066583936275408757443879 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_2_3 : certB.Jof 2 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 3 := by
  show certB.Jof 2 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up7 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_2_3_lo, DrowBallBox.B_comp_2_3_hi]
  have hl : loNum_B 2 3 = -24479559838039370162664256963601291087298942942897010091399484715825601401401798538440976295996499 := rfl
  have hh : hiNum_B 2 3 = -24479301607934786274333509425983581937232935960447928528660439441901663646003319207939425433246812 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_2_4 : certB.Jof 2 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 4 := by
  show certB.Jof 2 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up7 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_2_4_lo, DrowBallBox.B_comp_2_4_hi]
  have hl : loNum_B 2 4 = -1741310037014721979488754587236694559999576662486226330129260420151929121354549269276013741210207 := rfl
  have hh : hiNum_B 2 4 = -1741307722380867976311498329739643746632609550705792490779796523925981471859514741953603909408173 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_2_5 : certB.Jof 2 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 5 := by
  show certB.Jof 2 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up7 5)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_2_5_lo, DrowBallBox.B_comp_2_5_hi]
  have hl : loNum_B 2 5 = 0 := rfl
  have hh : hiNum_B 2 5 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_2_6 : certB.Jof 2 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 6 := by
  show certB.Jof 2 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up7 6)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_2_6_lo, DrowBallBox.B_comp_2_6_hi]
  have hl : loNum_B 2 6 = -33818790654609966107697829117170340314928993925631971811623806509898009110692049197252477079336648 := rfl
  have hh : hiNum_B 2 6 = -33818630663649005779732488046331699373564701437911522149884392340854067180563152137876677405448794 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_2_7 : certB.Jof 2 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 7 := by
  show certB.Jof 2 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 2 7 = 0 := rfl
  have hh : hiNum_B 2 7 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_2_8 : certB.Jof 2 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 8 := by
  show certB.Jof 2 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 2 8 = 0 := rfl
  have hh : hiNum_B 2 8 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_2_9 : certB.Jof 2 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 9 := by
  show certB.Jof 2 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 2 9 = 0 := rfl
  have hh : hiNum_B 2 9 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_2_10 : certB.Jof 2 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 10 := by
  show certB.Jof 2 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 2 10 = 0 := rfl
  have hh : hiNum_B 2 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_2_11 : certB.Jof 2 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 2 11 := by
  show certB.Jof 2 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 2) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 2 11 = 0 := rfl
  have hh : hiNum_B 2 11 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_3_0 : certB.Jof 3 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 0 := by
  show certB.Jof 3 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up7 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_3_0_lo, DrowBallBox.B_comp_3_0_hi]
  have hl : loNum_B 3 0 = 9447599009806436259864042507053040273594418526031706002642417967699979629137242861081756639694156 := rfl
  have hh : hiNum_B 3 0 = 9447603019266328222004186360842027757547758259487941368111480412702066357308180226672168849385791 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_3_1 : certB.Jof 3 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 1 := by
  show certB.Jof 3 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up7 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_3_1_lo, DrowBallBox.B_comp_3_1_hi]
  have hl : loNum_B 3 1 = 0 := rfl
  have hh : hiNum_B 3 1 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_3_2 : certB.Jof 3 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 2 := by
  show certB.Jof 3 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up7 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_3_2_lo, DrowBallBox.B_comp_3_2_hi]
  have hl : loNum_B 3 2 = 0 := rfl
  have hh : hiNum_B 3 2 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_3_3 : certB.Jof 3 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 3 := by
  show certB.Jof 3 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up7 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_3_3_lo, DrowBallBox.B_comp_3_3_hi]
  have hl : loNum_B 3 3 = 0 := rfl
  have hh : hiNum_B 3 3 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_3_4 : certB.Jof 3 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 4 := by
  show certB.Jof 3 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up7 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_3_4_lo, DrowBallBox.B_comp_3_4_hi]
  have hl : loNum_B 3 4 = 0 := rfl
  have hh : hiNum_B 3 4 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_3_5 : certB.Jof 3 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 5 := by
  show certB.Jof 3 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up7 5)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_3_5_lo, DrowBallBox.B_comp_3_5_hi]
  have hl : loNum_B 3 5 = 2135986780510359658340237950676353932702028285720392240156043600821101610142083895081684130904883 := rfl
  have hh : hiNum_B 3 5 = 2135987291331476777452785163758305866696351339853825664127985167039702205772946869307810232212968 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_3_6 : certB.Jof 3 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 6 := by
  show certB.Jof 3 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up7 6)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_3_6_lo, DrowBallBox.B_comp_3_6_hi]
  have hl : loNum_B 3 6 = -15791104019754958870732502999142486629413708540277404856054719766395020655351135782297070563709311 := rfl
  have hh : hiNum_B 3 6 = -15791098922269188502221830354759267804078935400976348316564722151390035121101783974493475584345599 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_3_7 : certB.Jof 3 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 7 := by
  show certB.Jof 3 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 3 7 = 0 := rfl
  have hh : hiNum_B 3 7 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_3_8 : certB.Jof 3 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 8 := by
  show certB.Jof 3 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 3 8 = 0 := rfl
  have hh : hiNum_B 3 8 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_3_9 : certB.Jof 3 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 9 := by
  show certB.Jof 3 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 3 9 = 0 := rfl
  have hh : hiNum_B 3 9 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_3_10 : certB.Jof 3 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 10 := by
  show certB.Jof 3 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 3 10 = 0 := rfl
  have hh : hiNum_B 3 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_3_11 : certB.Jof 3 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 3 11 := by
  show certB.Jof 3 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 3) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 3 11 = 0 := rfl
  have hh : hiNum_B 3 11 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_4_0 : certB.Jof 4 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 0 := by
  show certB.Jof 4 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up7 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_4_0_lo, DrowBallBox.B_comp_4_0_hi]
  have hl : loNum_B 4 0 = -145484916777964040605234788249390417004171553251633411445953594044191501619998346886209612210236 := rfl
  have hh : hiNum_B 4 0 = -145484688078422175822438648163249331045572079089513607747600254691771463934298996336447160522562 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_4_1 : certB.Jof 4 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 1 := by
  show certB.Jof 4 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up7 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_4_1_lo, DrowBallBox.B_comp_4_1_hi]
  have hl : loNum_B 4 1 = -145484916777964040605234788249390417004171553251633411445953594044191501619998346886209612210236 := rfl
  have hh : hiNum_B 4 1 = -145484688078422175822438648163249331045572079089513607747600254691771463934298996336447160522562 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_4_2 : certB.Jof 4 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 2 := by
  show certB.Jof 4 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up7 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_4_2_lo, DrowBallBox.B_comp_4_2_hi]
  have hl : loNum_B 4 2 = 1521401460404055797657217836936076891892073533887293081455283156621227506110642700710138788247777 := rfl
  have hh : hiNum_B 4 2 = 1521401738981833886195946582642075965880918890043789787594124200974970616613274259733315128688154 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_4_3 : certB.Jof 4 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 3 := by
  show certB.Jof 4 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up7 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_4_3_lo, DrowBallBox.B_comp_4_3_hi]
  have hl : loNum_B 4 3 = 0 := rfl
  have hh : hiNum_B 4 3 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_4_4 : certB.Jof 4 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 4 := by
  show certB.Jof 4 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up7 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_4_4_lo, DrowBallBox.B_comp_4_4_hi]
  have hl : loNum_B 4 4 = 618443008337357952841624922596134103489721234099052252789224382992970775930771482336945379083980 := rfl
  have hh : hiNum_B 4 4 = 618443116292401786296881661153077516643351263662243552845804916005381995852476990391157554559869 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_4_5 : certB.Jof 4 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 5 := by
  show certB.Jof 4 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up7 5)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_4_5_lo, DrowBallBox.B_comp_4_5_hi]
  have hl : loNum_B 4 5 = -804293527892159837052131063137790506448835005532261811682548222449287560214285085504733686952884 := rfl
  have hh : hiNum_B 4 5 = -804293413661671796062382954893163368350665209223147363976838503463512364517757956687423733866389 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_4_6 : certB.Jof 4 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 6 := by
  show certB.Jof 4 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up7 6)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_z, DrowBallBox.B_comp_4_6_lo, DrowBallBox.B_comp_4_6_hi]
  have hl : loNum_B 4 6 = -7814202211714864477605843573491717917156735592431693985882730525766010222668926890373099120039269 := rfl
  have hh : hiNum_B 4 6 = -7814201696416330272372823186033018130624300617503179526706606651564312421904834486515804746293812 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_4_7 : certB.Jof 4 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 7 := by
  show certB.Jof 4 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 4 7 = 0 := rfl
  have hh : hiNum_B 4 7 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_4_8 : certB.Jof 4 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 8 := by
  show certB.Jof 4 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 4 8 = 0 := rfl
  have hh : hiNum_B 4 8 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_4_9 : certB.Jof 4 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 9 := by
  show certB.Jof 4 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 4 9 = 0 := rfl
  have hh : hiNum_B 4 9 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_4_10 : certB.Jof 4 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 10 := by
  show certB.Jof 4 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 4 10 = 0 := rfl
  have hh : hiNum_B 4 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_4_11 : certB.Jof 4 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 4 11 := by
  show certB.Jof 4 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (row5 4) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_res_lam]
  have hl : loNum_B 4 11 = 0 := rfl
  have hh : hiNum_B 4 11 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD, RatInterval.ofRat]
  norm_num

theorem cell_5_0 : certB.Jof 5 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 0 := by
  show certB.Jof 5 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (5 : Fin 12) (0 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_5_0_iv]
  have hl : loNum_B 5 0 = 170660567421987790294266689321679124310012164911003058457863069469052197117624767086129203460742995 := rfl
  have hh : hiNum_B 5 0 = 170663949461375167554060716324520591155654851247050805553014442036984889259615952488992227912354391 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_1 : certB.Jof 5 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 1 := by
  show certB.Jof 5 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (5 : Fin 12) (1 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_5_1_iv]
  have hl : loNum_B 5 1 = 163794647439828309874903191644658241781364376956814969407562531066107379334516231605420689518025107 := rfl
  have hh : hiNum_B 5 1 = 163798021725172960565060549573340825562407838885027401843972992121902136877429985543814975630472305 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_2 : certB.Jof 5 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 2 := by
  show certB.Jof 5 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (5 : Fin 12) (2 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_5_2_iv]
  have hl : loNum_B 5 2 = 163703623550066169627282798376481685369898970919666583535885024413439890753622269681531975745072757 := rfl
  have hh : hiNum_B 5 2 = 163706997497423357497938377846689564843706592004869817808094468642793305740763066406364529796951881 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_3 : certB.Jof 5 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 3 := by
  show certB.Jof 5 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (5 : Fin 12) (3 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_5_3_iv]
  have hl : loNum_B 5 3 = 164420291811622088458282446774572012710197598681231624138292799932209153212242264791970533076801741 := rfl
  have hh : hiNum_B 5 3 = 164423630130508166208051620208758083508122170316098479318239408173418557171066592533315225334283007 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_4 : certB.Jof 5 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 4 := by
  show certB.Jof 5 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (5 : Fin 12) (4 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_5_4_iv]
  have hl : loNum_B 5 4 = 36039592297937896666357608003640104808873819388372473799214993007865800041119905941193644309536 := rfl
  have hh : hiNum_B 5 4 = 36049497637777148800480572231907338628353111842913970395244734662914226779089001984394467006586 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_5 : certB.Jof 5 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 5 := by
  show certB.Jof 5 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (5 : Fin 12) (5 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_5_5_iv]
  have hl : loNum_B 5 5 = -565366438466317629212581397131891781741905989540836881059974204390338033190633436432576617712800 := rfl
  have hh : hiNum_B 5 5 = -565365739692433023297152513722072885806812716512117897753502983582898752308031256401603934107716 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_6 : certB.Jof 5 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 6 := by
  show certB.Jof 5 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (5 : Fin 12) (6 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_5_6_iv]
  have hl : loNum_B 5 6 = 80449752529400414903824645703531064081472738191919758789068649195690402747427589085890476287895626 := rfl
  have hh : hiNum_B 5 6 = 80451646377011636131394667836501547330765993739681996271417412251034594342292559172055489057286923 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_7 : certB.Jof 5 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 7 := by
  show certB.Jof 5 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 0) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_0_0_lo, DrowBallBox.B_comp_0_0_hi]
  have hl : loNum_B 5 7 = -635934054750534737471283918525032057550590314380880240685761217703621576332669676333335542385607 := rfl
  have hh : hiNum_B 5 7 = -635933387355719457923727501586821671909043866978792160524222117450487790336249701676397422326843 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_8 : certB.Jof 5 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 8 := by
  show certB.Jof 5 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 0) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_1_0_lo, DrowBallBox.B_comp_1_0_hi]
  have hl : loNum_B 5 8 = 1161729602426921880602112950424492775132732751163589356903922778427971098860870592844599431869695 := rfl
  have hh : hiNum_B 5 8 = 1161730476257958164384985366239773198840291012962645522748988019838315456864194723104099172464315 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_9 : certB.Jof 5 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 9 := by
  show certB.Jof 5 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 0) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_2_0_lo, DrowBallBox.B_comp_2_0_hi]
  have hl : loNum_B 5 9 = 34055544541879582414940602683182528325541492629086425245503844477177765768066583936275408757443879 := rfl
  have hh : hiNum_B 5 9 = 34055807460251866854075926103193411995553404399695940615739081994315123011123159225890735184468397 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_10 : certB.Jof 5 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 10 := by
  show certB.Jof 5 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 0) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_3_0_lo, DrowBallBox.B_comp_3_0_hi]
  have hl : loNum_B 5 10 = -9447603019266328222004186360842027757547758259487941368111480412702066357308180226672168849385791 := rfl
  have hh : hiNum_B 5 10 = -9447599009806436259864042507053040273594418526031706002642417967699979629137242861081756639694156 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_5_11 : certB.Jof 5 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 5 11 := by
  show certB.Jof 5 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 0) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_4_0_lo, DrowBallBox.B_comp_4_0_hi]
  have hl : loNum_B 5 11 = 145484688078422175822438648163249331045572079089513607747600254691771463934298996336447160522562 := rfl
  have hh : hiNum_B 5 11 = 145484916777964040605234788249390417004171553251633411445953594044191501619998346886209612210236 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_0 : certB.Jof 6 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 0 := by
  show certB.Jof 6 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (6 : Fin 12) (0 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_6_0_iv]
  have hl : loNum_B 6 0 = 163794647439828309874903191644658241781364376956814969407562531066107379334516231605420689518025107 := rfl
  have hh : hiNum_B 6 0 = 163798021725172960565060549573340825562407838885027401843972992121902136877429985543814975630472305 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_1 : certB.Jof 6 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 1 := by
  show certB.Jof 6 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (6 : Fin 12) (1 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_6_1_iv]
  have hl : loNum_B 6 1 = 168676536902507772572501664108823862585633246647912705650186428492363706460603874653105432682899205 := rfl
  have hh : hiNum_B 6 1 = 168679913527944742134143445665595685218942899341638007772126617276015271880771171844532331428840805 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_2 : certB.Jof 6 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 2 := by
  show certB.Jof 6 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (6 : Fin 12) (2 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_6_2_iv]
  have hl : loNum_B 6 2 = 163041931732598722476968084580215495607448015756963948106063560147361159088867308340366457314553556 := rfl
  have hh : hiNum_B 6 2 = 163045306008907301056921372700848530376205947515500343123206310502069555373036242879805006971004409 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_3 : certB.Jof 6 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 3 := by
  show certB.Jof 6 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (6 : Fin 12) (3 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_6_3_iv]
  have hl : loNum_B 6 3 = 164420291811622088458282446774572012710197598681231624138292799932209153212242264791970533076801741 := rfl
  have hh : hiNum_B 6 3 = 164423630130508166208051620208758083508122170316098479318239408173418557171066592533315225334283007 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_4 : certB.Jof 6 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 4 := by
  show certB.Jof 6 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (6 : Fin 12) (4 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_6_4_iv]
  have hl : loNum_B 6 4 = 36039592297937896666357608003640104808873819388372473799214993007865800041119905941193644309536 := rfl
  have hh : hiNum_B 6 4 = 36049497637777148800480572231907338628353111842913970395244734662914226779089001984394467006586 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_5 : certB.Jof 6 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 5 := by
  show certB.Jof 6 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (6 : Fin 12) (5 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_6_5_iv]
  have hl : loNum_B 6 5 = 329836700196896536122041096718788391082887340568070241442098041050063969324699198970996259769658 := rfl
  have hh : hiNum_B 6 5 = 329836992000200266200746688953418401428879601398335794853844577415967174520741235858997717844673 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_6 : certB.Jof 6 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 6 := by
  show certB.Jof 6 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (6 : Fin 12) (6 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_6_6_iv]
  have hl : loNum_B 6 6 = 82996927627756167093318484315330323882537254814195821881282022199000380324064720956263360949440871 := rfl
  have hh : hiNum_B 6 6 = 82998814612119495780762380072597002911888988051784694151699983845864245831800762697211491979400469 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_7 : certB.Jof 6 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 7 := by
  show certB.Jof 6 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 1) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_0_1_lo, DrowBallBox.B_comp_0_1_hi]
  have hl : loNum_B 6 7 = -2283322059107186984636407375728412392565067250161503269648537059133531011396501230522181905641540 := rfl
  have hh : hiNum_B 6 7 = -2283321006287451861730544825883400795435965045198637198715477142030015819683296974473799700402615 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_8 : certB.Jof 6 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 8 := by
  show certB.Jof 6 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 1) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_1_1_lo, DrowBallBox.B_comp_1_1_hi]
  have hl : loNum_B 6 8 = 1161729602426921880602112950424492775132732751163589356903922778427971098860870592844599431869695 := rfl
  have hh : hiNum_B 6 8 = 1161730476257958164384985366239773198840291012962645522748988019838315456864194723104099172464315 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_9 : certB.Jof 6 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 9 := by
  show certB.Jof 6 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 1) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_2_1_lo, DrowBallBox.B_comp_2_1_hi]
  have hl : loNum_B 6 9 = 34055544541879582414940602683182528325541492629086425245503844477177765768066583936275408757443879 := rfl
  have hh : hiNum_B 6 9 = 34055807460251866854075926103193411995553404399695940615739081994315123011123159225890735184468397 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_10 : certB.Jof 6 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 10 := by
  show certB.Jof 6 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 1) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_3_1_lo, DrowBallBox.B_comp_3_1_hi]
  have hl : loNum_B 6 10 = 0 := rfl
  have hh : hiNum_B 6 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_6_11 : certB.Jof 6 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 6 11 := by
  show certB.Jof 6 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 1) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_4_1_lo, DrowBallBox.B_comp_4_1_hi]
  have hl : loNum_B 6 11 = 145484688078422175822438648163249331045572079089513607747600254691771463934298996336447160522562 := rfl
  have hh : hiNum_B 6 11 = 145484916777964040605234788249390417004171553251633411445953594044191501619998346886209612210236 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_0 : certB.Jof 7 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 0 := by
  show certB.Jof 7 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (7 : Fin 12) (0 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_7_0_iv]
  have hl : loNum_B 7 0 = 163703623550066169627282798376481685369898970919666583535885024413439890753622269681531975745072757 := rfl
  have hh : hiNum_B 7 0 = 163706997497423357497938377846689564843706592004869817808094468642793305740763066406364529796951881 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_1 : certB.Jof 7 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 1 := by
  show certB.Jof 7 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (7 : Fin 12) (1 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_7_1_iv]
  have hl : loNum_B 7 1 = 163041931732598722476968084580215495607448015756963948106063560147361159088867308340366457314553556 := rfl
  have hh : hiNum_B 7 1 = 163045306008907301056921372700848530376205947515500343123206310502069555373036242879805006971004409 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_2 : certB.Jof 7 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 2 := by
  show certB.Jof 7 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (7 : Fin 12) (2 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_7_2_iv]
  have hl : loNum_B 7 2 = 166106983592715689747147754406505549985721889121210086410060935998456935694636444019790820469707599 := rfl
  have hh : hiNum_B 7 2 = 166110358130796827556666780474554062905587320785482393220938281796485564133495968284173229528153423 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_3 : certB.Jof 7 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 3 := by
  show certB.Jof 7 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (7 : Fin 12) (3 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_7_3_iv]
  have hl : loNum_B 7 3 = 164066358903255733309112845041047135212812796354330381304806174715036887608218520100362926348154701 := rfl
  have hh : hiNum_B 7 3 = 164069696876447193588135596310943011214341593688965227490127193810862585618668320248678158699042134 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_4 : certB.Jof 7 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 4 := by
  show certB.Jof 7 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (7 : Fin 12) (4 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_7_4_iv]
  have hl : loNum_B 7 4 = 183222585075021935296254023234691509511820275488309298449285332735050937886671157325030856119810 := rfl
  have hh : hiNum_B 7 4 = 183232464965766955461453548895305872935223254112302997289263666037769934365741711751478777372158 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_5 : certB.Jof 7 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 5 := by
  show certB.Jof 7 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (7 : Fin 12) (5 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_7_5_iv]
  have hl : loNum_B 7 5 = -520670253240816561782171931969350152039771157922482555431925547118874038376983976119440558882286 := rfl
  have hh : hiNum_B 7 5 = -520670050891327528061440630227274582406850550765221134176383579185469435151072397195517758323754 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_6 : certB.Jof 7 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 6 := by
  show certB.Jof 7 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (7 : Fin 12) (6 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_7_6_iv]
  have hl : loNum_B 7 6 = 86669250853971807016254404539308777328638044107050206509886421608099021862744165803097145452624728 := rfl
  have hh : hiNum_B 7 6 = 86671134907948416179883007871966663239527926356758811013034243856999605694586732623871707466120196 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_7 : certB.Jof 7 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 7 := by
  show certB.Jof 7 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 2) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_0_2_lo, DrowBallBox.B_comp_0_2_hi]
  have hl : loNum_B 7 7 = -1521401921935746153607672843661673705706869025788535621660410226157192579819413108294391498597912 := rfl
  have hh : hiNum_B 7 7 = -1521401277450162745486597649461012200007007786052386998449906854622864969335770407348030677596351 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_8 : certB.Jof 7 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 8 := by
  show certB.Jof 7 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 2) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_1_2_lo, DrowBallBox.B_comp_1_2_hi]
  have hl : loNum_B 7 8 = -505156615957489768451911358586043432274459206960107429249614949030054247830727515861172972491761 := rfl
  have hh : hiNum_B 7 8 = -505156109600004816657444074050595279855477397977457995594550282494432630510182208547764155080886 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_9 : certB.Jof 7 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 9 := by
  show certB.Jof 7 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 2) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_2_2_lo, DrowBallBox.B_comp_2_2_hi]
  have hl : loNum_B 7 9 = 34055544541879582414940602683182528325541492629086425245503844477177765768066583936275408757443879 := rfl
  have hh : hiNum_B 7 9 = 34055807460251866854075926103193411995553404399695940615739081994315123011123159225890735184468397 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_10 : certB.Jof 7 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 10 := by
  show certB.Jof 7 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 2) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_3_2_lo, DrowBallBox.B_comp_3_2_hi]
  have hl : loNum_B 7 10 = 0 := rfl
  have hh : hiNum_B 7 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_7_11 : certB.Jof 7 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 7 11 := by
  show certB.Jof 7 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 2) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_4_2_lo, DrowBallBox.B_comp_4_2_hi]
  have hl : loNum_B 7 11 = -1521401738981833886195946582642075965880918890043789787594124200974970616613274259733315128688154 := rfl
  have hh : hiNum_B 7 11 = -1521401460404055797657217836936076891892073533887293081455283156621227506110642700710138788247777 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_0 : certB.Jof 8 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 0 := by
  show certB.Jof 8 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (8 : Fin 12) (0 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_8_0_iv]
  have hl : loNum_B 8 0 = 164420291811622088458282446774572012710197598681231624138292799932209153212242264791970533076801741 := rfl
  have hh : hiNum_B 8 0 = 164423630130508166208051620208758083508122170316098479318239408173418557171066592533315225334283007 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_1 : certB.Jof 8 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 1 := by
  show certB.Jof 8 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (8 : Fin 12) (1 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_8_1_iv]
  have hl : loNum_B 8 1 = 164420291811622088458282446774572012710197598681231624138292799932209153212242264791970533076801741 := rfl
  have hh : hiNum_B 8 1 = 164423630130508166208051620208758083508122170316098479318239408173418557171066592533315225334283007 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_2 : certB.Jof 8 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 2 := by
  show certB.Jof 8 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (8 : Fin 12) (2 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_8_2_iv]
  have hl : loNum_B 8 2 = 164066358903255733309112845041047135212812796354330381304806174715036887608218520100362926348154701 := rfl
  have hh : hiNum_B 8 2 = 164069696876447193588135596310943011214341593688965227490127193810862585618668320248678158699042134 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_3 : certB.Jof 8 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 3 := by
  show certB.Jof 8 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (8 : Fin 12) (3 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_8_3_iv]
  have hl : loNum_B 8 3 = 187855921221363129720561178007291544227778025225936824857208240812925159878151925234828482351377934 := rfl
  have hh : hiNum_B 8 3 = 187859264119384383311279087788430428542892073221812704362841763368397124370269508052327942026246090 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_4 : certB.Jof 8 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 4 := by
  show certB.Jof 8 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (8 : Fin 12) (4 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_8_4_iv]
  have hl : loNum_B 8 4 = -235931467679008752312647047996863549525191042658882304475181515730293768990782735865599997068451 := rfl
  have hh : hiNum_B 8 4 = -235921561501826140997141221250701516076655448786813779852404120626633317498410536947616192743412 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_5 : certB.Jof 8 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 5 := by
  show certB.Jof 8 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (8 : Fin 12) (5 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_8_5_iv]
  have hl : loNum_B 8 5 = 0 := rfl
  have hh : hiNum_B 8 5 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_6 : certB.Jof 8 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 6 := by
  show certB.Jof 8 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (8 : Fin 12) (6 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_8_6_iv]
  have hl : loNum_B 8 6 = 63948332765278256101966563146384585537487542362130597001920565979058704547187290533914222789865566 := rfl
  have hh : hiNum_B 8 6 = 63950221558986180143823362773392880252770163969783051047946473419674745811467883531324332682723522 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_7 : certB.Jof 8 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 7 := by
  show certB.Jof 8 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 3) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_0_3_lo, DrowBallBox.B_comp_0_3_hi]
  have hl : loNum_B 8 7 = 0 := rfl
  have hh : hiNum_B 8 7 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_8 : certB.Jof 8 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 8 := by
  show certB.Jof 8 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 3) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_1_3_lo, DrowBallBox.B_comp_1_3_hi]
  have hl : loNum_B 8 8 = -6349004345492154502619825326565896861900239453898614281180571913998816565936593007754807001962238 := rfl
  have hh : hiNum_B 8 8 = -6348998643497504507586546090945900992698864193568476043687164334424696209985082183509628993015222 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_9 : certB.Jof 8 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 9 := by
  show certB.Jof 8 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 3) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_2_3_lo, DrowBallBox.B_comp_2_3_hi]
  have hl : loNum_B 8 9 = 24479301607934786274333509425983581937232935960447928528660439441901663646003319207939425433246812 := rfl
  have hh : hiNum_B 8 9 = 24479559838039370162664256963601291087298942942897010091399484715825601401401798538440976295996499 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_10 : certB.Jof 8 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 10 := by
  show certB.Jof 8 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 3) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_3_3_lo, DrowBallBox.B_comp_3_3_hi]
  have hl : loNum_B 8 10 = 0 := rfl
  have hh : hiNum_B 8 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_8_11 : certB.Jof 8 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 8 11 := by
  show certB.Jof 8 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 3) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_4_3_lo, DrowBallBox.B_comp_4_3_hi]
  have hl : loNum_B 8 11 = 0 := rfl
  have hh : hiNum_B 8 11 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_0 : certB.Jof 9 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 0 := by
  show certB.Jof 9 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (9 : Fin 12) (0 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_9_0_iv]
  have hl : loNum_B 9 0 = 36039592297937896666357608003640104808873819388372473799214993007865800041119905941193644309536 := rfl
  have hh : hiNum_B 9 0 = 36049497637777148800480572231907338628353111842913970395244734662914226779089001984394467006586 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_1 : certB.Jof 9 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 1 := by
  show certB.Jof 9 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (9 : Fin 12) (1 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_9_1_iv]
  have hl : loNum_B 9 1 = 36039592297937896666357608003640104808873819388372473799214993007865800041119905941193644309536 := rfl
  have hh : hiNum_B 9 1 = 36049497637777148800480572231907338628353111842913970395244734662914226779089001984394467006586 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_2 : certB.Jof 9 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 2 := by
  show certB.Jof 9 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (9 : Fin 12) (2 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_9_2_iv]
  have hl : loNum_B 9 2 = 183222585075021935296254023234691509511820275488309298449285332735050937886671157325030856119810 := rfl
  have hh : hiNum_B 9 2 = 183232464965766955461453548895305872935223254112302997289263666037769934365741711751478777372158 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_3 : certB.Jof 9 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 3 := by
  show certB.Jof 9 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (9 : Fin 12) (3 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_9_3_iv]
  have hl : loNum_B 9 3 = -235931467679008752312647047996863549525191042658882304475181515730293768990782735865599997068451 := rfl
  have hh : hiNum_B 9 3 = -235921561501826140997141221250701516076655448786813779852404120626633317498410536947616192743412 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_4 : certB.Jof 9 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 4 := by
  show certB.Jof 9 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (9 : Fin 12) (4 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_9_4_iv]
  have hl : loNum_B 9 4 = 261090711413229667881212034149271991084169044608095226274472316698320975854636873838491961871082 := rfl
  have hh : hiNum_B 9 4 = 261090872352749450540882371761451538459338761284189089908137346037632216102078960362363232959216 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_5 : certB.Jof 9 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 5 := by
  show certB.Jof 9 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (9 : Fin 12) (5 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_9_5_iv]
  have hl : loNum_B 9 5 = -27652827979220786989267236293182739763993208262538600441600591279618785731038679042878735007379 := rfl
  have hh : hiNum_B 9 5 = -27652813108185850999550056726038369861127927747293074247654009466712846106996639914157104831228 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_6 : certB.Jof 9 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 6 := by
  show certB.Jof 9 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (9 : Fin 12) (6 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_9_6_iv]
  have hl : loNum_B 9 6 = 580240267991768449100600044155440450757909061528373894283916659053512613714299771431941228596498 := rfl
  have hh : hiNum_B 9 6 = 580246904688812671402219661368991631516346902291056583171857572135048283510930428391490791119704 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_7 : certB.Jof 9 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 7 := by
  show certB.Jof 9 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 4) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_0_4_lo, DrowBallBox.B_comp_0_4_hi]
  have hl : loNum_B 9 7 = 0 := rfl
  have hh : hiNum_B 9 7 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_8 : certB.Jof 9 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 8 := by
  show certB.Jof 9 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 4) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_1_4_lo, DrowBallBox.B_comp_1_4_hi]
  have hl : loNum_B 9 8 = 185850209670824946672350093718590463728044711543244186893708750082506208314872518312727101226298 := rfl
  have hh : hiNum_B 9 8 = 185850607253278002108166717698080132992715178717398707361213262825792588144056875077905130585838 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_9 : certB.Jof 9 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 9 := by
  show certB.Jof 9 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 4) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_2_4_lo, DrowBallBox.B_comp_2_4_hi]
  have hl : loNum_B 9 9 = 1741307722380867976311498329739643746632609550705792490779796523925981471859514741953603909408173 := rfl
  have hh : hiNum_B 9 9 = 1741310037014721979488754587236694559999576662486226330129260420151929121354549269276013741210207 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_10 : certB.Jof 9 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 10 := by
  show certB.Jof 9 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 4) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_3_4_lo, DrowBallBox.B_comp_3_4_hi]
  have hl : loNum_B 9 10 = 0 := rfl
  have hh : hiNum_B 9 10 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_9_11 : certB.Jof 9 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 9 11 := by
  show certB.Jof 9 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 4) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_4_4_lo, DrowBallBox.B_comp_4_4_hi]
  have hl : loNum_B 9 11 = -618443116292401786296881661153077516643351263662243552845804916005381995852476990391157554559869 := rfl
  have hh : hiNum_B 9 11 = -618443008337357952841624922596134103489721234099052252789224382992970775930771482336945379083980 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_0 : certB.Jof 10 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 0 := by
  show certB.Jof 10 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (10 : Fin 12) (0 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_10_0_iv]
  have hl : loNum_B 10 0 = -565366438466317629212581397131891781741905989540836881059974204390338033190633436432576617712800 := rfl
  have hh : hiNum_B 10 0 = -565365739692433023297152513722072885806812716512117897753502983582898752308031256401603934107716 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_1 : certB.Jof 10 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 1 := by
  show certB.Jof 10 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (10 : Fin 12) (1 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_10_1_iv]
  have hl : loNum_B 10 1 = 329836700196896536122041096718788391082887340568070241442098041050063969324699198970996259769658 := rfl
  have hh : hiNum_B 10 1 = 329836992000200266200746688953418401428879601398335794853844577415967174520741235858997717844673 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_2 : certB.Jof 10 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 2 := by
  show certB.Jof 10 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (10 : Fin 12) (2 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_10_2_iv]
  have hl : loNum_B 10 2 = -520670253240816561782171931969350152039771157922482555431925547118874038376983976119440558882286 := rfl
  have hh : hiNum_B 10 2 = -520670050891327528061440630227274582406850550765221134176383579185469435151072397195517758323754 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_3 : certB.Jof 10 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 3 := by
  show certB.Jof 10 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (10 : Fin 12) (3 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_10_3_iv]
  have hl : loNum_B 10 3 = 0 := rfl
  have hh : hiNum_B 10 3 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_4 : certB.Jof 10 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 4 := by
  show certB.Jof 10 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (10 : Fin 12) (4 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_10_4_iv]
  have hl : loNum_B 10 4 = -27652827979220786989267236293182739763993208262538600441600591279618785731038679042878735007379 := rfl
  have hh : hiNum_B 10 4 = -27652813108185850999550056726038369861127927747293074247654009466712846106996639914157104831228 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_5 : certB.Jof 10 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 5 := by
  show certB.Jof 10 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (10 : Fin 12) (5 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_10_5_iv]
  have hl : loNum_B 10 5 = 732067607795770244080828461666881457599424965119927876776274066619894599451048593848943666809425 := rfl
  have hh : hiNum_B 10 5 = 732067799487542361836598704810624687978447291526344223034719344652109052011057063752500133837268 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_6 : certB.Jof 10 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 6 := by
  show certB.Jof 10 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (10 : Fin 12) (6 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_10_6_iv]
  have hl : loNum_B 10 6 = -612437468796464817620484959171626351171659329557866967458773630472426641726247913694081373396748 := rfl
  have hh : hiNum_B 10 6 = -612436114070919168036699771933489665174653916565156071455050434079893896811598678169255786697519 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_7 : certB.Jof 10 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 7 := by
  show certB.Jof 10 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 5) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_0_5_lo, DrowBallBox.B_comp_0_5_hi]
  have hl : loNum_B 10 7 = 185850211415007430479042463801775560460429302847758101741776948074031892819419395139750494653837 := rfl
  have hh : hiNum_B 10 7 = 185850605509079638005510722033999226420217284426433756021677639865091021379132570022810020556607 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_8 : certB.Jof 10 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 8 := by
  show certB.Jof 10 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 5) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_1_5_lo, DrowBallBox.B_comp_1_5_hi]
  have hl : loNum_B 10 8 = 0 := rfl
  have hh : hiNum_B 10 8 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_9 : certB.Jof 10 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 9 := by
  show certB.Jof 10 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 5) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_2_5_lo, DrowBallBox.B_comp_2_5_hi]
  have hl : loNum_B 10 9 = 0 := rfl
  have hh : hiNum_B 10 9 = 0 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_10 : certB.Jof 10 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 10 := by
  show certB.Jof 10 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 5) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_3_5_lo, DrowBallBox.B_comp_3_5_hi]
  have hl : loNum_B 10 10 = -2135987291331476777452785163758305866696351339853825664127985167039702205772946869307810232212968 := rfl
  have hh : hiNum_B 10 10 = -2135986780510359658340237950676353932702028285720392240156043600821101610142083895081684130904883 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_10_11 : certB.Jof 10 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 10 11 := by
  show certB.Jof 10 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 5) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_4_5_lo, DrowBallBox.B_comp_4_5_hi]
  have hl : loNum_B 10 11 = 804293413661671796062382954893163368350665209223147363976838503463512364517757956687423733866389 := rfl
  have hh : hiNum_B 10 11 = 804293527892159837052131063137790506448835005532261811682548222449287560214285085504733686952884 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_0 : certB.Jof 11 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 0 := by
  show certB.Jof 11 0 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (11 : Fin 12) (0 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_11_0_iv]
  have hl : loNum_B 11 0 = 80449752529400414903824645703531064081472738191919758789068649195690402747427589085890476287895626 := rfl
  have hh : hiNum_B 11 0 = 80451646377011636131394667836501547330765993739681996271417412251034594342292559172055489057286923 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_1 : certB.Jof 11 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 1 := by
  show certB.Jof 11 1 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (11 : Fin 12) (1 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_11_1_iv]
  have hl : loNum_B 11 1 = 82996927627756167093318484315330323882537254814195821881282022199000380324064720956263360949440871 := rfl
  have hh : hiNum_B 11 1 = 82998814612119495780762380072597002911888988051784694151699983845864245831800762697211491979400469 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_2 : certB.Jof 11 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 2 := by
  show certB.Jof 11 2 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (11 : Fin 12) (2 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_11_2_iv]
  have hl : loNum_B 11 2 = 86669250853971807016254404539308777328638044107050206509886421608099021862744165803097145452624728 := rfl
  have hh : hiNum_B 11 2 = 86671134907948416179883007871966663239527926356758811013034243856999605694586732623871707466120196 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_3 : certB.Jof 11 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 3 := by
  show certB.Jof 11 3 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (11 : Fin 12) (3 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_11_3_iv]
  have hl : loNum_B 11 3 = 63948332765278256101966563146384585537487542362130597001920565979058704547187290533914222789865566 := rfl
  have hh : hiNum_B 11 3 = 63950221558986180143823362773392880252770163969783051047946473419674745811467883531324332682723522 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_4 : certB.Jof 11 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 4 := by
  show certB.Jof 11 4 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (11 : Fin 12) (4 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_11_4_iv]
  have hl : loNum_B 11 4 = 580240267991768449100600044155440450757909061528373894283916659053512613714299771431941228596498 := rfl
  have hh : hiNum_B 11 4 = 580246904688812671402219661368991631516346902291056583171857572135048283510930428391490791119704 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_5 : certB.Jof 11 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 5 := by
  show certB.Jof 11 5 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (11 : Fin 12) (5 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_11_5_iv]
  have hl : loNum_B 11 5 = -612437468796464817620484959171626351171659329557866967458773630472426641726247913694081373396748 := rfl
  have hh : hiNum_B 11 5 = -612436114070919168036699771933489665174653916565156071455050434079893896811598678169255786697519 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_6 : certB.Jof 11 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 6 := by
  show certB.Jof 11 6 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (11 : Fin 12) (6 : Fin 12)
  simp only [km_gridTable]
  rw [Ladder49.B49_jt_11_6_iv]
  have hl : loNum_B 11 6 = 86859446969471371176948263885258773708722020718382336628733637825161476621956007276008166048354844 := rfl
  have hh : hiNum_B 11 6 = 86860576249236657198147962139862273905431921305650156266777225651657103285311516838615810866077917 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_7 : certB.Jof 11 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 7 := by
  show certB.Jof 11 7 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 6) (up5 0)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_0_6_lo, DrowBallBox.B_comp_0_6_hi]
  have hl : loNum_B 11 7 = 9029120805924275987757330138661895801361532424570198447069998465751182751664232844384797984763772 := rfl
  have hh : hiNum_B 11 7 = 9029122596683253373823269305256320403171987278296286874731089181330320021119749342973100170512084 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_8 : certB.Jof 11 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 8 := by
  show certB.Jof 11 8 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 6) (up5 1)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_1_6_lo, DrowBallBox.B_comp_1_6_hi]
  have hl : loNum_B 11 8 = 14190947809981727994261975108427437146109313868133671323138240872716668864134410918392898417448276 := rfl
  have hh : hiNum_B 11 8 = 14190955278263618779071195841414037504365147304428661828390098098629776395353439241641216066782449 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_9 : certB.Jof 11 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 9 := by
  show certB.Jof 11 9 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 6) (up5 2)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_2_6_lo, DrowBallBox.B_comp_2_6_hi]
  have hl : loNum_B 11 9 = 33818630663649005779732488046331699373564701437911522149884392340854067180563152137876677405448794 := rfl
  have hh : hiNum_B 11 9 = 33818790654609966107697829117170340314928993925631971811623806509898009110692049197252477079336648 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_10 : certB.Jof 11 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 10 := by
  show certB.Jof 11 10 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 6) (up5 3)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_3_6_lo, DrowBallBox.B_comp_3_6_hi]
  have hl : loNum_B 11 10 = 15791098922269188502221830354759267804078935400976348316564722151390035121101783974493475584345599 := rfl
  have hh : hiNum_B 11 10 = 15791104019754958870732502999142486629413708540277404856054719766395020655351135782297070563709311 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem cell_11_11 : certB.Jof 11 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) 11 11 := by
  show certB.Jof 11 11 = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) (kkt12 6) (up5 4)
  simp only [km_gridTable]
  rw [Lead.JtBall2.Jt''_kkt_lam]
  simp only [RatInterval.neg]
  rw [DrowBallBox.B_comp_4_6_lo, DrowBallBox.B_comp_4_6_hi]
  have hl : loNum_B 11 11 = 7814201696416330272372823186033018130624300617503179526706606651564312421904834486515804746293812 := rfl
  have hh : hiNum_B 11 11 = 7814202211714864477605843573491717917156735592431693985882730525766010222668926890373099120039269 := rfl
  simp only [HsumCert.Jof, certB, hl, hh, Dz_eq, km_gridDown, km_gridUp, km_gridD]
  norm_num

theorem gridBridge : ∀ r c : Fin 12, certB.Jof r c = km_gridTable km_gridD (Lead.JtBall2.Jt'' (Lead.HessBox.HessOfBox HJBoxInstant.d2xBox HJBoxInstant.d2yBox)) r c := by
  intro r c
  fin_cases r <;> fin_cases c
  · exact cell_0_0
  · exact cell_0_1
  · exact cell_0_2
  · exact cell_0_3
  · exact cell_0_4
  · exact cell_0_5
  · exact cell_0_6
  · exact cell_0_7
  · exact cell_0_8
  · exact cell_0_9
  · exact cell_0_10
  · exact cell_0_11
  · exact cell_1_0
  · exact cell_1_1
  · exact cell_1_2
  · exact cell_1_3
  · exact cell_1_4
  · exact cell_1_5
  · exact cell_1_6
  · exact cell_1_7
  · exact cell_1_8
  · exact cell_1_9
  · exact cell_1_10
  · exact cell_1_11
  · exact cell_2_0
  · exact cell_2_1
  · exact cell_2_2
  · exact cell_2_3
  · exact cell_2_4
  · exact cell_2_5
  · exact cell_2_6
  · exact cell_2_7
  · exact cell_2_8
  · exact cell_2_9
  · exact cell_2_10
  · exact cell_2_11
  · exact cell_3_0
  · exact cell_3_1
  · exact cell_3_2
  · exact cell_3_3
  · exact cell_3_4
  · exact cell_3_5
  · exact cell_3_6
  · exact cell_3_7
  · exact cell_3_8
  · exact cell_3_9
  · exact cell_3_10
  · exact cell_3_11
  · exact cell_4_0
  · exact cell_4_1
  · exact cell_4_2
  · exact cell_4_3
  · exact cell_4_4
  · exact cell_4_5
  · exact cell_4_6
  · exact cell_4_7
  · exact cell_4_8
  · exact cell_4_9
  · exact cell_4_10
  · exact cell_4_11
  · exact cell_5_0
  · exact cell_5_1
  · exact cell_5_2
  · exact cell_5_3
  · exact cell_5_4
  · exact cell_5_5
  · exact cell_5_6
  · exact cell_5_7
  · exact cell_5_8
  · exact cell_5_9
  · exact cell_5_10
  · exact cell_5_11
  · exact cell_6_0
  · exact cell_6_1
  · exact cell_6_2
  · exact cell_6_3
  · exact cell_6_4
  · exact cell_6_5
  · exact cell_6_6
  · exact cell_6_7
  · exact cell_6_8
  · exact cell_6_9
  · exact cell_6_10
  · exact cell_6_11
  · exact cell_7_0
  · exact cell_7_1
  · exact cell_7_2
  · exact cell_7_3
  · exact cell_7_4
  · exact cell_7_5
  · exact cell_7_6
  · exact cell_7_7
  · exact cell_7_8
  · exact cell_7_9
  · exact cell_7_10
  · exact cell_7_11
  · exact cell_8_0
  · exact cell_8_1
  · exact cell_8_2
  · exact cell_8_3
  · exact cell_8_4
  · exact cell_8_5
  · exact cell_8_6
  · exact cell_8_7
  · exact cell_8_8
  · exact cell_8_9
  · exact cell_8_10
  · exact cell_8_11
  · exact cell_9_0
  · exact cell_9_1
  · exact cell_9_2
  · exact cell_9_3
  · exact cell_9_4
  · exact cell_9_5
  · exact cell_9_6
  · exact cell_9_7
  · exact cell_9_8
  · exact cell_9_9
  · exact cell_9_10
  · exact cell_9_11
  · exact cell_10_0
  · exact cell_10_1
  · exact cell_10_2
  · exact cell_10_3
  · exact cell_10_4
  · exact cell_10_5
  · exact cell_10_6
  · exact cell_10_7
  · exact cell_10_8
  · exact cell_10_9
  · exact cell_10_10
  · exact cell_10_11
  · exact cell_11_0
  · exact cell_11_1
  · exact cell_11_2
  · exact cell_11_3
  · exact cell_11_4
  · exact cell_11_5
  · exact cell_11_6
  · exact cell_11_7
  · exact cell_11_8
  · exact cell_11_9
  · exact cell_11_10
  · exact cell_11_11

theorem gridBridgeR : ∀ r c : Fin 12, certBR.Jof r c = km_gridTable km_gridD NdBox.JtBox r c :=
  fun r c => gridBridge r c

theorem certB_Yof : certB.Yof = HsumPayload.certReal.Yof := by
  unfold HsumCert.Yof; rfl
theorem certBR_Yof : certBR.Yof = HsumPayload.certReal.Yof := by
  unfold HsumCert.Yof; rfl

/-- hsum 网格形(对齐 NdBox.nd_box 的 hsumB 槽)。 -/
theorem hsumB_grid : ∀ i : Fin 12, ∑ j : Fin 12,
    max |((krawczykMat HsumPayload.certReal.Yof (km_gridTable km_gridD NdBox.JtBox) i j).lo : ℝ)|
      |((krawczykMat HsumPayload.certReal.Yof (km_gridTable km_gridD NdBox.JtBox) i j).hi : ℝ)|
      ≤ (numK_B : ℝ) / (HsumPayload.Ez : ℝ) := by
  have hJ : certB.Jof = km_gridTable km_gridD NdBox.JtBox := funext fun r => funext fun c => gridBridge r c
  have hs := certB_hsum
  rw [hJ, certB_Yof] at hs
  exact hs

theorem hsumRB_grid : ∀ i : Fin 12, ∑ j : Fin 12,
    max |((krawczykMatR (km_gridTable km_gridD NdBox.JtBox) HsumPayload.certReal.Yof i j).lo : ℝ)|
      |((krawczykMatR (km_gridTable km_gridD NdBox.JtBox) HsumPayload.certReal.Yof i j).hi : ℝ)|
      ≤ (numKR_B : ℝ) / (HsumPayload.Ez : ℝ) := by
  have hJ : certBR.Jof = km_gridTable km_gridD NdBox.JtBox := funext fun r => funext fun c => gridBridgeR r c
  have hs := certBR_hsumR
  rw [hJ, certBR_Yof] at hs
  exact hs

/-- hsum 迁到 Jt''(消费点形)。 -/
theorem hsum_Jt : ∀ i : Fin 12, ∑ j : Fin 12,
    max |((krawczykMat HsumPayload.certReal.Yof NdBox.JtBox i j).lo : ℝ)|
      |((krawczykMat HsumPayload.certReal.Yof NdBox.JtBox i j).hi : ℝ)|
      ≤ (numK_B : ℝ) / (HsumPayload.Ez : ℝ) :=
  km_hsum_transfer_grid _ NdBox.JtBox NdBox.JtBox_valid hsumB_grid

theorem hsumR_Jt : ∀ i : Fin 12, ∑ j : Fin 12,
    max |((krawczykMatR NdBox.JtBox HsumPayload.certReal.Yof i j).lo : ℝ)|
      |((krawczykMatR NdBox.JtBox HsumPayload.certReal.Yof i j).hi : ℝ)|
      ≤ (numKR_B : ℝ) / (HsumPayload.Ez : ℝ) :=
  km_hsumR_transfer_grid _ NdBox.JtBox NdBox.JtBox_valid hsumRB_grid

/-- ★ 无条件终定理。 -/
theorem nd_box_final :
    ∃ S : C891RootSpec,
      S.sys = TCSystem ∧ S.boxLo = boxLoCert ∧ S.boxHi = boxHiCert ∧ S.radiusIndex = 6 ∧
        ((boxLoCert 6 : ℝ) ≤ Rstar S ∧ Rstar S ≤ (boxHiCert 6 : ℝ)) ∧ Rstar S < 19 / 50 :=
  NdBox.nd_box _ _ hK0_B hK1_B hK'0_B hK'1_B hresCons_B hsumB_grid hsumRB_grid

end N11Formalization.GridBridge
