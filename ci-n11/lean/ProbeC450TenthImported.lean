import N11Formalization
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthImportedAudit
open scoped Interval
open MeasureTheory
open C450TenthData C450TenthSegment C450GroupedClosedAssembly C450GroupedPacketKernel

theorem actual_segment : C450NormalizedInterface.SegmentNormalized tenth := tenth_paid

theorem actual_integrals (c : Point) (e : ℝ)
    (hr : ‖c‖ ∈ Set.Icc ((31:ℝ)/50) (69/50))
    (he : e ∈ Set.Icc ((4:ℝ)/125) (9/250)) :
    (∫ θ in (0)..(2*Real.pi),
      if dist (angPt θ) c ≤ (19/50:ℝ) then (tenth.W0 nn0).toFun θ else 0) +
    (∫ θ in (0)..(2*Real.pi),
      if dist (hubPt e+(19/50:ℝ) • angPt θ) c ≤ (19/50:ℝ)
        then (tenth.W1 nn1).toFun θ else 0) <
      (2*Real.pi*(tenth.a0:ℝ)+2*Real.pi*(tenth.b0:ℝ))/10 := by
  have h0 : 1-19/50 ≤ ‖c‖ := by linarith [hr.1]
  have h1 : ‖c‖ ≤ 1+19/50 := by linarith [hr.2]
  have he0 : 0 ≤ e := by linarith [he.1]
  have heLo : (tenth.eLo:ℝ) ≤ e := by
    simpa only [tenth,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using he.1
  have heHi : e ≤ (tenth.eHi:ℝ) := by
    simpa only [tenth,Rat.cast_div,Rat.cast_ofNat] using he.2
  exact tenth_paid nn0 nn1 c e h0 h1 he0 heLo heHi

private def Endpoints (ps : List Packet) : Prop :=
  ∀ p ∈ ps, RatInterval.Mem p.R (p.lo:ℝ) ∧ RatInterval.Mem p.R (p.hi:ℝ)

private theorem endpoints_of_checks (ps : List Packet)
    (h : ps.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true) : Endpoints ps := by
  intro p hp
  have hh := (list_all_eq_true (fun p : Packet => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi))
    ps).mp h p hp
  have ho := (of_decide_eq_true hh).1
  have hr : (p.lo:ℝ) ≤ (p.hi:ℝ) := Rat.cast_le.mpr ho
  exact ⟨⟨le_rfl,hr⟩,⟨hr,le_rfl⟩⟩

private theorem append_endpoints {xs ys : List Packet}
    (hx : Endpoints xs) (hy : Endpoints ys) : Endpoints (xs++ys) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hx p hp
  · exact hy p hp

private theorem h01 : Endpoints C450TenthGroupedC01.packets :=
  endpoints_of_checks C450TenthGroupedC01.packets C450TenthGroupedC01.endpoint_checks
private theorem h02 : Endpoints C450TenthGroupedC02.packets :=
  endpoints_of_checks C450TenthGroupedC02.packets C450TenthGroupedC02.endpoint_checks
private theorem h03 : Endpoints C450TenthGroupedC03.packets :=
  endpoints_of_checks C450TenthGroupedC03.packets C450TenthGroupedC03.endpoint_checks
private theorem h04 : Endpoints C450TenthGroupedC04.packets :=
  endpoints_of_checks C450TenthGroupedC04.packets C450TenthGroupedC04.endpoint_checks
private theorem h05 : Endpoints C450TenthGroupedC05.packets :=
  endpoints_of_checks C450TenthGroupedC05.packets C450TenthGroupedC05.endpoint_checks
private theorem h06 : Endpoints C450TenthGroupedC06.packets :=
  endpoints_of_checks C450TenthGroupedC06.packets C450TenthGroupedC06.endpoint_checks
private theorem h07 : Endpoints C450TenthGroupedC07.packets :=
  endpoints_of_checks C450TenthGroupedC07.packets C450TenthGroupedC07.endpoint_checks
private theorem h08 : Endpoints C450TenthGroupedC08.packets :=
  endpoints_of_checks C450TenthGroupedC08.packets C450TenthGroupedC08.endpoint_checks
private theorem h09 : Endpoints C450TenthGroupedC09.packets :=
  endpoints_of_checks C450TenthGroupedC09.packets C450TenthGroupedC09.endpoint_checks
private theorem h10 : Endpoints C450TenthGroupedC10.packets :=
  endpoints_of_checks C450TenthGroupedC10.packets C450TenthGroupedC10.endpoint_checks
private theorem h11 : Endpoints C450TenthGroupedC11.packets :=
  endpoints_of_checks C450TenthGroupedC11.packets C450TenthGroupedC11.endpoint_checks
private theorem h12 : Endpoints C450TenthGroupedC12.packets :=
  endpoints_of_checks C450TenthGroupedC12.packets C450TenthGroupedC12.endpoint_checks
private theorem h13 : Endpoints C450TenthGroupedC13.packets :=
  endpoints_of_checks C450TenthGroupedC13.packets C450TenthGroupedC13.endpoint_checks
private theorem h14 : Endpoints C450TenthGroupedC14.packets :=
  endpoints_of_checks C450TenthGroupedC14.packets C450TenthGroupedC14.endpoint_checks
private theorem h15 : Endpoints C450TenthGroupedC15.packets :=
  endpoints_of_checks C450TenthGroupedC15.packets C450TenthGroupedC15.endpoint_checks
private theorem h16 : Endpoints C450TenthGroupedC16.packets :=
  endpoints_of_checks C450TenthGroupedC16.packets C450TenthGroupedC16.endpoint_checks
private theorem h17 : Endpoints C450TenthGroupedC17.packets :=
  endpoints_of_checks C450TenthGroupedC17.packets C450TenthGroupedC17.endpoint_checks
private theorem h18 : Endpoints C450TenthGroupedC18.packets :=
  endpoints_of_checks C450TenthGroupedC18.packets C450TenthGroupedC18.endpoint_checks
private theorem h19 : Endpoints C450TenthGroupedC19.packets :=
  endpoints_of_checks C450TenthGroupedC19.packets C450TenthGroupedC19.endpoint_checks
private theorem h20 : Endpoints C450TenthGroupedC20.packets :=
  endpoints_of_checks C450TenthGroupedC20.packets C450TenthGroupedC20.endpoint_checks
private theorem h21 : Endpoints C450TenthGroupedC21.packets :=
  endpoints_of_checks C450TenthGroupedC21.packets C450TenthGroupedC21.endpoint_checks
private theorem h22 : Endpoints C450TenthGroupedC22.packets :=
  endpoints_of_checks C450TenthGroupedC22.packets C450TenthGroupedC22.endpoint_checks
private theorem h23 : Endpoints C450TenthGroupedC23.packets :=
  endpoints_of_checks C450TenthGroupedC23.packets C450TenthGroupedC23.endpoint_checks
private theorem h24 : Endpoints C450TenthGroupedC24.packets :=
  endpoints_of_checks C450TenthGroupedC24.packets C450TenthGroupedC24.endpoint_checks
private theorem h25 : Endpoints C450TenthGroupedC25.packets :=
  endpoints_of_checks C450TenthGroupedC25.packets C450TenthGroupedC25.endpoint_checks
private theorem h26 : Endpoints C450TenthGroupedC26.packets :=
  endpoints_of_checks C450TenthGroupedC26.packets C450TenthGroupedC26.endpoint_checks
private theorem h27 : Endpoints C450TenthGroupedC27.packets :=
  endpoints_of_checks C450TenthGroupedC27.packets C450TenthGroupedC27.endpoint_checks
private theorem h28 : Endpoints C450TenthGroupedC28.packets :=
  endpoints_of_checks C450TenthGroupedC28.packets C450TenthGroupedC28.endpoint_checks
private theorem h29 : Endpoints C450TenthGroupedC29.packets :=
  endpoints_of_checks C450TenthGroupedC29.packets C450TenthGroupedC29.endpoint_checks
private theorem h30 : Endpoints C450TenthGroupedC30.packets :=
  endpoints_of_checks C450TenthGroupedC30.packets C450TenthGroupedC30.endpoint_checks
private theorem h31 : Endpoints C450TenthGroupedC31.packets :=
  endpoints_of_checks C450TenthGroupedC31.packets C450TenthGroupedC31.endpoint_checks
private theorem h32 : Endpoints C450TenthGroupedC32.packets :=
  endpoints_of_checks C450TenthGroupedC32.packets C450TenthGroupedC32.endpoint_checks

private def prefix01 : List Packet := C450TenthGroupedC01.packets
private def prefix02 : List Packet := prefix01 ++ C450TenthGroupedC02.packets
private def prefix03 : List Packet := prefix02 ++ C450TenthGroupedC03.packets
private def prefix04 : List Packet := prefix03 ++ C450TenthGroupedC04.packets
private def prefix05 : List Packet := prefix04 ++ C450TenthGroupedC05.packets
private def prefix06 : List Packet := prefix05 ++ C450TenthGroupedC06.packets
private def prefix07 : List Packet := prefix06 ++ C450TenthGroupedC07.packets
private def prefix08 : List Packet := prefix07 ++ C450TenthGroupedC08.packets
private def prefix09 : List Packet := prefix08 ++ C450TenthGroupedC09.packets
private def prefix10 : List Packet := prefix09 ++ C450TenthGroupedC10.packets
private def prefix11 : List Packet := prefix10 ++ C450TenthGroupedC11.packets
private def prefix12 : List Packet := prefix11 ++ C450TenthGroupedC12.packets
private def prefix13 : List Packet := prefix12 ++ C450TenthGroupedC13.packets
private def prefix14 : List Packet := prefix13 ++ C450TenthGroupedC14.packets
private def prefix15 : List Packet := prefix14 ++ C450TenthGroupedC15.packets
private def prefix16 : List Packet := prefix15 ++ C450TenthGroupedC16.packets
private def prefix17 : List Packet := prefix16 ++ C450TenthGroupedC17.packets
private def prefix18 : List Packet := prefix17 ++ C450TenthGroupedC18.packets
private def prefix19 : List Packet := prefix18 ++ C450TenthGroupedC19.packets
private def prefix20 : List Packet := prefix19 ++ C450TenthGroupedC20.packets
private def prefix21 : List Packet := prefix20 ++ C450TenthGroupedC21.packets
private def prefix22 : List Packet := prefix21 ++ C450TenthGroupedC22.packets
private def prefix23 : List Packet := prefix22 ++ C450TenthGroupedC23.packets
private def prefix24 : List Packet := prefix23 ++ C450TenthGroupedC24.packets
private def prefix25 : List Packet := prefix24 ++ C450TenthGroupedC25.packets
private def prefix26 : List Packet := prefix25 ++ C450TenthGroupedC26.packets
private def prefix27 : List Packet := prefix26 ++ C450TenthGroupedC27.packets
private def prefix28 : List Packet := prefix27 ++ C450TenthGroupedC28.packets
private def prefix29 : List Packet := prefix28 ++ C450TenthGroupedC29.packets
private def prefix30 : List Packet := prefix29 ++ C450TenthGroupedC30.packets
private def prefix31 : List Packet := prefix30 ++ C450TenthGroupedC31.packets
private def prefix32 : List Packet := prefix31 ++ C450TenthGroupedC32.packets
private theorem p01 : Endpoints prefix01 := h01
private theorem p02 : Endpoints prefix02 := append_endpoints p01 h02
private theorem p03 : Endpoints prefix03 := append_endpoints p02 h03
private theorem p04 : Endpoints prefix04 := append_endpoints p03 h04
private theorem p05 : Endpoints prefix05 := append_endpoints p04 h05
private theorem p06 : Endpoints prefix06 := append_endpoints p05 h06
private theorem p07 : Endpoints prefix07 := append_endpoints p06 h07
private theorem p08 : Endpoints prefix08 := append_endpoints p07 h08
private theorem p09 : Endpoints prefix09 := append_endpoints p08 h09
private theorem p10 : Endpoints prefix10 := append_endpoints p09 h10
private theorem p11 : Endpoints prefix11 := append_endpoints p10 h11
private theorem p12 : Endpoints prefix12 := append_endpoints p11 h12
private theorem p13 : Endpoints prefix13 := append_endpoints p12 h13
private theorem p14 : Endpoints prefix14 := append_endpoints p13 h14
private theorem p15 : Endpoints prefix15 := append_endpoints p14 h15
private theorem p16 : Endpoints prefix16 := append_endpoints p15 h16
private theorem p17 : Endpoints prefix17 := append_endpoints p16 h17
private theorem p18 : Endpoints prefix18 := append_endpoints p17 h18
private theorem p19 : Endpoints prefix19 := append_endpoints p18 h19
private theorem p20 : Endpoints prefix20 := append_endpoints p19 h20
private theorem p21 : Endpoints prefix21 := append_endpoints p20 h21
private theorem p22 : Endpoints prefix22 := append_endpoints p21 h22
private theorem p23 : Endpoints prefix23 := append_endpoints p22 h23
private theorem p24 : Endpoints prefix24 := append_endpoints p23 h24
private theorem p25 : Endpoints prefix25 := append_endpoints p24 h25
private theorem p26 : Endpoints prefix26 := append_endpoints p25 h26
private theorem p27 : Endpoints prefix27 := append_endpoints p26 h27
private theorem p28 : Endpoints prefix28 := append_endpoints p27 h28
private theorem p29 : Endpoints prefix29 := append_endpoints p28 h29
private theorem p30 : Endpoints prefix30 := append_endpoints p29 h30
private theorem p31 : Endpoints prefix31 := append_endpoints p30 h31
private theorem p32 : Endpoints prefix32 := append_endpoints p31 h32

private theorem prefix_eq : prefix32 = allPackets := by
  delta prefix32 prefix31 prefix30 prefix29 prefix28 prefix27 prefix26 prefix25
    prefix24 prefix23 prefix22 prefix21 prefix20 prefix19 prefix18 prefix17
    prefix16 prefix15 prefix14 prefix13 prefix12 prefix11 prefix10 prefix09
    prefix08 prefix07 prefix06 prefix05 prefix04 prefix03 prefix02 prefix01 allPackets
  rfl

theorem all_endpoint_checks : Endpoints allPackets := by
  rw [← prefix_eq]
  exact p32

theorem all_radial_endpoints (p : Packet) (hp : p ∈ allPackets) :
    RatInterval.Mem p.R (p.lo:ℝ) ∧ RatInterval.Mem p.R (p.hi:ℝ) :=
  all_endpoint_checks p hp

theorem all_direction_endpoints (i : Fin 33) :
    ∃ j : Case, RatInterval.Mem (Qs j) (((-1:ℚ)+(i.val:ℚ)/16:ℚ):ℝ) := by
  have hn : (i.val:ℝ) ≤ 32 := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hn0 : (0:ℝ) ≤ (i.val:ℝ) := Nat.cast_nonneg i.val
  apply directions_cover
  push_cast
  constructor <;> linarith

example : allPackets.length = 599 := C450TenthSegment.packet_count
example : remainingSegs.length = 26 := remaining_count
example : SourceExactRoot.sourceRadius = SourceExactRoot.sourceRoot 6 := rfl
example : EnergyTerminalBatchB11.paidIDs.card = 310 := EnergyTerminalBatchB11.paid_count
end N11Formalization.C450TenthImportedAudit
#check @N11Formalization.C450TenthSegment.tenth_paid
#check @N11Formalization.C450TenthSegment.atom_of_remaining
#check @N11Formalization.SourceExactRoot.source_attainment
#check @N11Formalization.SourceExactRoot.main_of_lower_bound
#print axioms N11Formalization.C450GroupedClosedAssembly.cell_of_packet
#print axioms N11Formalization.C450GroupedClosedAssembly.cell_join
#print axioms N11Formalization.C450GroupedClosedAssembly.normalized_of_cells
#print axioms N11Formalization.C450TenthData.source_eq
#print axioms N11Formalization.C450TenthData.nn0
#print axioms N11Formalization.C450TenthData.nn1
#print axioms N11Formalization.C450TenthSegment.directions_cover
#print axioms N11Formalization.C450TenthSegment.cells_paid
#print axioms N11Formalization.C450TenthSegment.tenth_paid
#print axioms N11Formalization.C450TenthSegment.ninth_remaining_split
#print axioms N11Formalization.C450TenthSegment.source_of_remaining
#print axioms N11Formalization.C450TenthSegment.atom_of_remaining
#print axioms N11Formalization.C450TenthImportedAudit.actual_segment
#print axioms N11Formalization.C450TenthImportedAudit.actual_integrals
#print axioms N11Formalization.C450TenthImportedAudit.all_endpoint_checks
#print axioms N11Formalization.C450TenthImportedAudit.all_radial_endpoints
#print axioms N11Formalization.C450TenthImportedAudit.all_direction_endpoints
