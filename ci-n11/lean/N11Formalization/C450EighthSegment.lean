import N11Formalization.C450SeventhSegment
import N11Formalization.C450EighthGroupedC01
import N11Formalization.C450EighthGroupedC02
import N11Formalization.C450EighthGroupedC03
import N11Formalization.C450EighthGroupedC04
import N11Formalization.C450EighthGroupedC05
import N11Formalization.C450EighthGroupedC06
import N11Formalization.C450EighthGroupedC07
import N11Formalization.C450EighthGroupedC08
import N11Formalization.C450EighthGroupedC09
import N11Formalization.C450EighthGroupedC10
import N11Formalization.C450EighthGroupedC11
import N11Formalization.C450EighthGroupedC12
import N11Formalization.C450EighthGroupedC13
import N11Formalization.C450EighthGroupedC14
import N11Formalization.C450EighthGroupedC15
import N11Formalization.C450EighthGroupedC16
import N11Formalization.C450EighthGroupedC17
import N11Formalization.C450EighthGroupedC18
import N11Formalization.C450EighthGroupedC19
import N11Formalization.C450EighthGroupedC20
import N11Formalization.C450EighthGroupedC21
import N11Formalization.C450EighthGroupedC22
import N11Formalization.C450EighthGroupedC23
import N11Formalization.C450EighthGroupedC24
import N11Formalization.C450EighthGroupedC25
import N11Formalization.C450EighthGroupedC26
import N11Formalization.C450EighthGroupedC27
import N11Formalization.C450EighthGroupedC28
import N11Formalization.C450EighthGroupedC29
import N11Formalization.C450EighthGroupedC30
import N11Formalization.C450EighthGroupedC31
import N11Formalization.C450EighthGroupedC32
/-! Actual source8 full grouped closed certificate draft.
No source/root acceptance claimed by the file comment. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthSegment
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData C450NormalizedInterface
abbrev Case := Fin 32
def Qs : Case → RatInterval := ![C450EighthGroupedC01.Qcell,C450EighthGroupedC02.Qcell,C450EighthGroupedC03.Qcell,C450EighthGroupedC04.Qcell,C450EighthGroupedC05.Qcell,C450EighthGroupedC06.Qcell,C450EighthGroupedC07.Qcell,C450EighthGroupedC08.Qcell,C450EighthGroupedC09.Qcell,C450EighthGroupedC10.Qcell,C450EighthGroupedC11.Qcell,C450EighthGroupedC12.Qcell,C450EighthGroupedC13.Qcell,C450EighthGroupedC14.Qcell,C450EighthGroupedC15.Qcell,C450EighthGroupedC16.Qcell,C450EighthGroupedC17.Qcell,C450EighthGroupedC18.Qcell,C450EighthGroupedC19.Qcell,C450EighthGroupedC20.Qcell,C450EighthGroupedC21.Qcell,C450EighthGroupedC22.Qcell,C450EighthGroupedC23.Qcell,C450EighthGroupedC24.Qcell,C450EighthGroupedC25.Qcell,C450EighthGroupedC26.Qcell,C450EighthGroupedC27.Qcell,C450EighthGroupedC28.Qcell,C450EighthGroupedC29.Qcell,C450EighthGroupedC30.Qcell,C450EighthGroupedC31.Qcell,C450EighthGroupedC32.Qcell]
private def DirectionPaid (q : ℝ) : Prop := ∃ i : Case, RatInterval.Mem (Qs i) q
private theorem direction0 :
    ∀ q ∈ Set.Icc (-1:ℝ) ((-15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨0,?_⟩
  simpa [Qs,C450EighthGroupedC01.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction1 :
    ∀ q ∈ Set.Icc ((-15:ℝ)/16) ((-7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨1,?_⟩
  simpa [Qs,C450EighthGroupedC02.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction2 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8) ((-13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨2,?_⟩
  simpa [Qs,C450EighthGroupedC03.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction3 :
    ∀ q ∈ Set.Icc ((-13:ℝ)/16) ((-3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨3,?_⟩
  simpa [Qs,C450EighthGroupedC04.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction4 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4) ((-11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨4,?_⟩
  simpa [Qs,C450EighthGroupedC05.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction5 :
    ∀ q ∈ Set.Icc ((-11:ℝ)/16) ((-5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨5,?_⟩
  simpa [Qs,C450EighthGroupedC06.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction6 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8) ((-9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨6,?_⟩
  simpa [Qs,C450EighthGroupedC07.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction7 :
    ∀ q ∈ Set.Icc ((-9:ℝ)/16) ((-1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨7,?_⟩
  simpa [Qs,C450EighthGroupedC08.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction8 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2) ((-7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨8,?_⟩
  simpa [Qs,C450EighthGroupedC09.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction9 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/16) ((-3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨9,?_⟩
  simpa [Qs,C450EighthGroupedC10.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction10 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8) ((-5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨10,?_⟩
  simpa [Qs,C450EighthGroupedC11.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction11 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/16) ((-1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨11,?_⟩
  simpa [Qs,C450EighthGroupedC12.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction12 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4) ((-3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨12,?_⟩
  simpa [Qs,C450EighthGroupedC13.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction13 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/16) ((-1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨13,?_⟩
  simpa [Qs,C450EighthGroupedC14.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction14 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8) ((-1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨14,?_⟩
  simpa [Qs,C450EighthGroupedC15.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction15 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/16) (0:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨15,?_⟩
  simpa [Qs,C450EighthGroupedC16.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction16 :
    ∀ q ∈ Set.Icc (0:ℝ) ((1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨16,?_⟩
  simpa [Qs,C450EighthGroupedC17.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction17 :
    ∀ q ∈ Set.Icc ((1:ℝ)/16) ((1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨17,?_⟩
  simpa [Qs,C450EighthGroupedC18.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction18 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8) ((3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨18,?_⟩
  simpa [Qs,C450EighthGroupedC19.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction19 :
    ∀ q ∈ Set.Icc ((3:ℝ)/16) ((1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨19,?_⟩
  simpa [Qs,C450EighthGroupedC20.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction20 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4) ((5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨20,?_⟩
  simpa [Qs,C450EighthGroupedC21.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction21 :
    ∀ q ∈ Set.Icc ((5:ℝ)/16) ((3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨21,?_⟩
  simpa [Qs,C450EighthGroupedC22.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction22 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8) ((7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨22,?_⟩
  simpa [Qs,C450EighthGroupedC23.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction23 :
    ∀ q ∈ Set.Icc ((7:ℝ)/16) ((1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨23,?_⟩
  simpa [Qs,C450EighthGroupedC24.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction24 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2) ((9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨24,?_⟩
  simpa [Qs,C450EighthGroupedC25.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction25 :
    ∀ q ∈ Set.Icc ((9:ℝ)/16) ((5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨25,?_⟩
  simpa [Qs,C450EighthGroupedC26.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction26 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8) ((11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨26,?_⟩
  simpa [Qs,C450EighthGroupedC27.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction27 :
    ∀ q ∈ Set.Icc ((11:ℝ)/16) ((3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨27,?_⟩
  simpa [Qs,C450EighthGroupedC28.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction28 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4) ((13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨28,?_⟩
  simpa [Qs,C450EighthGroupedC29.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction29 :
    ∀ q ∈ Set.Icc ((13:ℝ)/16) ((7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨29,?_⟩
  simpa [Qs,C450EighthGroupedC30.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction30 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8) ((15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨30,?_⟩
  simpa [Qs,C450EighthGroupedC31.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction31 :
    ∀ q ∈ Set.Icc ((15:ℝ)/16) (1:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨31,?_⟩
  simpa [Qs,C450EighthGroupedC32.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem directions0_2 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      ((-7:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction0 direction1
private theorem directions2_4 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8)
      ((-3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction2 direction3
private theorem directions0_4 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      ((-3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_2 directions2_4
private theorem directions4_6 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4)
      ((-5:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction4 direction5
private theorem directions6_8 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8)
      ((-1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction6 direction7
private theorem directions4_8 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4)
      ((-1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions4_6 directions6_8
private theorem directions0_8 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      ((-1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_4 directions4_8
private theorem directions8_10 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2)
      ((-3:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction8 direction9
private theorem directions10_12 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8)
      ((-1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction10 direction11
private theorem directions8_12 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2)
      ((-1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions8_10 directions10_12
private theorem directions12_14 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4)
      ((-1:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction12 direction13
private theorem directions14_16 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction14 direction15
private theorem directions12_16 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions12_14 directions14_16
private theorem directions8_16 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions8_12 directions12_16
private theorem directions0_16 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_8 directions8_16
private theorem directions16_18 :
    ∀ q ∈ Set.Icc (0:ℝ)
      ((1:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction16 direction17
private theorem directions18_20 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8)
      ((1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction18 direction19
private theorem directions16_20 :
    ∀ q ∈ Set.Icc (0:ℝ)
      ((1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions16_18 directions18_20
private theorem directions20_22 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4)
      ((3:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction20 direction21
private theorem directions22_24 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8)
      ((1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction22 direction23
private theorem directions20_24 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4)
      ((1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions20_22 directions22_24
private theorem directions16_24 :
    ∀ q ∈ Set.Icc (0:ℝ)
      ((1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions16_20 directions20_24
private theorem directions24_26 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2)
      ((5:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction24 direction25
private theorem directions26_28 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8)
      ((3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction26 direction27
private theorem directions24_28 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2)
      ((3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions24_26 directions26_28
private theorem directions28_30 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4)
      ((7:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction28 direction29
private theorem directions30_32 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction30 direction31
private theorem directions28_32 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions28_30 directions30_32
private theorem directions24_32 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions24_28 directions28_32
private theorem directions16_32 :
    ∀ q ∈ Set.Icc (0:ℝ)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions16_24 directions24_32
private theorem directions0_32 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_16 directions16_32
theorem directions_cover : DirectionsCover Qs := directions0_32
theorem cells_paid (i : Case) : CellBound eighth nn0 nn1 (Qs i) (31/50) (69/50) := by
  fin_cases i
  · exact C450EighthGroupedC01.bound
  · exact C450EighthGroupedC02.bound
  · exact C450EighthGroupedC03.bound
  · exact C450EighthGroupedC04.bound
  · exact C450EighthGroupedC05.bound
  · exact C450EighthGroupedC06.bound
  · exact C450EighthGroupedC07.bound
  · exact C450EighthGroupedC08.bound
  · exact C450EighthGroupedC09.bound
  · exact C450EighthGroupedC10.bound
  · exact C450EighthGroupedC11.bound
  · exact C450EighthGroupedC12.bound
  · exact C450EighthGroupedC13.bound
  · exact C450EighthGroupedC14.bound
  · exact C450EighthGroupedC15.bound
  · exact C450EighthGroupedC16.bound
  · exact C450EighthGroupedC17.bound
  · exact C450EighthGroupedC18.bound
  · exact C450EighthGroupedC19.bound
  · exact C450EighthGroupedC20.bound
  · exact C450EighthGroupedC21.bound
  · exact C450EighthGroupedC22.bound
  · exact C450EighthGroupedC23.bound
  · exact C450EighthGroupedC24.bound
  · exact C450EighthGroupedC25.bound
  · exact C450EighthGroupedC26.bound
  · exact C450EighthGroupedC27.bound
  · exact C450EighthGroupedC28.bound
  · exact C450EighthGroupedC29.bound
  · exact C450EighthGroupedC30.bound
  · exact C450EighthGroupedC31.bound
  · exact C450EighthGroupedC32.bound
theorem eighth_paid : SegmentNormalized eighth := by
  intro h0 h1
  exact normalized_of_cells eighth h0 h1 eHi_le Qs directions_cover cells_paid
def allPackets : List Packet := C450EighthGroupedC01.packets ++ C450EighthGroupedC02.packets ++ C450EighthGroupedC03.packets ++ C450EighthGroupedC04.packets ++ C450EighthGroupedC05.packets ++ C450EighthGroupedC06.packets ++ C450EighthGroupedC07.packets ++ C450EighthGroupedC08.packets ++ C450EighthGroupedC09.packets ++ C450EighthGroupedC10.packets ++ C450EighthGroupedC11.packets ++ C450EighthGroupedC12.packets ++ C450EighthGroupedC13.packets ++ C450EighthGroupedC14.packets ++ C450EighthGroupedC15.packets ++ C450EighthGroupedC16.packets ++ C450EighthGroupedC17.packets ++ C450EighthGroupedC18.packets ++ C450EighthGroupedC19.packets ++ C450EighthGroupedC20.packets ++ C450EighthGroupedC21.packets ++ C450EighthGroupedC22.packets ++ C450EighthGroupedC23.packets ++ C450EighthGroupedC24.packets ++ C450EighthGroupedC25.packets ++ C450EighthGroupedC26.packets ++ C450EighthGroupedC27.packets ++ C450EighthGroupedC28.packets ++ C450EighthGroupedC29.packets ++ C450EighthGroupedC30.packets ++ C450EighthGroupedC31.packets ++ C450EighthGroupedC32.packets
theorem packet_count : allPackets.length = 607 := by decide +kernel
def remainingSegs : List TenSeg := c450Segs.drop 8
theorem remaining_count : remainingSegs.length = 28 := by decide +kernel
theorem seventh_remaining_split : C450SeventhSegment.remainingSegs = eighth :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem seventh_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450SeventhSegment.RemainingSourceObligation := by
  intro s hs
  rw [seventh_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hseven | hrest
  · rw [hseven]
    exact eighth_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450SeventhSegment.source_of_remaining (seventh_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450EighthSegment
#check @N11Formalization.C450EighthSegment.eighth_paid
#check @N11Formalization.C450EighthSegment.atom_of_remaining
#print axioms N11Formalization.C450EighthSegment.directions_cover
#print axioms N11Formalization.C450EighthSegment.cells_paid
#print axioms N11Formalization.C450EighthSegment.eighth_paid
#print axioms N11Formalization.C450EighthSegment.atom_of_remaining
