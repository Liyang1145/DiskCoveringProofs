import N11Formalization.C450SixthSegment
import N11Formalization.C450SeventhGroupedC01
import N11Formalization.C450SeventhGroupedC02
import N11Formalization.C450SeventhGroupedC03
import N11Formalization.C450SeventhGroupedC04
import N11Formalization.C450SeventhGroupedC05
import N11Formalization.C450SeventhGroupedC06
import N11Formalization.C450SeventhGroupedC07
import N11Formalization.C450SeventhGroupedC08
import N11Formalization.C450SeventhGroupedC09
import N11Formalization.C450SeventhGroupedC10
import N11Formalization.C450SeventhGroupedC11
import N11Formalization.C450SeventhGroupedC12
import N11Formalization.C450SeventhGroupedC13
import N11Formalization.C450SeventhGroupedC14
import N11Formalization.C450SeventhGroupedC15
import N11Formalization.C450SeventhGroupedC16
import N11Formalization.C450SeventhGroupedC17
import N11Formalization.C450SeventhGroupedC18
import N11Formalization.C450SeventhGroupedC19
import N11Formalization.C450SeventhGroupedC20
import N11Formalization.C450SeventhGroupedC21
import N11Formalization.C450SeventhGroupedC22
import N11Formalization.C450SeventhGroupedC23
import N11Formalization.C450SeventhGroupedC24
import N11Formalization.C450SeventhGroupedC25
import N11Formalization.C450SeventhGroupedC26
import N11Formalization.C450SeventhGroupedC27
import N11Formalization.C450SeventhGroupedC28
import N11Formalization.C450SeventhGroupedC29
import N11Formalization.C450SeventhGroupedC30
import N11Formalization.C450SeventhGroupedC31
import N11Formalization.C450SeventhGroupedC32
/-! Actual source7 full grouped closed certificate draft.
No source/root acceptance claimed by the file comment. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhSegment
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData C450NormalizedInterface
abbrev Case := Fin 32
def Qs : Case → RatInterval := ![C450SeventhGroupedC01.Qcell,C450SeventhGroupedC02.Qcell,C450SeventhGroupedC03.Qcell,C450SeventhGroupedC04.Qcell,C450SeventhGroupedC05.Qcell,C450SeventhGroupedC06.Qcell,C450SeventhGroupedC07.Qcell,C450SeventhGroupedC08.Qcell,C450SeventhGroupedC09.Qcell,C450SeventhGroupedC10.Qcell,C450SeventhGroupedC11.Qcell,C450SeventhGroupedC12.Qcell,C450SeventhGroupedC13.Qcell,C450SeventhGroupedC14.Qcell,C450SeventhGroupedC15.Qcell,C450SeventhGroupedC16.Qcell,C450SeventhGroupedC17.Qcell,C450SeventhGroupedC18.Qcell,C450SeventhGroupedC19.Qcell,C450SeventhGroupedC20.Qcell,C450SeventhGroupedC21.Qcell,C450SeventhGroupedC22.Qcell,C450SeventhGroupedC23.Qcell,C450SeventhGroupedC24.Qcell,C450SeventhGroupedC25.Qcell,C450SeventhGroupedC26.Qcell,C450SeventhGroupedC27.Qcell,C450SeventhGroupedC28.Qcell,C450SeventhGroupedC29.Qcell,C450SeventhGroupedC30.Qcell,C450SeventhGroupedC31.Qcell,C450SeventhGroupedC32.Qcell]
private def DirectionPaid (q : ℝ) : Prop := ∃ i : Case, RatInterval.Mem (Qs i) q
private theorem direction0 :
    ∀ q ∈ Set.Icc (-1:ℝ) ((-15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨0,?_⟩
  simpa [Qs,C450SeventhGroupedC01.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction1 :
    ∀ q ∈ Set.Icc ((-15:ℝ)/16) ((-7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨1,?_⟩
  simpa [Qs,C450SeventhGroupedC02.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction2 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8) ((-13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨2,?_⟩
  simpa [Qs,C450SeventhGroupedC03.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction3 :
    ∀ q ∈ Set.Icc ((-13:ℝ)/16) ((-3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨3,?_⟩
  simpa [Qs,C450SeventhGroupedC04.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction4 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4) ((-11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨4,?_⟩
  simpa [Qs,C450SeventhGroupedC05.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction5 :
    ∀ q ∈ Set.Icc ((-11:ℝ)/16) ((-5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨5,?_⟩
  simpa [Qs,C450SeventhGroupedC06.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction6 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8) ((-9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨6,?_⟩
  simpa [Qs,C450SeventhGroupedC07.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction7 :
    ∀ q ∈ Set.Icc ((-9:ℝ)/16) ((-1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨7,?_⟩
  simpa [Qs,C450SeventhGroupedC08.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction8 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2) ((-7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨8,?_⟩
  simpa [Qs,C450SeventhGroupedC09.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction9 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/16) ((-3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨9,?_⟩
  simpa [Qs,C450SeventhGroupedC10.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction10 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8) ((-5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨10,?_⟩
  simpa [Qs,C450SeventhGroupedC11.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction11 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/16) ((-1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨11,?_⟩
  simpa [Qs,C450SeventhGroupedC12.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction12 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4) ((-3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨12,?_⟩
  simpa [Qs,C450SeventhGroupedC13.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction13 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/16) ((-1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨13,?_⟩
  simpa [Qs,C450SeventhGroupedC14.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction14 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8) ((-1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨14,?_⟩
  simpa [Qs,C450SeventhGroupedC15.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction15 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/16) (0:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨15,?_⟩
  simpa [Qs,C450SeventhGroupedC16.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction16 :
    ∀ q ∈ Set.Icc (0:ℝ) ((1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨16,?_⟩
  simpa [Qs,C450SeventhGroupedC17.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction17 :
    ∀ q ∈ Set.Icc ((1:ℝ)/16) ((1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨17,?_⟩
  simpa [Qs,C450SeventhGroupedC18.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction18 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8) ((3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨18,?_⟩
  simpa [Qs,C450SeventhGroupedC19.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction19 :
    ∀ q ∈ Set.Icc ((3:ℝ)/16) ((1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨19,?_⟩
  simpa [Qs,C450SeventhGroupedC20.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction20 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4) ((5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨20,?_⟩
  simpa [Qs,C450SeventhGroupedC21.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction21 :
    ∀ q ∈ Set.Icc ((5:ℝ)/16) ((3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨21,?_⟩
  simpa [Qs,C450SeventhGroupedC22.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction22 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8) ((7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨22,?_⟩
  simpa [Qs,C450SeventhGroupedC23.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction23 :
    ∀ q ∈ Set.Icc ((7:ℝ)/16) ((1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨23,?_⟩
  simpa [Qs,C450SeventhGroupedC24.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction24 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2) ((9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨24,?_⟩
  simpa [Qs,C450SeventhGroupedC25.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction25 :
    ∀ q ∈ Set.Icc ((9:ℝ)/16) ((5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨25,?_⟩
  simpa [Qs,C450SeventhGroupedC26.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction26 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8) ((11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨26,?_⟩
  simpa [Qs,C450SeventhGroupedC27.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction27 :
    ∀ q ∈ Set.Icc ((11:ℝ)/16) ((3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨27,?_⟩
  simpa [Qs,C450SeventhGroupedC28.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction28 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4) ((13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨28,?_⟩
  simpa [Qs,C450SeventhGroupedC29.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction29 :
    ∀ q ∈ Set.Icc ((13:ℝ)/16) ((7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨29,?_⟩
  simpa [Qs,C450SeventhGroupedC30.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction30 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8) ((15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨30,?_⟩
  simpa [Qs,C450SeventhGroupedC31.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction31 :
    ∀ q ∈ Set.Icc ((15:ℝ)/16) (1:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨31,?_⟩
  simpa [Qs,C450SeventhGroupedC32.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
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
theorem cells_paid (i : Case) : CellBound seventh nn0 nn1 (Qs i) (31/50) (69/50) := by
  fin_cases i
  · exact C450SeventhGroupedC01.bound
  · exact C450SeventhGroupedC02.bound
  · exact C450SeventhGroupedC03.bound
  · exact C450SeventhGroupedC04.bound
  · exact C450SeventhGroupedC05.bound
  · exact C450SeventhGroupedC06.bound
  · exact C450SeventhGroupedC07.bound
  · exact C450SeventhGroupedC08.bound
  · exact C450SeventhGroupedC09.bound
  · exact C450SeventhGroupedC10.bound
  · exact C450SeventhGroupedC11.bound
  · exact C450SeventhGroupedC12.bound
  · exact C450SeventhGroupedC13.bound
  · exact C450SeventhGroupedC14.bound
  · exact C450SeventhGroupedC15.bound
  · exact C450SeventhGroupedC16.bound
  · exact C450SeventhGroupedC17.bound
  · exact C450SeventhGroupedC18.bound
  · exact C450SeventhGroupedC19.bound
  · exact C450SeventhGroupedC20.bound
  · exact C450SeventhGroupedC21.bound
  · exact C450SeventhGroupedC22.bound
  · exact C450SeventhGroupedC23.bound
  · exact C450SeventhGroupedC24.bound
  · exact C450SeventhGroupedC25.bound
  · exact C450SeventhGroupedC26.bound
  · exact C450SeventhGroupedC27.bound
  · exact C450SeventhGroupedC28.bound
  · exact C450SeventhGroupedC29.bound
  · exact C450SeventhGroupedC30.bound
  · exact C450SeventhGroupedC31.bound
  · exact C450SeventhGroupedC32.bound
theorem seventh_paid : SegmentNormalized seventh := by
  intro h0 h1
  exact normalized_of_cells seventh h0 h1 eHi_le Qs directions_cover cells_paid
def allPackets : List Packet := C450SeventhGroupedC01.packets ++ C450SeventhGroupedC02.packets ++ C450SeventhGroupedC03.packets ++ C450SeventhGroupedC04.packets ++ C450SeventhGroupedC05.packets ++ C450SeventhGroupedC06.packets ++ C450SeventhGroupedC07.packets ++ C450SeventhGroupedC08.packets ++ C450SeventhGroupedC09.packets ++ C450SeventhGroupedC10.packets ++ C450SeventhGroupedC11.packets ++ C450SeventhGroupedC12.packets ++ C450SeventhGroupedC13.packets ++ C450SeventhGroupedC14.packets ++ C450SeventhGroupedC15.packets ++ C450SeventhGroupedC16.packets ++ C450SeventhGroupedC17.packets ++ C450SeventhGroupedC18.packets ++ C450SeventhGroupedC19.packets ++ C450SeventhGroupedC20.packets ++ C450SeventhGroupedC21.packets ++ C450SeventhGroupedC22.packets ++ C450SeventhGroupedC23.packets ++ C450SeventhGroupedC24.packets ++ C450SeventhGroupedC25.packets ++ C450SeventhGroupedC26.packets ++ C450SeventhGroupedC27.packets ++ C450SeventhGroupedC28.packets ++ C450SeventhGroupedC29.packets ++ C450SeventhGroupedC30.packets ++ C450SeventhGroupedC31.packets ++ C450SeventhGroupedC32.packets
theorem packet_count : allPackets.length = 606 := by decide +kernel
def remainingSegs : List TenSeg := c450Segs.drop 7
theorem remaining_count : remainingSegs.length = 29 := by decide +kernel
theorem sixth_remaining_split : C450SixthSegment.remainingSegs = seventh :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem sixth_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450SixthSegment.RemainingSourceObligation := by
  intro s hs
  rw [sixth_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hseven | hrest
  · rw [hseven]
    exact seventh_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450SixthSegment.source_of_remaining (sixth_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450SeventhSegment
#check @N11Formalization.C450SeventhSegment.seventh_paid
#check @N11Formalization.C450SeventhSegment.atom_of_remaining
#print axioms N11Formalization.C450SeventhSegment.directions_cover
#print axioms N11Formalization.C450SeventhSegment.cells_paid
#print axioms N11Formalization.C450SeventhSegment.seventh_paid
#print axioms N11Formalization.C450SeventhSegment.atom_of_remaining
