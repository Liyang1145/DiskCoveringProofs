import N11Formalization.C450NinthSegment
import N11Formalization.C450TenthGroupedC01
import N11Formalization.C450TenthGroupedC02
import N11Formalization.C450TenthGroupedC03
import N11Formalization.C450TenthGroupedC04
import N11Formalization.C450TenthGroupedC05
import N11Formalization.C450TenthGroupedC06
import N11Formalization.C450TenthGroupedC07
import N11Formalization.C450TenthGroupedC08
import N11Formalization.C450TenthGroupedC09
import N11Formalization.C450TenthGroupedC10
import N11Formalization.C450TenthGroupedC11
import N11Formalization.C450TenthGroupedC12
import N11Formalization.C450TenthGroupedC13
import N11Formalization.C450TenthGroupedC14
import N11Formalization.C450TenthGroupedC15
import N11Formalization.C450TenthGroupedC16
import N11Formalization.C450TenthGroupedC17
import N11Formalization.C450TenthGroupedC18
import N11Formalization.C450TenthGroupedC19
import N11Formalization.C450TenthGroupedC20
import N11Formalization.C450TenthGroupedC21
import N11Formalization.C450TenthGroupedC22
import N11Formalization.C450TenthGroupedC23
import N11Formalization.C450TenthGroupedC24
import N11Formalization.C450TenthGroupedC25
import N11Formalization.C450TenthGroupedC26
import N11Formalization.C450TenthGroupedC27
import N11Formalization.C450TenthGroupedC28
import N11Formalization.C450TenthGroupedC29
import N11Formalization.C450TenthGroupedC30
import N11Formalization.C450TenthGroupedC31
import N11Formalization.C450TenthGroupedC32
/-! Actual source10 full grouped closed certificate draft.
No source/root acceptance claimed by the file comment. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthSegment
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData C450NormalizedInterface
abbrev Case := Fin 32
def Qs : Case → RatInterval := ![C450TenthGroupedC01.Qcell,C450TenthGroupedC02.Qcell,C450TenthGroupedC03.Qcell,C450TenthGroupedC04.Qcell,C450TenthGroupedC05.Qcell,C450TenthGroupedC06.Qcell,C450TenthGroupedC07.Qcell,C450TenthGroupedC08.Qcell,C450TenthGroupedC09.Qcell,C450TenthGroupedC10.Qcell,C450TenthGroupedC11.Qcell,C450TenthGroupedC12.Qcell,C450TenthGroupedC13.Qcell,C450TenthGroupedC14.Qcell,C450TenthGroupedC15.Qcell,C450TenthGroupedC16.Qcell,C450TenthGroupedC17.Qcell,C450TenthGroupedC18.Qcell,C450TenthGroupedC19.Qcell,C450TenthGroupedC20.Qcell,C450TenthGroupedC21.Qcell,C450TenthGroupedC22.Qcell,C450TenthGroupedC23.Qcell,C450TenthGroupedC24.Qcell,C450TenthGroupedC25.Qcell,C450TenthGroupedC26.Qcell,C450TenthGroupedC27.Qcell,C450TenthGroupedC28.Qcell,C450TenthGroupedC29.Qcell,C450TenthGroupedC30.Qcell,C450TenthGroupedC31.Qcell,C450TenthGroupedC32.Qcell]
private def DirectionPaid (q : ℝ) : Prop := ∃ i : Case, RatInterval.Mem (Qs i) q
private theorem direction0 :
    ∀ q ∈ Set.Icc (-1:ℝ) ((-15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨0,?_⟩
  simpa [Qs,C450TenthGroupedC01.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction1 :
    ∀ q ∈ Set.Icc ((-15:ℝ)/16) ((-7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨1,?_⟩
  simpa [Qs,C450TenthGroupedC02.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction2 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8) ((-13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨2,?_⟩
  simpa [Qs,C450TenthGroupedC03.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction3 :
    ∀ q ∈ Set.Icc ((-13:ℝ)/16) ((-3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨3,?_⟩
  simpa [Qs,C450TenthGroupedC04.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction4 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4) ((-11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨4,?_⟩
  simpa [Qs,C450TenthGroupedC05.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction5 :
    ∀ q ∈ Set.Icc ((-11:ℝ)/16) ((-5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨5,?_⟩
  simpa [Qs,C450TenthGroupedC06.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction6 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8) ((-9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨6,?_⟩
  simpa [Qs,C450TenthGroupedC07.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction7 :
    ∀ q ∈ Set.Icc ((-9:ℝ)/16) ((-1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨7,?_⟩
  simpa [Qs,C450TenthGroupedC08.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction8 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2) ((-7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨8,?_⟩
  simpa [Qs,C450TenthGroupedC09.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction9 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/16) ((-3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨9,?_⟩
  simpa [Qs,C450TenthGroupedC10.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction10 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8) ((-5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨10,?_⟩
  simpa [Qs,C450TenthGroupedC11.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction11 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/16) ((-1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨11,?_⟩
  simpa [Qs,C450TenthGroupedC12.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction12 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4) ((-3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨12,?_⟩
  simpa [Qs,C450TenthGroupedC13.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction13 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/16) ((-1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨13,?_⟩
  simpa [Qs,C450TenthGroupedC14.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction14 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8) ((-1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨14,?_⟩
  simpa [Qs,C450TenthGroupedC15.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction15 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/16) (0:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨15,?_⟩
  simpa [Qs,C450TenthGroupedC16.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction16 :
    ∀ q ∈ Set.Icc (0:ℝ) ((1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨16,?_⟩
  simpa [Qs,C450TenthGroupedC17.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction17 :
    ∀ q ∈ Set.Icc ((1:ℝ)/16) ((1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨17,?_⟩
  simpa [Qs,C450TenthGroupedC18.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction18 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8) ((3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨18,?_⟩
  simpa [Qs,C450TenthGroupedC19.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction19 :
    ∀ q ∈ Set.Icc ((3:ℝ)/16) ((1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨19,?_⟩
  simpa [Qs,C450TenthGroupedC20.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction20 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4) ((5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨20,?_⟩
  simpa [Qs,C450TenthGroupedC21.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction21 :
    ∀ q ∈ Set.Icc ((5:ℝ)/16) ((3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨21,?_⟩
  simpa [Qs,C450TenthGroupedC22.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction22 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8) ((7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨22,?_⟩
  simpa [Qs,C450TenthGroupedC23.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction23 :
    ∀ q ∈ Set.Icc ((7:ℝ)/16) ((1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨23,?_⟩
  simpa [Qs,C450TenthGroupedC24.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction24 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2) ((9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨24,?_⟩
  simpa [Qs,C450TenthGroupedC25.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction25 :
    ∀ q ∈ Set.Icc ((9:ℝ)/16) ((5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨25,?_⟩
  simpa [Qs,C450TenthGroupedC26.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction26 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8) ((11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨26,?_⟩
  simpa [Qs,C450TenthGroupedC27.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction27 :
    ∀ q ∈ Set.Icc ((11:ℝ)/16) ((3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨27,?_⟩
  simpa [Qs,C450TenthGroupedC28.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction28 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4) ((13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨28,?_⟩
  simpa [Qs,C450TenthGroupedC29.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction29 :
    ∀ q ∈ Set.Icc ((13:ℝ)/16) ((7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨29,?_⟩
  simpa [Qs,C450TenthGroupedC30.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction30 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8) ((15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨30,?_⟩
  simpa [Qs,C450TenthGroupedC31.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction31 :
    ∀ q ∈ Set.Icc ((15:ℝ)/16) (1:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨31,?_⟩
  simpa [Qs,C450TenthGroupedC32.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
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
theorem cells_paid (i : Case) : CellBound tenth nn0 nn1 (Qs i) (31/50) (69/50) := by
  fin_cases i
  · exact C450TenthGroupedC01.bound
  · exact C450TenthGroupedC02.bound
  · exact C450TenthGroupedC03.bound
  · exact C450TenthGroupedC04.bound
  · exact C450TenthGroupedC05.bound
  · exact C450TenthGroupedC06.bound
  · exact C450TenthGroupedC07.bound
  · exact C450TenthGroupedC08.bound
  · exact C450TenthGroupedC09.bound
  · exact C450TenthGroupedC10.bound
  · exact C450TenthGroupedC11.bound
  · exact C450TenthGroupedC12.bound
  · exact C450TenthGroupedC13.bound
  · exact C450TenthGroupedC14.bound
  · exact C450TenthGroupedC15.bound
  · exact C450TenthGroupedC16.bound
  · exact C450TenthGroupedC17.bound
  · exact C450TenthGroupedC18.bound
  · exact C450TenthGroupedC19.bound
  · exact C450TenthGroupedC20.bound
  · exact C450TenthGroupedC21.bound
  · exact C450TenthGroupedC22.bound
  · exact C450TenthGroupedC23.bound
  · exact C450TenthGroupedC24.bound
  · exact C450TenthGroupedC25.bound
  · exact C450TenthGroupedC26.bound
  · exact C450TenthGroupedC27.bound
  · exact C450TenthGroupedC28.bound
  · exact C450TenthGroupedC29.bound
  · exact C450TenthGroupedC30.bound
  · exact C450TenthGroupedC31.bound
  · exact C450TenthGroupedC32.bound
theorem tenth_paid : SegmentNormalized tenth := by
  intro h0 h1
  exact normalized_of_cells tenth h0 h1 eHi_le Qs directions_cover cells_paid
def allPackets : List Packet := C450TenthGroupedC01.packets ++ C450TenthGroupedC02.packets ++ C450TenthGroupedC03.packets ++ C450TenthGroupedC04.packets ++ C450TenthGroupedC05.packets ++ C450TenthGroupedC06.packets ++ C450TenthGroupedC07.packets ++ C450TenthGroupedC08.packets ++ C450TenthGroupedC09.packets ++ C450TenthGroupedC10.packets ++ C450TenthGroupedC11.packets ++ C450TenthGroupedC12.packets ++ C450TenthGroupedC13.packets ++ C450TenthGroupedC14.packets ++ C450TenthGroupedC15.packets ++ C450TenthGroupedC16.packets ++ C450TenthGroupedC17.packets ++ C450TenthGroupedC18.packets ++ C450TenthGroupedC19.packets ++ C450TenthGroupedC20.packets ++ C450TenthGroupedC21.packets ++ C450TenthGroupedC22.packets ++ C450TenthGroupedC23.packets ++ C450TenthGroupedC24.packets ++ C450TenthGroupedC25.packets ++ C450TenthGroupedC26.packets ++ C450TenthGroupedC27.packets ++ C450TenthGroupedC28.packets ++ C450TenthGroupedC29.packets ++ C450TenthGroupedC30.packets ++ C450TenthGroupedC31.packets ++ C450TenthGroupedC32.packets
theorem packet_count : allPackets.length = 599 := by decide +kernel
def remainingSegs : List TenSeg := c450Segs.drop 10
theorem remaining_count : remainingSegs.length = 26 := by decide +kernel
theorem ninth_remaining_split : C450NinthSegment.remainingSegs = tenth :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem ninth_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450NinthSegment.RemainingSourceObligation := by
  intro s hs
  rw [ninth_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hseven | hrest
  · rw [hseven]
    exact tenth_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450NinthSegment.source_of_remaining (ninth_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450TenthSegment
#check @N11Formalization.C450TenthSegment.tenth_paid
#check @N11Formalization.C450TenthSegment.atom_of_remaining
#print axioms N11Formalization.C450TenthSegment.directions_cover
#print axioms N11Formalization.C450TenthSegment.cells_paid
#print axioms N11Formalization.C450TenthSegment.tenth_paid
#print axioms N11Formalization.C450TenthSegment.atom_of_remaining
