import N11Formalization.C450EighthSegment
import N11Formalization.C450NinthGroupedC01
import N11Formalization.C450NinthGroupedC02
import N11Formalization.C450NinthGroupedC03
import N11Formalization.C450NinthGroupedC04
import N11Formalization.C450NinthGroupedC05
import N11Formalization.C450NinthGroupedC06
import N11Formalization.C450NinthGroupedC07
import N11Formalization.C450NinthGroupedC08
import N11Formalization.C450NinthGroupedC09
import N11Formalization.C450NinthGroupedC10
import N11Formalization.C450NinthGroupedC11
import N11Formalization.C450NinthGroupedC12
import N11Formalization.C450NinthGroupedC13
import N11Formalization.C450NinthGroupedC14
import N11Formalization.C450NinthGroupedC15
import N11Formalization.C450NinthGroupedC16
import N11Formalization.C450NinthGroupedC17
import N11Formalization.C450NinthGroupedC18
import N11Formalization.C450NinthGroupedC19
import N11Formalization.C450NinthGroupedC20
import N11Formalization.C450NinthGroupedC21
import N11Formalization.C450NinthGroupedC22
import N11Formalization.C450NinthGroupedC23
import N11Formalization.C450NinthGroupedC24
import N11Formalization.C450NinthGroupedC25
import N11Formalization.C450NinthGroupedC26
import N11Formalization.C450NinthGroupedC27
import N11Formalization.C450NinthGroupedC28
import N11Formalization.C450NinthGroupedC29
import N11Formalization.C450NinthGroupedC30
import N11Formalization.C450NinthGroupedC31
import N11Formalization.C450NinthGroupedC32
/-! Actual source9 full grouped closed certificate draft.
No source/root acceptance claimed by the file comment. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthSegment
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData C450NormalizedInterface
abbrev Case := Fin 32
def Qs : Case → RatInterval := ![C450NinthGroupedC01.Qcell,C450NinthGroupedC02.Qcell,C450NinthGroupedC03.Qcell,C450NinthGroupedC04.Qcell,C450NinthGroupedC05.Qcell,C450NinthGroupedC06.Qcell,C450NinthGroupedC07.Qcell,C450NinthGroupedC08.Qcell,C450NinthGroupedC09.Qcell,C450NinthGroupedC10.Qcell,C450NinthGroupedC11.Qcell,C450NinthGroupedC12.Qcell,C450NinthGroupedC13.Qcell,C450NinthGroupedC14.Qcell,C450NinthGroupedC15.Qcell,C450NinthGroupedC16.Qcell,C450NinthGroupedC17.Qcell,C450NinthGroupedC18.Qcell,C450NinthGroupedC19.Qcell,C450NinthGroupedC20.Qcell,C450NinthGroupedC21.Qcell,C450NinthGroupedC22.Qcell,C450NinthGroupedC23.Qcell,C450NinthGroupedC24.Qcell,C450NinthGroupedC25.Qcell,C450NinthGroupedC26.Qcell,C450NinthGroupedC27.Qcell,C450NinthGroupedC28.Qcell,C450NinthGroupedC29.Qcell,C450NinthGroupedC30.Qcell,C450NinthGroupedC31.Qcell,C450NinthGroupedC32.Qcell]
private def DirectionPaid (q : ℝ) : Prop := ∃ i : Case, RatInterval.Mem (Qs i) q
private theorem direction0 :
    ∀ q ∈ Set.Icc (-1:ℝ) ((-15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨0,?_⟩
  simpa [Qs,C450NinthGroupedC01.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction1 :
    ∀ q ∈ Set.Icc ((-15:ℝ)/16) ((-7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨1,?_⟩
  simpa [Qs,C450NinthGroupedC02.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction2 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8) ((-13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨2,?_⟩
  simpa [Qs,C450NinthGroupedC03.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction3 :
    ∀ q ∈ Set.Icc ((-13:ℝ)/16) ((-3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨3,?_⟩
  simpa [Qs,C450NinthGroupedC04.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction4 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4) ((-11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨4,?_⟩
  simpa [Qs,C450NinthGroupedC05.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction5 :
    ∀ q ∈ Set.Icc ((-11:ℝ)/16) ((-5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨5,?_⟩
  simpa [Qs,C450NinthGroupedC06.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction6 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8) ((-9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨6,?_⟩
  simpa [Qs,C450NinthGroupedC07.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction7 :
    ∀ q ∈ Set.Icc ((-9:ℝ)/16) ((-1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨7,?_⟩
  simpa [Qs,C450NinthGroupedC08.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction8 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2) ((-7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨8,?_⟩
  simpa [Qs,C450NinthGroupedC09.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction9 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/16) ((-3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨9,?_⟩
  simpa [Qs,C450NinthGroupedC10.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction10 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8) ((-5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨10,?_⟩
  simpa [Qs,C450NinthGroupedC11.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction11 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/16) ((-1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨11,?_⟩
  simpa [Qs,C450NinthGroupedC12.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction12 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4) ((-3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨12,?_⟩
  simpa [Qs,C450NinthGroupedC13.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction13 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/16) ((-1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨13,?_⟩
  simpa [Qs,C450NinthGroupedC14.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction14 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8) ((-1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨14,?_⟩
  simpa [Qs,C450NinthGroupedC15.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction15 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/16) (0:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨15,?_⟩
  simpa [Qs,C450NinthGroupedC16.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction16 :
    ∀ q ∈ Set.Icc (0:ℝ) ((1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨16,?_⟩
  simpa [Qs,C450NinthGroupedC17.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction17 :
    ∀ q ∈ Set.Icc ((1:ℝ)/16) ((1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨17,?_⟩
  simpa [Qs,C450NinthGroupedC18.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction18 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8) ((3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨18,?_⟩
  simpa [Qs,C450NinthGroupedC19.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction19 :
    ∀ q ∈ Set.Icc ((3:ℝ)/16) ((1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨19,?_⟩
  simpa [Qs,C450NinthGroupedC20.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction20 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4) ((5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨20,?_⟩
  simpa [Qs,C450NinthGroupedC21.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction21 :
    ∀ q ∈ Set.Icc ((5:ℝ)/16) ((3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨21,?_⟩
  simpa [Qs,C450NinthGroupedC22.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction22 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8) ((7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨22,?_⟩
  simpa [Qs,C450NinthGroupedC23.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction23 :
    ∀ q ∈ Set.Icc ((7:ℝ)/16) ((1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨23,?_⟩
  simpa [Qs,C450NinthGroupedC24.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction24 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2) ((9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨24,?_⟩
  simpa [Qs,C450NinthGroupedC25.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction25 :
    ∀ q ∈ Set.Icc ((9:ℝ)/16) ((5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨25,?_⟩
  simpa [Qs,C450NinthGroupedC26.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction26 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8) ((11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨26,?_⟩
  simpa [Qs,C450NinthGroupedC27.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction27 :
    ∀ q ∈ Set.Icc ((11:ℝ)/16) ((3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨27,?_⟩
  simpa [Qs,C450NinthGroupedC28.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction28 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4) ((13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨28,?_⟩
  simpa [Qs,C450NinthGroupedC29.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction29 :
    ∀ q ∈ Set.Icc ((13:ℝ)/16) ((7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨29,?_⟩
  simpa [Qs,C450NinthGroupedC30.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction30 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8) ((15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨30,?_⟩
  simpa [Qs,C450NinthGroupedC31.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction31 :
    ∀ q ∈ Set.Icc ((15:ℝ)/16) (1:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨31,?_⟩
  simpa [Qs,C450NinthGroupedC32.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
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
theorem cells_paid (i : Case) : CellBound ninth nn0 nn1 (Qs i) (31/50) (69/50) := by
  fin_cases i
  · exact C450NinthGroupedC01.bound
  · exact C450NinthGroupedC02.bound
  · exact C450NinthGroupedC03.bound
  · exact C450NinthGroupedC04.bound
  · exact C450NinthGroupedC05.bound
  · exact C450NinthGroupedC06.bound
  · exact C450NinthGroupedC07.bound
  · exact C450NinthGroupedC08.bound
  · exact C450NinthGroupedC09.bound
  · exact C450NinthGroupedC10.bound
  · exact C450NinthGroupedC11.bound
  · exact C450NinthGroupedC12.bound
  · exact C450NinthGroupedC13.bound
  · exact C450NinthGroupedC14.bound
  · exact C450NinthGroupedC15.bound
  · exact C450NinthGroupedC16.bound
  · exact C450NinthGroupedC17.bound
  · exact C450NinthGroupedC18.bound
  · exact C450NinthGroupedC19.bound
  · exact C450NinthGroupedC20.bound
  · exact C450NinthGroupedC21.bound
  · exact C450NinthGroupedC22.bound
  · exact C450NinthGroupedC23.bound
  · exact C450NinthGroupedC24.bound
  · exact C450NinthGroupedC25.bound
  · exact C450NinthGroupedC26.bound
  · exact C450NinthGroupedC27.bound
  · exact C450NinthGroupedC28.bound
  · exact C450NinthGroupedC29.bound
  · exact C450NinthGroupedC30.bound
  · exact C450NinthGroupedC31.bound
  · exact C450NinthGroupedC32.bound
theorem ninth_paid : SegmentNormalized ninth := by
  intro h0 h1
  exact normalized_of_cells ninth h0 h1 eHi_le Qs directions_cover cells_paid
def allPackets : List Packet := C450NinthGroupedC01.packets ++ C450NinthGroupedC02.packets ++ C450NinthGroupedC03.packets ++ C450NinthGroupedC04.packets ++ C450NinthGroupedC05.packets ++ C450NinthGroupedC06.packets ++ C450NinthGroupedC07.packets ++ C450NinthGroupedC08.packets ++ C450NinthGroupedC09.packets ++ C450NinthGroupedC10.packets ++ C450NinthGroupedC11.packets ++ C450NinthGroupedC12.packets ++ C450NinthGroupedC13.packets ++ C450NinthGroupedC14.packets ++ C450NinthGroupedC15.packets ++ C450NinthGroupedC16.packets ++ C450NinthGroupedC17.packets ++ C450NinthGroupedC18.packets ++ C450NinthGroupedC19.packets ++ C450NinthGroupedC20.packets ++ C450NinthGroupedC21.packets ++ C450NinthGroupedC22.packets ++ C450NinthGroupedC23.packets ++ C450NinthGroupedC24.packets ++ C450NinthGroupedC25.packets ++ C450NinthGroupedC26.packets ++ C450NinthGroupedC27.packets ++ C450NinthGroupedC28.packets ++ C450NinthGroupedC29.packets ++ C450NinthGroupedC30.packets ++ C450NinthGroupedC31.packets ++ C450NinthGroupedC32.packets
theorem packet_count : allPackets.length = 609 := by decide +kernel
def remainingSegs : List TenSeg := c450Segs.drop 9
theorem remaining_count : remainingSegs.length = 27 := by decide +kernel
theorem eighth_remaining_split : C450EighthSegment.remainingSegs = ninth :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem eighth_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450EighthSegment.RemainingSourceObligation := by
  intro s hs
  rw [eighth_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hseven | hrest
  · rw [hseven]
    exact ninth_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450EighthSegment.source_of_remaining (eighth_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450NinthSegment
#check @N11Formalization.C450NinthSegment.ninth_paid
#check @N11Formalization.C450NinthSegment.atom_of_remaining
#print axioms N11Formalization.C450NinthSegment.directions_cover
#print axioms N11Formalization.C450NinthSegment.cells_paid
#print axioms N11Formalization.C450NinthSegment.ninth_paid
#print axioms N11Formalization.C450NinthSegment.atom_of_remaining
