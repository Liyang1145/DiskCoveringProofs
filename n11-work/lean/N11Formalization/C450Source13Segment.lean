import N11Formalization.C450Source12Segment
import N11Formalization.C450Source13GroupedC01
import N11Formalization.C450Source13GroupedC02
import N11Formalization.C450Source13GroupedC03
import N11Formalization.C450Source13GroupedC04
import N11Formalization.C450Source13GroupedC05
import N11Formalization.C450Source13GroupedC06
import N11Formalization.C450Source13GroupedC07
import N11Formalization.C450Source13GroupedC08
import N11Formalization.C450Source13GroupedC09
import N11Formalization.C450Source13GroupedC10
import N11Formalization.C450Source13GroupedC11
import N11Formalization.C450Source13GroupedC12
import N11Formalization.C450Source13GroupedC13
import N11Formalization.C450Source13GroupedC14
import N11Formalization.C450Source13GroupedC15
import N11Formalization.C450Source13GroupedC16
import N11Formalization.C450Source13GroupedC17
import N11Formalization.C450Source13GroupedC18
import N11Formalization.C450Source13GroupedC19
import N11Formalization.C450Source13GroupedC20
import N11Formalization.C450Source13GroupedC21
import N11Formalization.C450Source13GroupedC22
import N11Formalization.C450Source13GroupedC23
import N11Formalization.C450Source13GroupedC24
import N11Formalization.C450Source13GroupedC25
import N11Formalization.C450Source13GroupedC26
import N11Formalization.C450Source13GroupedC27
import N11Formalization.C450Source13GroupedC28
import N11Formalization.C450Source13GroupedC29
import N11Formalization.C450Source13GroupedC30
import N11Formalization.C450Source13GroupedC31
import N11Formalization.C450Source13GroupedC32
import N11Formalization.C450FirstRadialKernel
/-! Actual source13 full grouped closed certificate draft.
No source/root acceptance claimed by the file comment. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13Segment
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data C450NormalizedInterface
abbrev Case := Fin 32
def Qs : Case → RatInterval := ![C450Source13GroupedC01.Qcell,C450Source13GroupedC02.Qcell,C450Source13GroupedC03.Qcell,C450Source13GroupedC04.Qcell,C450Source13GroupedC05.Qcell,C450Source13GroupedC06.Qcell,C450Source13GroupedC07.Qcell,C450Source13GroupedC08.Qcell,C450Source13GroupedC09.Qcell,C450Source13GroupedC10.Qcell,C450Source13GroupedC11.Qcell,C450Source13GroupedC12.Qcell,C450Source13GroupedC13.Qcell,C450Source13GroupedC14.Qcell,C450Source13GroupedC15.Qcell,C450Source13GroupedC16.Qcell,C450Source13GroupedC17.Qcell,C450Source13GroupedC18.Qcell,C450Source13GroupedC19.Qcell,C450Source13GroupedC20.Qcell,C450Source13GroupedC21.Qcell,C450Source13GroupedC22.Qcell,C450Source13GroupedC23.Qcell,C450Source13GroupedC24.Qcell,C450Source13GroupedC25.Qcell,C450Source13GroupedC26.Qcell,C450Source13GroupedC27.Qcell,C450Source13GroupedC28.Qcell,C450Source13GroupedC29.Qcell,C450Source13GroupedC30.Qcell,C450Source13GroupedC31.Qcell,C450Source13GroupedC32.Qcell]
private def DirectionPaid (q : ℝ) : Prop := ∃ i : Case, RatInterval.Mem (Qs i) q
private theorem direction0 :
    ∀ q ∈ Set.Icc (-1:ℝ) ((-15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨0,?_⟩
  simpa [Qs,C450Source13GroupedC01.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction1 :
    ∀ q ∈ Set.Icc ((-15:ℝ)/16) ((-7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨1,?_⟩
  simpa [Qs,C450Source13GroupedC02.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction2 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8) ((-13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨2,?_⟩
  simpa [Qs,C450Source13GroupedC03.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction3 :
    ∀ q ∈ Set.Icc ((-13:ℝ)/16) ((-3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨3,?_⟩
  simpa [Qs,C450Source13GroupedC04.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction4 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4) ((-11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨4,?_⟩
  simpa [Qs,C450Source13GroupedC05.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction5 :
    ∀ q ∈ Set.Icc ((-11:ℝ)/16) ((-5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨5,?_⟩
  simpa [Qs,C450Source13GroupedC06.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction6 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8) ((-9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨6,?_⟩
  simpa [Qs,C450Source13GroupedC07.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction7 :
    ∀ q ∈ Set.Icc ((-9:ℝ)/16) ((-1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨7,?_⟩
  simpa [Qs,C450Source13GroupedC08.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction8 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2) ((-7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨8,?_⟩
  simpa [Qs,C450Source13GroupedC09.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction9 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/16) ((-3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨9,?_⟩
  simpa [Qs,C450Source13GroupedC10.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction10 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8) ((-5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨10,?_⟩
  simpa [Qs,C450Source13GroupedC11.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction11 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/16) ((-1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨11,?_⟩
  simpa [Qs,C450Source13GroupedC12.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction12 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4) ((-3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨12,?_⟩
  simpa [Qs,C450Source13GroupedC13.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction13 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/16) ((-1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨13,?_⟩
  simpa [Qs,C450Source13GroupedC14.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction14 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8) ((-1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨14,?_⟩
  simpa [Qs,C450Source13GroupedC15.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction15 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/16) (0:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨15,?_⟩
  simpa [Qs,C450Source13GroupedC16.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction16 :
    ∀ q ∈ Set.Icc (0:ℝ) ((1:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨16,?_⟩
  simpa [Qs,C450Source13GroupedC17.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction17 :
    ∀ q ∈ Set.Icc ((1:ℝ)/16) ((1:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨17,?_⟩
  simpa [Qs,C450Source13GroupedC18.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction18 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8) ((3:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨18,?_⟩
  simpa [Qs,C450Source13GroupedC19.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction19 :
    ∀ q ∈ Set.Icc ((3:ℝ)/16) ((1:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨19,?_⟩
  simpa [Qs,C450Source13GroupedC20.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction20 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4) ((5:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨20,?_⟩
  simpa [Qs,C450Source13GroupedC21.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction21 :
    ∀ q ∈ Set.Icc ((5:ℝ)/16) ((3:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨21,?_⟩
  simpa [Qs,C450Source13GroupedC22.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction22 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8) ((7:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨22,?_⟩
  simpa [Qs,C450Source13GroupedC23.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction23 :
    ∀ q ∈ Set.Icc ((7:ℝ)/16) ((1:ℝ)/2), DirectionPaid q := by
  intro q hq
  refine ⟨23,?_⟩
  simpa [Qs,C450Source13GroupedC24.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction24 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2) ((9:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨24,?_⟩
  simpa [Qs,C450Source13GroupedC25.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction25 :
    ∀ q ∈ Set.Icc ((9:ℝ)/16) ((5:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨25,?_⟩
  simpa [Qs,C450Source13GroupedC26.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction26 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8) ((11:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨26,?_⟩
  simpa [Qs,C450Source13GroupedC27.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction27 :
    ∀ q ∈ Set.Icc ((11:ℝ)/16) ((3:ℝ)/4), DirectionPaid q := by
  intro q hq
  refine ⟨27,?_⟩
  simpa [Qs,C450Source13GroupedC28.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction28 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4) ((13:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨28,?_⟩
  simpa [Qs,C450Source13GroupedC29.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction29 :
    ∀ q ∈ Set.Icc ((13:ℝ)/16) ((7:ℝ)/8), DirectionPaid q := by
  intro q hq
  refine ⟨29,?_⟩
  simpa [Qs,C450Source13GroupedC30.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction30 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8) ((15:ℝ)/16), DirectionPaid q := by
  intro q hq
  refine ⟨30,?_⟩
  simpa [Qs,C450Source13GroupedC31.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
private theorem direction31 :
    ∀ q ∈ Set.Icc ((15:ℝ)/16) (1:ℝ), DirectionPaid q := by
  intro q hq
  refine ⟨31,?_⟩
  simpa [Qs,C450Source13GroupedC32.Qcell,RatInterval.Mem,RatInterval.toSet] using hq
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
theorem cells_paid (i : Case) : CellBound source13 nn0 nn1 (Qs i) (31/50) (69/50) := by
  fin_cases i
  · exact C450Source13GroupedC01.bound
  · exact C450Source13GroupedC02.bound
  · exact C450Source13GroupedC03.bound
  · exact C450Source13GroupedC04.bound
  · exact C450Source13GroupedC05.bound
  · exact C450Source13GroupedC06.bound
  · exact C450Source13GroupedC07.bound
  · exact C450Source13GroupedC08.bound
  · exact C450Source13GroupedC09.bound
  · exact C450Source13GroupedC10.bound
  · exact C450Source13GroupedC11.bound
  · exact C450Source13GroupedC12.bound
  · exact C450Source13GroupedC13.bound
  · exact C450Source13GroupedC14.bound
  · exact C450Source13GroupedC15.bound
  · exact C450Source13GroupedC16.bound
  · exact C450Source13GroupedC17.bound
  · exact C450Source13GroupedC18.bound
  · exact C450Source13GroupedC19.bound
  · exact C450Source13GroupedC20.bound
  · exact C450Source13GroupedC21.bound
  · exact C450Source13GroupedC22.bound
  · exact C450Source13GroupedC23.bound
  · exact C450Source13GroupedC24.bound
  · exact C450Source13GroupedC25.bound
  · exact C450Source13GroupedC26.bound
  · exact C450Source13GroupedC27.bound
  · exact C450Source13GroupedC28.bound
  · exact C450Source13GroupedC29.bound
  · exact C450Source13GroupedC30.bound
  · exact C450Source13GroupedC31.bound
  · exact C450Source13GroupedC32.bound
theorem source13_paid : SegmentNormalized source13 := by
  intro h0 h1
  exact normalized_of_cells source13 h0 h1 eHi_le Qs directions_cover cells_paid
def allPackets : List Packet := C450Source13GroupedC01.packets ++ C450Source13GroupedC02.packets ++ C450Source13GroupedC03.packets ++ C450Source13GroupedC04.packets ++ C450Source13GroupedC05.packets ++ C450Source13GroupedC06.packets ++ C450Source13GroupedC07.packets ++ C450Source13GroupedC08.packets ++ C450Source13GroupedC09.packets ++ C450Source13GroupedC10.packets ++ C450Source13GroupedC11.packets ++ C450Source13GroupedC12.packets ++ C450Source13GroupedC13.packets ++ C450Source13GroupedC14.packets ++ C450Source13GroupedC15.packets ++ C450Source13GroupedC16.packets ++ C450Source13GroupedC17.packets ++ C450Source13GroupedC18.packets ++ C450Source13GroupedC19.packets ++ C450Source13GroupedC20.packets ++ C450Source13GroupedC21.packets ++ C450Source13GroupedC22.packets ++ C450Source13GroupedC23.packets ++ C450Source13GroupedC24.packets ++ C450Source13GroupedC25.packets ++ C450Source13GroupedC26.packets ++ C450Source13GroupedC27.packets ++ C450Source13GroupedC28.packets ++ C450Source13GroupedC29.packets ++ C450Source13GroupedC30.packets ++ C450Source13GroupedC31.packets ++ C450Source13GroupedC32.packets
theorem packet_count : allPackets.length = 586 := by decide +kernel
def remainingSegs : List TenSeg := c450Segs.drop 13
theorem remaining_count : remainingSegs.length = 23 := by decide +kernel
theorem source12_remaining_split : C450Source12Segment.remainingSegs = source13 :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem source12_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450Source12Segment.RemainingSourceObligation := by
  intro s hs
  rw [source12_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hnext | hrest
  · rw [hnext]
    exact source13_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450Source12Segment.source_of_remaining (source12_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450Source13Segment
#check @N11Formalization.C450Source13Segment.source13_paid
#check @N11Formalization.C450Source13Segment.atom_of_remaining
#print axioms N11Formalization.C450Source13Segment.directions_cover
#print axioms N11Formalization.C450Source13Segment.cells_paid
#print axioms N11Formalization.C450Source13Segment.source13_paid
#print axioms N11Formalization.C450Source13Segment.atom_of_remaining
