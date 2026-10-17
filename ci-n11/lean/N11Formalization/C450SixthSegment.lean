import N11Formalization.C450SixthAnalytic
import N11Formalization.C450SixthRadialC01
import N11Formalization.C450SixthRadialC02
import N11Formalization.C450SixthRadialC03
import N11Formalization.C450SixthRadialC04
import N11Formalization.C450SixthRadialC05
import N11Formalization.C450SixthRadialC06
import N11Formalization.C450SixthRadialC07
import N11Formalization.C450SixthRadialC08
import N11Formalization.C450SixthRadialC09
import N11Formalization.C450SixthRadialC10
import N11Formalization.C450SixthRadialC11
import N11Formalization.C450SixthRadialC12
import N11Formalization.C450SixthRadialC13
import N11Formalization.C450SixthRadialC14
import N11Formalization.C450SixthRadialC15
import N11Formalization.C450SixthRadialC16
import N11Formalization.C450SixthRadialC17
import N11Formalization.C450SixthRadialC18
import N11Formalization.C450SixthRadialC19
import N11Formalization.C450SixthRadialC20
import N11Formalization.C450SixthRadialC21
import N11Formalization.C450SixthRadialC22
import N11Formalization.C450SixthRadialC23
import N11Formalization.C450SixthRadialC24
import N11Formalization.C450SixthRadialC25
import N11Formalization.C450SixthRadialC26
import N11Formalization.C450SixthRadialC27
import N11Formalization.C450SixthRadialC28
import N11Formalization.C450SixthRadialC29
import N11Formalization.C450SixthRadialC30
import N11Formalization.C450SixthRadialC31
import N11Formalization.C450SixthRadialC32
import N11Formalization.C450SixthRadialC33
import N11Formalization.C450SixthRadialC34
import N11Formalization.C450SixthRadialC35
import N11Formalization.C450SixthRadialC36
import N11Formalization.C450SixthRadialC37
import N11Formalization.C450SixthRadialC38
import N11Formalization.C450SixthRadialC39
import N11Formalization.C450SixthRadialC40
import N11Formalization.C450SixthRadialC41
import N11Formalization.C450SixthRadialC42
import N11Formalization.C450SixthRadialC43
import N11Formalization.C450SixthRadialC44
import N11Formalization.C450SixthRadialC45
import N11Formalization.C450SixthRadialC46
import N11Formalization.C450SixthRadialC47
import N11Formalization.C450SixthRadialC48
import N11Formalization.C450SixthRadialC49
import N11Formalization.C450SixthRadialC50
import N11Formalization.C450SixthRadialC51
import N11Formalization.C450SixthRadialC52
import N11Formalization.C450SixthRadialC53
import N11Formalization.C450SixthRadialC54
import N11Formalization.C450SixthRadialC55
import N11Formalization.C450SixthRadialC56
import N11Formalization.C450SixthRadialC57
import N11Formalization.C450SixthRadialC58
import N11Formalization.C450SixthRadialC59
import N11Formalization.C450SixthRadialC60
import N11Formalization.C450SixthRadialC61
import N11Formalization.C450SixthRadialC62
import N11Formalization.C450SixthRadialC63
import N11Formalization.C450SixthRadialC64
/-! Actual sixth normalized C450 certificate: complete closed direction
and radial domains; all other30 source segments remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthSegment
open C450RadialPacketKernel C450AngularCellMajorant C450AngularMajorant
open C450OuterCellMajorant C450SixthAnalytic C450NormalizedInterface
abbrev Case := Fin 64
def cells : Case → Cell := ![⟨-1,(-31/32)⟩,⟨(-31/32),(-15/16)⟩,⟨(-15/16),(-29/32)⟩,⟨(-29/32),(-7/8)⟩,⟨(-7/8),(-27/32)⟩,⟨(-27/32),(-13/16)⟩,⟨(-13/16),(-25/32)⟩,⟨(-25/32),(-3/4)⟩,⟨(-3/4),(-23/32)⟩,⟨(-23/32),(-11/16)⟩,⟨(-11/16),(-21/32)⟩,⟨(-21/32),(-5/8)⟩,⟨(-5/8),(-19/32)⟩,⟨(-19/32),(-9/16)⟩,⟨(-9/16),(-17/32)⟩,⟨(-17/32),(-1/2)⟩,⟨(-1/2),(-15/32)⟩,⟨(-15/32),(-7/16)⟩,⟨(-7/16),(-13/32)⟩,⟨(-13/32),(-3/8)⟩,⟨(-3/8),(-11/32)⟩,⟨(-11/32),(-5/16)⟩,⟨(-5/16),(-9/32)⟩,⟨(-9/32),(-1/4)⟩,⟨(-1/4),(-7/32)⟩,⟨(-7/32),(-3/16)⟩,⟨(-3/16),(-5/32)⟩,⟨(-5/32),(-1/8)⟩,⟨(-1/8),(-3/32)⟩,⟨(-3/32),(-1/16)⟩,⟨(-1/16),(-1/32)⟩,⟨(-1/32),0⟩,⟨0,(1/32)⟩,⟨(1/32),(1/16)⟩,⟨(1/16),(3/32)⟩,⟨(3/32),(1/8)⟩,⟨(1/8),(5/32)⟩,⟨(5/32),(3/16)⟩,⟨(3/16),(7/32)⟩,⟨(7/32),(1/4)⟩,⟨(1/4),(9/32)⟩,⟨(9/32),(5/16)⟩,⟨(5/16),(11/32)⟩,⟨(11/32),(3/8)⟩,⟨(3/8),(13/32)⟩,⟨(13/32),(7/16)⟩,⟨(7/16),(15/32)⟩,⟨(15/32),(1/2)⟩,⟨(1/2),(17/32)⟩,⟨(17/32),(9/16)⟩,⟨(9/16),(19/32)⟩,⟨(19/32),(5/8)⟩,⟨(5/8),(21/32)⟩,⟨(21/32),(11/16)⟩,⟨(11/16),(23/32)⟩,⟨(23/32),(3/4)⟩,⟨(3/4),(25/32)⟩,⟨(25/32),(13/16)⟩,⟨(13/16),(27/32)⟩,⟨(27/32),(7/8)⟩,⟨(7/8),(29/32)⟩,⟨(29/32),(15/16)⟩,⟨(15/16),(31/32)⟩,⟨(31/32),1⟩]
def params : Case → Params := ![C450SixthRadialC01.params,C450SixthRadialC02.params,C450SixthRadialC03.params,C450SixthRadialC04.params,C450SixthRadialC05.params,C450SixthRadialC06.params,C450SixthRadialC07.params,C450SixthRadialC08.params,C450SixthRadialC09.params,C450SixthRadialC10.params,C450SixthRadialC11.params,C450SixthRadialC12.params,C450SixthRadialC13.params,C450SixthRadialC14.params,C450SixthRadialC15.params,C450SixthRadialC16.params,C450SixthRadialC17.params,C450SixthRadialC18.params,C450SixthRadialC19.params,C450SixthRadialC20.params,C450SixthRadialC21.params,C450SixthRadialC22.params,C450SixthRadialC23.params,C450SixthRadialC24.params,C450SixthRadialC25.params,C450SixthRadialC26.params,C450SixthRadialC27.params,C450SixthRadialC28.params,C450SixthRadialC29.params,C450SixthRadialC30.params,C450SixthRadialC31.params,C450SixthRadialC32.params,C450SixthRadialC33.params,C450SixthRadialC34.params,C450SixthRadialC35.params,C450SixthRadialC36.params,C450SixthRadialC37.params,C450SixthRadialC38.params,C450SixthRadialC39.params,C450SixthRadialC40.params,C450SixthRadialC41.params,C450SixthRadialC42.params,C450SixthRadialC43.params,C450SixthRadialC44.params,C450SixthRadialC45.params,C450SixthRadialC46.params,C450SixthRadialC47.params,C450SixthRadialC48.params,C450SixthRadialC49.params,C450SixthRadialC50.params,C450SixthRadialC51.params,C450SixthRadialC52.params,C450SixthRadialC53.params,C450SixthRadialC54.params,C450SixthRadialC55.params,C450SixthRadialC56.params,C450SixthRadialC57.params,C450SixthRadialC58.params,C450SixthRadialC59.params,C450SixthRadialC60.params,C450SixthRadialC61.params,C450SixthRadialC62.params,C450SixthRadialC63.params,C450SixthRadialC64.params]
private theorem cell_valid0 : ValidCell (cells 0) := by
  change ValidCell (⟨-1,(-31/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid1 : ValidCell (cells 1) := by
  change ValidCell (⟨(-31/32),(-15/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid2 : ValidCell (cells 2) := by
  change ValidCell (⟨(-15/16),(-29/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid3 : ValidCell (cells 3) := by
  change ValidCell (⟨(-29/32),(-7/8)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid4 : ValidCell (cells 4) := by
  change ValidCell (⟨(-7/8),(-27/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid5 : ValidCell (cells 5) := by
  change ValidCell (⟨(-27/32),(-13/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid6 : ValidCell (cells 6) := by
  change ValidCell (⟨(-13/16),(-25/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid7 : ValidCell (cells 7) := by
  change ValidCell (⟨(-25/32),(-3/4)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid8 : ValidCell (cells 8) := by
  change ValidCell (⟨(-3/4),(-23/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid9 : ValidCell (cells 9) := by
  change ValidCell (⟨(-23/32),(-11/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid10 : ValidCell (cells 10) := by
  change ValidCell (⟨(-11/16),(-21/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid11 : ValidCell (cells 11) := by
  change ValidCell (⟨(-21/32),(-5/8)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid12 : ValidCell (cells 12) := by
  change ValidCell (⟨(-5/8),(-19/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid13 : ValidCell (cells 13) := by
  change ValidCell (⟨(-19/32),(-9/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid14 : ValidCell (cells 14) := by
  change ValidCell (⟨(-9/16),(-17/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid15 : ValidCell (cells 15) := by
  change ValidCell (⟨(-17/32),(-1/2)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid16 : ValidCell (cells 16) := by
  change ValidCell (⟨(-1/2),(-15/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid17 : ValidCell (cells 17) := by
  change ValidCell (⟨(-15/32),(-7/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid18 : ValidCell (cells 18) := by
  change ValidCell (⟨(-7/16),(-13/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid19 : ValidCell (cells 19) := by
  change ValidCell (⟨(-13/32),(-3/8)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid20 : ValidCell (cells 20) := by
  change ValidCell (⟨(-3/8),(-11/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid21 : ValidCell (cells 21) := by
  change ValidCell (⟨(-11/32),(-5/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid22 : ValidCell (cells 22) := by
  change ValidCell (⟨(-5/16),(-9/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid23 : ValidCell (cells 23) := by
  change ValidCell (⟨(-9/32),(-1/4)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid24 : ValidCell (cells 24) := by
  change ValidCell (⟨(-1/4),(-7/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid25 : ValidCell (cells 25) := by
  change ValidCell (⟨(-7/32),(-3/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid26 : ValidCell (cells 26) := by
  change ValidCell (⟨(-3/16),(-5/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid27 : ValidCell (cells 27) := by
  change ValidCell (⟨(-5/32),(-1/8)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid28 : ValidCell (cells 28) := by
  change ValidCell (⟨(-1/8),(-3/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid29 : ValidCell (cells 29) := by
  change ValidCell (⟨(-3/32),(-1/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid30 : ValidCell (cells 30) := by
  change ValidCell (⟨(-1/16),(-1/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid31 : ValidCell (cells 31) := by
  change ValidCell (⟨(-1/32),0⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid32 : ValidCell (cells 32) := by
  change ValidCell (⟨0,(1/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid33 : ValidCell (cells 33) := by
  change ValidCell (⟨(1/32),(1/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid34 : ValidCell (cells 34) := by
  change ValidCell (⟨(1/16),(3/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid35 : ValidCell (cells 35) := by
  change ValidCell (⟨(3/32),(1/8)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid36 : ValidCell (cells 36) := by
  change ValidCell (⟨(1/8),(5/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid37 : ValidCell (cells 37) := by
  change ValidCell (⟨(5/32),(3/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid38 : ValidCell (cells 38) := by
  change ValidCell (⟨(3/16),(7/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid39 : ValidCell (cells 39) := by
  change ValidCell (⟨(7/32),(1/4)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid40 : ValidCell (cells 40) := by
  change ValidCell (⟨(1/4),(9/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid41 : ValidCell (cells 41) := by
  change ValidCell (⟨(9/32),(5/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid42 : ValidCell (cells 42) := by
  change ValidCell (⟨(5/16),(11/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid43 : ValidCell (cells 43) := by
  change ValidCell (⟨(11/32),(3/8)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid44 : ValidCell (cells 44) := by
  change ValidCell (⟨(3/8),(13/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid45 : ValidCell (cells 45) := by
  change ValidCell (⟨(13/32),(7/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid46 : ValidCell (cells 46) := by
  change ValidCell (⟨(7/16),(15/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid47 : ValidCell (cells 47) := by
  change ValidCell (⟨(15/32),(1/2)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid48 : ValidCell (cells 48) := by
  change ValidCell (⟨(1/2),(17/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid49 : ValidCell (cells 49) := by
  change ValidCell (⟨(17/32),(9/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid50 : ValidCell (cells 50) := by
  change ValidCell (⟨(9/16),(19/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid51 : ValidCell (cells 51) := by
  change ValidCell (⟨(19/32),(5/8)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid52 : ValidCell (cells 52) := by
  change ValidCell (⟨(5/8),(21/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid53 : ValidCell (cells 53) := by
  change ValidCell (⟨(21/32),(11/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid54 : ValidCell (cells 54) := by
  change ValidCell (⟨(11/16),(23/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid55 : ValidCell (cells 55) := by
  change ValidCell (⟨(23/32),(3/4)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid56 : ValidCell (cells 56) := by
  change ValidCell (⟨(3/4),(25/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid57 : ValidCell (cells 57) := by
  change ValidCell (⟨(25/32),(13/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid58 : ValidCell (cells 58) := by
  change ValidCell (⟨(13/16),(27/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid59 : ValidCell (cells 59) := by
  change ValidCell (⟨(27/32),(7/8)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid60 : ValidCell (cells 60) := by
  change ValidCell (⟨(7/8),(29/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid61 : ValidCell (cells 61) := by
  change ValidCell (⟨(29/32),(15/16)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid62 : ValidCell (cells 62) := by
  change ValidCell (⟨(15/16),(31/32)⟩ : Cell)
  constructor <;> norm_num
private theorem cell_valid63 : ValidCell (cells 63) := by
  change ValidCell (⟨(31/32),1⟩ : Cell)
  constructor <;> norm_num
theorem cells_valid (i : Case) : ValidCell (cells i) := by
  fin_cases i
  · exact cell_valid0
  · exact cell_valid1
  · exact cell_valid2
  · exact cell_valid3
  · exact cell_valid4
  · exact cell_valid5
  · exact cell_valid6
  · exact cell_valid7
  · exact cell_valid8
  · exact cell_valid9
  · exact cell_valid10
  · exact cell_valid11
  · exact cell_valid12
  · exact cell_valid13
  · exact cell_valid14
  · exact cell_valid15
  · exact cell_valid16
  · exact cell_valid17
  · exact cell_valid18
  · exact cell_valid19
  · exact cell_valid20
  · exact cell_valid21
  · exact cell_valid22
  · exact cell_valid23
  · exact cell_valid24
  · exact cell_valid25
  · exact cell_valid26
  · exact cell_valid27
  · exact cell_valid28
  · exact cell_valid29
  · exact cell_valid30
  · exact cell_valid31
  · exact cell_valid32
  · exact cell_valid33
  · exact cell_valid34
  · exact cell_valid35
  · exact cell_valid36
  · exact cell_valid37
  · exact cell_valid38
  · exact cell_valid39
  · exact cell_valid40
  · exact cell_valid41
  · exact cell_valid42
  · exact cell_valid43
  · exact cell_valid44
  · exact cell_valid45
  · exact cell_valid46
  · exact cell_valid47
  · exact cell_valid48
  · exact cell_valid49
  · exact cell_valid50
  · exact cell_valid51
  · exact cell_valid52
  · exact cell_valid53
  · exact cell_valid54
  · exact cell_valid55
  · exact cell_valid56
  · exact cell_valid57
  · exact cell_valid58
  · exact cell_valid59
  · exact cell_valid60
  · exact cell_valid61
  · exact cell_valid62
  · exact cell_valid63
private def DirectionPaid (q : ℝ) : Prop := ∃ i : Case, q ∈ Set.Icc (cells i).lo (cells i).hi
private theorem direction0 :
    ∀ q ∈ Set.Icc (-1:ℝ) ((-31:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨0,by simpa [cells] using h⟩
private theorem direction1 :
    ∀ q ∈ Set.Icc ((-31:ℝ)/32) ((-15:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨1,by simpa [cells] using h⟩
private theorem direction2 :
    ∀ q ∈ Set.Icc ((-15:ℝ)/16) ((-29:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨2,by simpa [cells] using h⟩
private theorem direction3 :
    ∀ q ∈ Set.Icc ((-29:ℝ)/32) ((-7:ℝ)/8), DirectionPaid q := by
  intro q h
  exact ⟨3,by simpa [cells] using h⟩
private theorem direction4 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8) ((-27:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨4,by simpa [cells] using h⟩
private theorem direction5 :
    ∀ q ∈ Set.Icc ((-27:ℝ)/32) ((-13:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨5,by simpa [cells] using h⟩
private theorem direction6 :
    ∀ q ∈ Set.Icc ((-13:ℝ)/16) ((-25:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨6,by simpa [cells] using h⟩
private theorem direction7 :
    ∀ q ∈ Set.Icc ((-25:ℝ)/32) ((-3:ℝ)/4), DirectionPaid q := by
  intro q h
  exact ⟨7,by simpa [cells] using h⟩
private theorem direction8 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4) ((-23:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨8,by simpa [cells] using h⟩
private theorem direction9 :
    ∀ q ∈ Set.Icc ((-23:ℝ)/32) ((-11:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨9,by simpa [cells] using h⟩
private theorem direction10 :
    ∀ q ∈ Set.Icc ((-11:ℝ)/16) ((-21:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨10,by simpa [cells] using h⟩
private theorem direction11 :
    ∀ q ∈ Set.Icc ((-21:ℝ)/32) ((-5:ℝ)/8), DirectionPaid q := by
  intro q h
  exact ⟨11,by simpa [cells] using h⟩
private theorem direction12 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8) ((-19:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨12,by simpa [cells] using h⟩
private theorem direction13 :
    ∀ q ∈ Set.Icc ((-19:ℝ)/32) ((-9:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨13,by simpa [cells] using h⟩
private theorem direction14 :
    ∀ q ∈ Set.Icc ((-9:ℝ)/16) ((-17:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨14,by simpa [cells] using h⟩
private theorem direction15 :
    ∀ q ∈ Set.Icc ((-17:ℝ)/32) ((-1:ℝ)/2), DirectionPaid q := by
  intro q h
  exact ⟨15,by simpa [cells] using h⟩
private theorem direction16 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2) ((-15:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨16,by simpa [cells] using h⟩
private theorem direction17 :
    ∀ q ∈ Set.Icc ((-15:ℝ)/32) ((-7:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨17,by simpa [cells] using h⟩
private theorem direction18 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/16) ((-13:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨18,by simpa [cells] using h⟩
private theorem direction19 :
    ∀ q ∈ Set.Icc ((-13:ℝ)/32) ((-3:ℝ)/8), DirectionPaid q := by
  intro q h
  exact ⟨19,by simpa [cells] using h⟩
private theorem direction20 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8) ((-11:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨20,by simpa [cells] using h⟩
private theorem direction21 :
    ∀ q ∈ Set.Icc ((-11:ℝ)/32) ((-5:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨21,by simpa [cells] using h⟩
private theorem direction22 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/16) ((-9:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨22,by simpa [cells] using h⟩
private theorem direction23 :
    ∀ q ∈ Set.Icc ((-9:ℝ)/32) ((-1:ℝ)/4), DirectionPaid q := by
  intro q h
  exact ⟨23,by simpa [cells] using h⟩
private theorem direction24 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4) ((-7:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨24,by simpa [cells] using h⟩
private theorem direction25 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/32) ((-3:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨25,by simpa [cells] using h⟩
private theorem direction26 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/16) ((-5:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨26,by simpa [cells] using h⟩
private theorem direction27 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/32) ((-1:ℝ)/8), DirectionPaid q := by
  intro q h
  exact ⟨27,by simpa [cells] using h⟩
private theorem direction28 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8) ((-3:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨28,by simpa [cells] using h⟩
private theorem direction29 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/32) ((-1:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨29,by simpa [cells] using h⟩
private theorem direction30 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/16) ((-1:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨30,by simpa [cells] using h⟩
private theorem direction31 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/32) (0:ℝ), DirectionPaid q := by
  intro q h
  exact ⟨31,by simpa [cells] using h⟩
private theorem direction32 :
    ∀ q ∈ Set.Icc (0:ℝ) ((1:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨32,by simpa [cells] using h⟩
private theorem direction33 :
    ∀ q ∈ Set.Icc ((1:ℝ)/32) ((1:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨33,by simpa [cells] using h⟩
private theorem direction34 :
    ∀ q ∈ Set.Icc ((1:ℝ)/16) ((3:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨34,by simpa [cells] using h⟩
private theorem direction35 :
    ∀ q ∈ Set.Icc ((3:ℝ)/32) ((1:ℝ)/8), DirectionPaid q := by
  intro q h
  exact ⟨35,by simpa [cells] using h⟩
private theorem direction36 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8) ((5:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨36,by simpa [cells] using h⟩
private theorem direction37 :
    ∀ q ∈ Set.Icc ((5:ℝ)/32) ((3:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨37,by simpa [cells] using h⟩
private theorem direction38 :
    ∀ q ∈ Set.Icc ((3:ℝ)/16) ((7:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨38,by simpa [cells] using h⟩
private theorem direction39 :
    ∀ q ∈ Set.Icc ((7:ℝ)/32) ((1:ℝ)/4), DirectionPaid q := by
  intro q h
  exact ⟨39,by simpa [cells] using h⟩
private theorem direction40 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4) ((9:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨40,by simpa [cells] using h⟩
private theorem direction41 :
    ∀ q ∈ Set.Icc ((9:ℝ)/32) ((5:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨41,by simpa [cells] using h⟩
private theorem direction42 :
    ∀ q ∈ Set.Icc ((5:ℝ)/16) ((11:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨42,by simpa [cells] using h⟩
private theorem direction43 :
    ∀ q ∈ Set.Icc ((11:ℝ)/32) ((3:ℝ)/8), DirectionPaid q := by
  intro q h
  exact ⟨43,by simpa [cells] using h⟩
private theorem direction44 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8) ((13:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨44,by simpa [cells] using h⟩
private theorem direction45 :
    ∀ q ∈ Set.Icc ((13:ℝ)/32) ((7:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨45,by simpa [cells] using h⟩
private theorem direction46 :
    ∀ q ∈ Set.Icc ((7:ℝ)/16) ((15:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨46,by simpa [cells] using h⟩
private theorem direction47 :
    ∀ q ∈ Set.Icc ((15:ℝ)/32) ((1:ℝ)/2), DirectionPaid q := by
  intro q h
  exact ⟨47,by simpa [cells] using h⟩
private theorem direction48 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2) ((17:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨48,by simpa [cells] using h⟩
private theorem direction49 :
    ∀ q ∈ Set.Icc ((17:ℝ)/32) ((9:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨49,by simpa [cells] using h⟩
private theorem direction50 :
    ∀ q ∈ Set.Icc ((9:ℝ)/16) ((19:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨50,by simpa [cells] using h⟩
private theorem direction51 :
    ∀ q ∈ Set.Icc ((19:ℝ)/32) ((5:ℝ)/8), DirectionPaid q := by
  intro q h
  exact ⟨51,by simpa [cells] using h⟩
private theorem direction52 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8) ((21:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨52,by simpa [cells] using h⟩
private theorem direction53 :
    ∀ q ∈ Set.Icc ((21:ℝ)/32) ((11:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨53,by simpa [cells] using h⟩
private theorem direction54 :
    ∀ q ∈ Set.Icc ((11:ℝ)/16) ((23:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨54,by simpa [cells] using h⟩
private theorem direction55 :
    ∀ q ∈ Set.Icc ((23:ℝ)/32) ((3:ℝ)/4), DirectionPaid q := by
  intro q h
  exact ⟨55,by simpa [cells] using h⟩
private theorem direction56 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4) ((25:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨56,by simpa [cells] using h⟩
private theorem direction57 :
    ∀ q ∈ Set.Icc ((25:ℝ)/32) ((13:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨57,by simpa [cells] using h⟩
private theorem direction58 :
    ∀ q ∈ Set.Icc ((13:ℝ)/16) ((27:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨58,by simpa [cells] using h⟩
private theorem direction59 :
    ∀ q ∈ Set.Icc ((27:ℝ)/32) ((7:ℝ)/8), DirectionPaid q := by
  intro q h
  exact ⟨59,by simpa [cells] using h⟩
private theorem direction60 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8) ((29:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨60,by simpa [cells] using h⟩
private theorem direction61 :
    ∀ q ∈ Set.Icc ((29:ℝ)/32) ((15:ℝ)/16), DirectionPaid q := by
  intro q h
  exact ⟨61,by simpa [cells] using h⟩
private theorem direction62 :
    ∀ q ∈ Set.Icc ((15:ℝ)/16) ((31:ℝ)/32), DirectionPaid q := by
  intro q h
  exact ⟨62,by simpa [cells] using h⟩
private theorem direction63 :
    ∀ q ∈ Set.Icc ((31:ℝ)/32) (1:ℝ), DirectionPaid q := by
  intro q h
  exact ⟨63,by simpa [cells] using h⟩
private theorem directions0_2 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      ((-15:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction0 direction1
private theorem directions2_4 :
    ∀ q ∈ Set.Icc ((-15:ℝ)/16)
      ((-7:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction2 direction3
private theorem directions0_4 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      ((-7:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_2 directions2_4
private theorem directions4_6 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8)
      ((-13:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction4 direction5
private theorem directions6_8 :
    ∀ q ∈ Set.Icc ((-13:ℝ)/16)
      ((-3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction6 direction7
private theorem directions4_8 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/8)
      ((-3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions4_6 directions6_8
private theorem directions0_8 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      ((-3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_4 directions4_8
private theorem directions8_10 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4)
      ((-11:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction8 direction9
private theorem directions10_12 :
    ∀ q ∈ Set.Icc ((-11:ℝ)/16)
      ((-5:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction10 direction11
private theorem directions8_12 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4)
      ((-5:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions8_10 directions10_12
private theorem directions12_14 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8)
      ((-9:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction12 direction13
private theorem directions14_16 :
    ∀ q ∈ Set.Icc ((-9:ℝ)/16)
      ((-1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction14 direction15
private theorem directions12_16 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/8)
      ((-1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions12_14 directions14_16
private theorem directions8_16 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/4)
      ((-1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions8_12 directions12_16
private theorem directions0_16 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      ((-1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_8 directions8_16
private theorem directions16_18 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2)
      ((-7:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction16 direction17
private theorem directions18_20 :
    ∀ q ∈ Set.Icc ((-7:ℝ)/16)
      ((-3:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction18 direction19
private theorem directions16_20 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2)
      ((-3:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions16_18 directions18_20
private theorem directions20_22 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8)
      ((-5:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction20 direction21
private theorem directions22_24 :
    ∀ q ∈ Set.Icc ((-5:ℝ)/16)
      ((-1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction22 direction23
private theorem directions20_24 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/8)
      ((-1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions20_22 directions22_24
private theorem directions16_24 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2)
      ((-1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions16_20 directions20_24
private theorem directions24_26 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4)
      ((-3:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction24 direction25
private theorem directions26_28 :
    ∀ q ∈ Set.Icc ((-3:ℝ)/16)
      ((-1:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction26 direction27
private theorem directions24_28 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4)
      ((-1:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions24_26 directions26_28
private theorem directions28_30 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8)
      ((-1:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction28 direction29
private theorem directions30_32 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/16)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction30 direction31
private theorem directions28_32 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/8)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions28_30 directions30_32
private theorem directions24_32 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/4)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions24_28 directions28_32
private theorem directions16_32 :
    ∀ q ∈ Set.Icc ((-1:ℝ)/2)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions16_24 directions24_32
private theorem directions0_32 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      (0:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_16 directions16_32
private theorem directions32_34 :
    ∀ q ∈ Set.Icc (0:ℝ)
      ((1:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction32 direction33
private theorem directions34_36 :
    ∀ q ∈ Set.Icc ((1:ℝ)/16)
      ((1:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction34 direction35
private theorem directions32_36 :
    ∀ q ∈ Set.Icc (0:ℝ)
      ((1:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions32_34 directions34_36
private theorem directions36_38 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8)
      ((3:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction36 direction37
private theorem directions38_40 :
    ∀ q ∈ Set.Icc ((3:ℝ)/16)
      ((1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction38 direction39
private theorem directions36_40 :
    ∀ q ∈ Set.Icc ((1:ℝ)/8)
      ((1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions36_38 directions38_40
private theorem directions32_40 :
    ∀ q ∈ Set.Icc (0:ℝ)
      ((1:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions32_36 directions36_40
private theorem directions40_42 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4)
      ((5:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction40 direction41
private theorem directions42_44 :
    ∀ q ∈ Set.Icc ((5:ℝ)/16)
      ((3:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction42 direction43
private theorem directions40_44 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4)
      ((3:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions40_42 directions42_44
private theorem directions44_46 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8)
      ((7:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction44 direction45
private theorem directions46_48 :
    ∀ q ∈ Set.Icc ((7:ℝ)/16)
      ((1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction46 direction47
private theorem directions44_48 :
    ∀ q ∈ Set.Icc ((3:ℝ)/8)
      ((1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions44_46 directions46_48
private theorem directions40_48 :
    ∀ q ∈ Set.Icc ((1:ℝ)/4)
      ((1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions40_44 directions44_48
private theorem directions32_48 :
    ∀ q ∈ Set.Icc (0:ℝ)
      ((1:ℝ)/2), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions32_40 directions40_48
private theorem directions48_50 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2)
      ((9:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction48 direction49
private theorem directions50_52 :
    ∀ q ∈ Set.Icc ((9:ℝ)/16)
      ((5:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction50 direction51
private theorem directions48_52 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2)
      ((5:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions48_50 directions50_52
private theorem directions52_54 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8)
      ((11:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction52 direction53
private theorem directions54_56 :
    ∀ q ∈ Set.Icc ((11:ℝ)/16)
      ((3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction54 direction55
private theorem directions52_56 :
    ∀ q ∈ Set.Icc ((5:ℝ)/8)
      ((3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions52_54 directions54_56
private theorem directions48_56 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2)
      ((3:ℝ)/4), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions48_52 directions52_56
private theorem directions56_58 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4)
      ((13:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction56 direction57
private theorem directions58_60 :
    ∀ q ∈ Set.Icc ((13:ℝ)/16)
      ((7:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction58 direction59
private theorem directions56_60 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4)
      ((7:ℝ)/8), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions56_58 directions58_60
private theorem directions60_62 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8)
      ((15:ℝ)/16), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction60 direction61
private theorem directions62_64 :
    ∀ q ∈ Set.Icc ((15:ℝ)/16)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join direction62 direction63
private theorem directions60_64 :
    ∀ q ∈ Set.Icc ((7:ℝ)/8)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions60_62 directions62_64
private theorem directions56_64 :
    ∀ q ∈ Set.Icc ((3:ℝ)/4)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions56_60 directions60_64
private theorem directions48_64 :
    ∀ q ∈ Set.Icc ((1:ℝ)/2)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions48_56 directions56_64
private theorem directions32_64 :
    ∀ q ∈ Set.Icc (0:ℝ)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions32_48 directions48_64
private theorem directions0_64 :
    ∀ q ∈ Set.Icc (-1:ℝ)
      (1:ℝ), DirectionPaid q :=
  C450FirstRadialKernel.interval_join directions0_32 directions32_64
theorem cells_cover : CoversDirections cells := directions0_64
theorem params_valid (i : Case) : ValidParams (params i) := by
  fin_cases i
  · exact C450SixthRadialC01.params_valid
  · exact C450SixthRadialC02.params_valid
  · exact C450SixthRadialC03.params_valid
  · exact C450SixthRadialC04.params_valid
  · exact C450SixthRadialC05.params_valid
  · exact C450SixthRadialC06.params_valid
  · exact C450SixthRadialC07.params_valid
  · exact C450SixthRadialC08.params_valid
  · exact C450SixthRadialC09.params_valid
  · exact C450SixthRadialC10.params_valid
  · exact C450SixthRadialC11.params_valid
  · exact C450SixthRadialC12.params_valid
  · exact C450SixthRadialC13.params_valid
  · exact C450SixthRadialC14.params_valid
  · exact C450SixthRadialC15.params_valid
  · exact C450SixthRadialC16.params_valid
  · exact C450SixthRadialC17.params_valid
  · exact C450SixthRadialC18.params_valid
  · exact C450SixthRadialC19.params_valid
  · exact C450SixthRadialC20.params_valid
  · exact C450SixthRadialC21.params_valid
  · exact C450SixthRadialC22.params_valid
  · exact C450SixthRadialC23.params_valid
  · exact C450SixthRadialC24.params_valid
  · exact C450SixthRadialC25.params_valid
  · exact C450SixthRadialC26.params_valid
  · exact C450SixthRadialC27.params_valid
  · exact C450SixthRadialC28.params_valid
  · exact C450SixthRadialC29.params_valid
  · exact C450SixthRadialC30.params_valid
  · exact C450SixthRadialC31.params_valid
  · exact C450SixthRadialC32.params_valid
  · exact C450SixthRadialC33.params_valid
  · exact C450SixthRadialC34.params_valid
  · exact C450SixthRadialC35.params_valid
  · exact C450SixthRadialC36.params_valid
  · exact C450SixthRadialC37.params_valid
  · exact C450SixthRadialC38.params_valid
  · exact C450SixthRadialC39.params_valid
  · exact C450SixthRadialC40.params_valid
  · exact C450SixthRadialC41.params_valid
  · exact C450SixthRadialC42.params_valid
  · exact C450SixthRadialC43.params_valid
  · exact C450SixthRadialC44.params_valid
  · exact C450SixthRadialC45.params_valid
  · exact C450SixthRadialC46.params_valid
  · exact C450SixthRadialC47.params_valid
  · exact C450SixthRadialC48.params_valid
  · exact C450SixthRadialC49.params_valid
  · exact C450SixthRadialC50.params_valid
  · exact C450SixthRadialC51.params_valid
  · exact C450SixthRadialC52.params_valid
  · exact C450SixthRadialC53.params_valid
  · exact C450SixthRadialC54.params_valid
  · exact C450SixthRadialC55.params_valid
  · exact C450SixthRadialC56.params_valid
  · exact C450SixthRadialC57.params_valid
  · exact C450SixthRadialC58.params_valid
  · exact C450SixthRadialC59.params_valid
  · exact C450SixthRadialC60.params_valid
  · exact C450SixthRadialC61.params_valid
  · exact C450SixthRadialC62.params_valid
  · exact C450SixthRadialC63.params_valid
  · exact C450SixthRadialC64.params_valid
theorem params_sum (i : Case) :
    (params i).A+(params i).B = sixth.a0+sixth.b0 := by
  have hs : sixth.a0+sixth.b0 = ((811927:ℚ)/250000) := by
    norm_num [sixth,c450Segs]
  rw [hs]
  fin_cases i
  · exact C450SixthRadialC01.params_sum
  · exact C450SixthRadialC02.params_sum
  · exact C450SixthRadialC03.params_sum
  · exact C450SixthRadialC04.params_sum
  · exact C450SixthRadialC05.params_sum
  · exact C450SixthRadialC06.params_sum
  · exact C450SixthRadialC07.params_sum
  · exact C450SixthRadialC08.params_sum
  · exact C450SixthRadialC09.params_sum
  · exact C450SixthRadialC10.params_sum
  · exact C450SixthRadialC11.params_sum
  · exact C450SixthRadialC12.params_sum
  · exact C450SixthRadialC13.params_sum
  · exact C450SixthRadialC14.params_sum
  · exact C450SixthRadialC15.params_sum
  · exact C450SixthRadialC16.params_sum
  · exact C450SixthRadialC17.params_sum
  · exact C450SixthRadialC18.params_sum
  · exact C450SixthRadialC19.params_sum
  · exact C450SixthRadialC20.params_sum
  · exact C450SixthRadialC21.params_sum
  · exact C450SixthRadialC22.params_sum
  · exact C450SixthRadialC23.params_sum
  · exact C450SixthRadialC24.params_sum
  · exact C450SixthRadialC25.params_sum
  · exact C450SixthRadialC26.params_sum
  · exact C450SixthRadialC27.params_sum
  · exact C450SixthRadialC28.params_sum
  · exact C450SixthRadialC29.params_sum
  · exact C450SixthRadialC30.params_sum
  · exact C450SixthRadialC31.params_sum
  · exact C450SixthRadialC32.params_sum
  · exact C450SixthRadialC33.params_sum
  · exact C450SixthRadialC34.params_sum
  · exact C450SixthRadialC35.params_sum
  · exact C450SixthRadialC36.params_sum
  · exact C450SixthRadialC37.params_sum
  · exact C450SixthRadialC38.params_sum
  · exact C450SixthRadialC39.params_sum
  · exact C450SixthRadialC40.params_sum
  · exact C450SixthRadialC41.params_sum
  · exact C450SixthRadialC42.params_sum
  · exact C450SixthRadialC43.params_sum
  · exact C450SixthRadialC44.params_sum
  · exact C450SixthRadialC45.params_sum
  · exact C450SixthRadialC46.params_sum
  · exact C450SixthRadialC47.params_sum
  · exact C450SixthRadialC48.params_sum
  · exact C450SixthRadialC49.params_sum
  · exact C450SixthRadialC50.params_sum
  · exact C450SixthRadialC51.params_sum
  · exact C450SixthRadialC52.params_sum
  · exact C450SixthRadialC53.params_sum
  · exact C450SixthRadialC54.params_sum
  · exact C450SixthRadialC55.params_sum
  · exact C450SixthRadialC56.params_sum
  · exact C450SixthRadialC57.params_sum
  · exact C450SixthRadialC58.params_sum
  · exact C450SixthRadialC59.params_sum
  · exact C450SixthRadialC60.params_sum
  · exact C450SixthRadialC61.params_sum
  · exact C450SixthRadialC62.params_sum
  · exact C450SixthRadialC63.params_sum
  · exact C450SixthRadialC64.params_sum
theorem model_bound (i : Case) :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50), model (params i) r < (cap (params i):ℝ) := by
  fin_cases i
  · exact C450SixthRadialC01.bound
  · exact C450SixthRadialC02.bound
  · exact C450SixthRadialC03.bound
  · exact C450SixthRadialC04.bound
  · exact C450SixthRadialC05.bound
  · exact C450SixthRadialC06.bound
  · exact C450SixthRadialC07.bound
  · exact C450SixthRadialC08.bound
  · exact C450SixthRadialC09.bound
  · exact C450SixthRadialC10.bound
  · exact C450SixthRadialC11.bound
  · exact C450SixthRadialC12.bound
  · exact C450SixthRadialC13.bound
  · exact C450SixthRadialC14.bound
  · exact C450SixthRadialC15.bound
  · exact C450SixthRadialC16.bound
  · exact C450SixthRadialC17.bound
  · exact C450SixthRadialC18.bound
  · exact C450SixthRadialC19.bound
  · exact C450SixthRadialC20.bound
  · exact C450SixthRadialC21.bound
  · exact C450SixthRadialC22.bound
  · exact C450SixthRadialC23.bound
  · exact C450SixthRadialC24.bound
  · exact C450SixthRadialC25.bound
  · exact C450SixthRadialC26.bound
  · exact C450SixthRadialC27.bound
  · exact C450SixthRadialC28.bound
  · exact C450SixthRadialC29.bound
  · exact C450SixthRadialC30.bound
  · exact C450SixthRadialC31.bound
  · exact C450SixthRadialC32.bound
  · exact C450SixthRadialC33.bound
  · exact C450SixthRadialC34.bound
  · exact C450SixthRadialC35.bound
  · exact C450SixthRadialC36.bound
  · exact C450SixthRadialC37.bound
  · exact C450SixthRadialC38.bound
  · exact C450SixthRadialC39.bound
  · exact C450SixthRadialC40.bound
  · exact C450SixthRadialC41.bound
  · exact C450SixthRadialC42.bound
  · exact C450SixthRadialC43.bound
  · exact C450SixthRadialC44.bound
  · exact C450SixthRadialC45.bound
  · exact C450SixthRadialC46.bound
  · exact C450SixthRadialC47.bound
  · exact C450SixthRadialC48.bound
  · exact C450SixthRadialC49.bound
  · exact C450SixthRadialC50.bound
  · exact C450SixthRadialC51.bound
  · exact C450SixthRadialC52.bound
  · exact C450SixthRadialC53.bound
  · exact C450SixthRadialC54.bound
  · exact C450SixthRadialC55.bound
  · exact C450SixthRadialC56.bound
  · exact C450SixthRadialC57.bound
  · exact C450SixthRadialC58.bound
  · exact C450SixthRadialC59.bound
  · exact C450SixthRadialC60.bound
  · exact C450SixthRadialC61.bound
  · exact C450SixthRadialC62.bound
  · exact C450SixthRadialC63.bound
  · exact C450SixthRadialC64.bound
theorem model_eq0 (r : ℝ) : model (params 0) r =
    CellModel W0 W1 (2/125) (1/50) (cells 0) r := by
  change model C450SixthRadialC01.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨-1,(-31/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC01.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq1 (r : ℝ) : model (params 1) r =
    CellModel W0 W1 (2/125) (1/50) (cells 1) r := by
  change model C450SixthRadialC02.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-31/32),(-15/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC02.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq2 (r : ℝ) : model (params 2) r =
    CellModel W0 W1 (2/125) (1/50) (cells 2) r := by
  change model C450SixthRadialC03.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-15/16),(-29/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC03.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq3 (r : ℝ) : model (params 3) r =
    CellModel W0 W1 (2/125) (1/50) (cells 3) r := by
  change model C450SixthRadialC04.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-29/32),(-7/8)⟩ : Cell) r
  norm_num [model,C450SixthRadialC04.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq4 (r : ℝ) : model (params 4) r =
    CellModel W0 W1 (2/125) (1/50) (cells 4) r := by
  change model C450SixthRadialC05.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-7/8),(-27/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC05.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq5 (r : ℝ) : model (params 5) r =
    CellModel W0 W1 (2/125) (1/50) (cells 5) r := by
  change model C450SixthRadialC06.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-27/32),(-13/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC06.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq6 (r : ℝ) : model (params 6) r =
    CellModel W0 W1 (2/125) (1/50) (cells 6) r := by
  change model C450SixthRadialC07.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-13/16),(-25/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC07.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq7 (r : ℝ) : model (params 7) r =
    CellModel W0 W1 (2/125) (1/50) (cells 7) r := by
  change model C450SixthRadialC08.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-25/32),(-3/4)⟩ : Cell) r
  norm_num [model,C450SixthRadialC08.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq8 (r : ℝ) : model (params 8) r =
    CellModel W0 W1 (2/125) (1/50) (cells 8) r := by
  change model C450SixthRadialC09.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-3/4),(-23/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC09.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq9 (r : ℝ) : model (params 9) r =
    CellModel W0 W1 (2/125) (1/50) (cells 9) r := by
  change model C450SixthRadialC10.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-23/32),(-11/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC10.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq10 (r : ℝ) : model (params 10) r =
    CellModel W0 W1 (2/125) (1/50) (cells 10) r := by
  change model C450SixthRadialC11.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-11/16),(-21/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC11.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq11 (r : ℝ) : model (params 11) r =
    CellModel W0 W1 (2/125) (1/50) (cells 11) r := by
  change model C450SixthRadialC12.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-21/32),(-5/8)⟩ : Cell) r
  norm_num [model,C450SixthRadialC12.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq12 (r : ℝ) : model (params 12) r =
    CellModel W0 W1 (2/125) (1/50) (cells 12) r := by
  change model C450SixthRadialC13.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-5/8),(-19/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC13.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq13 (r : ℝ) : model (params 13) r =
    CellModel W0 W1 (2/125) (1/50) (cells 13) r := by
  change model C450SixthRadialC14.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-19/32),(-9/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC14.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq14 (r : ℝ) : model (params 14) r =
    CellModel W0 W1 (2/125) (1/50) (cells 14) r := by
  change model C450SixthRadialC15.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-9/16),(-17/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC15.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq15 (r : ℝ) : model (params 15) r =
    CellModel W0 W1 (2/125) (1/50) (cells 15) r := by
  change model C450SixthRadialC16.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-17/32),(-1/2)⟩ : Cell) r
  norm_num [model,C450SixthRadialC16.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq16 (r : ℝ) : model (params 16) r =
    CellModel W0 W1 (2/125) (1/50) (cells 16) r := by
  change model C450SixthRadialC17.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-1/2),(-15/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC17.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq17 (r : ℝ) : model (params 17) r =
    CellModel W0 W1 (2/125) (1/50) (cells 17) r := by
  change model C450SixthRadialC18.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-15/32),(-7/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC18.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq18 (r : ℝ) : model (params 18) r =
    CellModel W0 W1 (2/125) (1/50) (cells 18) r := by
  change model C450SixthRadialC19.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-7/16),(-13/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC19.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq19 (r : ℝ) : model (params 19) r =
    CellModel W0 W1 (2/125) (1/50) (cells 19) r := by
  change model C450SixthRadialC20.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-13/32),(-3/8)⟩ : Cell) r
  norm_num [model,C450SixthRadialC20.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq20 (r : ℝ) : model (params 20) r =
    CellModel W0 W1 (2/125) (1/50) (cells 20) r := by
  change model C450SixthRadialC21.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-3/8),(-11/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC21.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq21 (r : ℝ) : model (params 21) r =
    CellModel W0 W1 (2/125) (1/50) (cells 21) r := by
  change model C450SixthRadialC22.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-11/32),(-5/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC22.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq22 (r : ℝ) : model (params 22) r =
    CellModel W0 W1 (2/125) (1/50) (cells 22) r := by
  change model C450SixthRadialC23.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-5/16),(-9/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC23.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq23 (r : ℝ) : model (params 23) r =
    CellModel W0 W1 (2/125) (1/50) (cells 23) r := by
  change model C450SixthRadialC24.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-9/32),(-1/4)⟩ : Cell) r
  norm_num [model,C450SixthRadialC24.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq24 (r : ℝ) : model (params 24) r =
    CellModel W0 W1 (2/125) (1/50) (cells 24) r := by
  change model C450SixthRadialC25.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-1/4),(-7/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC25.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq25 (r : ℝ) : model (params 25) r =
    CellModel W0 W1 (2/125) (1/50) (cells 25) r := by
  change model C450SixthRadialC26.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-7/32),(-3/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC26.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq26 (r : ℝ) : model (params 26) r =
    CellModel W0 W1 (2/125) (1/50) (cells 26) r := by
  change model C450SixthRadialC27.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-3/16),(-5/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC27.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq27 (r : ℝ) : model (params 27) r =
    CellModel W0 W1 (2/125) (1/50) (cells 27) r := by
  change model C450SixthRadialC28.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-5/32),(-1/8)⟩ : Cell) r
  norm_num [model,C450SixthRadialC28.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq28 (r : ℝ) : model (params 28) r =
    CellModel W0 W1 (2/125) (1/50) (cells 28) r := by
  change model C450SixthRadialC29.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-1/8),(-3/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC29.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq29 (r : ℝ) : model (params 29) r =
    CellModel W0 W1 (2/125) (1/50) (cells 29) r := by
  change model C450SixthRadialC30.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-3/32),(-1/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC30.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq30 (r : ℝ) : model (params 30) r =
    CellModel W0 W1 (2/125) (1/50) (cells 30) r := by
  change model C450SixthRadialC31.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-1/16),(-1/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC31.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq31 (r : ℝ) : model (params 31) r =
    CellModel W0 W1 (2/125) (1/50) (cells 31) r := by
  change model C450SixthRadialC32.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(-1/32),0⟩ : Cell) r
  norm_num [model,C450SixthRadialC32.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq32 (r : ℝ) : model (params 32) r =
    CellModel W0 W1 (2/125) (1/50) (cells 32) r := by
  change model C450SixthRadialC33.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨0,(1/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC33.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq33 (r : ℝ) : model (params 33) r =
    CellModel W0 W1 (2/125) (1/50) (cells 33) r := by
  change model C450SixthRadialC34.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(1/32),(1/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC34.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq34 (r : ℝ) : model (params 34) r =
    CellModel W0 W1 (2/125) (1/50) (cells 34) r := by
  change model C450SixthRadialC35.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(1/16),(3/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC35.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq35 (r : ℝ) : model (params 35) r =
    CellModel W0 W1 (2/125) (1/50) (cells 35) r := by
  change model C450SixthRadialC36.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(3/32),(1/8)⟩ : Cell) r
  norm_num [model,C450SixthRadialC36.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq36 (r : ℝ) : model (params 36) r =
    CellModel W0 W1 (2/125) (1/50) (cells 36) r := by
  change model C450SixthRadialC37.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(1/8),(5/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC37.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq37 (r : ℝ) : model (params 37) r =
    CellModel W0 W1 (2/125) (1/50) (cells 37) r := by
  change model C450SixthRadialC38.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(5/32),(3/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC38.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq38 (r : ℝ) : model (params 38) r =
    CellModel W0 W1 (2/125) (1/50) (cells 38) r := by
  change model C450SixthRadialC39.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(3/16),(7/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC39.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq39 (r : ℝ) : model (params 39) r =
    CellModel W0 W1 (2/125) (1/50) (cells 39) r := by
  change model C450SixthRadialC40.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(7/32),(1/4)⟩ : Cell) r
  norm_num [model,C450SixthRadialC40.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq40 (r : ℝ) : model (params 40) r =
    CellModel W0 W1 (2/125) (1/50) (cells 40) r := by
  change model C450SixthRadialC41.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(1/4),(9/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC41.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq41 (r : ℝ) : model (params 41) r =
    CellModel W0 W1 (2/125) (1/50) (cells 41) r := by
  change model C450SixthRadialC42.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(9/32),(5/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC42.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq42 (r : ℝ) : model (params 42) r =
    CellModel W0 W1 (2/125) (1/50) (cells 42) r := by
  change model C450SixthRadialC43.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(5/16),(11/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC43.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq43 (r : ℝ) : model (params 43) r =
    CellModel W0 W1 (2/125) (1/50) (cells 43) r := by
  change model C450SixthRadialC44.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(11/32),(3/8)⟩ : Cell) r
  norm_num [model,C450SixthRadialC44.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq44 (r : ℝ) : model (params 44) r =
    CellModel W0 W1 (2/125) (1/50) (cells 44) r := by
  change model C450SixthRadialC45.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(3/8),(13/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC45.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq45 (r : ℝ) : model (params 45) r =
    CellModel W0 W1 (2/125) (1/50) (cells 45) r := by
  change model C450SixthRadialC46.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(13/32),(7/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC46.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq46 (r : ℝ) : model (params 46) r =
    CellModel W0 W1 (2/125) (1/50) (cells 46) r := by
  change model C450SixthRadialC47.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(7/16),(15/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC47.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq47 (r : ℝ) : model (params 47) r =
    CellModel W0 W1 (2/125) (1/50) (cells 47) r := by
  change model C450SixthRadialC48.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(15/32),(1/2)⟩ : Cell) r
  norm_num [model,C450SixthRadialC48.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq48 (r : ℝ) : model (params 48) r =
    CellModel W0 W1 (2/125) (1/50) (cells 48) r := by
  change model C450SixthRadialC49.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(1/2),(17/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC49.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq49 (r : ℝ) : model (params 49) r =
    CellModel W0 W1 (2/125) (1/50) (cells 49) r := by
  change model C450SixthRadialC50.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(17/32),(9/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC50.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq50 (r : ℝ) : model (params 50) r =
    CellModel W0 W1 (2/125) (1/50) (cells 50) r := by
  change model C450SixthRadialC51.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(9/16),(19/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC51.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq51 (r : ℝ) : model (params 51) r =
    CellModel W0 W1 (2/125) (1/50) (cells 51) r := by
  change model C450SixthRadialC52.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(19/32),(5/8)⟩ : Cell) r
  norm_num [model,C450SixthRadialC52.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq52 (r : ℝ) : model (params 52) r =
    CellModel W0 W1 (2/125) (1/50) (cells 52) r := by
  change model C450SixthRadialC53.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(5/8),(21/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC53.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq53 (r : ℝ) : model (params 53) r =
    CellModel W0 W1 (2/125) (1/50) (cells 53) r := by
  change model C450SixthRadialC54.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(21/32),(11/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC54.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq54 (r : ℝ) : model (params 54) r =
    CellModel W0 W1 (2/125) (1/50) (cells 54) r := by
  change model C450SixthRadialC55.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(11/16),(23/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC55.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq55 (r : ℝ) : model (params 55) r =
    CellModel W0 W1 (2/125) (1/50) (cells 55) r := by
  change model C450SixthRadialC56.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(23/32),(3/4)⟩ : Cell) r
  norm_num [model,C450SixthRadialC56.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq56 (r : ℝ) : model (params 56) r =
    CellModel W0 W1 (2/125) (1/50) (cells 56) r := by
  change model C450SixthRadialC57.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(3/4),(25/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC57.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq57 (r : ℝ) : model (params 57) r =
    CellModel W0 W1 (2/125) (1/50) (cells 57) r := by
  change model C450SixthRadialC58.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(25/32),(13/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC58.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq58 (r : ℝ) : model (params 58) r =
    CellModel W0 W1 (2/125) (1/50) (cells 58) r := by
  change model C450SixthRadialC59.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(13/16),(27/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC59.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq59 (r : ℝ) : model (params 59) r =
    CellModel W0 W1 (2/125) (1/50) (cells 59) r := by
  change model C450SixthRadialC60.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(27/32),(7/8)⟩ : Cell) r
  norm_num [model,C450SixthRadialC60.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq60 (r : ℝ) : model (params 60) r =
    CellModel W0 W1 (2/125) (1/50) (cells 60) r := by
  change model C450SixthRadialC61.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(7/8),(29/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC61.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq61 (r : ℝ) : model (params 61) r =
    CellModel W0 W1 (2/125) (1/50) (cells 61) r := by
  change model C450SixthRadialC62.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(29/32),(15/16)⟩ : Cell) r
  norm_num [model,C450SixthRadialC62.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq62 (r : ℝ) : model (params 62) r =
    CellModel W0 W1 (2/125) (1/50) (cells 62) r := by
  change model C450SixthRadialC63.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(15/16),(31/32)⟩ : Cell) r
  norm_num [model,C450SixthRadialC63.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq63 (r : ℝ) : model (params 63) r =
    CellModel W0 W1 (2/125) (1/50) (cells 63) r := by
  change model C450SixthRadialC64.params r =
    CellModel W0 W1 (2/125) (1/50) (⟨(31/32),1⟩ : Cell) r
  norm_num [model,C450SixthRadialC64.params,CellModel,outerCoefficient,firstCoeff,
    secondCoeff,thirdCoeff,signedFactor,C450OuterGeometry.P2,C450OuterGeometry.P3,
    coefficient,offset,tailSup,W0,W1,sixth,c450Segs,TenSeg.W0,TenSeg.W1]
theorem model_eq (i : Case) (r : ℝ) : model (params i) r =
    CellModel W0 W1 (2/125) (1/50) (cells i) r := by
  fin_cases i
  · exact model_eq0 r
  · exact model_eq1 r
  · exact model_eq2 r
  · exact model_eq3 r
  · exact model_eq4 r
  · exact model_eq5 r
  · exact model_eq6 r
  · exact model_eq7 r
  · exact model_eq8 r
  · exact model_eq9 r
  · exact model_eq10 r
  · exact model_eq11 r
  · exact model_eq12 r
  · exact model_eq13 r
  · exact model_eq14 r
  · exact model_eq15 r
  · exact model_eq16 r
  · exact model_eq17 r
  · exact model_eq18 r
  · exact model_eq19 r
  · exact model_eq20 r
  · exact model_eq21 r
  · exact model_eq22 r
  · exact model_eq23 r
  · exact model_eq24 r
  · exact model_eq25 r
  · exact model_eq26 r
  · exact model_eq27 r
  · exact model_eq28 r
  · exact model_eq29 r
  · exact model_eq30 r
  · exact model_eq31 r
  · exact model_eq32 r
  · exact model_eq33 r
  · exact model_eq34 r
  · exact model_eq35 r
  · exact model_eq36 r
  · exact model_eq37 r
  · exact model_eq38 r
  · exact model_eq39 r
  · exact model_eq40 r
  · exact model_eq41 r
  · exact model_eq42 r
  · exact model_eq43 r
  · exact model_eq44 r
  · exact model_eq45 r
  · exact model_eq46 r
  · exact model_eq47 r
  · exact model_eq48 r
  · exact model_eq49 r
  · exact model_eq50 r
  · exact model_eq51 r
  · exact model_eq52 r
  · exact model_eq53 r
  · exact model_eq54 r
  · exact model_eq55 r
  · exact model_eq56 r
  · exact model_eq57 r
  · exact model_eq58 r
  · exact model_eq59 r
  · exact model_eq60 r
  · exact model_eq61 r
  · exact model_eq62 r
  · exact model_eq63 r
theorem radial_paid (i : Case) :
    C450OuterCellMajorant.CellRadialBound W0 W1 (2/125) (1/50) (cells i) := by
  intro r hr0 hr1
  have hb := model_bound i r ⟨hr0,hr1⟩
  rw [model_eq] at hb
  have hc := cap_lt_actual (params i) (params_valid i)
  have hs : ((params i).A:ℝ)+((params i).B:ℝ) = W0.a0+W1.a0 := by
    have hh := congrArg (fun x : ℚ => (x:ℝ)) (params_sum i)
    simpa only [W0,W1,TenSeg.W0,TenSeg.W1,Rat.cast_add] using hh
  rw [hs] at hc
  exact hb.trans hc
theorem sixth_paid : SegmentNormalized sixth :=
  normalized_of_certificate cells cells_valid cells_cover radial_paid
def remainingSegs : List TenSeg := c450Segs.drop 6
theorem remaining_count : remainingSegs.length = 30 := by decide +kernel
theorem fifth_remaining_split : C450FifthSegment.remainingSegs = sixth :: remainingSegs := rfl
def RemainingSourceObligation : Prop := ∀ s ∈ remainingSegs, SegmentNormalized s
theorem fifth_remaining_of_remaining (hr : RemainingSourceObligation) :
    C450FifthSegment.RemainingSourceObligation := by
  intro s hs
  rw [fifth_remaining_split] at hs
  simp only [List.mem_cons] at hs
  rcases hs with hsixth | hrest
  · rw [hsixth]
    exact sixth_paid
  · exact hr s hrest
theorem source_of_remaining (hr : RemainingSourceObligation) : SourceObligation :=
  C450FifthSegment.source_of_remaining (fifth_remaining_of_remaining hr)
theorem atom_of_remaining (hr : RemainingSourceObligation) : C450Atom :=
  atom_of_source (source_of_remaining hr)
end N11Formalization.C450SixthSegment
#check @N11Formalization.C450SixthSegment.sixth_paid
#check @N11Formalization.C450SixthSegment.atom_of_remaining
#print axioms N11Formalization.C450SixthSegment.cells_cover
#print axioms N11Formalization.C450SixthSegment.params_sum
#print axioms N11Formalization.C450SixthSegment.radial_paid
#print axioms N11Formalization.C450SixthSegment.sixth_paid
#print axioms N11Formalization.C450SixthSegment.atom_of_remaining
