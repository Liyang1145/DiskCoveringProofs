import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC56
open C450RadialPacketKernel
def params : Params := ⟨((261533414789:ℚ)/102400000000),((71031884411:ℚ)/102400000000),((2479457:ℚ)/4000000),((77:ℚ)/5000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((13177:ℚ)/20000),((2065796553:ℚ)/10000000000),((3254603091:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((13177:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((13177:ℚ)/20000),((27131:ℚ)/40000),((492321459:ℚ)/2000000000),((561148027:ℚ)/1000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((13177:ℝ)/20000) ((27131:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((27131:ℚ)/40000),((55039:ℚ)/80000),((131128333:ℚ)/500000000),((5111062099:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((27131:ℝ)/40000) ((55039:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((55039:ℚ)/80000),((6977:ℚ)/10000),((1382669907:ℚ)/5000000000),((2421688203:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((55039:ℝ)/80000) ((6977:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((6977:ℚ)/10000),((112409:ℚ)/160000),((2830884713:ℚ)/10000000000),((1140328999:ℚ)/2500000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((6977:ℝ)/10000) ((112409:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((112409:ℚ)/160000),((56593:ℚ)/80000),((578589171:ℚ)/2000000000),((4414035137:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((112409:ℝ)/160000) ((56593:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((56593:ℚ)/80000),((113963:ℚ)/160000),((2951780383:ℚ)/10000000000),((4262012799:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((56593:ℝ)/80000) ((113963:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((113963:ℚ)/160000),((228703:ℚ)/320000),((2980059127:ℚ)/10000000000),((820944057:ℚ)/2000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((113963:ℝ)/160000) ((228703:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((228703:ℚ)/320000),((5737:ℚ)/8000),((3007613473:ℚ)/10000000000),((4023904787:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((228703:ℝ)/320000) ((5737:ℝ)/8000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((5737:ℚ)/8000),((230257:ℚ)/320000),((23706777:ℚ)/78125000),((1970762363:ℚ)/5000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((5737:ℝ)/8000) ((230257:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((230257:ℚ)/320000),((461291:ℚ)/640000),((1523819471:ℚ)/5000000000),((60273119:ℚ)/156250000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((230257:ℝ)/320000) ((461291:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((461291:ℚ)/640000),((115517:ℚ)/160000),((191290233:ℚ)/625000000),((953699571:ℚ)/2500000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((461291:ℝ)/640000) ((115517:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((115517:ℚ)/160000),((92569:ℚ)/128000),((96046389:ℚ)/312500000),((471457237:ℚ)/1250000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((115517:ℝ)/160000) ((92569:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((92569:ℚ)/128000),((231811:ℚ)/320000),((1543081831:ℚ)/5000000000),((932010621:ℚ)/2500000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((92569:ℝ)/128000) ((231811:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((231811:ℚ)/320000),((464399:ℚ)/640000),((3098683857:ℚ)/10000000000),((460491893:ℚ)/1250000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((231811:ℝ)/320000) ((464399:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((464399:ℚ)/640000),((58147:ℚ)/80000),((3111047457:ℚ)/10000000000),((909829489:ℚ)/2500000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((464399:ℝ)/640000) ((58147:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((58147:ℚ)/80000),((931129:ℚ)/1280000),((3117171271:ℚ)/10000000000),((1797085951:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((58147:ℝ)/80000) ((931129:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((931129:ℚ)/1280000),((465953:ℚ)/640000),((624651363:ℚ)/2000000000),((3571394281:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((931129:ℝ)/1280000) ((465953:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((465953:ℚ)/640000),((932683:ℚ)/1280000),((3129304373:ℚ)/10000000000),((3548476761:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((465953:ℝ)/640000) ((932683:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((932683:ℚ)/1280000),((46673:ℚ)/64000),((3135314227:ℚ)/10000000000),((3525416611:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((932683:ℝ)/1280000) ((46673:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((46673:ℚ)/64000),((934237:ℚ)/1280000),((785321663:ℚ)/2500000000),((54722047:ℚ)/156250000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((46673:ℝ)/64000) ((934237:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((934237:ℚ)/1280000),((467507:ℚ)/640000),((786805481:ℚ)/2500000000),((3478857037:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((934237:ℝ)/1280000) ((467507:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((467507:ℚ)/640000),((935791:ℚ)/1280000),((394140039:ℚ)/1250000000),((3455351687:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((467507:ℝ)/640000) ((935791:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((935791:ℚ)/1280000),((117071:ℚ)/160000),((3158982083:ℚ)/10000000000),((1715845921:ℚ)/5000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((935791:ℝ)/1280000) ((117071:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((117071:ℚ)/160000),((187469:ℚ)/256000),((3164807499:ℚ)/10000000000),((3407874279:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((117071:ℝ)/160000) ((187469:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((187469:ℚ)/256000),((469061:ℚ)/640000),((1585298411:ℚ)/5000000000),((676779133:ℚ)/2000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((187469:ℝ)/256000) ((469061:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((469061:ℚ)/640000),((938899:ℚ)/1280000),((1588175153:ℚ)/5000000000),((3359752547:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((469061:ℝ)/640000) ((938899:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((938899:ℚ)/1280000),((234919:ℚ)/320000),((1591034103:ℚ)/5000000000),((3335441347:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((938899:ℝ)/1280000) ((234919:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((234919:ℚ)/320000),((940453:ℚ)/1280000),((3187750771:ℚ)/10000000000),((82773959:ℚ)/250000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((234919:ℝ)/320000) ((940453:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((940453:ℚ)/1280000),((94123:ℚ)/128000),((3193398249:ℚ)/10000000000),((3286299741:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((940453:ℝ)/1280000) ((94123:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((94123:ℚ)/128000),((942007:ℚ)/1280000),((3199010883:ℚ)/10000000000),((1630730751:ℚ)/5000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((94123:ℝ)/128000) ((942007:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((942007:ℚ)/1280000),((14731:ℚ)/20000),((1602294457:ℚ)/5000000000),((202277469:ℚ)/625000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((942007:ℝ)/1280000) ((14731:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((14731:ℚ)/20000),((943561:ℚ)/1280000),((160506629:ℚ)/500000000),((642245889:ℚ)/2000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((14731:ℝ)/20000) ((943561:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((943561:ℚ)/1280000),((472169:ℚ)/640000),((803910529:ℚ)/2500000000),((1592913429:ℚ)/5000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((943561:ℝ)/1280000) ((472169:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((472169:ℚ)/640000),((236473:ℚ)/320000),((1613279861:ℚ)/5000000000),((1580113547:ℚ)/5000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((472169:ℝ)/640000) ((236473:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((236473:ℚ)/320000),((473723:ℚ)/640000),((3237343557:ℚ)/10000000000),((1554208247:ℚ)/5000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((236473:ℝ)/320000) ((473723:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((473723:ℚ)/640000),((949:ℚ)/1280),((1623997699:ℚ)/5000000000),((1527878249:ℚ)/5000000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((473723:ℝ)/640000) ((949:ℝ)/1280),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((949:ℚ)/1280),((475277:ℚ)/640000),((651703397:ℚ)/2000000000),((3002202369:ℚ)/10000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((949:ℝ)/1280) ((475277:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((475277:ℚ)/640000),((238027:ℚ)/320000),((3268910013:ℚ)/10000000000),((368463167:ℚ)/1250000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((475277:ℝ)/640000) ((238027:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((238027:ℚ)/320000),((59701:ℚ)/80000),((657863397:ℚ)/2000000000),((1446106029:ℚ)/5000000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((238027:ℝ)/320000) ((59701:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((59701:ℚ)/80000),((239581:ℚ)/320000),((827307281:ℚ)/2500000000),((2777996731:ℚ)/10000000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((59701:ℝ)/80000) ((239581:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((239581:ℚ)/320000),((120179:ℚ)/160000),((3328658671:ℚ)/10000000000),((1329505827:ℚ)/5000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((239581:ℝ)/320000) ((120179:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((120179:ℚ)/160000),((30239:ℚ)/40000),((3366116299:ℚ)/10000000000),((506916963:ℚ)/2000000000)⟩
theorem valid42 : Valid params packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((120179:ℝ)/160000) ((30239:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((30239:ℚ)/40000),((12251:ℚ)/16000),((429465421:ℚ)/1250000000),((2265781883:ℚ)/10000000000)⟩
theorem valid43 : Valid params packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((30239:ℝ)/40000) ((12251:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((12251:ℚ)/16000),((3877:ℚ)/5000),((1749379727:ℚ)/5000000000),((1600432327:ℚ)/10000000000)⟩
theorem valid44 : Valid params packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((12251:ℝ)/16000) ((3877:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((27131:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((55039:ℝ)/80000) ((112409:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((27131:ℝ)/40000) ((112409:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((112409:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((56593:ℝ)/80000) ((228703:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((112409:ℝ)/160000) ((228703:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((5737:ℝ)/8000) ((461291:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((228703:ℝ)/320000) ((461291:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((112409:ℝ)/160000) ((461291:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((461291:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((461291:ℝ)/640000) ((92569:ℝ)/128000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((231811:ℝ)/320000) ((58147:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node13_16 :
    ∀ r ∈ Set.Icc ((92569:ℝ)/128000) ((58147:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 node14_16
private theorem node11_16 :
    ∀ r ∈ Set.Icc ((461291:ℝ)/640000) ((58147:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((931129:ℝ)/1280000) ((932683:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((58147:ℝ)/80000) ((932683:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((46673:ℝ)/64000) ((467507:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node19_22 :
    ∀ r ∈ Set.Icc ((932683:ℝ)/1280000) ((467507:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 node20_22
private theorem node16_22 :
    ∀ r ∈ Set.Icc ((58147:ℝ)/80000) ((467507:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_19 node19_22
private theorem node11_22 :
    ∀ r ∈ Set.Icc ((461291:ℝ)/640000) ((467507:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_16 node16_22
private theorem node0_22 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((467507:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((467507:ℝ)/640000) ((117071:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((187469:ℝ)/256000) ((938899:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node24_27 :
    ∀ r ∈ Set.Icc ((117071:ℝ)/160000) ((938899:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 node25_27
private theorem node22_27 :
    ∀ r ∈ Set.Icc ((467507:ℝ)/640000) ((938899:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((234919:ℝ)/320000) ((94123:ℝ)/128000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((938899:ℝ)/1280000) ((94123:ℝ)/128000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((942007:ℝ)/1280000) ((943561:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((94123:ℝ)/128000) ((943561:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node27_33 :
    ∀ r ∈ Set.Icc ((938899:ℝ)/1280000) ((943561:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node27_30 node30_33
private theorem node22_33 :
    ∀ r ∈ Set.Icc ((467507:ℝ)/640000) ((943561:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_27 node27_33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((472169:ℝ)/640000) ((473723:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 leaf35
private theorem node33_36 :
    ∀ r ∈ Set.Icc ((943561:ℝ)/1280000) ((473723:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 node34_36
private theorem node37_39 :
    ∀ r ∈ Set.Icc ((949:ℝ)/1280) ((238027:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 leaf38
private theorem node36_39 :
    ∀ r ∈ Set.Icc ((473723:ℝ)/640000) ((238027:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 node37_39
private theorem node33_39 :
    ∀ r ∈ Set.Icc ((943561:ℝ)/1280000) ((238027:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_36 node36_39
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((59701:ℝ)/80000) ((120179:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 leaf41
private theorem node39_42 :
    ∀ r ∈ Set.Icc ((238027:ℝ)/320000) ((120179:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 node40_42
private theorem node43_45 :
    ∀ r ∈ Set.Icc ((30239:ℝ)/40000) ((3877:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf43 leaf44
private theorem node42_45 :
    ∀ r ∈ Set.Icc ((120179:ℝ)/160000) ((3877:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf42 node43_45
private theorem node39_45 :
    ∀ r ∈ Set.Icc ((238027:ℝ)/320000) ((3877:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node39_42 node42_45
private theorem node33_45 :
    ∀ r ∈ Set.Icc ((943561:ℝ)/1280000) ((3877:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_39 node39_45
private theorem node22_45 :
    ∀ r ∈ Set.Icc ((467507:ℝ)/640000) ((3877:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_33 node33_45
private theorem node0_45 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3877:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_22 node22_45
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_45
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC56
#check @N11Formalization.C450SixthRadialC56.bound
#print axioms N11Formalization.C450SixthRadialC56.params_valid
#print axioms N11Formalization.C450SixthRadialC56.params_sum
#print axioms N11Formalization.C450SixthRadialC56.bound
