import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC37
open C450RadialPacketKernel
def params : Params := ⟨((1026587137:ℚ)/400000000),((272496063:ℚ)/400000000),((690017:ℚ)/1000000),((141:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((104941:ℚ)/160000),((498408617:ℚ)/2500000000),((6246782789:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((104941:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((104941:ℚ)/160000),((215623:ℚ)/320000),((2380619657:ℚ)/10000000000),((1346812601:ℚ)/2500000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((104941:ℝ)/160000) ((215623:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((215623:ℚ)/320000),((436987:ℚ)/640000),((634741361:ℚ)/2500000000),((4907713641:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((215623:ℝ)/320000) ((436987:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((436987:ℚ)/640000),((55341:ℚ)/80000),((2680031799:ℚ)/10000000000),((2325545749:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((436987:ℝ)/640000) ((55341:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55341:ℚ)/80000),((891197:ℚ)/1280000),((5361363:ℚ)/19531250),((1095153683:ℚ)/2500000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55341:ℝ)/80000) ((891197:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((891197:ℚ)/1280000),((448469:ℚ)/640000),((701674297:ℚ)/2500000000),((4239353857:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((891197:ℝ)/1280000) ((448469:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((448469:ℚ)/640000),((902679:ℚ)/1280000),((2865314723:ℚ)/10000000000),((2046762871:ℚ)/5000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((448469:ℝ)/640000) ((902679:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((902679:ℚ)/1280000),((1811099:ℚ)/2560000),((2893543361:ℚ)/10000000000),((3942622069:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((902679:ℝ)/1280000) ((1811099:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1811099:ℚ)/2560000),((45421:ℚ)/64000),((730271217:ℚ)/2500000000),((3865081413:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1811099:ℝ)/2560000) ((45421:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45421:ℚ)/64000),((1822581:ℚ)/2560000),((2947962123:ℚ)/10000000000),((3786034377:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45421:ℝ)/64000) ((1822581:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1822581:ℚ)/2560000),((914161:ℚ)/1280000),((2974196681:ℚ)/10000000000),((3705384351:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1822581:ℝ)/2560000) ((914161:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((914161:ℚ)/1280000),((1834063:ℚ)/2560000),((749952221:ℚ)/2500000000),((3623024081:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((914161:ℝ)/1280000) ((1834063:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((1834063:ℚ)/2560000),((3673867:ℚ)/5120000),((60247753:ℚ)/200000000),((884708487:ℚ)/2500000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((1834063:ℝ)/2560000) ((3673867:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((3673867:ℚ)/5120000),((459951:ℚ)/640000),((3024817951:ℚ)/10000000000),((3496011417:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((3673867:ℝ)/5120000) ((459951:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((459951:ℚ)/640000),((3685349:ℚ)/5120000),((303710203:ℚ)/1000000000),((1726339941:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((459951:ℝ)/640000) ((3685349:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((3685349:ℚ)/5120000),((369109:ℚ)/512000),((3049242069:ℚ)/10000000000),((681763981:ℚ)/2000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((3685349:ℝ)/5120000) ((369109:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((369109:ℚ)/512000),((3696831:ℚ)/5120000),((23915939:ℚ)/78125000),((3364410791:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((369109:ℝ)/512000) ((3696831:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((3696831:ℚ)/5120000),((925643:ℚ)/1280000),((768274617:ℚ)/2500000000),((3319430473:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((3696831:ℝ)/5120000) ((925643:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((925643:ℚ)/1280000),((3708313:ℚ)/5120000),((3084818913:ℚ)/10000000000),((3273855379:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((925643:ℝ)/1280000) ((3708313:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((3708313:ℚ)/5120000),((1857027:ℚ)/2560000),((774100873:ℚ)/2500000000),((1613830143:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((3708313:ℝ)/5120000) ((1857027:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1857027:ℚ)/2560000),((116423:ℚ)/160000),((1559586331:ℚ)/5000000000),((397602269:ℚ)/1250000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1857027:ℝ)/2560000) ((116423:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((116423:ℚ)/160000),((1868509:ℚ)/2560000),((1570710369:ℚ)/5000000000),((3085074347:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((116423:ℝ)/160000) ((1868509:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((1868509:ℚ)/2560000),((7497:ℚ)/10240),((3163161763:ℚ)/10000000000),((2986363409:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((1868509:ℝ)/2560000) ((7497:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((7497:ℚ)/10240),((1879991:ℚ)/2560000),((3184409123:ℚ)/10000000000),((2884380473:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((7497:ℝ)/10240) ((1879991:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((1879991:ℚ)/2560000),((471433:ℚ)/640000),((1602587789:ℚ)/5000000000),((347345631:ℚ)/1250000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((1879991:ℝ)/2560000) ((471433:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((471433:ℚ)/640000),((948607:ℚ)/1280000),((1622656983:ℚ)/5000000000),((1334542843:ℚ)/5000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((471433:ℝ)/640000) ((948607:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((948607:ℚ)/1280000),((238587:ℚ)/320000),((41045851:ℚ)/125000000),((1217659153:ℚ)/5000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((948607:ℝ)/1280000) ((238587:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((238587:ℚ)/320000),((96583:ℚ)/128000),((3355350651:ℚ)/10000000000),((1088566701:ℚ)/5000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((238587:ℝ)/320000) ((96583:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((96583:ℚ)/128000),((30541:ℚ)/40000),((3420814251:ℚ)/10000000000),((1537942443:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((96583:ℝ)/128000) ((30541:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((104941:ℝ)/160000) ((436987:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((436987:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((436987:ℝ)/640000) ((891197:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((891197:ℝ)/1280000) ((902679:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((436987:ℝ)/640000) ((902679:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((902679:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((1811099:ℝ)/2560000) ((1822581:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((902679:ℝ)/1280000) ((1822581:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((1822581:ℝ)/2560000) ((1834063:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((1834063:ℝ)/2560000) ((459951:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node10_14 :
    ∀ r ∈ Set.Icc ((1822581:ℝ)/2560000) ((459951:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_14
private theorem node7_14 :
    ∀ r ∈ Set.Icc ((902679:ℝ)/1280000) ((459951:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_10 node10_14
private theorem node0_14 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((459951:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_14
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((3685349:ℝ)/5120000) ((3696831:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((459951:ℝ)/640000) ((3696831:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((3696831:ℝ)/5120000) ((3708313:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((3708313:ℝ)/5120000) ((116423:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node17_21 :
    ∀ r ∈ Set.Icc ((3696831:ℝ)/5120000) ((116423:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_19 node19_21
private theorem node14_21 :
    ∀ r ∈ Set.Icc ((459951:ℝ)/640000) ((116423:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_17 node17_21
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((116423:ℝ)/160000) ((7497:ℝ)/10240),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((7497:ℝ)/10240) ((471433:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node21_25 :
    ∀ r ∈ Set.Icc ((116423:ℝ)/160000) ((471433:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_23 node23_25
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((471433:ℝ)/640000) ((238587:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((238587:ℝ)/320000) ((30541:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node25_29 :
    ∀ r ∈ Set.Icc ((471433:ℝ)/640000) ((30541:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node25_27 node27_29
private theorem node21_29 :
    ∀ r ∈ Set.Icc ((116423:ℝ)/160000) ((30541:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_25 node25_29
private theorem node14_29 :
    ∀ r ∈ Set.Icc ((459951:ℝ)/640000) ((30541:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_21 node21_29
private theorem node0_29 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((30541:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_14 node14_29
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_29
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC37
#check @N11Formalization.C450SixthRadialC37.bound
#print axioms N11Formalization.C450SixthRadialC37.params_valid
#print axioms N11Formalization.C450SixthRadialC37.params_sum
#print axioms N11Formalization.C450SixthRadialC37.bound
