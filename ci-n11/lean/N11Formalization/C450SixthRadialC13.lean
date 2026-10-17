import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC13
open C450RadialPacketKernel
def params : Params := ⟨((20591957:ℚ)/8000000),((5389707:ℚ)/8000000),((3188369:ℚ)/4000000),((-91:ℚ)/10000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((26109:ℚ)/40000),((956216137:ℚ)/5000000000),((2978435679:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((26109:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((26109:ℚ)/40000),((53527:ℚ)/80000),((2288760837:ℚ)/10000000000),((513923629:ℚ)/1000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((26109:ℝ)/40000) ((53527:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((53527:ℚ)/80000),((108363:ℚ)/160000),((244373521:ℚ)/1000000000),((187306647:ℚ)/400000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((53527:ℝ)/80000) ((108363:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((108363:ℚ)/160000),((13709:ℚ)/20000),((2582415603:ℚ)/10000000000),((4438227969:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((108363:ℝ)/160000) ((13709:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((13709:ℚ)/20000),((220653:ℚ)/320000),((529305741:ℚ)/2000000000),((4180518667:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((13709:ℝ)/20000) ((220653:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((220653:ℚ)/320000),((110981:ℚ)/160000),((84610231:ℚ)/312500000),((202294857:ℚ)/500000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((220653:ℝ)/320000) ((110981:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((110981:ℚ)/160000),((445233:ℚ)/640000),((2736932409:ℚ)/10000000000),((3906903367:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((110981:ℝ)/160000) ((445233:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((445233:ℚ)/640000),((223271:ℚ)/320000),((1382821649:ℚ)/5000000000),((3835618561:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((445233:ℝ)/640000) ((223271:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((223271:ℚ)/320000),((447851:ℚ)/640000),((2793684537:ℚ)/10000000000),((3763051667:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((223271:ℝ)/320000) ((447851:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((447851:ℚ)/640000),((11229:ℚ)/16000),((564215823:ℚ)/2000000000),((3689126873:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((447851:ℝ)/640000) ((11229:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((11229:ℚ)/16000),((899629:ℚ)/1280000),((354317589:ℚ)/1250000000),((3613760689:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((11229:ℝ)/16000) ((899629:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((899629:ℚ)/1280000),((450469:ℚ)/640000),((56956973:ℚ)/200000000),((3575508611:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((899629:ℝ)/1280000) ((450469:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((450469:ℚ)/640000),((902247:ℚ)/1280000),((2861005437:ℚ)/10000000000),((1768430407:ℚ)/5000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((450469:ℝ)/640000) ((902247:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((902247:ℚ)/1280000),((225889:ℚ)/320000),((2874013509:ℚ)/10000000000),((3497804159:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((902247:ℝ)/1280000) ((225889:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((225889:ℚ)/320000),((180973:ℚ)/256000),((90214851:ℚ)/312500000),((1729162387:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((225889:ℝ)/320000) ((180973:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((180973:ℚ)/256000),((453087:ℚ)/640000),((1449796453:ℚ)/5000000000),((3418407993:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((180973:ℝ)/256000) ((453087:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((453087:ℚ)/640000),((907483:ℚ)/1280000),((2912168769:ℚ)/10000000000),((337803829:ℚ)/1000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((453087:ℝ)/640000) ((907483:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((907483:ℚ)/1280000),((113599:ℚ)/160000),((731151249:ℚ)/2500000000),((667439841:ℚ)/2000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((907483:ℝ)/1280000) ((113599:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((113599:ℚ)/160000),((910101:ℚ)/1280000),((367112963:ℚ)/1250000000),((3295873271:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((113599:ℝ)/160000) ((910101:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((910101:ℚ)/1280000),((91141:ℚ)/128000),((2949066953:ℚ)/10000000000),((813510479:ℚ)/2500000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((910101:ℝ)/1280000) ((91141:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((91141:ℚ)/128000),((912719:ℚ)/1280000),((11844387:ℚ)/40000000),((321168537:ℚ)/1000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((91141:ℝ)/128000) ((912719:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((912719:ℚ)/1280000),((228507:ℚ)/320000),((2972995047:ℚ)/10000000000),((3168782551:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((912719:ℝ)/1280000) ((228507:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((228507:ℚ)/320000),((915337:ℚ)/1280000),((2984763749:ℚ)/10000000000),((156265547:ℚ)/500000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((228507:ℝ)/320000) ((915337:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((915337:ℚ)/1280000),((458323:ℚ)/640000),((299640471:ℚ)/1000000000),((3081246441:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((915337:ℝ)/1280000) ((458323:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((458323:ℚ)/640000),((28727:ℚ)/40000),((603862119:ℚ)/2000000000),((3036563219:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((458323:ℝ)/640000) ((28727:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((28727:ℚ)/40000),((460941:ℚ)/640000),((3041726633:ℚ)/10000000000),((736306871:ℚ)/2500000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((28727:ℝ)/40000) ((460941:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((460941:ℚ)/640000),((1849:ℚ)/2560),((3063666083:ℚ)/10000000000),((2851054827:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((460941:ℝ)/640000) ((1849:ℝ)/2560),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((1849:ℚ)/2560),((116217:ℚ)/160000),((97067661:ℚ)/312500000),((1376877007:ℚ)/5000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((1849:ℝ)/2560) ((116217:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((116217:ℚ)/160000),((233743:ℚ)/320000),((786725511:ℚ)/2500000000),((2548322667:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((116217:ℝ)/160000) ((233743:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((233743:ℚ)/320000),((58763:ℚ)/80000),((3185962771:ℚ)/10000000000),((1162617517:ℚ)/5000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((233743:ℝ)/320000) ((58763:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((58763:ℚ)/80000),((23767:ℚ)/32000),((3259364429:ℚ)/10000000000),((1039406223:ℚ)/5000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((58763:ℝ)/80000) ((23767:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((23767:ℚ)/32000),((7509:ℚ)/10000),((831731933:ℚ)/2500000000),((734308239:ℚ)/5000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((23767:ℝ)/32000) ((7509:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((53527:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((53527:ℝ)/80000) ((13709:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((13709:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((13709:ℝ)/20000) ((110981:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((110981:ℝ)/160000) ((223271:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((13709:ℝ)/20000) ((223271:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((223271:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((223271:ℝ)/320000) ((11229:ℝ)/16000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((11229:ℝ)/16000) ((450469:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((223271:ℝ)/320000) ((450469:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((450469:ℝ)/640000) ((225889:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((225889:ℝ)/320000) ((453087:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((450469:ℝ)/640000) ((453087:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((223271:ℝ)/320000) ((453087:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((453087:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((453087:ℝ)/640000) ((113599:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((113599:ℝ)/160000) ((91141:ℝ)/128000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((453087:ℝ)/640000) ((91141:ℝ)/128000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((91141:ℝ)/128000) ((228507:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((228507:ℝ)/320000) ((458323:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((91141:ℝ)/128000) ((458323:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((453087:ℝ)/640000) ((458323:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((458323:ℝ)/640000) ((460941:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((460941:ℝ)/640000) ((116217:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((458323:ℝ)/640000) ((116217:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((116217:ℝ)/160000) ((58763:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((58763:ℝ)/80000) ((7509:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((116217:ℝ)/160000) ((7509:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((458323:ℝ)/640000) ((7509:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((453087:ℝ)/640000) ((7509:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7509:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_16 node16_32
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_32
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC13
#check @N11Formalization.C450SixthRadialC13.bound
#print axioms N11Formalization.C450SixthRadialC13.params_valid
#print axioms N11Formalization.C450SixthRadialC13.params_sum
#print axioms N11Formalization.C450SixthRadialC13.bound
