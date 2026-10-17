import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC45
open C450RadialPacketKernel
def params : Params := ⟨((256257209:ℚ)/100000000),((68513591:ℚ)/100000000),((660479:ℚ)/1000000),((341:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((105141:ℚ)/160000),((2024488723:ℚ)/10000000000),((1589603263:ℚ)/2500000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((105141:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((105141:ℚ)/160000),((216223:ℚ)/320000),((603831061:ℚ)/2500000000),((5482665821:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((105141:ℝ)/160000) ((216223:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((216223:ℚ)/320000),((438387:ℚ)/640000),((643708257:ℚ)/2500000000),((31214109:ℚ)/62500000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((216223:ℝ)/320000) ((438387:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((438387:ℚ)/640000),((55541:ℚ)/80000),((2716678331:ℚ)/10000000000),((2366466593:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((438387:ℝ)/640000) ((55541:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55541:ℚ)/80000),((894597:ℚ)/1280000),((556385823:ℚ)/2000000000),((2228766051:ℚ)/5000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55541:ℝ)/80000) ((894597:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((894597:ℚ)/1280000),((450269:ℚ)/640000),((568759641:ℚ)/2000000000),((4313711629:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((894597:ℝ)/1280000) ((450269:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((450269:ℚ)/640000),((906479:ℚ)/1280000),((1451267851:ℚ)/5000000000),((520656191:ℚ)/1250000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((450269:ℝ)/640000) ((906479:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((906479:ℚ)/1280000),((1818899:ℚ)/2560000),((732699899:ℚ)/2500000000),((4011628799:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((906479:ℝ)/1280000) ((1818899:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1818899:ℚ)/2560000),((45621:ℚ)/64000),((1479180289:ℚ)/5000000000),((1966347647:ℚ)/5000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1818899:ℝ)/2560000) ((45621:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45621:ℚ)/64000),((1830781:ℚ)/2560000),((2985242017:ℚ)/10000000000),((1926115291:ℚ)/5000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45621:ℝ)/64000) ((1830781:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1830781:ℚ)/2560000),((3667503:ℚ)/5120000),((2998434839:ℚ)/10000000000),((3770136403:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1830781:ℝ)/2560000) ((3667503:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((3667503:ℚ)/5120000),((918361:ℚ)/1280000),((3011465933:ℚ)/10000000000),((23302779:ℚ)/62500000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((3667503:ℝ)/5120000) ((918361:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((918361:ℚ)/1280000),((735877:ℚ)/1024000),((151216893:ℚ)/500000000),((1843151833:ℚ)/5000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((918361:ℝ)/1280000) ((735877:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((735877:ℚ)/1024000),((1842663:ℚ)/2560000),((1518526553:ℚ)/5000000000),((728739573:ℚ)/2000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((735877:ℝ)/1024000) ((1842663:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1842663:ℚ)/2560000),((3691267:ℚ)/5120000),((3049614091:ℚ)/10000000000),((3600610707:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1842663:ℝ)/2560000) ((3691267:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((3691267:ℚ)/5120000),((462151:ℚ)/640000),((3062023169:ℚ)/10000000000),((111157021:ℚ)/312500000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((3691267:ℝ)/5120000) ((462151:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((462151:ℚ)/640000),((3703149:ℚ)/5120000),((307428263:ℚ)/1000000000),((87823029:ℚ)/250000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((462151:ℝ)/640000) ((3703149:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((3703149:ℚ)/5120000),((370909:ℚ)/512000),((3086394703:ℚ)/10000000000),((1734140201:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((3703149:ℝ)/5120000) ((370909:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((370909:ℚ)/512000),((3715031:ℚ)/5120000),((3098361559:ℚ)/10000000000),((855770337:ℚ)/2500000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((370909:ℝ)/512000) ((3715031:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((3715031:ℚ)/5120000),((930243:ℚ)/1280000),((3110185311:ℚ)/10000000000),((3377301553:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((3715031:ℝ)/5120000) ((930243:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((930243:ℚ)/1280000),((3726913:ℚ)/5120000),((156093401:ℚ)/500000000),((3330917041:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((930243:ℝ)/1280000) ((3726913:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((3726913:ℚ)/5120000),((1866427:ℚ)/2560000),((783352923:ℚ)/2500000000),((820975539:ℚ)/2500000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((3726913:ℝ)/5120000) ((1866427:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((1866427:ℚ)/2560000),((747759:ℚ)/1024000),((628963657:ℚ)/2000000000),((647245879:ℚ)/2000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((1866427:ℝ)/2560000) ((747759:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((747759:ℚ)/1024000),((117023:ℚ)/160000),((1578044853:ℚ)/5000000000),((318786921:ℚ)/1000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((747759:ℝ)/1024000) ((117023:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((117023:ℚ)/160000),((3750677:ℚ)/5120000),((395903477:ℚ)/1250000000),((627757959:ℚ)/2000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((117023:ℝ)/160000) ((3750677:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((3750677:ℚ)/5120000),((1878309:ℚ)/2560000),((3178234431:ℚ)/10000000000),((617791367:ℚ)/2000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((3750677:ℝ)/5120000) ((1878309:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((1878309:ℚ)/2560000),((3762559:ℚ)/5120000),((1594555661:ℚ)/5000000000),((151916661:ℚ)/500000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((1878309:ℝ)/2560000) ((3762559:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((3762559:ℚ)/5120000),((7537:ℚ)/10240),((159993011:ℚ)/500000000),((1493439357:ℚ)/5000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((3762559:ℝ)/5120000) ((7537:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((7537:ℚ)/10240),((1890191:ℚ)/2560000),((3220980747:ℚ)/10000000000),((366818697:ℚ)/1250000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((7537:ℝ)/10240) ((1890191:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((1890191:ℚ)/2560000),((474033:ℚ)/640000),((1620804527:ℚ)/5000000000),((1413536093:ℚ)/5000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((1890191:ℝ)/2560000) ((474033:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((474033:ℚ)/640000),((954007:ℚ)/1280000),((410179781:ℚ)/1250000000),((1357731099:ℚ)/5000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((474033:ℝ)/640000) ((954007:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((954007:ℚ)/1280000),((239987:ℚ)/320000),((829860237:ℚ)/2500000000),((309698689:ℚ)/1250000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((954007:ℝ)/1280000) ((239987:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((239987:ℚ)/320000),((97183:ℚ)/128000),((3390301177:ℚ)/10000000000),((2214884433:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((239987:ℝ)/320000) ((97183:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((97183:ℚ)/128000),((30741:ℚ)/40000),((3454793587:ℚ)/10000000000),((24446183:ℚ)/156250000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((97183:ℝ)/128000) ((30741:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((216223:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((216223:ℝ)/320000) ((55541:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((55541:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((55541:ℝ)/80000) ((450269:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((450269:ℝ)/640000) ((1818899:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((55541:ℝ)/80000) ((1818899:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1818899:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((1818899:ℝ)/2560000) ((1830781:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((1830781:ℝ)/2560000) ((918361:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((1818899:ℝ)/2560000) ((918361:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((918361:ℝ)/1280000) ((1842663:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((3691267:ℝ)/5120000) ((3703149:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((1842663:ℝ)/2560000) ((3703149:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node12_17 :
    ∀ r ∈ Set.Icc ((918361:ℝ)/1280000) ((3703149:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_14 node14_17
private theorem node8_17 :
    ∀ r ∈ Set.Icc ((1818899:ℝ)/2560000) ((3703149:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_12 node12_17
private theorem node0_17 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3703149:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_8 node8_17
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((3703149:ℝ)/5120000) ((3715031:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((3715031:ℝ)/5120000) ((3726913:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node17_21 :
    ∀ r ∈ Set.Icc ((3703149:ℝ)/5120000) ((3726913:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_19 node19_21
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((3726913:ℝ)/5120000) ((747759:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((747759:ℝ)/1024000) ((3750677:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node21_25 :
    ∀ r ∈ Set.Icc ((3726913:ℝ)/5120000) ((3750677:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_23 node23_25
private theorem node17_25 :
    ∀ r ∈ Set.Icc ((3703149:ℝ)/5120000) ((3750677:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_21 node21_25
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((3750677:ℝ)/5120000) ((3762559:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((3762559:ℝ)/5120000) ((1890191:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node25_29 :
    ∀ r ∈ Set.Icc ((3750677:ℝ)/5120000) ((1890191:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node25_27 node27_29
private theorem node29_31 :
    ∀ r ∈ Set.Icc ((1890191:ℝ)/2560000) ((954007:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf29 leaf30
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((239987:ℝ)/320000) ((30741:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 leaf33
private theorem node31_34 :
    ∀ r ∈ Set.Icc ((954007:ℝ)/1280000) ((30741:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 node32_34
private theorem node29_34 :
    ∀ r ∈ Set.Icc ((1890191:ℝ)/2560000) ((30741:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node29_31 node31_34
private theorem node25_34 :
    ∀ r ∈ Set.Icc ((3750677:ℝ)/5120000) ((30741:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node25_29 node29_34
private theorem node17_34 :
    ∀ r ∈ Set.Icc ((3703149:ℝ)/5120000) ((30741:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_25 node25_34
private theorem node0_34 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((30741:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_17 node17_34
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_34
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC45
#check @N11Formalization.C450SixthRadialC45.bound
#print axioms N11Formalization.C450SixthRadialC45.params_valid
#print axioms N11Formalization.C450SixthRadialC45.params_sum
#print axioms N11Formalization.C450SixthRadialC45.bound
