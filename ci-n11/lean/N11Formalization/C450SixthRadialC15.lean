import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC15
open C450RadialPacketKernel
def params : Params := ⟨((41174081:ℚ)/16000000),((10789247:ℚ)/16000000),((6302893:ℚ)/8000000),((-81:ℚ)/10000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((26119:ℚ)/40000),((1919046139:ℚ)/10000000000),((2990141031:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((26119:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((26119:ℚ)/40000),((53557:ℚ)/80000),((459254031:ℚ)/2000000000),((2579637457:ℚ)/5000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((26119:ℝ)/40000) ((53557:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((53557:ℚ)/80000),((108433:ℚ)/160000),((2451535457:ℚ)/10000000000),((4700854073:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((53557:ℝ)/80000) ((108433:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((108433:ℚ)/160000),((13719:ℚ)/20000),((518085571:ℚ)/2000000000),((4455433459:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((108433:ℝ)/160000) ((13719:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((13719:ℚ)/20000),((220823:ℚ)/320000),((2654621333:ℚ)/10000000000),((1049173573:ℚ)/2500000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((13719:ℝ)/20000) ((220823:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((220823:ℚ)/320000),((111071:ℚ)/160000),((1357842499:ℚ)/5000000000),((2030768529:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((220823:ℝ)/320000) ((111071:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((111071:ℚ)/160000),((445603:ℚ)/640000),((686279267:ℚ)/2500000000),((3921991737:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((111071:ℝ)/160000) ((445603:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((445603:ℚ)/640000),((223461:ℚ)/320000),((693462887:ℚ)/2500000000),((3850424657:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((445603:ℝ)/640000) ((223461:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((223461:ℚ)/320000),((448241:ℚ)/640000),((2801913033:ℚ)/10000000000),((3689034:ℚ)/9765625)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((223461:ℝ)/320000) ((448241:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((448241:ℚ)/640000),((11239:ℚ)/16000),((353665577:ℚ)/1250000000),((740670823:ℚ)/2000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((448241:ℝ)/640000) ((11239:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((11239:ℚ)/16000),((900439:ℚ)/1280000),((710698383:ℚ)/2500000000),((3627690749:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((11239:ℝ)/16000) ((900439:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((900439:ℚ)/1280000),((450879:ℚ)/640000),((2856108017:ℚ)/10000000000),((1794643997:ℚ)/5000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((900439:ℝ)/1280000) ((450879:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((450879:ℚ)/640000),((903077:ℚ)/1280000),((2869270591:ℚ)/10000000000),((887622017:ℚ)/2500000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((450879:ℝ)/640000) ((903077:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((903077:ℚ)/1280000),((226099:ℚ)/320000),((2882283699:ℚ)/10000000000),((1755638891:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((903077:ℝ)/1280000) ((226099:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((226099:ℚ)/320000),((181143:ℚ)/256000),((72378743:ℚ)/250000000),((867910803:ℚ)/2500000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((226099:ℝ)/320000) ((181143:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((181143:ℚ)/256000),((453517:ℚ)/640000),((1453935483:ℚ)/5000000000),((686313927:ℚ)/2000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((181143:ℝ)/256000) ((453517:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((453517:ℚ)/640000),((908353:ℚ)/1280000),((2920449683:ℚ)/10000000000),((3391041467:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((453517:ℝ)/640000) ((908353:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((908353:ℚ)/1280000),((113709:ℚ)/160000),((2932888057:ℚ)/10000000000),((837510547:ℚ)/2500000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((908353:ℝ)/1280000) ((113709:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((113709:ℚ)/160000),((910991:ℚ)/1280000),((589037643:ℚ)/2000000000),((3308554261:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((113709:ℝ)/160000) ((910991:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((910991:ℚ)/1280000),((91231:ℚ)/128000),((739338057:ℚ)/2500000000),((3266559047:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((910991:ℝ)/1280000) ((91231:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((91231:ℚ)/128000),((913629:ℚ)/1280000),((2969382111:ℚ)/10000000000),((3224036701:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((91231:ℝ)/128000) ((913629:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((913629:ℚ)/1280000),((228737:ℚ)/320000),((2981279827:ℚ)/10000000000),((3180966059:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((913629:ℝ)/1280000) ((228737:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((228737:ℚ)/320000),((916267:ℚ)/1280000),((374130911:ℚ)/1250000000),((3137324519:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((228737:ℝ)/320000) ((916267:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((916267:ℚ)/1280000),((458793:ℚ)/640000),((3004686357:ℚ)/10000000000),((3093087891:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((916267:ℝ)/1280000) ((458793:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((458793:ℚ)/640000),((28757:ℚ)/40000),((3027586543:ℚ)/10000000000),((609646049:ℚ)/2000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((458793:ℝ)/640000) ((28757:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((28757:ℚ)/40000),((461431:ℚ)/640000),((3049994381:ℚ)/10000000000),((1478269173:ℚ)/5000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((28757:ℝ)/40000) ((461431:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((461431:ℚ)/640000),((1851:ℚ)/2560),((3071923193:ℚ)/10000000000),((2861998971:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((461431:ℝ)/640000) ((1851:ℝ)/2560),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((1851:ℚ)/2560),((116347:ℚ)/160000),((3114393913:ℚ)/10000000000),((138215989:ℚ)/500000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((1851:ℝ)/2560) ((116347:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((116347:ℚ)/160000),((234013:ℚ)/320000),((631018679:ℚ)/2000000000),((102323649:ℚ)/400000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((116347:ℝ)/160000) ((234013:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((234013:ℚ)/320000),((58833:ℚ)/80000),((99815877:ℚ)/312500000),((2334140249:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((234013:ℝ)/320000) ((58833:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((58833:ℚ)/80000),((23797:ℚ)/32000),((65347863:ℚ)/200000000),((521691657:ℚ)/2500000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((58833:ℝ)/80000) ((23797:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((23797:ℚ)/32000),((7519:ℚ)/10000),((3334809457:ℚ)/10000000000),((1474225637:ℚ)/10000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((23797:ℝ)/32000) ((7519:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((53557:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((53557:ℝ)/80000) ((13719:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((13719:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((13719:ℝ)/20000) ((111071:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((111071:ℝ)/160000) ((223461:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((13719:ℝ)/20000) ((223461:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((223461:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((223461:ℝ)/320000) ((11239:ℝ)/16000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((11239:ℝ)/16000) ((450879:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((223461:ℝ)/320000) ((450879:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((450879:ℝ)/640000) ((226099:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((226099:ℝ)/320000) ((453517:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((450879:ℝ)/640000) ((453517:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((223461:ℝ)/320000) ((453517:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((453517:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((453517:ℝ)/640000) ((113709:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((113709:ℝ)/160000) ((91231:ℝ)/128000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((453517:ℝ)/640000) ((91231:ℝ)/128000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((91231:ℝ)/128000) ((228737:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((228737:ℝ)/320000) ((458793:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((91231:ℝ)/128000) ((458793:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((453517:ℝ)/640000) ((458793:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((458793:ℝ)/640000) ((461431:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((461431:ℝ)/640000) ((116347:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((458793:ℝ)/640000) ((116347:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((116347:ℝ)/160000) ((58833:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((58833:ℝ)/80000) ((7519:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((116347:ℝ)/160000) ((7519:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((458793:ℝ)/640000) ((7519:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((453517:ℝ)/640000) ((7519:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7519:ℝ)/10000),
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
end N11Formalization.C450SixthRadialC15
#check @N11Formalization.C450SixthRadialC15.bound
#print axioms N11Formalization.C450SixthRadialC15.params_valid
#print axioms N11Formalization.C450SixthRadialC15.params_sum
#print axioms N11Formalization.C450SixthRadialC15.bound
