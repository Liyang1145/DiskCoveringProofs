import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC64
open C450RadialPacketKernel
def params : Params := ⟨((1042346442407:ℚ)/409600000000),((287914754393:ℚ)/409600000000),((472261:ℚ)/800000),((51:ℚ)/2500)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((6601:ℚ)/10000),((2095067257:ℚ)/10000000000),((6617023167:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((6601:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((6601:ℚ)/10000),((13603:ℚ)/20000),((2494275001:ℚ)/10000000000),((5703528267:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((6601:ℝ)/10000) ((13603:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((13603:ℚ)/20000),((3501:ℚ)/5000),((11198139:ℚ)/40000000),((259725229:ℚ)/500000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((13603:ℝ)/20000) ((3501:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((3501:ℚ)/5000),((28409:ℚ)/40000),((1463699011:ℚ)/5000000000),((927087273:ℚ)/2000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((3501:ℝ)/5000) ((28409:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((28409:ℚ)/40000),((57219:ℚ)/80000),((1493127977:ℚ)/5000000000),((4331109869:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((28409:ℝ)/40000) ((57219:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((57219:ℚ)/80000),((114839:ℚ)/160000),((1507261073:ℚ)/5000000000),((4171190959:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((57219:ℝ)/80000) ((114839:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((114839:ℚ)/160000),((2881:ℚ)/4000),((152102423:ℚ)/500000000),((255564343:ℚ)/625000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((114839:ℝ)/160000) ((2881:ℝ)/4000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((2881:ℚ)/4000),((115641:ℚ)/160000),((3068859411:ℚ)/10000000000),((801055947:ℚ)/2000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((2881:ℝ)/4000) ((115641:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((115641:ℚ)/160000),((58021:ℚ)/80000),((3094978103:ℚ)/10000000000),((3919839627:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((115641:ℝ)/160000) ((58021:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((58021:ℚ)/80000),((46497:ℚ)/64000),((388473089:ℚ)/1250000000),((5988431:ℚ)/15625000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((58021:ℝ)/80000) ((46497:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((46497:ℚ)/64000),((116443:ℚ)/160000),((3120426337:ℚ)/10000000000),((1894129319:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((46497:ℝ)/64000) ((116443:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((116443:ℚ)/160000),((233287:ℚ)/320000),((783226379:ℚ)/2500000000),((1871710993:ℚ)/5000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((116443:ℝ)/160000) ((233287:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((233287:ℚ)/320000),((29211:ℚ)/40000),((3145224719:ℚ)/10000000000),((23112923:ℚ)/62500000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((233287:ℝ)/320000) ((29211:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((29211:ℚ)/40000),((234089:ℚ)/320000),((3157386349:ℚ)/10000000000),((1826088201:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((29211:ℝ)/40000) ((234089:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((234089:ℚ)/320000),((23449:ℚ)/32000),((3169392747:ℚ)/10000000000),((360572761:ℚ)/1000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((234089:ℝ)/320000) ((23449:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((23449:ℚ)/32000),((234891:ℚ)/320000),((318124619:ℚ)/1000000000),((44483743:ℚ)/125000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((23449:ℝ)/32000) ((234891:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((234891:ℚ)/320000),((58823:ℚ)/80000),((99779653:ℚ)/312500000),((877767143:ℚ)/2500000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((234891:ℝ)/320000) ((58823:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((58823:ℚ)/80000),((235693:ℚ)/320000),((3204503029:ℚ)/10000000000),((3462810099:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((58823:ℝ)/80000) ((235693:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((235693:ℚ)/320000),((118047:ℚ)/160000),((1607955347:ℚ)/5000000000),((3413897369:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((235693:ℝ)/320000) ((118047:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((118047:ℚ)/160000),((47299:ℚ)/64000),((1613586973:ℚ)/5000000000),((1682150903:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((118047:ℝ)/160000) ((47299:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((47299:ℚ)/64000),((7403:ℚ)/10000),((3238294787:ℚ)/10000000000),((662798543:ℚ)/2000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((47299:ℝ)/64000) ((7403:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((7403:ℚ)/10000),((237297:ℚ)/320000),((812318793:ℚ)/2500000000),((3262937053:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((7403:ℝ)/10000) ((237297:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((237297:ℚ)/320000),((118849:ℚ)/160000),((652023401:ℚ)/2000000000),((3211099169:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((237297:ℝ)/320000) ((118849:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((118849:ℚ)/160000),((238099:ℚ)/320000),((1635411073:ℚ)/5000000000),((3158440509:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((118849:ℝ)/160000) ((238099:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((238099:ℚ)/320000),((477:ℚ)/640),((820348103:ℚ)/2500000000),((310491927:ℚ)/1000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((238099:ℝ)/320000) ((477:ℝ)/640),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((477:ℚ)/640),((238901:ℚ)/320000),((1645914787:ℚ)/5000000000),((305049001:ℚ)/1000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((477:ℝ)/640) ((238901:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((238901:ℚ)/320000),((119651:ℚ)/160000),((3302135363:ℚ)/10000000000),((1497551591:ℚ)/5000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((238901:ℝ)/320000) ((119651:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((119651:ℚ)/160000),((30013:ℚ)/40000),((66447191:ℚ)/200000000),((2938704601:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((119651:ℝ)/160000) ((30013:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((30013:ℚ)/40000),((120453:ℚ)/160000),((3342078039:ℚ)/10000000000),((176414271:ℚ)/625000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((30013:ℝ)/40000) ((120453:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((120453:ℚ)/160000),((60427:ℚ)/80000),((3361303319:ℚ)/10000000000),((2701707839:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((120453:ℝ)/160000) ((60427:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((60427:ℚ)/80000),((15207:ℚ)/20000),((1699160747:ℚ)/5000000000),((2575260433:ℚ)/10000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((60427:ℝ)/80000) ((15207:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((15207:ℚ)/20000),((6163:ℚ)/8000),((3466931967:ℚ)/10000000000),((1151051693:ℚ)/5000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((15207:ℝ)/20000) ((6163:ℝ)/8000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((6163:ℚ)/8000),((1951:ℚ)/2500),((3528824669:ℚ)/10000000000),((813015727:ℚ)/5000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((6163:ℝ)/8000) ((1951:ℝ)/2500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((13603:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((13603:ℝ)/20000) ((28409:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((28409:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((28409:ℝ)/40000) ((114839:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((114839:ℝ)/160000) ((115641:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((28409:ℝ)/40000) ((115641:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((115641:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((115641:ℝ)/160000) ((46497:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((46497:ℝ)/64000) ((233287:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((115641:ℝ)/160000) ((233287:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((233287:ℝ)/320000) ((234089:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((234089:ℝ)/320000) ((234891:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((233287:ℝ)/320000) ((234891:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((115641:ℝ)/160000) ((234891:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((234891:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((234891:ℝ)/320000) ((235693:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((235693:ℝ)/320000) ((47299:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((234891:ℝ)/320000) ((47299:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((47299:ℝ)/64000) ((237297:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((237297:ℝ)/320000) ((238099:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((47299:ℝ)/64000) ((238099:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((234891:ℝ)/320000) ((238099:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((238099:ℝ)/320000) ((238901:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((238901:ℝ)/320000) ((30013:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((238099:ℝ)/320000) ((30013:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((30013:ℝ)/40000) ((60427:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((15207:ℝ)/20000) ((1951:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((60427:ℝ)/80000) ((1951:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node28_33 :
    ∀ r ∈ Set.Icc ((30013:ℝ)/40000) ((1951:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node28_30 node30_33
private theorem node24_33 :
    ∀ r ∈ Set.Icc ((238099:ℝ)/320000) ((1951:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_28 node28_33
private theorem node16_33 :
    ∀ r ∈ Set.Icc ((234891:ℝ)/320000) ((1951:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_24 node24_33
private theorem node0_33 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1951:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_16 node16_33
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_33
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC64
#check @N11Formalization.C450SixthRadialC64.bound
#print axioms N11Formalization.C450SixthRadialC64.params_valid
#print axioms N11Formalization.C450SixthRadialC64.params_sum
#print axioms N11Formalization.C450SixthRadialC64.bound
