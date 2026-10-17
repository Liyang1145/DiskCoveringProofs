import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FourthRadialC08
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((677853:ℚ)/1000000),((785373:ℚ)/1250000),((759:ℚ)/62500)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((164509:ℚ)/250000),((1023195037:ℚ)/5000000000),((6438168321:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((164509:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((164509:ℚ)/250000),((338527:ℚ)/500000),((2439889479:ℚ)/10000000000),((693850919:ℚ)/1250000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((164509:ℝ)/250000) ((338527:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((338527:ℚ)/500000),((686563:ℚ)/1000000),((104007311:ℚ)/400000000),((252802533:ℚ)/500000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((338527:ℝ)/500000) ((686563:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((686563:ℚ)/1000000),((87009:ℚ)/125000),((1371268337:ℚ)/5000000000),((4791363209:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((686563:ℝ)/1000000) ((87009:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((87009:ℚ)/125000),((1401653:ℚ)/2000000),((2807952127:ℚ)/10000000000),((902488209:ℚ)/2000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((87009:ℝ)/125000) ((1401653:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((1401653:ℚ)/2000000),((705581:ℚ)/1000000),((573986403:ℚ)/2000000000),((2183395381:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((1401653:ℝ)/2000000) ((705581:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((705581:ℚ)/1000000),((1420671:ℚ)/2000000),((2928730159:ℚ)/10000000000),((2108222973:ℚ)/5000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((705581:ℝ)/1000000) ((1420671:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((1420671:ℚ)/2000000),((2850851:ℚ)/4000000),((184812913:ℚ)/625000000),((253805213:ℚ)/625000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((1420671:ℝ)/2000000) ((2850851:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2850851:ℚ)/4000000),((71509:ℚ)/100000),((596913761:ℚ)/2000000000),((1990477289:ℚ)/5000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2850851:ℝ)/4000000) ((71509:ℝ)/100000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((71509:ℚ)/100000),((2869869:ℚ)/4000000),((3011440471:ℚ)/10000000000),((3899476873:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((71509:ℝ)/100000) ((2869869:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((2869869:ℚ)/4000000),((5749247:ℚ)/8000000),((3024624391:ℚ)/10000000000),((1908175427:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((2869869:ℝ)/4000000) ((5749247:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((5749247:ℚ)/8000000),((1439689:ℚ)/2000000),((75941099:ℚ)/250000000),((1887067851:ℚ)/5000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((5749247:ℝ)/8000000) ((1439689:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((1439689:ℚ)/2000000),((1153653:ℚ)/1600000),((122020071:ℚ)/400000000),((932866531:ℚ)/2500000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((1439689:ℝ)/2000000) ((1153653:ℝ)/1600000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((1153653:ℚ)/1600000),((2888887:ℚ)/4000000),((3063200363:ℚ)/10000000000),((1844163159:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((1153653:ℝ)/1600000) ((2888887:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((2888887:ℚ)/4000000),((5787283:ℚ)/8000000),((3075742179:ℚ)/10000000000),((3644699557:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((2888887:ℝ)/4000000) ((5787283:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((5787283:ℚ)/8000000),((724599:ℚ)/1000000),((1544064807:ℚ)/5000000000),((360056811:ℚ)/1000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((5787283:ℝ)/8000000) ((724599:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((724599:ℚ)/1000000),((5806301:ℚ)/8000000),((3100364991:ℚ)/10000000000),((1777956577:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((724599:ℝ)/1000000) ((5806301:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((5806301:ℚ)/8000000),((11622111:ℚ)/16000000),((6067239:ℚ)/19531250),((3510714681:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((5806301:ℝ)/8000000) ((11622111:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((11622111:ℚ)/16000000),((581581:ℚ)/800000),((124498023:ℚ)/400000000),((1743952511:ℚ)/5000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((11622111:ℝ)/16000000) ((581581:ℝ)/800000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((581581:ℚ)/800000),((11641129:ℚ)/16000000),((779609471:ℚ)/2500000000),((3464951389:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((581581:ℝ)/800000) ((11641129:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((11641129:ℚ)/16000000),((5825319:ℚ)/8000000),((390548571:ℚ)/1250000000),((3441850897:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((11641129:ℝ)/16000000) ((5825319:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((5825319:ℚ)/8000000),((11660147:ℚ)/16000000),((3130302891:ℚ)/10000000000),((683720113:ℚ)/2000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((5825319:ℝ)/8000000) ((11660147:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((11660147:ℚ)/16000000),((1458707:ℚ)/2000000),((3136181117:ℚ)/10000000000),((339519731:ℚ)/1000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((11660147:ℝ)/16000000) ((1458707:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((1458707:ℚ)/2000000),((2335833:ℚ)/3200000),((628404701:ℚ)/2000000000),((421454743:ℚ)/1250000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((1458707:ℝ)/2000000) ((2335833:ℝ)/3200000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((2335833:ℚ)/3200000),((5844337:ℚ)/8000000),((3147830313:ℚ)/10000000000),((3347919167:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((2335833:ℝ)/3200000) ((5844337:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((5844337:ℚ)/8000000),((11698183:ℚ)/16000000),((12318757:ℚ)/39062500),((1662018781:ℚ)/5000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((5844337:ℝ)/8000000) ((11698183:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((11698183:ℚ)/16000000),((2926923:ℚ)/4000000),((3159338193:ℚ)/10000000000),((3299989591:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((11698183:ℝ)/16000000) ((2926923:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((2926923:ℚ)/4000000),((11717201:ℚ)/16000000),((3165039763:ℚ)/10000000000),((51183931:ℚ)/156250000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((2926923:ℝ)/4000000) ((11717201:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((11717201:ℚ)/16000000),((1172671:ℚ)/1600000),((1585353373:ℚ)/5000000000),((3251379739:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((11717201:ℝ)/16000000) ((1172671:ℝ)/1600000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((1172671:ℚ)/1600000),((11736219:ℚ)/16000000),((3176339381:ℚ)/10000000000),((3226810109:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((1172671:ℝ)/1600000) ((11736219:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((11736219:ℚ)/16000000),((183527:ℚ)/250000),((3181937907:ℚ)/10000000000),((1601029299:ℚ)/5000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((11736219:ℝ)/16000000) ((183527:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((183527:ℚ)/250000),((5882373:ℚ)/8000000),((638606713:ℚ)/2000000000),((3177120949:ℚ)/10000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((183527:ℝ)/250000) ((5882373:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((5882373:ℚ)/8000000),((2945941:ℚ)/4000000),((1601997783:ℚ)/5000000000),((5002671:ℚ)/16000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((5882373:ℝ)/8000000) ((2945941:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((2945941:ℚ)/4000000),((5901391:ℚ)/8000000),((1607412853:ℚ)/5000000000),((3075417831:ℚ)/10000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((2945941:ℝ)/4000000) ((5901391:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((5901391:ℚ)/8000000),((59109:ℚ)/80000),((1612762871:ℚ)/5000000000),((1511662799:ℚ)/5000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((5901391:ℝ)/8000000) ((59109:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((59109:ℚ)/80000),((5920409:ℚ)/8000000),((3236097389:ℚ)/10000000000),((371293551:ℚ)/1250000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((59109:ℝ)/80000) ((5920409:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((5920409:ℚ)/8000000),((2964959:ℚ)/4000000),((40581779:ℚ)/125000000),((1458219:ℚ)/5000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((5920409:ℝ)/8000000) ((2964959:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((2964959:ℚ)/4000000),((743617:ℚ)/1000000),((163352927:ℚ)/500000000),((357692699:ℚ)/1250000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((2964959:ℝ)/4000000) ((743617:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((743617:ℚ)/1000000),((2983977:ℚ)/4000000),((1643543521:ℚ)/5000000000),((10994213:ℚ)/40000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((743617:ℝ)/1000000) ((2983977:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((2983977:ℚ)/4000000),((1496743:ℚ)/2000000),((3306639903:ℚ)/10000000000),((52616887:ℚ)/200000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((2983977:ℝ)/4000000) ((1496743:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((1496743:ℚ)/2000000),((376563:ℚ)/500000),((3344364403:ℚ)/10000000000),((15673437:ℚ)/62500000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((1496743:ℝ)/2000000) ((376563:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((376563:ℚ)/500000),((152527:ℚ)/200000),((1707291119:ℚ)/5000000000),((2241818479:ℚ)/10000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((376563:ℝ)/500000) ((152527:ℝ)/200000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((152527:ℚ)/200000),((48259:ℚ)/62500),((695665021:ℚ)/2000000000),((1583541637:ℚ)/10000000000)⟩
theorem valid42 : Valid params packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((152527:ℝ)/200000) ((48259:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((338527:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((686563:ℝ)/1000000) ((1401653:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((338527:ℝ)/500000) ((1401653:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1401653:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((1401653:ℝ)/2000000) ((1420671:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((2850851:ℝ)/4000000) ((2869869:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((1420671:ℝ)/2000000) ((2869869:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node5_10 :
    ∀ r ∈ Set.Icc ((1401653:ℝ)/2000000) ((2869869:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_7 node7_10
private theorem node0_10 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((2869869:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((2869869:ℝ)/4000000) ((1439689:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((1153653:ℝ)/1600000) ((5787283:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((1439689:ℝ)/2000000) ((5787283:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node10_15 :
    ∀ r ∈ Set.Icc ((2869869:ℝ)/4000000) ((5787283:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((724599:ℝ)/1000000) ((11622111:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((5787283:ℝ)/8000000) ((11622111:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((581581:ℝ)/800000) ((5825319:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node18_21 :
    ∀ r ∈ Set.Icc ((11622111:ℝ)/16000000) ((5825319:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 node19_21
private theorem node15_21 :
    ∀ r ∈ Set.Icc ((5787283:ℝ)/8000000) ((5825319:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_18 node18_21
private theorem node10_21 :
    ∀ r ∈ Set.Icc ((2869869:ℝ)/4000000) ((5825319:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_15 node15_21
private theorem node0_21 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((5825319:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_10 node10_21
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((5825319:ℝ)/8000000) ((1458707:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((2335833:ℝ)/3200000) ((11698183:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node23_26 :
    ∀ r ∈ Set.Icc ((1458707:ℝ)/2000000) ((11698183:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 node24_26
private theorem node21_26 :
    ∀ r ∈ Set.Icc ((5825319:ℝ)/8000000) ((11698183:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_23 node23_26
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((2926923:ℝ)/4000000) ((1172671:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node26_29 :
    ∀ r ∈ Set.Icc ((11698183:ℝ)/16000000) ((1172671:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 node27_29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((11736219:ℝ)/16000000) ((5882373:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node29_32 :
    ∀ r ∈ Set.Icc ((1172671:ℝ)/1600000) ((5882373:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf29 node30_32
private theorem node26_32 :
    ∀ r ∈ Set.Icc ((11698183:ℝ)/16000000) ((5882373:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node26_29 node29_32
private theorem node21_32 :
    ∀ r ∈ Set.Icc ((5825319:ℝ)/8000000) ((5882373:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_26 node26_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((5882373:ℝ)/8000000) ((5901391:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 leaf33
private theorem node35_37 :
    ∀ r ∈ Set.Icc ((59109:ℝ)/80000) ((2964959:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf35 leaf36
private theorem node34_37 :
    ∀ r ∈ Set.Icc ((5901391:ℝ)/8000000) ((2964959:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 node35_37
private theorem node32_37 :
    ∀ r ∈ Set.Icc ((5882373:ℝ)/8000000) ((2964959:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node32_34 node34_37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((743617:ℝ)/1000000) ((1496743:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf38 leaf39
private theorem node37_40 :
    ∀ r ∈ Set.Icc ((2964959:ℝ)/4000000) ((1496743:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 node38_40
private theorem node41_43 :
    ∀ r ∈ Set.Icc ((376563:ℝ)/500000) ((48259:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf41 leaf42
private theorem node40_43 :
    ∀ r ∈ Set.Icc ((1496743:ℝ)/2000000) ((48259:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 node41_43
private theorem node37_43 :
    ∀ r ∈ Set.Icc ((2964959:ℝ)/4000000) ((48259:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node37_40 node40_43
private theorem node32_43 :
    ∀ r ∈ Set.Icc ((5882373:ℝ)/8000000) ((48259:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node32_37 node37_43
private theorem node21_43 :
    ∀ r ∈ Set.Icc ((5825319:ℝ)/8000000) ((48259:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_32 node32_43
private theorem node0_43 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((48259:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_21 node21_43
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_43
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450FourthRadialC08
#check @N11Formalization.C450FourthRadialC08.bound
#print axioms N11Formalization.C450FourthRadialC08.params_valid
#print axioms N11Formalization.C450FourthRadialC08.bound
