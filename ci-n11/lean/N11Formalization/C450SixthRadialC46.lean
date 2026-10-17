import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC46
open C450RadialPacketKernel
def params : Params := ⟨((32793329423:ℚ)/12800000000),((8777332977:ℚ)/12800000000),((2627147:ℚ)/4000000),((183:ℚ)/20000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((52583:ℚ)/80000),((2028296477:ℚ)/10000000000),((3186124033:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((52583:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((52583:ℚ)/80000),((108149:ℚ)/160000),((2419599311:ℚ)/10000000000),((5494487959:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((52583:ℝ)/80000) ((108149:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((108149:ℚ)/160000),((219281:ℚ)/320000),((32240587:ℚ)/125000000),((5004978943:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((108149:ℝ)/160000) ((219281:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((219281:ℚ)/320000),((27783:ℚ)/40000),((2721183357:ℚ)/10000000000),((948614301:ℚ)/2000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((219281:ℝ)/320000) ((27783:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((27783:ℚ)/40000),((447511:ℚ)/640000),((278646417:ℚ)/1000000000),((4467059797:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((27783:ℝ)/40000) ((447511:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((447511:ℚ)/640000),((225247:ℚ)/320000),((1424176981:ℚ)/5000000000),((2161460987:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((447511:ℝ)/640000) ((225247:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((225247:ℚ)/320000),((453477:ℚ)/640000),((2907103479:ℚ)/10000000000),((1043533333:ℚ)/2500000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((225247:ℝ)/320000) ((453477:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((453477:ℚ)/640000),((909937:ℚ)/1280000),((2935370307:ℚ)/10000000000),((1005043949:ℚ)/2500000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((453477:ℝ)/640000) ((909937:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((909937:ℚ)/1280000),((22823:ℚ)/32000),((2962932259:ℚ)/10000000000),((788213929:ℚ)/2000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((909937:ℝ)/1280000) ((22823:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((22823:ℚ)/32000),((915903:ℚ)/1280000),((1494906383:ℚ)/5000000000),((1930214609:ℚ)/5000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((22823:ℝ)/32000) ((915903:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((915903:ℚ)/1280000),((1834789:ℚ)/2560000),((3003004427:ℚ)/10000000000),((75563121:ℚ)/200000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((915903:ℝ)/1280000) ((1834789:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((1834789:ℚ)/2560000),((459443:ℚ)/640000),((1508016953:ℚ)/5000000000),((467046687:ℚ)/1250000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((1834789:ℝ)/2560000) ((459443:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((459443:ℚ)/640000),((368151:ℚ)/512000),((302890377:ℚ)/1000000000),((461767603:ℚ)/1250000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((459443:ℝ)/640000) ((368151:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((368151:ℚ)/512000),((921869:ℚ)/1280000),((23762629:ℚ)/78125000),((3651442387:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((368151:ℝ)/512000) ((921869:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((921869:ℚ)/1280000),((1846721:ℚ)/2560000),((3054174559:ℚ)/10000000000),((1804130811:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((921869:ℝ)/1280000) ((1846721:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((1846721:ℚ)/2560000),((231213:ℚ)/320000),((306658027:ℚ)/1000000000),((356458097:ℚ)/1000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((1846721:ℝ)/2560000) ((231213:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((231213:ℚ)/320000),((1852687:ℚ)/2560000),((1539417971:ℚ)/5000000000),((1760190897:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((231213:ℝ)/320000) ((1852687:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((1852687:ℚ)/2560000),((185567:ℚ)/256000),((3090943809:ℚ)/10000000000),((3475644283:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((1852687:ℝ)/2560000) ((185567:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((185567:ℚ)/256000),((1858653:ℚ)/2560000),((48482907:ℚ)/156250000),((3430347343:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((185567:ℝ)/256000) ((1858653:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((1858653:ℚ)/2560000),((465409:ℚ)/640000),((3114724779:ℚ)/10000000000),((1692234241:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((1858653:ℝ)/2560000) ((465409:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((465409:ℚ)/640000),((1864619:ℚ)/2560000),((1563201033:ℚ)/5000000000),((133519347:ℚ)/400000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((465409:ℝ)/640000) ((1864619:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((1864619:ℚ)/2560000),((933801:ℚ)/1280000),((1568969961:ℚ)/5000000000),((3290867213:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((1864619:ℝ)/2560000) ((933801:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((933801:ℚ)/1280000),((374117:ℚ)/512000),((3149340309:ℚ)/10000000000),((3243091533:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((933801:ℝ)/1280000) ((374117:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((374117:ℚ)/512000),((58549:ℚ)/80000),((3160605141:ℚ)/10000000000),((798656757:ℚ)/2500000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((374117:ℝ)/512000) ((58549:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((58549:ℚ)/80000),((1876551:ℚ)/2560000),((1585868141:ℚ)/5000000000),((98295057:ℚ)/312500000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((58549:ℝ)/80000) ((1876551:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((1876551:ℚ)/2560000),((939767:ℚ)/1280000),((1591367777:ℚ)/5000000000),((96734423:ℚ)/312500000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((1876551:ℝ)/2560000) ((939767:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((939767:ℚ)/1280000),((1882517:ℚ)/2560000),((798401183:ℚ)/2500000000),((121790759:ℚ)/400000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((939767:ℝ)/1280000) ((1882517:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((1882517:ℚ)/2560000),((3771:ℚ)/5120),((3204345551:ℚ)/10000000000),((2993203821:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((1882517:ℝ)/2560000) ((3771:ℝ)/5120),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((3771:ℚ)/5120),((945733:ℚ)/1280000),((806362211:ℚ)/2500000000),((735190561:ℚ)/2500000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((3771:ℝ)/5120) ((945733:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((945733:ℚ)/1280000),((237179:ℚ)/320000),((3246058507:ℚ)/10000000000),((708263547:ℚ)/2500000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((945733:ℝ)/1280000) ((237179:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((237179:ℚ)/320000),((951699:ℚ)/1280000),((130647481:ℚ)/400000000),((2721205039:ℚ)/10000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((237179:ℝ)/320000) ((951699:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((951699:ℚ)/1280000),((477341:ℚ)/640000),((1642923161:ℚ)/5000000000),((520936213:ℚ)/2000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((951699:ℝ)/1280000) ((477341:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((477341:ℚ)/640000),((120081:ℚ)/160000),((1661901193:ℚ)/5000000000),((2482823833:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((477341:ℝ)/640000) ((120081:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((120081:ℚ)/160000),((48629:ℚ)/64000),((3394554461:ℚ)/10000000000),((1109779447:ℚ)/5000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((120081:ℝ)/160000) ((48629:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((48629:ℚ)/64000),((15383:ℚ)/20000),((3458920179:ℚ)/10000000000),((1567850863:ℚ)/10000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((48629:ℝ)/64000) ((15383:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((108149:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((108149:ℝ)/160000) ((27783:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((27783:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((27783:ℝ)/40000) ((225247:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((225247:ℝ)/320000) ((909937:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((27783:ℝ)/40000) ((909937:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((909937:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((909937:ℝ)/1280000) ((915903:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((915903:ℝ)/1280000) ((459443:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((909937:ℝ)/1280000) ((459443:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((459443:ℝ)/640000) ((921869:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((1846721:ℝ)/2560000) ((1852687:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((921869:ℝ)/1280000) ((1852687:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node12_17 :
    ∀ r ∈ Set.Icc ((459443:ℝ)/640000) ((1852687:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_14 node14_17
private theorem node8_17 :
    ∀ r ∈ Set.Icc ((909937:ℝ)/1280000) ((1852687:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_12 node12_17
private theorem node0_17 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1852687:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_8 node8_17
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((1852687:ℝ)/2560000) ((1858653:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((1858653:ℝ)/2560000) ((1864619:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node17_21 :
    ∀ r ∈ Set.Icc ((1852687:ℝ)/2560000) ((1864619:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_19 node19_21
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((1864619:ℝ)/2560000) ((374117:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((58549:ℝ)/80000) ((939767:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node23_26 :
    ∀ r ∈ Set.Icc ((374117:ℝ)/512000) ((939767:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 node24_26
private theorem node21_26 :
    ∀ r ∈ Set.Icc ((1864619:ℝ)/2560000) ((939767:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_23 node23_26
private theorem node17_26 :
    ∀ r ∈ Set.Icc ((1852687:ℝ)/2560000) ((939767:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_21 node21_26
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((939767:ℝ)/1280000) ((3771:ℝ)/5120),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((3771:ℝ)/5120) ((237179:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node26_30 :
    ∀ r ∈ Set.Icc ((939767:ℝ)/1280000) ((237179:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node26_28 node28_30
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((237179:ℝ)/320000) ((477341:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node33_35 :
    ∀ r ∈ Set.Icc ((120081:ℝ)/160000) ((15383:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 leaf34
private theorem node32_35 :
    ∀ r ∈ Set.Icc ((477341:ℝ)/640000) ((15383:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 node33_35
private theorem node30_35 :
    ∀ r ∈ Set.Icc ((237179:ℝ)/320000) ((15383:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node30_32 node32_35
private theorem node26_35 :
    ∀ r ∈ Set.Icc ((939767:ℝ)/1280000) ((15383:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node26_30 node30_35
private theorem node17_35 :
    ∀ r ∈ Set.Icc ((1852687:ℝ)/2560000) ((15383:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_26 node26_35
private theorem node0_35 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((15383:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_17 node17_35
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_35
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC46
#check @N11Formalization.C450SixthRadialC46.bound
#print axioms N11Formalization.C450SixthRadialC46.params_valid
#print axioms N11Formalization.C450SixthRadialC46.params_sum
#print axioms N11Formalization.C450SixthRadialC46.bound
