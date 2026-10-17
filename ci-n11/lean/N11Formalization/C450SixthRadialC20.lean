import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC20
open C450RadialPacketKernel
def params : Params := ⟨((82298997:ℚ)/32000000),((21627659:ℚ)/32000000),((12236561:ℚ)/16000000),((-7:ℚ)/1250)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((817:ℚ)/1250),((483859869:ℚ)/2500000000),((6038460117:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((817:ℝ)/1250),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((817:ℚ)/1250),((419:ℚ)/625),((46297247:ℚ)/200000000),((2604532303:ℚ)/5000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((817:ℝ)/1250) ((419:ℝ)/625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((419:ℚ)/625),((1697:ℚ)/2500),((617709121:ℚ)/2500000000),((949208323:ℚ)/2000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((419:ℝ)/625) ((1697:ℝ)/2500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((1697:ℚ)/2500),((859:ℚ)/1250),((2610241079:ℚ)/10000000000),((1124544629:ℚ)/2500000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((1697:ℝ)/2500) ((859:ℝ)/1250),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((859:ℚ)/1250),((3457:ℚ)/5000),((534925361:ℚ)/2000000000),((211843959:ℚ)/500000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((859:ℝ)/1250) ((3457:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((3457:ℚ)/5000),((1739:ℚ)/2500),((54716887:ℚ)/200000000),((2050195167:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((3457:ℝ)/5000) ((1739:ℝ)/2500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((1739:ℚ)/2500),((6977:ℚ)/10000),((1382669907:ℚ)/5000000000),((791894821:ℚ)/2000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((1739:ℝ)/2500) ((6977:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((6977:ℚ)/10000),((3499:ℚ)/5000),((2794129067:ℚ)/10000000000),((485900681:ℚ)/1250000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((6977:ℝ)/10000) ((3499:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((3499:ℚ)/5000),((7019:ℚ)/10000),((564447397:ℚ)/2000000000),((3813638433:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((3499:ℝ)/5000) ((7019:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((7019:ℚ)/10000),((88:ℚ)/125),((2849686927:ℚ)/10000000000),((3738696253:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((7019:ℝ)/10000) ((88:ℝ)/125),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((88:ℚ)/125),((7061:ℚ)/10000),((1438250433:ℚ)/5000000000),((45778679:ℚ)/125000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((88:ℝ)/125) ((7061:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((7061:ℚ)/10000),((14143:ℚ)/20000),((2889675849:ℚ)/10000000000),((896084779:ℚ)/2500000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((7061:ℝ)/10000) ((14143:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((14143:ℚ)/20000),((3541:ℚ)/5000),((2902699501:ℚ)/10000000000),((22154669:ℚ)/62500000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((14143:ℝ)/20000) ((3541:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((3541:ℚ)/5000),((2837:ℚ)/4000),((1457787113:ℚ)/5000000000),((1752363411:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((3541:ℝ)/5000) ((2837:ℝ)/4000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((2837:ℚ)/4000),((7103:ℚ)/10000),((1464151181:ℚ)/5000000000),((1732131801:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((2837:ℝ)/4000) ((7103:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((7103:ℚ)/10000),((14227:ℚ)/20000),((2940886183:ℚ)/10000000000),((68466833:ℚ)/200000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((7103:ℝ)/10000) ((14227:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((14227:ℚ)/20000),((1781:ℚ)/2500),((2953327901:ℚ)/10000000000),((3381944291:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((14227:ℝ)/20000) ((1781:ℝ)/2500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((1781:ℚ)/2500),((14269:ℚ)/20000),((1482814833:ℚ)/5000000000),((133602153:ℚ)/400000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((1781:ℝ)/2500) ((14269:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((14269:ℚ)/20000),((1429:ℚ)/2000),((119111743:ℚ)/400000000),((3297651437:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((14269:ℝ)/20000) ((1429:ℝ)/2000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((1429:ℚ)/2000),((14311:ℚ)/20000),((1494910833:ℚ)/5000000000),((1627358549:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((1429:ℝ)/2000) ((14311:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((14311:ℚ)/20000),((3583:ℚ)/5000),((750428981:ℚ)/2500000000),((642245889:ℚ)/2000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((14311:ℝ)/20000) ((3583:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((3583:ℚ)/5000),((7187:ℚ)/10000),((1512555317:ℚ)/5000000000),((98973927:ℚ)/312500000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((3583:ℝ)/5000) ((7187:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((7187:ℚ)/10000),((901:ℚ)/1250),((1523996301:ℚ)/5000000000),((3077210299:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((7187:ℝ)/10000) ((901:ℝ)/1250),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((901:ℚ)/1250),((7229:ℚ)/10000),((3070375991:ℚ)/10000000000),((2984633451:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((901:ℝ)/1250) ((7229:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((7229:ℚ)/10000),((29:ℚ)/40),((3092274279:ℚ)/10000000000),((115567317:ℚ)/400000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((7229:ℝ)/10000) ((29:ℝ)/40),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((29:ℚ)/40),((1823:ℚ)/2500),((1567333161:ℚ)/5000000000),((697640911:ℚ)/2500000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((29:ℝ)/40) ((1823:ℝ)/2500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((1823:ℚ)/2500),((3667:ℚ)/5000),((1587632273:ℚ)/5000000000),((322794311:ℚ)/1250000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((1823:ℝ)/2500) ((3667:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((3667:ℚ)/5000),((461:ℚ)/625),((803539101:ℚ)/2500000000),((2356258719:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((3667:ℝ)/5000) ((461:ℝ)/625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((461:ℚ)/625),((373:ℚ)/500),((657426981:ℚ)/2000000000),((65828831:ℚ)/312500000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((461:ℝ)/625) ((373:ℝ)/500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((373:ℚ)/500),((943:ℚ)/1250),((3354168789:ℚ)/10000000000),((1488156709:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((373:ℝ)/500) ((943:ℝ)/1250),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((817:ℝ)/1250) ((1697:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1697:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((1697:ℝ)/2500) ((3457:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((3457:ℝ)/5000) ((6977:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((1697:ℝ)/2500) ((6977:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((6977:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((6977:ℝ)/10000) ((7019:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((7019:ℝ)/10000) ((7061:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node7_11 :
    ∀ r ∈ Set.Icc ((6977:ℝ)/10000) ((7061:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_9 node9_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((7061:ℝ)/10000) ((3541:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((3541:ℝ)/5000) ((7103:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node11_15 :
    ∀ r ∈ Set.Icc ((7061:ℝ)/10000) ((7103:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_15
private theorem node7_15 :
    ∀ r ∈ Set.Icc ((6977:ℝ)/10000) ((7103:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_11 node11_15
private theorem node0_15 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7103:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((14227:ℝ)/20000) ((14269:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((7103:ℝ)/10000) ((14269:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((14269:ℝ)/20000) ((14311:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((14311:ℝ)/20000) ((7187:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node18_22 :
    ∀ r ∈ Set.Icc ((14269:ℝ)/20000) ((7187:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node18_20 node20_22
private theorem node15_22 :
    ∀ r ∈ Set.Icc ((7103:ℝ)/10000) ((7187:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_18 node18_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((7187:ℝ)/10000) ((7229:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((7229:ℝ)/10000) ((1823:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node22_26 :
    ∀ r ∈ Set.Icc ((7187:ℝ)/10000) ((1823:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_26
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((1823:ℝ)/2500) ((461:ℝ)/625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((461:ℝ)/625) ((943:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node26_30 :
    ∀ r ∈ Set.Icc ((1823:ℝ)/2500) ((943:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node26_28 node28_30
private theorem node22_30 :
    ∀ r ∈ Set.Icc ((7187:ℝ)/10000) ((943:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_26 node26_30
private theorem node15_30 :
    ∀ r ∈ Set.Icc ((7103:ℝ)/10000) ((943:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_22 node22_30
private theorem node0_30 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((943:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_15 node15_30
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_30
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC20
#check @N11Formalization.C450SixthRadialC20.bound
#print axioms N11Formalization.C450SixthRadialC20.params_valid
#print axioms N11Formalization.C450SixthRadialC20.params_sum
#print axioms N11Formalization.C450SixthRadialC20.bound
