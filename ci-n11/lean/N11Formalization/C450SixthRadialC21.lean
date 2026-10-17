import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC21
open C450RadialPacketKernel
def params : Params := ⟨((20572291:ℚ)/8000000),((5409373:ℚ)/8000000),((3040679:ℚ)/4000000),((-51:ℚ)/10000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((26149:ℚ)/40000),((969347127:ℚ)/5000000000),((6050036883:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((26149:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((26149:ℚ)/40000),((53647:ℚ)/80000),((289818771:ℚ)/1250000000),((1304742687:ℚ)/2500000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((26149:ℝ)/40000) ((53647:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((53647:ℚ)/80000),((108643:ℚ)/160000),((2474662939:ℚ)/10000000000),((2377515743:ℚ)/5000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((53647:ℝ)/80000) ((108643:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((108643:ℚ)/160000),((13749:ℚ)/20000),((2614166957:ℚ)/10000000000),((1126670543:ℚ)/2500000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((108643:ℝ)/160000) ((13749:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((13749:ℚ)/20000),((221333:ℚ)/320000),((133929483:ℚ)/500000000),((4244873247:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((13749:ℝ)/20000) ((221333:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((221333:ℚ)/320000),((111341:ℚ)/160000),((684959133:ℚ)/2500000000),((410811937:ℚ)/1000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((221333:ℝ)/320000) ((111341:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((111341:ℚ)/160000),((446713:ℚ)/640000),((1384671979:ℚ)/5000000000),((30991643:ℚ)/78125000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((111341:ℝ)/160000) ((446713:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((446713:ℚ)/640000),((224031:ℚ)/320000),((2798143453:ℚ)/10000000000),((3894522023:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((446713:ℝ)/640000) ((224031:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((224031:ℚ)/320000),((449411:ℚ)/640000),((2826259949:ℚ)/10000000000),((1910406541:ℚ)/5000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((224031:ℝ)/320000) ((449411:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((449411:ℚ)/640000),((11269:ℚ)/16000),((142685843:ℚ)/500000000),((374572653:ℚ)/1000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((449411:ℝ)/640000) ((11269:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((11269:ℚ)/16000),((452109:ℚ)/640000),((180033513:ℚ)/625000000),((3669177623:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((11269:ℝ)/16000) ((452109:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((452109:ℚ)/640000),((905567:ℚ)/1280000),((1446856663:ℚ)/5000000000),((3591072673:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((452109:ℝ)/640000) ((905567:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((905567:ℚ)/1280000),((226729:ℚ)/320000),((2906738739:ℚ)/10000000000),((28411237:ℚ)/80000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((905567:ℝ)/1280000) ((226729:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((226729:ℚ)/320000),((181653:ℚ)/256000),((2919614859:ℚ)/10000000000),((877826917:ℚ)/2500000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((226729:ℝ)/320000) ((181653:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((181653:ℚ)/256000),((454807:ℚ)/640000),((733086007:ℚ)/2500000000),((867691729:ℚ)/2500000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((181653:ℝ)/256000) ((454807:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((454807:ℚ)/640000),((910963:ℚ)/1280000),((2944928527:ℚ)/10000000000),((214360413:ℚ)/625000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((454807:ℝ)/640000) ((910963:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((910963:ℚ)/1280000),((114039:ℚ)/160000),((295737057:ℚ)/1000000000),((3388290039:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((910963:ℝ)/1280000) ((114039:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((114039:ℚ)/160000),((913661:ℚ)/1280000),((742418079:ℚ)/2500000000),((3346319477:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((114039:ℝ)/160000) ((913661:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((913661:ℚ)/1280000),((91501:ℚ)/128000),((1490917931:ℚ)/5000000000),((3303836073:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((913661:ℝ)/1280000) ((91501:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((91501:ℚ)/128000),((916359:ℚ)/1280000),((1496931627:ℚ)/5000000000),((1630409879:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((91501:ℝ)/128000) ((916359:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((916359:ℚ)/1280000),((229427:ℚ)/320000),((1502878241:ℚ)/5000000000),((3217249133:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((916359:ℝ)/1280000) ((229427:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((229427:ℚ)/320000),((460203:ℚ)/640000),((3029148153:ℚ)/10000000000),((158655067:ℚ)/500000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((229427:ℝ)/320000) ((460203:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((460203:ℚ)/640000),((28847:ℚ)/40000),((1526012903:ℚ)/5000000000),((61659493:ℚ)/200000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((460203:ℝ)/640000) ((28847:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((28847:ℚ)/40000),((462901:ℚ)/640000),((768600909:ℚ)/2500000000),((747555433:ℚ)/2500000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((28847:ℝ)/40000) ((462901:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((462901:ℚ)/640000),((1857:ℚ)/2560),((1548147577:ℚ)/5000000000),((289458993:ℚ)/1000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((462901:ℝ)/640000) ((1857:ℝ)/2560),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((1857:ℚ)/2560),((116737:ℚ)/160000),((156933507:ℚ)/500000000),((139789181:ℚ)/500000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((1857:ℝ)/2560) ((116737:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((116737:ℚ)/160000),((234823:ℚ)/320000),((3179246803:ℚ)/10000000000),((2587180439:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((116737:ℝ)/160000) ((234823:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((234823:ℚ)/320000),((59043:ℚ)/80000),((3218112801:ℚ)/10000000000),((2360658001:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((234823:ℝ)/320000) ((59043:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((59043:ℚ)/80000),((23887:ℚ)/32000),((1645513709:ℚ)/5000000000),((2110451919:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((59043:ℝ)/80000) ((23887:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((23887:ℚ)/32000),((7549:ℚ)/10000),((209873893:ℚ)/625000000),((1490927417:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((23887:ℝ)/32000) ((7549:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((26149:ℝ)/40000) ((108643:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((108643:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((108643:ℝ)/160000) ((221333:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((221333:ℝ)/320000) ((446713:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((108643:ℝ)/160000) ((446713:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((446713:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((446713:ℝ)/640000) ((449411:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((449411:ℝ)/640000) ((452109:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node7_11 :
    ∀ r ∈ Set.Icc ((446713:ℝ)/640000) ((452109:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_9 node9_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((452109:ℝ)/640000) ((226729:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((226729:ℝ)/320000) ((454807:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node11_15 :
    ∀ r ∈ Set.Icc ((452109:ℝ)/640000) ((454807:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_15
private theorem node7_15 :
    ∀ r ∈ Set.Icc ((446713:ℝ)/640000) ((454807:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_11 node11_15
private theorem node0_15 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((454807:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((910963:ℝ)/1280000) ((913661:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((454807:ℝ)/640000) ((913661:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((913661:ℝ)/1280000) ((916359:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((916359:ℝ)/1280000) ((460203:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node18_22 :
    ∀ r ∈ Set.Icc ((913661:ℝ)/1280000) ((460203:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node18_20 node20_22
private theorem node15_22 :
    ∀ r ∈ Set.Icc ((454807:ℝ)/640000) ((460203:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_18 node18_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((460203:ℝ)/640000) ((462901:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((462901:ℝ)/640000) ((116737:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node22_26 :
    ∀ r ∈ Set.Icc ((460203:ℝ)/640000) ((116737:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_26
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((116737:ℝ)/160000) ((59043:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((59043:ℝ)/80000) ((7549:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node26_30 :
    ∀ r ∈ Set.Icc ((116737:ℝ)/160000) ((7549:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node26_28 node28_30
private theorem node22_30 :
    ∀ r ∈ Set.Icc ((460203:ℝ)/640000) ((7549:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_26 node26_30
private theorem node15_30 :
    ∀ r ∈ Set.Icc ((454807:ℝ)/640000) ((7549:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_22 node22_30
private theorem node0_30 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7549:ℝ)/10000),
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
end N11Formalization.C450SixthRadialC21
#check @N11Formalization.C450SixthRadialC21.bound
#print axioms N11Formalization.C450SixthRadialC21.params_valid
#print axioms N11Formalization.C450SixthRadialC21.params_sum
#print axioms N11Formalization.C450SixthRadialC21.bound
