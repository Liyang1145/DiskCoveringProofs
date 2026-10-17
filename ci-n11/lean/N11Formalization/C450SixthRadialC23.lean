import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC23
open C450RadialPacketKernel
def params : Params := ⟨((41134749:ℚ)/16000000),((10828579:ℚ)/16000000),((6007513:ℚ)/8000000),((-41:ℚ)/10000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((26159:ℚ)/40000),((486295063:ℚ)/2500000000),((6073132481:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((26159:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((26159:ℚ)/40000),((53677:ℚ)/80000),((2325895599:ℚ)/10000000000),((654841503:ℚ)/1250000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((26159:ℝ)/40000) ((53677:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((53677:ℚ)/80000),((108713:ℚ)/160000),((310285319:ℚ)/1250000000),((477296431:ℚ)/1000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((53677:ℝ)/80000) ((108713:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((108713:ℚ)/160000),((13759:ℚ)/20000),((1310991219:ℚ)/5000000000),((2261822407:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((108713:ℝ)/160000) ((13759:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((13759:ℚ)/20000),((221503:ℚ)/320000),((671619411:ℚ)/2500000000),((4260819117:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((13759:ℝ)/20000) ((221503:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((221503:ℚ)/320000),((111431:ℚ)/160000),((2747781737:ℚ)/10000000000),((82470729:ℚ)/200000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((221503:ℝ)/320000) ((111431:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((111431:ℚ)/160000),((447083:ℚ)/640000),((1388656189:ℚ)/5000000000),((3981803031:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((111431:ℝ)/160000) ((447083:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((447083:ℚ)/640000),((224221:ℚ)/320000),((2806131653:ℚ)/10000000000),((3909116187:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((447083:ℝ)/640000) ((224221:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((224221:ℚ)/320000),((449801:ℚ)/640000),((88570769:ℚ)/312500000),((3835124089:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((224221:ℝ)/320000) ((449801:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((449801:ℚ)/640000),((11279:ℚ)/16000),((1430867381:ℚ)/5000000000),((751949901:ℚ)/2000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((449801:ℝ)/640000) ((11279:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((11279:ℚ)/16000),((452519:ℚ)/640000),((2888564237:ℚ)/10000000000),((3682907381:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((11279:ℝ)/16000) ((452519:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((452519:ℚ)/640000),((226939:ℚ)/320000),((1457386937:ℚ)/5000000000),((901125921:ℚ)/2500000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((452519:ℝ)/640000) ((226939:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((226939:ℚ)/320000),((181823:ℚ)/256000),((1463826221:ℚ)/5000000000),((1762217011:ℚ)/5000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((226939:ℝ)/320000) ((181823:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((181823:ℚ)/256000),((455237:ℚ)/640000),((1470191669:ℚ)/5000000000),((1741869297:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((181823:ℝ)/256000) ((455237:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((455237:ℚ)/640000),((911833:ℚ)/1280000),((59059377:ℚ)/200000000),((3442581969:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((455237:ℝ)/640000) ((911833:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((911833:ℚ)/1280000),((114149:ℚ)/160000),((2965411207:ℚ)/10000000000),((3400947381:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((911833:ℝ)/1280000) ((114149:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((114149:ℚ)/160000),((914551:ℚ)/1280000),((1488856287:ℚ)/5000000000),((3358817033:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((114149:ℝ)/160000) ((914551:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((914551:ℚ)/1280000),((91591:ℚ)/128000),((2989875061:ℚ)/10000000000),((1658086003:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((914551:ℝ)/1280000) ((91591:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((91591:ℚ)/128000),((917269:ℚ)/1280000),((37523759:ℚ)/125000000),((1636496079:ℚ)/5000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((91591:ℝ)/128000) ((917269:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((917269:ℚ)/1280000),((229657:ℚ)/320000),((47090493:ℚ)/156250000),((807314003:ℚ)/2500000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((917269:ℝ)/1280000) ((229657:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((229657:ℚ)/320000),((460673:ℚ)/640000),((759294119:ℚ)/2500000000),((1019181:ℚ)/3200000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((229657:ℝ)/320000) ((460673:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((460673:ℚ)/640000),((28877:ℚ)/40000),((1530022417:ℚ)/5000000000),((1547236081:ℚ)/5000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((460673:ℝ)/640000) ((28877:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((28877:ℚ)/40000),((463391:ℚ)/640000),((3082410887:ℚ)/10000000000),((187585501:ℚ)/625000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((28877:ℝ)/40000) ((463391:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((463391:ℚ)/640000),((1859:ℚ)/2560),((194018013:ℚ)/625000000),((2905374599:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((463391:ℝ)/640000) ((1859:ℝ)/2560),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((1859:ℚ)/2560),((116867:ℚ)/160000),((125865111:ℚ)/400000000),((1403097601:ℚ)/5000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((1859:ℝ)/2560) ((116867:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((116867:ℚ)/160000),((235093:ℚ)/320000),((3187160023:ℚ)/10000000000),((2596806037:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((116867:ℝ)/160000) ((235093:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((235093:ℚ)/320000),((59113:ℚ)/80000),((1612986509:ℚ)/5000000000),((2369432519:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((235093:ℝ)/320000) ((59113:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((59113:ℚ)/80000),((23917:ℚ)/32000),((1649378667:ℚ)/5000000000),((264786129:ℚ)/1250000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((59113:ℝ)/80000) ((23917:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((23917:ℚ)/32000),((7559:ℚ)/10000),((841387919:ℚ)/2500000000),((748226779:ℚ)/5000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((23917:ℝ)/32000) ((7559:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((26159:ℝ)/40000) ((108713:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((108713:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((108713:ℝ)/160000) ((221503:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((221503:ℝ)/320000) ((447083:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((108713:ℝ)/160000) ((447083:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((447083:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((224221:ℝ)/320000) ((11279:ℝ)/16000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((447083:ℝ)/640000) ((11279:ℝ)/16000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((11279:ℝ)/16000) ((226939:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((226939:ℝ)/320000) ((455237:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node10_14 :
    ∀ r ∈ Set.Icc ((11279:ℝ)/16000) ((455237:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_14
private theorem node7_14 :
    ∀ r ∈ Set.Icc ((447083:ℝ)/640000) ((455237:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_10 node10_14
private theorem node0_14 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((455237:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_14
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((911833:ℝ)/1280000) ((914551:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((455237:ℝ)/640000) ((914551:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((914551:ℝ)/1280000) ((917269:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((917269:ℝ)/1280000) ((460673:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node17_21 :
    ∀ r ∈ Set.Icc ((914551:ℝ)/1280000) ((460673:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_19 node19_21
private theorem node14_21 :
    ∀ r ∈ Set.Icc ((455237:ℝ)/640000) ((460673:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_17 node17_21
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((460673:ℝ)/640000) ((463391:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((463391:ℝ)/640000) ((116867:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node21_25 :
    ∀ r ∈ Set.Icc ((460673:ℝ)/640000) ((116867:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_23 node23_25
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((116867:ℝ)/160000) ((59113:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((59113:ℝ)/80000) ((7559:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node25_29 :
    ∀ r ∈ Set.Icc ((116867:ℝ)/160000) ((7559:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node25_27 node27_29
private theorem node21_29 :
    ∀ r ∈ Set.Icc ((460673:ℝ)/640000) ((7559:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_25 node25_29
private theorem node14_29 :
    ∀ r ∈ Set.Icc ((455237:ℝ)/640000) ((7559:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_21 node21_29
private theorem node0_29 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7559:ℝ)/10000),
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
end N11Formalization.C450SixthRadialC23
#check @N11Formalization.C450SixthRadialC23.bound
#print axioms N11Formalization.C450SixthRadialC23.params_valid
#print axioms N11Formalization.C450SixthRadialC23.params_sum
#print axioms N11Formalization.C450SixthRadialC23.bound
