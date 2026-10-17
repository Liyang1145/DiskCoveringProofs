import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC39
open C450RadialPacketKernel
def params : Params := ⟨((8210033869:ℚ)/3200000000),((2182631731:ℚ)/3200000000),((273053:ℚ)/400000),((191:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((104991:ℚ)/160000),((400282863:ℚ)/2000000000),((3137425609:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((104991:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((104991:ℚ)/160000),((215773:ℚ)/320000),((597345241:ℚ)/2500000000),((5411246149:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((104991:ℝ)/160000) ((215773:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((215773:ℚ)/320000),((437337:ℚ)/640000),((2548026287:ℚ)/10000000000),((2464740103:ℚ)/5000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((215773:ℝ)/320000) ((437337:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((437337:ℚ)/640000),((55391:ℚ)/80000),((53785917:ℚ)/200000000),((583959541:ℚ)/1250000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((437337:ℝ)/640000) ((55391:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55391:ℚ)/80000),((892047:ℚ)/1280000),((2754352223:ℚ)/10000000000),((2199980911:ℚ)/5000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55391:ℝ)/80000) ((892047:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((892047:ℚ)/1280000),((448919:ℚ)/640000),((2816083067:ℚ)/10000000000),((1064514381:ℚ)/2500000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((892047:ℝ)/1280000) ((448919:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((448919:ℚ)/640000),((903629:ℚ)/1280000),((287473461:ℚ)/1000000000),((822313449:ℚ)/2000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((448919:ℝ)/640000) ((903629:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((903629:ℚ)/1280000),((1813049:ℚ)/2560000),((2902974051:ℚ)/10000000000),((1979990241:ℚ)/5000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((903629:ℝ)/1280000) ((1813049:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1813049:ℚ)/2560000),((45471:ℚ)/64000),((2930522403:ℚ)/10000000000),((970522409:ℚ)/2500000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1813049:ℝ)/2560000) ((45471:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45471:ℚ)/64000),((1824631:ℚ)/2560000),((739350667:ℚ)/2500000000),((3802686157:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45471:ℝ)/64000) ((1824631:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1824631:ℚ)/2560000),((915211:ℚ)/1280000),((1491818259:ℚ)/5000000000),((186083651:ℚ)/500000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1824631:ℝ)/2560000) ((915211:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((915211:ℚ)/1280000),((733327:ℚ)/1024000),((1498258737:ℚ)/5000000000),((909735627:ℚ)/2500000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((915211:ℝ)/1280000) ((733327:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((733327:ℚ)/1024000),((1836213:ℚ)/2560000),((752311101:ℚ)/2500000000),((1798448117:ℚ)/5000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((733327:ℝ)/1024000) ((1836213:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((1836213:ℚ)/2560000),((3678217:ℚ)/5120000),((3021819691:ℚ)/10000000000),((444296811:ℚ)/1250000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((1836213:ℝ)/2560000) ((3678217:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((3678217:ℚ)/5120000),((460501:ℚ)/640000),((3034245651:ℚ)/10000000000),((109729999:ℚ)/312500000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((3678217:ℝ)/5120000) ((460501:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((460501:ℚ)/640000),((3689799:ℚ)/5120000),((3046524537:ℚ)/10000000000),((3467834311:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((460501:ℝ)/640000) ((3689799:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((3689799:ℚ)/5120000),((369559:ℚ)/512000),((3058658543:ℚ)/10000000000),((684755599:ℚ)/2000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((3689799:ℝ)/5120000) ((369559:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((369559:ℚ)/512000),((3701381:ℚ)/5120000),((767662451:ℚ)/2500000000),((3379170237:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((369559:ℝ)/512000) ((3701381:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((3701381:ℚ)/5120000),((926793:ℚ)/1280000),((3082500403:ℚ)/10000000000),((416748609:ℚ)/1250000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((3701381:ℝ)/5120000) ((926793:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((926793:ℚ)/1280000),((3712963:ℚ)/5120000),((618842473:ℚ)/2000000000),((3288210229:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((926793:ℝ)/1280000) ((3712963:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((3712963:ℚ)/5120000),((1859377:ℚ)/2560000),((621157533:ℚ)/2000000000),((129672359:ℚ)/400000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((3712963:ℝ)/5120000) ((1859377:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((1859377:ℚ)/2560000),((744909:ℚ)/1024000),((311722823:ℚ)/1000000000),((49918093:ℚ)/156250000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((1859377:ℝ)/2560000) ((744909:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((744909:ℚ)/1024000),((116573:ℚ)/160000),((3128535937:ℚ)/10000000000),((1573513993:ℚ)/5000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((744909:ℝ)/1024000) ((116573:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((116573:ℚ)/160000),((1870959:ℚ)/2560000),((630152011:ℚ)/2000000000),((387323459:ℚ)/1250000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((116573:ℝ)/160000) ((1870959:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((1870959:ℚ)/2560000),((7507:ℚ)/10240),((99139817:ℚ)/312500000),((187464857:ℚ)/625000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((1870959:ℝ)/2560000) ((7507:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((7507:ℚ)/10240),((1882541:ℚ)/2560000),((1596845829:ℚ)/5000000000),((289700189:ℚ)/1000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((7507:ℝ)/10240) ((1882541:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((1882541:ℚ)/2560000),((472083:ℚ)/640000),((3214425431:ℚ)/10000000000),((1395459079:ℚ)/5000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((1882541:ℝ)/2560000) ((472083:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((472083:ℚ)/640000),((949957:ℚ)/1280000),((3254490207:ℚ)/10000000000),((536150641:ℚ)/2000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((472083:ℝ)/640000) ((949957:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((949957:ℚ)/1280000),((238937:ℚ)/320000),((823190031:ℚ)/2500000000),((2445953213:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((949957:ℝ)/1280000) ((238937:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((238937:ℚ)/320000),((96733:ℚ)/128000),((3364244343:ℚ)/10000000000),((2186631277:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((238937:ℝ)/320000) ((96733:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((96733:ℚ)/128000),((30591:ℚ)/40000),((3429472287:ℚ)/10000000000),((1544638403:ℚ)/10000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((96733:ℝ)/128000) ((30591:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((104991:ℝ)/160000) ((437337:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((437337:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((437337:ℝ)/640000) ((892047:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((892047:ℝ)/1280000) ((903629:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((437337:ℝ)/640000) ((903629:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((903629:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((903629:ℝ)/1280000) ((45471:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((45471:ℝ)/64000) ((915211:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node7_11 :
    ∀ r ∈ Set.Icc ((903629:ℝ)/1280000) ((915211:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_9 node9_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((915211:ℝ)/1280000) ((1836213:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((1836213:ℝ)/2560000) ((460501:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node11_15 :
    ∀ r ∈ Set.Icc ((915211:ℝ)/1280000) ((460501:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_15
private theorem node7_15 :
    ∀ r ∈ Set.Icc ((903629:ℝ)/1280000) ((460501:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_11 node11_15
private theorem node0_15 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((460501:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_15
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((460501:ℝ)/640000) ((369559:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((369559:ℝ)/512000) ((926793:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node15_19 :
    ∀ r ∈ Set.Icc ((460501:ℝ)/640000) ((926793:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_17 node17_19
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((926793:ℝ)/1280000) ((1859377:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((1859377:ℝ)/2560000) ((116573:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node19_23 :
    ∀ r ∈ Set.Icc ((926793:ℝ)/1280000) ((116573:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_21 node21_23
private theorem node15_23 :
    ∀ r ∈ Set.Icc ((460501:ℝ)/640000) ((116573:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_19 node19_23
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((116573:ℝ)/160000) ((7507:ℝ)/10240),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((7507:ℝ)/10240) ((472083:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node23_27 :
    ∀ r ∈ Set.Icc ((116573:ℝ)/160000) ((472083:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node23_25 node25_27
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((472083:ℝ)/640000) ((238937:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node29_31 :
    ∀ r ∈ Set.Icc ((238937:ℝ)/320000) ((30591:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf29 leaf30
private theorem node27_31 :
    ∀ r ∈ Set.Icc ((472083:ℝ)/640000) ((30591:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node27_29 node29_31
private theorem node23_31 :
    ∀ r ∈ Set.Icc ((116573:ℝ)/160000) ((30591:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node23_27 node27_31
private theorem node15_31 :
    ∀ r ∈ Set.Icc ((460501:ℝ)/640000) ((30591:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_23 node23_31
private theorem node0_31 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((30591:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_15 node15_31
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_31
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC39
#check @N11Formalization.C450SixthRadialC39.bound
#print axioms N11Formalization.C450SixthRadialC39.params_valid
#print axioms N11Formalization.C450SixthRadialC39.params_sum
#print axioms N11Formalization.C450SixthRadialC39.bound
