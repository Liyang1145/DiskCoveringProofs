import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FifthRadialC14
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((339853:ℚ)/500000),((124821:ℚ)/200000),((383:ℚ)/31250)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((41129:ℚ)/62500),((409412451:ℚ)/2000000000),((3220311513:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((41129:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((41129:ℚ)/62500),((84637:ℚ)/125000),((1220321247:ℚ)/5000000000),((173528257:ℚ)/312500000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((41129:ℝ)/62500) ((84637:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((84637:ℚ)/125000),((10877:ℚ)/15625),((2743328237:ℚ)/10000000000),((5057952011:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((84637:ℝ)/125000) ((10877:ℝ)/15625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((10877:ℚ)/15625),((176411:ℚ)/250000),((717682851:ℚ)/2500000000),((564266303:ℚ)/1250000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((10877:ℝ)/15625) ((176411:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((176411:ℚ)/250000),((355201:ℚ)/500000),((2929531083:ℚ)/10000000000),((1054505259:ℚ)/2500000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((176411:ℝ)/250000) ((355201:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((355201:ℚ)/500000),((17879:ℚ)/25000),((2985369817:ℚ)/10000000000),((162495949:ℚ)/400000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((355201:ℝ)/500000) ((17879:ℝ)/25000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((17879:ℚ)/25000),((717539:ℚ)/1000000),((3012241013:ℚ)/10000000000),((1950465187:ℚ)/5000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((17879:ℝ)/25000) ((717539:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((717539:ℚ)/1000000),((359959:ℚ)/500000),((3038443703:ℚ)/10000000000),((3817772597:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((717539:ℝ)/1000000) ((359959:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((359959:ℚ)/500000),((722297:ℚ)/1000000),((3063998989:ℚ)/10000000000),((58325867:ℚ)/156250000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((359959:ℝ)/500000) ((722297:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((722297:ℚ)/1000000),((1446973:ℚ)/2000000),((3076540129:ℚ)/10000000000),((91151397:ℚ)/250000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((722297:ℝ)/1000000) ((1446973:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1446973:ℚ)/2000000),((181169:ℚ)/250000),((772231703:ℚ)/2500000000),((3601907647:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1446973:ℝ)/2000000) ((181169:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((181169:ℚ)/250000),((1451731:ℚ)/2000000),((1550580681:ℚ)/5000000000),((3557235719:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((181169:ℝ)/250000) ((1451731:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((1451731:ℚ)/2000000),((145411:ℚ)/200000),((778311511:ℚ)/2500000000),((3512020083:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((1451731:ℝ)/2000000) ((145411:ℝ)/200000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((145411:ℚ)/200000),((1456489:ℚ)/2000000),((1562591531:ℚ)/5000000000),((3466239427:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((145411:ℝ)/200000) ((1456489:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1456489:ℚ)/2000000),((364717:ℚ)/500000),((784243641:ℚ)/2500000000),((341987103:ℚ)/1000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1456489:ℝ)/2000000) ((364717:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((364717:ℚ)/500000),((1461247:ℚ)/2000000),((1574311321:ℚ)/5000000000),((1686445309:ℚ)/5000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((364717:ℝ)/500000) ((1461247:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((1461247:ℚ)/2000000),((731813:ℚ)/1000000),((632025867:ℚ)/2000000000),((3325272219:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((1461247:ℝ)/2000000) ((731813:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((731813:ℚ)/1000000),((293201:ℚ)/400000),((3171496629:ℚ)/10000000000),((1638493993:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((731813:ℝ)/1000000) ((293201:ℝ)/400000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((293201:ℚ)/400000),((45887:ℚ)/62500),((3182726463:ℚ)/10000000000),((403501001:ℚ)/1250000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((293201:ℝ)/400000) ((45887:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((45887:ℚ)/62500),((1470763:ℚ)/2000000),((399227591:ℚ)/1250000000),((635660017:ℚ)/2000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((45887:ℝ)/62500) ((1470763:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1470763:ℚ)/2000000),((736571:ℚ)/1000000),((3204781267:ℚ)/10000000000),((781957369:ℚ)/2500000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1470763:ℝ)/2000000) ((736571:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((736571:ℚ)/1000000),((1475521:ℚ)/2000000),((3215609881:ℚ)/10000000000),((307655861:ℚ)/1000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((736571:ℝ)/1000000) ((1475521:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((1475521:ℚ)/2000000),((14779:ℚ)/20000),((129052333:ℚ)/400000000),((3024446753:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((1475521:ℝ)/2000000) ((14779:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((14779:ℚ)/20000),((741329:ℚ)/1000000),((3247321527:ℚ)/10000000000),((2971449623:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((14779:ℝ)/20000) ((741329:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((741329:ℚ)/1000000),((185927:ℚ)/250000),((81695853:ℚ)/250000000),((1431300951:ℚ)/5000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((741329:ℝ)/1000000) ((185927:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((185927:ℚ)/250000),((746087:ℚ)/1000000),((2630287:ℚ)/8000000),((54991423:ℚ)/200000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((185927:ℝ)/250000) ((746087:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((746087:ℚ)/1000000),((374233:ℚ)/500000),((3307407499:ℚ)/10000000000),((2631818139:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((746087:ℝ)/1000000) ((374233:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((374233:ℚ)/500000),((94153:ℚ)/125000),((3345123077:ℚ)/10000000000),((2508677653:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((374233:ℝ)/500000) ((94153:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((94153:ℚ)/125000),((38137:ℚ)/50000),((683064083:ℚ)/2000000000),((2242646953:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((94153:ℝ)/125000) ((38137:ℝ)/50000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((38137:ℚ)/50000),((24133:ℚ)/31250),((139161579:ℚ)/400000000),((1584125609:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((38137:ℝ)/50000) ((24133:ℝ)/31250),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((41129:ℝ)/62500) ((10877:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((10877:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((10877:ℝ)/15625) ((355201:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((355201:ℝ)/500000) ((717539:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((10877:ℝ)/15625) ((717539:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((717539:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((717539:ℝ)/1000000) ((722297:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((722297:ℝ)/1000000) ((181169:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node7_11 :
    ∀ r ∈ Set.Icc ((717539:ℝ)/1000000) ((181169:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_9 node9_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((181169:ℝ)/250000) ((145411:ℝ)/200000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((145411:ℝ)/200000) ((364717:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node11_15 :
    ∀ r ∈ Set.Icc ((181169:ℝ)/250000) ((364717:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_15
private theorem node7_15 :
    ∀ r ∈ Set.Icc ((717539:ℝ)/1000000) ((364717:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_11 node11_15
private theorem node0_15 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((364717:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((1461247:ℝ)/2000000) ((293201:ℝ)/400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((364717:ℝ)/500000) ((293201:ℝ)/400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((293201:ℝ)/400000) ((1470763:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((1470763:ℝ)/2000000) ((1475521:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node18_22 :
    ∀ r ∈ Set.Icc ((293201:ℝ)/400000) ((1475521:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node18_20 node20_22
private theorem node15_22 :
    ∀ r ∈ Set.Icc ((364717:ℝ)/500000) ((1475521:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_18 node18_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((1475521:ℝ)/2000000) ((741329:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((741329:ℝ)/1000000) ((746087:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node22_26 :
    ∀ r ∈ Set.Icc ((1475521:ℝ)/2000000) ((746087:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_26
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((746087:ℝ)/1000000) ((94153:ℝ)/125000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((94153:ℝ)/125000) ((24133:ℝ)/31250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node26_30 :
    ∀ r ∈ Set.Icc ((746087:ℝ)/1000000) ((24133:ℝ)/31250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node26_28 node28_30
private theorem node22_30 :
    ∀ r ∈ Set.Icc ((1475521:ℝ)/2000000) ((24133:ℝ)/31250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_26 node26_30
private theorem node15_30 :
    ∀ r ∈ Set.Icc ((364717:ℝ)/500000) ((24133:ℝ)/31250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_22 node22_30
private theorem node0_30 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((24133:ℝ)/31250),
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
end N11Formalization.C450FifthRadialC14
#check @N11Formalization.C450FifthRadialC14.bound
#print axioms N11Formalization.C450FifthRadialC14.params_valid
#print axioms N11Formalization.C450FifthRadialC14.bound
