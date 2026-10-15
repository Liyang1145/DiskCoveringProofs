import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC52
open C450RadialPacketKernel
def params : Params := ⟨((261918284617:ℚ)/102400000000),((70647014583:ℚ)/102400000000),((2538533:ℚ)/4000000),((129:ℚ)/10000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((26329:ℚ)/40000),((1025460417:ℚ)/5000000000),((1613680511:ℚ)/2500000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((26329:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((26329:ℚ)/40000),((54187:ℚ)/80000),((2444964019:ℚ)/10000000000),((695618439:ℚ)/1250000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((26329:ℝ)/40000) ((54187:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((54187:ℚ)/80000),((109903:ℚ)/160000),((2605415283:ℚ)/10000000000),((253443607:ℚ)/500000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((54187:ℝ)/80000) ((109903:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((109903:ℚ)/160000),((13929:ℚ)/20000),((109914789:ℚ)/400000000),((2401743121:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((109903:ℝ)/160000) ((13929:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((13929:ℚ)/20000),((224393:ℚ)/320000),((1406658397:ℚ)/5000000000),((904766591:ℚ)/2000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((13929:ℝ)/20000) ((224393:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((224393:ℚ)/320000),((112961:ℚ)/160000),((1437658543:ℚ)/5000000000),((273612673:ℚ)/625000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((224393:ℝ)/320000) ((112961:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((112961:ℚ)/160000),((227451:ℚ)/320000),((1467062597:ℚ)/5000000000),((845413419:ℚ)/2000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((112961:ℝ)/160000) ((227451:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((227451:ℚ)/320000),((456431:ℚ)/640000),((2962402927:ℚ)/10000000000),((4071101461:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((227451:ℝ)/320000) ((456431:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((456431:ℚ)/640000),((11449:ℚ)/16000),((2989964047:ℚ)/10000000000),((159638641:ℚ)/400000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((456431:ℝ)/640000) ((11449:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((11449:ℚ)/16000),((459489:ℚ)/640000),((3016832349:ℚ)/10000000000),((1954639027:ℚ)/5000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((11449:ℝ)/16000) ((459489:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((459489:ℚ)/640000),((920507:ℚ)/1280000),((3030013751:ℚ)/10000000000),((765187573:ℚ)/2000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((459489:ℝ)/640000) ((920507:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((920507:ℚ)/1280000),((230509:ℚ)/320000),((190189391:ℚ)/625000000),((5911897:ℚ)/15625000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((920507:ℝ)/1280000) ((230509:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((230509:ℚ)/320000),((184713:ℚ)/256000),((3055884469:ℚ)/10000000000),((3740834789:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((230509:ℝ)/320000) ((184713:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((184713:ℚ)/256000),((462547:ℚ)/640000),((767144731:ℚ)/2500000000),((462198019:ℚ)/1250000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((184713:ℝ)/256000) ((462547:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((462547:ℚ)/640000),((926623:ℚ)/1280000),((1540558043:ℚ)/5000000000),((18269227:ℚ)/50000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((462547:ℝ)/640000) ((926623:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((926623:ℚ)/1280000),((74191:ℚ)/102400),((3087326433:ℚ)/10000000000),((3609600757:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((926623:ℝ)/1280000) ((74191:ℝ)/102400),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((74191:ℚ)/102400),((116019:ℚ)/160000),((61869967:ℚ)/200000000),((28698263:ℚ)/80000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((74191:ℝ)/102400) ((116019:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((116019:ℚ)/160000),((1857833:ℚ)/2560000),((3099632127:ℚ)/10000000000),((712966271:ℚ)/2000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((116019:ℝ)/160000) ((1857833:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((1857833:ℚ)/2560000),((929681:ℚ)/1280000),((3105728049:ℚ)/10000000000),((3542243651:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((1857833:ℝ)/2560000) ((929681:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((929681:ℚ)/1280000),((1860891:ℚ)/2560000),((3111786399:ℚ)/10000000000),((1759758569:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((929681:ℝ)/1280000) ((1860891:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1860891:ℚ)/2560000),((93121:ℚ)/128000),((3117807453:ℚ)/10000000000),((218540569:ℚ)/625000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1860891:ℝ)/2560000) ((93121:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((93121:ℚ)/128000),((1863949:ℚ)/2560000),((24404621:ℚ)/78125000),((3473636751:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((93121:ℝ)/128000) ((1863949:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((1863949:ℚ)/2560000),((932739:ℚ)/1280000),((3129738773:ℚ)/10000000000),((3450477187:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((1863949:ℝ)/2560000) ((932739:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((932739:ℚ)/1280000),((1867007:ℚ)/2560000),((3135649577:ℚ)/10000000000),((3427167423:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((932739:ℝ)/1280000) ((1867007:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((1867007:ℚ)/2560000),((233567:ℚ)/320000),((1570762081:ℚ)/5000000000),((340370437:ℚ)/1000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((1867007:ℝ)/2560000) ((233567:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((233567:ℚ)/320000),((374013:ℚ)/512000),((3147362789:ℚ)/10000000000),((3380084831:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((233567:ℝ)/320000) ((374013:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((374013:ℚ)/512000),((935797:ℚ)/1280000),((3153165717:ℚ)/10000000000),((3356305499:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((374013:ℝ)/512000) ((935797:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((935797:ℚ)/1280000),((1873123:ℚ)/2560000),((3158933197:ℚ)/10000000000),((833090737:ℚ)/2500000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((935797:ℝ)/1280000) ((1873123:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((1873123:ℚ)/2560000),((468663:ℚ)/640000),((1582332741:ℚ)/5000000000),((3308253631:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((1873123:ℝ)/2560000) ((468663:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((468663:ℚ)/640000),((1876181:ℚ)/2560000),((1585181409:ℚ)/5000000000),((328397387:ℚ)/1000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((468663:ℝ)/640000) ((1876181:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((1876181:ℚ)/2560000),((187771:ℚ)/256000),((63520509:ℚ)/200000000),((814879963:ℚ)/2500000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((1876181:ℝ)/2560000) ((187771:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((187771:ℚ)/256000),((1879239:ℚ)/2560000),((159082681:ℚ)/500000000),((3234887621:ℚ)/10000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((187771:ℝ)/256000) ((1879239:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((1879239:ℚ)/2560000),((29387:ℚ)/40000),((637449513:ℚ)/2000000000),((321007307:ℚ)/1000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((1879239:ℝ)/2560000) ((29387:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((29387:ℚ)/40000),((941913:ℚ)/1280000),((1599166861:ℚ)/5000000000),((3185071933:ℚ)/10000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((29387:ℝ)/40000) ((941913:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((941913:ℚ)/1280000),((471721:ℚ)/640000),((3209285769:ℚ)/10000000000),((626898399:ℚ)/2000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((941913:ℝ)/1280000) ((471721:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((471721:ℚ)/640000),((944971:ℚ)/1280000),((402513189:ℚ)/1250000000),((770777539:ℚ)/2500000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((471721:ℝ)/640000) ((944971:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((944971:ℚ)/1280000),((1893:ℚ)/2560),((3230794711:ℚ)/10000000000),((757721399:ℚ)/2500000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((944971:ℝ)/1280000) ((1893:ℝ)/2560),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((1893:ℚ)/2560),((948029:ℚ)/1280000),((3241355087:ℚ)/10000000000),((2977773941:ℚ)/10000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((1893:ℝ)/2560) ((948029:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((948029:ℚ)/1280000),((474779:ℚ)/640000),((3251788319:ℚ)/10000000000),((365465851:ℚ)/1250000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((948029:ℝ)/1280000) ((474779:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((474779:ℚ)/640000),((119077:ℚ)/160000),((1636139937:ℚ)/5000000000),((1434345643:ℚ)/5000000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((474779:ℝ)/640000) ((119077:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((119077:ℚ)/160000),((477837:ℚ)/640000),((3292282057:ℚ)/10000000000),((2755416963:ℚ)/10000000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((119077:ℝ)/160000) ((477837:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((477837:ℚ)/640000),((239683:ℚ)/320000),((1655903491:ℚ)/5000000000),((2637410611:ℚ)/10000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((477837:ℝ)/640000) ((239683:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((239683:ℚ)/320000),((60303:ℚ)/80000),((3349470901:ℚ)/10000000000),((157125351:ℚ)/625000000)⟩
theorem valid42 : Valid params packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((239683:ℝ)/320000) ((60303:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((60303:ℚ)/80000),((24427:ℚ)/32000),((3419549663:ℚ)/10000000000),((2247404853:ℚ)/10000000000)⟩
theorem valid43 : Valid params packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((60303:ℝ)/80000) ((24427:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((24427:ℚ)/32000),((7729:ℚ)/10000),((870782783:ℚ)/2500000000),((317495863:ℚ)/2000000000)⟩
theorem valid44 : Valid params packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((24427:ℝ)/32000) ((7729:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((54187:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((109903:ℝ)/160000) ((224393:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((54187:ℝ)/80000) ((224393:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((224393:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((112961:ℝ)/160000) ((456431:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((224393:ℝ)/320000) ((456431:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((11449:ℝ)/16000) ((920507:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((456431:ℝ)/640000) ((920507:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((224393:ℝ)/320000) ((920507:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((920507:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((920507:ℝ)/1280000) ((184713:ℝ)/256000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((462547:ℝ)/640000) ((74191:ℝ)/102400),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node13_16 :
    ∀ r ∈ Set.Icc ((184713:ℝ)/256000) ((74191:ℝ)/102400),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 node14_16
private theorem node11_16 :
    ∀ r ∈ Set.Icc ((920507:ℝ)/1280000) ((74191:ℝ)/102400),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((116019:ℝ)/160000) ((929681:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((74191:ℝ)/102400) ((929681:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((1860891:ℝ)/2560000) ((1863949:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node19_22 :
    ∀ r ∈ Set.Icc ((929681:ℝ)/1280000) ((1863949:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 node20_22
private theorem node16_22 :
    ∀ r ∈ Set.Icc ((74191:ℝ)/102400) ((1863949:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_19 node19_22
private theorem node11_22 :
    ∀ r ∈ Set.Icc ((920507:ℝ)/1280000) ((1863949:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_16 node16_22
private theorem node0_22 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1863949:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((1863949:ℝ)/2560000) ((1867007:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((233567:ℝ)/320000) ((935797:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node24_27 :
    ∀ r ∈ Set.Icc ((1867007:ℝ)/2560000) ((935797:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 node25_27
private theorem node22_27 :
    ∀ r ∈ Set.Icc ((1863949:ℝ)/2560000) ((935797:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((1873123:ℝ)/2560000) ((1876181:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((935797:ℝ)/1280000) ((1876181:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((187771:ℝ)/256000) ((29387:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((1876181:ℝ)/2560000) ((29387:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node27_33 :
    ∀ r ∈ Set.Icc ((935797:ℝ)/1280000) ((29387:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node27_30 node30_33
private theorem node22_33 :
    ∀ r ∈ Set.Icc ((1863949:ℝ)/2560000) ((29387:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_27 node27_33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((941913:ℝ)/1280000) ((944971:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 leaf35
private theorem node33_36 :
    ∀ r ∈ Set.Icc ((29387:ℝ)/40000) ((944971:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 node34_36
private theorem node37_39 :
    ∀ r ∈ Set.Icc ((1893:ℝ)/2560) ((474779:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 leaf38
private theorem node36_39 :
    ∀ r ∈ Set.Icc ((944971:ℝ)/1280000) ((474779:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 node37_39
private theorem node33_39 :
    ∀ r ∈ Set.Icc ((29387:ℝ)/40000) ((474779:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_36 node36_39
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((119077:ℝ)/160000) ((239683:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 leaf41
private theorem node39_42 :
    ∀ r ∈ Set.Icc ((474779:ℝ)/640000) ((239683:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 node40_42
private theorem node43_45 :
    ∀ r ∈ Set.Icc ((60303:ℝ)/80000) ((7729:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf43 leaf44
private theorem node42_45 :
    ∀ r ∈ Set.Icc ((239683:ℝ)/320000) ((7729:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf42 node43_45
private theorem node39_45 :
    ∀ r ∈ Set.Icc ((474779:ℝ)/640000) ((7729:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node39_42 node42_45
private theorem node33_45 :
    ∀ r ∈ Set.Icc ((29387:ℝ)/40000) ((7729:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_39 node39_45
private theorem node22_45 :
    ∀ r ∈ Set.Icc ((1863949:ℝ)/2560000) ((7729:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_33 node33_45
private theorem node0_45 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7729:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_22 node22_45
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_45
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC52
#check @N11Formalization.C450SixthRadialC52.bound
#print axioms N11Formalization.C450SixthRadialC52.params_valid
#print axioms N11Formalization.C450SixthRadialC52.params_sum
#print axioms N11Formalization.C450SixthRadialC52.bound
