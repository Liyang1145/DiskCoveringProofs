import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC22
open C450RadialPacketKernel
def params : Params := ⟨((82279331:ℚ)/32000000),((865893:ℚ)/1280000),((12088871:ℚ)/16000000),((-23:ℚ)/5000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((13077:ℚ)/20000),((970970583:ℚ)/5000000000),((60615943:ℚ)/100000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((13077:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((13077:ℚ)/20000),((26831:ℚ)/40000),((2322227901:ℚ)/10000000000),((1045771971:ℚ)/2000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((13077:ℝ)/20000) ((26831:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((26831:ℚ)/40000),((54339:ℚ)/80000),((619619569:ℚ)/2500000000),((595500711:ℚ)/1250000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((26831:ℝ)/40000) ((54339:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((54339:ℚ)/80000),((6877:ℚ)/10000),((2618080723:ℚ)/10000000000),((451517091:ℚ)/1000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((54339:ℝ)/80000) ((6877:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((6877:ℚ)/10000),((110709:ℚ)/160000),((2682539919:ℚ)/10000000000),((4252853199:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((6877:ℝ)/10000) ((110709:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((110709:ℚ)/160000),((55693:ℚ)/80000),((2743815639:ℚ)/10000000000),((1028958679:ℚ)/2500000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((110709:ℝ)/160000) ((55693:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((55693:ℚ)/80000),((223449:ℚ)/320000),((2773334791:ℚ)/10000000000),((1987186627:ℚ)/5000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((55693:ℝ)/80000) ((223449:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((223449:ℚ)/320000),((112063:ℚ)/160000),((2802144293:ℚ)/10000000000),((3901825579:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((223449:ℝ)/320000) ((112063:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((112063:ℚ)/160000),((224803:ℚ)/320000),((1415134567:ℚ)/5000000000),((3827974943:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((112063:ℝ)/160000) ((224803:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((224803:ℚ)/320000),((5637:ℚ)/8000),((1428866391:ℚ)/5000000000),((3752744257:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((224803:ℝ)/320000) ((5637:ℝ)/8000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((5637:ℚ)/8000),((226157:ℚ)/320000),((721139327:ℚ)/2500000000),((3676048621:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((5637:ℝ)/8000) ((226157:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((226157:ℚ)/320000),((113417:ℚ)/160000),((1455381753:ℚ)/5000000000),((1798897087:ℚ)/5000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((226157:ℝ)/320000) ((113417:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((113417:ℚ)/160000),((90869:ℚ)/128000),((2923640907:ℚ)/10000000000),((3517876713:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((113417:ℝ)/160000) ((90869:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((90869:ℚ)/128000),((227511:ℚ)/320000),((734092749:ℚ)/2500000000),((1738629279:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((90869:ℝ)/128000) ((227511:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((227511:ℚ)/320000),((455699:ℚ)/640000),((1474478029:ℚ)/5000000000),((1718090013:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((227511:ℝ)/320000) ((455699:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((455699:ℚ)/640000),((57047:ℚ)/80000),((1480699157:ℚ)/5000000000),((3394624381:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((455699:ℝ)/640000) ((57047:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((57047:ℚ)/80000),((457053:ℚ)/640000),((2973699927:ℚ)/10000000000),((3352573859:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((57047:ℝ)/80000) ((457053:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((457053:ℚ)/640000),((45773:ℚ)/64000),((2985863:ℚ)/10000000),((132400383:ℚ)/400000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((457053:ℝ)/640000) ((45773:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((45773:ℚ)/64000),((458407:ℚ)/640000),((2997889581:ℚ)/10000000000),((51045491:ℚ)/156250000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((45773:ℝ)/64000) ((458407:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((458407:ℚ)/640000),((114771:ℚ)/160000),((1504890833:ℚ)/5000000000),((201453623:ℚ)/625000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((458407:ℝ)/640000) ((114771:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((114771:ℚ)/160000),((230219:ℚ)/320000),((121326803:ℚ)/400000000),((3179026307:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((114771:ℝ)/160000) ((230219:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((230219:ℚ)/320000),((14431:ℚ)/20000),((3056043191:ℚ)/10000000000),((386091073:ℚ)/1250000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((230219:ℝ)/320000) ((14431:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((14431:ℚ)/20000),((231573:ℚ)/320000),((1539207621:ℚ)/5000000000),((1497899951:ℚ)/5000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((14431:ℝ)/20000) ((231573:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((231573:ℚ)/320000),((929:ℚ)/1280),((310029977:ℚ)/1000000000),((45312299:ℚ)/156250000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((231573:ℝ)/320000) ((929:ℝ)/1280),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((929:ℚ)/1280),((58401:ℚ)/80000),((196416079:ℚ)/625000000),((2800994121:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((929:ℝ)/1280) ((58401:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((58401:ℚ)/80000),((117479:ℚ)/160000),((1591605967:ℚ)/5000000000),((1295998803:ℚ)/5000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((58401:ℝ)/80000) ((117479:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((117479:ℚ)/160000),((29539:ℚ)/40000),((805512911:ℚ)/2500000000),((2365049253:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((117479:ℝ)/160000) ((29539:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((29539:ℚ)/40000),((11951:ℚ)/16000),((823725383:ℚ)/2500000000),((528593513:ℚ)/2500000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((29539:ℝ)/40000) ((11951:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((11951:ℚ)/16000),((3777:ℚ)/5000),((3361776553:ℚ)/10000000000),((46677907:ℚ)/312500000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((11951:ℝ)/16000) ((3777:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((13077:ℝ)/20000) ((54339:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((54339:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((54339:ℝ)/80000) ((110709:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((110709:ℝ)/160000) ((223449:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((54339:ℝ)/80000) ((223449:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((223449:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((112063:ℝ)/160000) ((5637:ℝ)/8000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((223449:ℝ)/320000) ((5637:ℝ)/8000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((5637:ℝ)/8000) ((113417:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((113417:ℝ)/160000) ((227511:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node10_14 :
    ∀ r ∈ Set.Icc ((5637:ℝ)/8000) ((227511:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_14
private theorem node7_14 :
    ∀ r ∈ Set.Icc ((223449:ℝ)/320000) ((227511:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_10 node10_14
private theorem node0_14 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((227511:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_14
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((455699:ℝ)/640000) ((457053:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((227511:ℝ)/320000) ((457053:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((457053:ℝ)/640000) ((458407:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((458407:ℝ)/640000) ((230219:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node17_21 :
    ∀ r ∈ Set.Icc ((457053:ℝ)/640000) ((230219:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_19 node19_21
private theorem node14_21 :
    ∀ r ∈ Set.Icc ((227511:ℝ)/320000) ((230219:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_17 node17_21
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((230219:ℝ)/320000) ((231573:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((231573:ℝ)/320000) ((58401:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node21_25 :
    ∀ r ∈ Set.Icc ((230219:ℝ)/320000) ((58401:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_23 node23_25
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((58401:ℝ)/80000) ((29539:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((29539:ℝ)/40000) ((3777:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node25_29 :
    ∀ r ∈ Set.Icc ((58401:ℝ)/80000) ((3777:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node25_27 node27_29
private theorem node21_29 :
    ∀ r ∈ Set.Icc ((230219:ℝ)/320000) ((3777:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_25 node25_29
private theorem node14_29 :
    ∀ r ∈ Set.Icc ((227511:ℝ)/320000) ((3777:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_21 node21_29
private theorem node0_29 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3777:ℝ)/5000),
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
end N11Formalization.C450SixthRadialC22
#check @N11Formalization.C450SixthRadialC22.bound
#print axioms N11Formalization.C450SixthRadialC22.params_valid
#print axioms N11Formalization.C450SixthRadialC22.params_sum
#print axioms N11Formalization.C450SixthRadialC22.bound
