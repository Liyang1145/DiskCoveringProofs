import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC40
open C450RadialPacketKernel
def params : Params := ⟨((32834355647:ℚ)/12800000000),((8736306753:ℚ)/12800000000),((2715761:ℚ)/4000000),((27:ℚ)/5000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((13127:ℚ)/20000),((1002643751:ℚ)/5000000000),((6288844763:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((13127:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((13127:ℚ)/20000),((26981:ℚ)/40000),((1196870059:ℚ)/5000000000),((1084641631:ℚ)/2000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((13127:ℝ)/20000) ((26981:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((26981:ℚ)/40000),((54689:ℚ)/80000),((1276266497:ℚ)/5000000000),((2470165237:ℚ)/5000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((26981:ℝ)/40000) ((54689:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((54689:ℚ)/80000),((6927:ℚ)/10000),((336737753:ℚ)/1250000000),((4681937299:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((54689:ℝ)/80000) ((6927:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((6927:ℚ)/10000),((111559:ℚ)/160000),((2758992511:ℚ)/10000000000),((4409605607:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((6927:ℝ)/10000) ((111559:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((111559:ℚ)/160000),((56143:ℚ)/80000),((564149617:ℚ)/2000000000),((4267380489:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((111559:ℝ)/160000) ((56143:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((56143:ℚ)/80000),((113013:ℚ)/160000),((1439707809:ℚ)/5000000000),((824112011:ℚ)/2000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((56143:ℝ)/80000) ((113013:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((113013:ℚ)/160000),((226753:ℚ)/320000),((2907659959:ℚ)/10000000000),((793726543:ℚ)/2000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((113013:ℝ)/160000) ((226753:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((226753:ℚ)/320000),((5687:ℚ)/8000),((587042247:ℚ)/2000000000),((1945283637:ℚ)/5000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((226753:ℝ)/320000) ((5687:ℝ)/8000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((5687:ℚ)/8000),((228207:ℚ)/320000),((2962092509:ℚ)/10000000000),((762197217:ℚ)/2000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((5687:ℝ)/8000) ((228207:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((228207:ℚ)/320000),((114467:ℚ)/160000),((2988325513:ℚ)/10000000000),((932447979:ℚ)/2500000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((228207:ℝ)/320000) ((114467:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((114467:ℚ)/160000),((91719:ℚ)/128000),((3001205367:ℚ)/10000000000),((182343841:ℚ)/500000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((114467:ℝ)/160000) ((91719:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((91719:ℚ)/128000),((229661:ℚ)/320000),((11773167:ℚ)/39062500),((901184211:ℚ)/2500000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((91719:ℝ)/128000) ((229661:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((229661:ℚ)/320000),((460049:ℚ)/640000),((378313007:ℚ)/1250000000),((445265051:ℚ)/1250000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((229661:ℝ)/320000) ((460049:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((460049:ℚ)/640000),((57597:ℚ)/80000),((3038927601:ℚ)/10000000000),((27492267:ℚ)/78125000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((460049:ℝ)/640000) ((57597:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((57597:ℚ)/80000),((461503:ℚ)/640000),((47675057:ℚ)/156250000),((3475387743:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((57597:ℝ)/80000) ((461503:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((461503:ℚ)/640000),((46223:ℚ)/64000),((612666879:ℚ)/2000000000),((3431233547:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((461503:ℝ)/640000) ((46223:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((46223:ℚ)/64000),((462957:ℚ)/640000),((1537660993:ℚ)/5000000000),((3386526759:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((46223:ℝ)/64000) ((462957:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((462957:ℚ)/640000),((115921:ℚ)/160000),((617433701:ℚ)/2000000000),((3341245169:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((462957:ℝ)/640000) ((115921:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((115921:ℚ)/160000),((464411:ℚ)/640000),((1549437993:ℚ)/5000000000),((3295365053:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((115921:ℝ)/160000) ((464411:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((464411:ℚ)/640000),((232569:ℚ)/320000),((388805801:ℚ)/1250000000),((129954441:ℚ)/400000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((464411:ℝ)/640000) ((232569:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((232569:ℚ)/320000),((93173:ℚ)/128000),((3121881703:ℚ)/10000000000),((3201705869:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((232569:ℝ)/320000) ((93173:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((93173:ℚ)/128000),((14581:ℚ)/20000),((3133183753:ℚ)/10000000000),((788467587:ℚ)/2500000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((93173:ℝ)/128000) ((14581:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((14581:ℚ)/20000),((234023:ℚ)/320000),((1577697709:ℚ)/5000000000),((310532299:ℚ)/1000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((14581:ℝ)/20000) ((234023:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((234023:ℚ)/320000),((939:ℚ)/1280),((1588547783:ℚ)/5000000000),((3005954179:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((234023:ℝ)/320000) ((939:ℝ)/1280),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((939:ℚ)/1280),((235477:ℚ)/320000),((399787211:ℚ)/1250000000),((2903292599:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((939:ℝ)/1280) ((235477:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((235477:ℚ)/320000),((59051:ℚ)/80000),((804753663:ℚ)/2500000000),((111879017:ℚ)/400000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((235477:ℝ)/320000) ((59051:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((59051:ℚ)/80000),((118829:ℚ)/160000),((3259041693:ℚ)/10000000000),((1343284209:ℚ)/5000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((59051:ℝ)/80000) ((118829:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((118829:ℚ)/160000),((29889:ℚ)/40000),((3297268589:ℚ)/10000000000),((2451253709:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((118829:ℝ)/160000) ((29889:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((29889:ℚ)/40000),((12101:ℚ)/16000),((105270369:ℚ)/312500000),((2191365023:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((29889:ℝ)/40000) ((12101:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((12101:ℚ)/16000),((3827:ℚ)/5000),((3433760123:ℚ)/10000000000),((193496951:ℚ)/1250000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((12101:ℝ)/16000) ((3827:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((13127:ℝ)/20000) ((54689:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((54689:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((54689:ℝ)/80000) ((111559:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((111559:ℝ)/160000) ((113013:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((54689:ℝ)/80000) ((113013:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((113013:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((113013:ℝ)/160000) ((5687:ℝ)/8000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((5687:ℝ)/8000) ((114467:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node7_11 :
    ∀ r ∈ Set.Icc ((113013:ℝ)/160000) ((114467:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_9 node9_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((114467:ℝ)/160000) ((229661:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((229661:ℝ)/320000) ((57597:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node11_15 :
    ∀ r ∈ Set.Icc ((114467:ℝ)/160000) ((57597:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_15
private theorem node7_15 :
    ∀ r ∈ Set.Icc ((113013:ℝ)/160000) ((57597:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node7_11 node11_15
private theorem node0_15 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((57597:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_15
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((57597:ℝ)/80000) ((46223:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((46223:ℝ)/64000) ((115921:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node15_19 :
    ∀ r ∈ Set.Icc ((57597:ℝ)/80000) ((115921:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_17 node17_19
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((115921:ℝ)/160000) ((232569:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((232569:ℝ)/320000) ((14581:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node19_23 :
    ∀ r ∈ Set.Icc ((115921:ℝ)/160000) ((14581:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_21 node21_23
private theorem node15_23 :
    ∀ r ∈ Set.Icc ((57597:ℝ)/80000) ((14581:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_19 node19_23
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((14581:ℝ)/20000) ((939:ℝ)/1280),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((939:ℝ)/1280) ((59051:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node23_27 :
    ∀ r ∈ Set.Icc ((14581:ℝ)/20000) ((59051:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node23_25 node25_27
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((59051:ℝ)/80000) ((29889:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node29_31 :
    ∀ r ∈ Set.Icc ((29889:ℝ)/40000) ((3827:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf29 leaf30
private theorem node27_31 :
    ∀ r ∈ Set.Icc ((59051:ℝ)/80000) ((3827:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node27_29 node29_31
private theorem node23_31 :
    ∀ r ∈ Set.Icc ((14581:ℝ)/20000) ((3827:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node23_27 node27_31
private theorem node15_31 :
    ∀ r ∈ Set.Icc ((57597:ℝ)/80000) ((3827:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_23 node23_31
private theorem node0_31 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3827:ℝ)/5000),
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
end N11Formalization.C450SixthRadialC40
#check @N11Formalization.C450SixthRadialC40.bound
#print axioms N11Formalization.C450SixthRadialC40.params_valid
#print axioms N11Formalization.C450SixthRadialC40.params_sum
#print axioms N11Formalization.C450SixthRadialC40.bound
