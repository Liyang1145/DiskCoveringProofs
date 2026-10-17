import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ThirdRadialNeg2
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((338529:ℚ)/500000),((1139:ℚ)/1600),((1:ℚ)/15625)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((81877:ℚ)/125000),((1971856693:ℚ)/10000000000),((3084244931:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((81877:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((81877:ℚ)/125000),((168131:ℚ)/250000),((1178028551:ℚ)/5000000000),((2660151119:ℚ)/5000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((81877:ℝ)/125000) ((168131:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((168131:ℚ)/250000),((340639:ℚ)/500000),((628385551:ℚ)/2500000000),((4846978161:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((168131:ℝ)/250000) ((340639:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((340639:ℚ)/500000),((43127:ℚ)/62500),((66350393:ℚ)/250000000),((35887893:ℚ)/78125000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((340639:ℝ)/500000) ((43127:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((43127:ℚ)/62500),((694409:ℚ)/1000000),((54375847:ℚ)/200000000),((540828063:ℚ)/1250000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((43127:ℝ)/62500) ((694409:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((694409:ℚ)/1000000),((349393:ℚ)/500000),((347539317:ℚ)/1250000000),((523394723:ℚ)/1250000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((694409:ℝ)/1000000) ((349393:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((349393:ℚ)/500000),((703163:ℚ)/1000000),((2838823591:ℚ)/10000000000),((4043176229:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((349393:ℝ)/500000) ((703163:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((703163:ℚ)/1000000),((1410703:ℚ)/2000000),((2867015231:ℚ)/10000000000),((486772203:ℚ)/1250000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((703163:ℝ)/1000000) ((1410703:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1410703:ℚ)/2000000),((35377:ℚ)/50000),((1447265371:ℚ)/5000000000),((3817613669:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1410703:ℝ)/2000000) ((35377:ℝ)/50000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((35377:ℚ)/50000),((1419457:ℚ)/2000000),((2921392661:ℚ)/10000000000),((934890203:ℚ)/2500000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((35377:ℝ)/50000) ((1419457:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1419457:ℚ)/2000000),((711917:ℚ)/1000000),((2947622221:ℚ)/10000000000),((1829961803:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1419457:ℝ)/2000000) ((711917:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((711917:ℚ)/1000000),((1428211:ℚ)/2000000),((1486619729:ℚ)/5000000000),((894649021:ℚ)/2500000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((711917:ℝ)/1000000) ((1428211:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((1428211:ℚ)/2000000),((358147:ℚ)/500000),((29982633:ℚ)/100000000),((1747730033:ℚ)/5000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((1428211:ℝ)/2000000) ((358147:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((358147:ℚ)/500000),((287393:ℚ)/400000),((3022711661:ℚ)/10000000000),((3410383093:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((358147:ℝ)/500000) ((287393:ℝ)/400000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((287393:ℚ)/400000),((720671:ℚ)/1000000),((3046601509:ℚ)/10000000000),((830803973:ℚ)/2500000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((287393:ℝ)/400000) ((720671:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((720671:ℚ)/1000000),((1445719:ℚ)/2000000),((3069948941:ℚ)/10000000000),((3233789229:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((720671:ℝ)/1000000) ((1445719:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((1445719:ℚ)/2000000),((90631:ℚ)/125000),((3092769243:ℚ)/10000000000),((1570954981:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((1445719:ℝ)/2000000) ((90631:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((90631:ℚ)/125000),((1454473:ℚ)/2000000),((778769237:ℚ)/2500000000),((1523678017:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((90631:ℝ)/125000) ((1454473:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((1454473:ℚ)/2000000),((29177:ℚ)/40000),((3136885889:ℚ)/10000000000),((294987003:ℚ)/1000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((1454473:ℝ)/2000000) ((29177:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((29177:ℚ)/40000),((366901:ℚ)/500000),((3179059579:ℚ)/10000000000),((2849150759:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((29177:ℝ)/40000) ((366901:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((366901:ℚ)/500000),((738179:ℚ)/1000000),((804847163:ℚ)/2500000000),((263651773:ℚ)/1000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((366901:ℝ)/500000) ((738179:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((738179:ℚ)/1000000),((185639:ℚ)/250000),((203622679:ℚ)/625000000),((1202815987:ℚ)/5000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((738179:ℝ)/1000000) ((185639:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((185639:ℚ)/250000),((75131:ℚ)/100000),((1665084437:ℚ)/5000000000),((1075310163:ℚ)/5000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((185639:ℝ)/250000) ((75131:ℝ)/100000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((75131:ℚ)/100000),((11876:ℚ)/15625),((169812977:ℚ)/500000000),((593457:ℚ)/3906250)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((75131:ℝ)/100000) ((11876:ℝ)/15625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((81877:ℝ)/125000) ((340639:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((340639:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((43127:ℝ)/62500) ((349393:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node3_6 :
    ∀ r ∈ Set.Icc ((340639:ℝ)/500000) ((349393:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 node4_6
private theorem node0_6 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((349393:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_6
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((703163:ℝ)/1000000) ((35377:ℝ)/50000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node6_9 :
    ∀ r ∈ Set.Icc ((349393:ℝ)/500000) ((35377:ℝ)/50000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 node7_9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((1419457:ℝ)/2000000) ((1428211:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node9_12 :
    ∀ r ∈ Set.Icc ((35377:ℝ)/50000) ((1428211:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 node10_12
private theorem node6_12 :
    ∀ r ∈ Set.Icc ((349393:ℝ)/500000) ((1428211:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node6_9 node9_12
private theorem node0_12 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1428211:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_6 node6_12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((358147:ℝ)/500000) ((720671:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((1428211:ℝ)/2000000) ((720671:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((1445719:ℝ)/2000000) ((1454473:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((720671:ℝ)/1000000) ((1454473:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node12_18 :
    ∀ r ∈ Set.Icc ((1428211:ℝ)/2000000) ((1454473:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_15 node15_18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((29177:ℝ)/40000) ((738179:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node18_21 :
    ∀ r ∈ Set.Icc ((1454473:ℝ)/2000000) ((738179:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 node19_21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((185639:ℝ)/250000) ((11876:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node21_24 :
    ∀ r ∈ Set.Icc ((738179:ℝ)/1000000) ((11876:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 node22_24
private theorem node18_24 :
    ∀ r ∈ Set.Icc ((1454473:ℝ)/2000000) ((11876:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node18_21 node21_24
private theorem node12_24 :
    ∀ r ∈ Set.Icc ((1428211:ℝ)/2000000) ((11876:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_18 node18_24
private theorem node0_24 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((11876:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_12 node12_24
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_24
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450ThirdRadialNeg2
#check @N11Formalization.C450ThirdRadialNeg2.bound
#print axioms N11Formalization.C450ThirdRadialNeg2.params_valid
#print axioms N11Formalization.C450ThirdRadialNeg2.bound
