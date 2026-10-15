import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FifthRadialC03
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((339853:ℚ)/500000),((62163:ℚ)/80000),((-1811:ℚ)/250000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((653189:ℚ)/1000000),((1924681799:ℚ)/10000000000),((60002579:ℚ)/100000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((653189:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((653189:ℚ)/1000000),((1339567:ℚ)/2000000),((1151332531:ℚ)/5000000000),((5176371903:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((653189:ℝ)/1000000) ((1339567:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((1339567:ℚ)/2000000),((2712323:ℚ)/4000000),((98327041:ℚ)/400000000),((4716371349:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((1339567:ℝ)/2000000) ((2712323:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((2712323:ℚ)/4000000),((343189:ℚ)/500000),((2597246647:ℚ)/10000000000),((1117528067:ℚ)/2500000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((2712323:ℝ)/4000000) ((343189:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((343189:ℚ)/500000),((5524213:ℚ)/8000000),((2661507341:ℚ)/10000000000),((2105247093:ℚ)/5000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((343189:ℝ)/500000) ((5524213:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((5524213:ℚ)/8000000),((2778701:ℚ)/4000000),((340328133:ℚ)/1250000000),((814975957:ℚ)/2000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((5524213:ℝ)/8000000) ((2778701:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((2778701:ℚ)/4000000),((5590591:ℚ)/8000000),((111233337:ℚ)/400000000),((1967431897:ℚ)/5000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((2778701:ℝ)/4000000) ((5590591:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((5590591:ℚ)/8000000),((11214371:ℚ)/16000000),((2808911477:ℚ)/10000000000),((3789957137:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((5590591:ℝ)/8000000) ((11214371:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((11214371:ℚ)/16000000),((281189:ℚ)/400000),((1418168429:ℚ)/5000000000),((3715491347:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((11214371:ℝ)/16000000) ((281189:ℝ)/400000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((281189:ℚ)/400000),((11280749:ℚ)/16000000),((22905051:ℚ)/80000000),((909893599:ℚ)/2500000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((281189:ℝ)/400000) ((11280749:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((11280749:ℚ)/16000000),((5656969:ℚ)/8000000),((722328893:ℚ)/2500000000),((1781056667:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((11280749:ℝ)/16000000) ((5656969:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((5656969:ℚ)/8000000),((11347127:ℚ)/16000000),((2914908831:ℚ)/10000000000),((870751243:ℚ)/2500000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((5656969:ℝ)/8000000) ((11347127:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((11347127:ℚ)/16000000),((2845079:ℚ)/4000000),((1469964731:ℚ)/5000000000),((850533557:ℚ)/2500000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((11347127:ℝ)/16000000) ((2845079:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((2845079:ℚ)/4000000),((2282701:ℚ)/3200000),((2964394793:ℚ)/10000000000),((829843029:ℚ)/2500000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((2845079:ℝ)/4000000) ((2282701:ℝ)/3200000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((2282701:ℚ)/3200000),((5723347:ℚ)/8000000),((747080309:ℚ)/2500000000),((3234573277:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((2282701:ℝ)/3200000) ((5723347:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((5723347:ℚ)/8000000),((11479883:ℚ)/16000000),((3011724357:ℚ)/10000000000),((786893229:ℚ)/2500000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((5723347:ℝ)/8000000) ((11479883:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((11479883:ℚ)/16000000),((719567:ℚ)/1000000),((3034618939:ℚ)/10000000000),((38227287:ℚ)/125000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((11479883:ℝ)/16000000) ((719567:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((719567:ℚ)/1000000),((11546261:ℚ)/16000000),((1528509519:ℚ)/5000000000),((2966187183:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((719567:ℝ)/1000000) ((11546261:ℝ)/16000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((11546261:ℚ)/16000000),((231589:ℚ)/320000),((3078938027:ℚ)/10000000000),((2871334927:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((11546261:ℝ)/16000000) ((231589:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((231589:ℚ)/320000),((2911457:ℚ)/4000000),((624276611:ℚ)/2000000000),((554666583:ℚ)/2000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((231589:ℝ)/320000) ((2911457:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((2911457:ℚ)/4000000),((5856103:ℚ)/8000000),((3162049103:ℚ)/10000000000),((128321211:ℚ)/500000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((2911457:ℝ)/4000000) ((5856103:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((5856103:ℚ)/8000000),((1472323:ℚ)/2000000),((800255737:ℚ)/2500000000),((2341736701:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((5856103:ℝ)/8000000) ((1472323:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((1472323:ℚ)/2000000),((595567:ℚ)/800000),((1637102741:ℚ)/5000000000),((2093551751:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((1472323:ℝ)/2000000) ((595567:ℝ)/800000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((595567:ℚ)/800000),((188189:ℚ)/250000),((835373309:ℚ)/2500000000),((1479010301:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((595567:ℝ)/800000) ((188189:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((653189:ℝ)/1000000) ((2712323:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((2712323:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((343189:ℝ)/500000) ((2778701:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node3_6 :
    ∀ r ∈ Set.Icc ((2712323:ℝ)/4000000) ((2778701:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 node4_6
private theorem node0_6 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((2778701:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_6
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((5590591:ℝ)/8000000) ((281189:ℝ)/400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node6_9 :
    ∀ r ∈ Set.Icc ((2778701:ℝ)/4000000) ((281189:ℝ)/400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 node7_9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((11280749:ℝ)/16000000) ((11347127:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node9_12 :
    ∀ r ∈ Set.Icc ((281189:ℝ)/400000) ((11347127:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 node10_12
private theorem node6_12 :
    ∀ r ∈ Set.Icc ((2778701:ℝ)/4000000) ((11347127:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node6_9 node9_12
private theorem node0_12 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((11347127:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_6 node6_12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((2845079:ℝ)/4000000) ((5723347:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((11347127:ℝ)/16000000) ((5723347:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((11479883:ℝ)/16000000) ((11546261:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((5723347:ℝ)/8000000) ((11546261:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node12_18 :
    ∀ r ∈ Set.Icc ((11347127:ℝ)/16000000) ((11546261:ℝ)/16000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_15 node15_18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((231589:ℝ)/320000) ((5856103:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node18_21 :
    ∀ r ∈ Set.Icc ((11546261:ℝ)/16000000) ((5856103:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 node19_21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((1472323:ℝ)/2000000) ((188189:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node21_24 :
    ∀ r ∈ Set.Icc ((5856103:ℝ)/8000000) ((188189:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 node22_24
private theorem node18_24 :
    ∀ r ∈ Set.Icc ((11546261:ℝ)/16000000) ((188189:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node18_21 node21_24
private theorem node12_24 :
    ∀ r ∈ Set.Icc ((11347127:ℝ)/16000000) ((188189:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_18 node18_24
private theorem node0_24 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((188189:ℝ)/250000),
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
end N11Formalization.C450FifthRadialC03
#check @N11Formalization.C450FifthRadialC03.bound
#print axioms N11Formalization.C450FifthRadialC03.params_valid
#print axioms N11Formalization.C450FifthRadialC03.bound
