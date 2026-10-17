import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FourthRadialC05
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((677853:ℚ)/1000000),((680649:ℚ)/1000000),((393:ℚ)/125000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((327893:ℚ)/500000),((248906779:ℚ)/1250000000),((1559551447:ℚ)/2500000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((327893:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((327893:ℚ)/500000),((673679:ℚ)/1000000),((237793773:ℚ)/1000000000),((5379917327:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((327893:ℝ)/500000) ((673679:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((673679:ℚ)/1000000),((1365251:ℚ)/2000000),((1268095517:ℚ)/5000000000),((612632693:ℚ)/1250000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((673679:ℝ)/1000000) ((1365251:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((1365251:ℚ)/2000000),((172893:ℚ)/250000),((2677194311:ℚ)/10000000000),((2322400217:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((1365251:ℝ)/2000000) ((172893:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((172893:ℚ)/250000),((1401037:ℚ)/2000000),((1401910731:ℚ)/5000000000),((546837729:ℚ)/1250000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((172893:ℝ)/250000) ((1401037:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((1401037:ℚ)/2000000),((2819967:ℚ)/4000000),((286242809:ℚ)/1000000000),((4088011757:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((1401037:ℝ)/2000000) ((2819967:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((2819967:ℚ)/4000000),((141893:ℚ)/200000),((2918192323:ℚ)/10000000000),((492164601:ℚ)/1250000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((2819967:ℝ)/4000000) ((141893:ℝ)/200000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((141893:ℚ)/200000),((5693613:ℚ)/8000000),((589013679:ℚ)/2000000000),((1890472519:ℚ)/5000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((141893:ℝ)/200000) ((5693613:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((5693613:ℚ)/8000000),((2855753:ℚ)/4000000),((2971302907:ℚ)/10000000000),((3700405969:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((5693613:ℝ)/8000000) ((2855753:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((2855753:ℚ)/4000000),((5729399:ℚ)/8000000),((749229041:ℚ)/2500000000),((723631767:ℚ)/2000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((2855753:ℝ)/4000000) ((5729399:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((5729399:ℚ)/8000000),((1436823:ℚ)/2000000),((604385471:ℚ)/2000000000),((3534084177:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((5729399:ℝ)/8000000) ((1436823:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((1436823:ℚ)/2000000),((1153037:ℚ)/1600000),((3046354637:ℚ)/10000000000),((34480481:ℚ)/100000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((1436823:ℝ)/2000000) ((1153037:ℝ)/1600000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((1153037:ℚ)/1600000),((2891539:ℚ)/4000000),((307021521:ℚ)/1000000000),((3359899711:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((1153037:ℝ)/1600000) ((2891539:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((2891539:ℚ)/4000000),((5800971:ℚ)/8000000),((3093525391:ℚ)/10000000000),((3269467941:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((2891539:ℝ)/4000000) ((5800971:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((5800971:ℚ)/8000000),((363679:ℚ)/500000),((1558150339:ℚ)/5000000000),((198534847:ℚ)/625000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((5800971:ℝ)/8000000) ((363679:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((363679:ℚ)/500000),((5836757:ℚ)/8000000),((1569277901:ℚ)/5000000000),((3080944077:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((363679:ℝ)/500000) ((5836757:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((5836757:ℚ)/8000000),((117093:ℚ)/160000),((1580152393:ℚ)/5000000000),((1491183653:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((5836757:ℝ)/8000000) ((117093:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((117093:ℚ)/160000),((1472609:ℚ)/2000000),((1601168579:ℚ)/5000000000),((2880522777:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((117093:ℝ)/160000) ((1472609:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((1472609:ℚ)/2000000),((2963111:ℚ)/4000000),((3242497487:ℚ)/10000000000),((1332759757:ℚ)/5000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((1472609:ℝ)/2000000) ((2963111:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((2963111:ℚ)/4000000),((745251:ℚ)/1000000),((820219193:ℚ)/2500000000),((608016931:ℚ)/2500000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((2963111:ℝ)/4000000) ((745251:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((745251:ℚ)/1000000),((301679:ℚ)/400000),((838154707:ℚ)/2500000000),((217423033:ℚ)/1000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((745251:ℝ)/1000000) ((301679:ℝ)/400000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((301679:ℚ)/400000),((95393:ℚ)/125000),((683630659:ℚ)/2000000000),((383973939:ℚ)/2500000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((301679:ℝ)/400000) ((95393:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((673679:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((1365251:ℝ)/2000000) ((1401037:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((673679:ℝ)/1000000) ((1401037:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1401037:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((2819967:ℝ)/4000000) ((5693613:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((1401037:ℝ)/2000000) ((5693613:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((2855753:ℝ)/4000000) ((1436823:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((5693613:ℝ)/8000000) ((1436823:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((1401037:ℝ)/2000000) ((1436823:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1436823:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((1436823:ℝ)/2000000) ((2891539:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((5800971:ℝ)/8000000) ((5836757:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node13_16 :
    ∀ r ∈ Set.Icc ((2891539:ℝ)/4000000) ((5836757:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 node14_16
private theorem node11_16 :
    ∀ r ∈ Set.Icc ((1436823:ℝ)/2000000) ((5836757:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((117093:ℝ)/160000) ((2963111:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((5836757:ℝ)/8000000) ((2963111:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((745251:ℝ)/1000000) ((95393:ℝ)/125000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node19_22 :
    ∀ r ∈ Set.Icc ((2963111:ℝ)/4000000) ((95393:ℝ)/125000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 node20_22
private theorem node16_22 :
    ∀ r ∈ Set.Icc ((5836757:ℝ)/8000000) ((95393:ℝ)/125000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_19 node19_22
private theorem node11_22 :
    ∀ r ∈ Set.Icc ((1436823:ℝ)/2000000) ((95393:ℝ)/125000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_16 node16_22
private theorem node0_22 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((95393:ℝ)/125000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_22
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_22
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450FourthRadialC05
#check @N11Formalization.C450FourthRadialC05.bound
#print axioms N11Formalization.C450FourthRadialC05.params_valid
#print axioms N11Formalization.C450FourthRadialC05.bound
