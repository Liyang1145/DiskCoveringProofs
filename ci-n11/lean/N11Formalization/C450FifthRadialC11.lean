import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FifthRadialC11
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((339853:ℚ)/500000),((826011:ℚ)/1250000),((391:ℚ)/62500)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((164141:ℚ)/250000),((2010574271:ℚ)/10000000000),((3153983379:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((164141:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((164141:ℚ)/250000),((337423:ℚ)/500000),((2399687359:ℚ)/10000000000),((2719776447:ℚ)/5000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((164141:ℝ)/250000) ((337423:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((337423:ℚ)/500000),((683987:ℚ)/1000000),((1279339971:ℚ)/5000000000),((4955155631:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((337423:ℝ)/500000) ((683987:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((683987:ℚ)/1000000),((86641:ℚ)/125000),((2700182909:ℚ)/10000000000),((939191407:ℚ)/2000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((683987:ℝ)/1000000) ((86641:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((86641:ℚ)/125000),((702269:ℚ)/1000000),((2827107341:ℚ)/10000000000),((88455637:ℚ)/200000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((86641:ℝ)/125000) ((702269:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((702269:ℚ)/1000000),((1413679:ℚ)/2000000),((2885795687:ℚ)/10000000000),((413284667:ℚ)/1000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((702269:ℝ)/1000000) ((1413679:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((1413679:ℚ)/2000000),((71141:ℚ)/100000),((1470800473:ℚ)/5000000000),((3980453911:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((1413679:ℝ)/2000000) ((71141:ℝ)/100000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((71141:ℚ)/100000),((2854781:ℚ)/4000000),((2968483071:ℚ)/10000000000),((477790731:ℚ)/1250000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((71141:ℝ)/100000) ((2854781:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2854781:ℚ)/4000000),((1431961:ℚ)/2000000),((2994714387:ℚ)/10000000000),((3740884299:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2854781:ℝ)/4000000) ((1431961:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((1431961:ℚ)/2000000),((2873063:ℚ)/4000000),((1510157737:ℚ)/5000000000),((3657716973:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((1431961:ℝ)/2000000) ((2873063:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((2873063:ℚ)/4000000),((720551:ℚ)/1000000),((1522652889:ℚ)/5000000000),((357270313:ℚ)/1000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((2873063:ℝ)/4000000) ((720551:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((720551:ℚ)/1000000),((578269:ℚ)/800000),((1534851851:ℚ)/5000000000),((1742853719:ℚ)/5000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((720551:ℝ)/1000000) ((578269:ℝ)/800000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((578269:ℚ)/800000),((1450243:ℚ)/2000000),((3093526679:ℚ)/10000000000),((3396577391:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((578269:ℝ)/800000) ((1450243:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((1450243:ℚ)/2000000),((2909627:ℚ)/4000000),((194799453:ℚ)/625000000),((3305140081:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((1450243:ℝ)/2000000) ((2909627:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((2909627:ℚ)/4000000),((182423:ℚ)/250000),((3139513117:ℚ)/10000000000),((3211198179:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((2909627:ℝ)/4000000) ((182423:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((182423:ℚ)/250000),((2927909:ℚ)/4000000),((1580853609:ℚ)/5000000000),((311452481:ℚ)/1000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((182423:ℝ)/250000) ((2927909:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((2927909:ℚ)/4000000),((58741:ℚ)/80000),((1591693883:ℚ)/5000000000),((376857121:ℚ)/1250000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((2927909:ℝ)/4000000) ((58741:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((58741:ℚ)/80000),((2946191:ℚ)/4000000),((1602284151:ℚ)/5000000000),((2911886923:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((58741:ℝ)/80000) ((2946191:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((2946191:ℚ)/4000000),((738833:ℚ)/1000000),((3225261743:ℚ)/10000000000),((2805250789:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((2946191:ℝ)/4000000) ((738833:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((738833:ℚ)/1000000),((1486807:ℚ)/2000000),((3265236103:ℚ)/10000000000),((2694513061:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((738833:ℝ)/1000000) ((1486807:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1486807:ℚ)/2000000),((373987:ℚ)/500000),((206462693:ℚ)/625000000),((2458495097:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1486807:ℝ)/2000000) ((373987:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((373987:ℚ)/500000),((151423:ℚ)/200000),((3374646019:ℚ)/10000000000),((1098916041:ℚ)/5000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((373987:ℝ)/500000) ((151423:ℝ)/200000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((151423:ℚ)/200000),((47891:ℚ)/62500),((3439588557:ℚ)/10000000000),((310506939:ℚ)/2000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((151423:ℝ)/200000) ((47891:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((337423:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((683987:ℝ)/1000000) ((702269:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((337423:ℝ)/500000) ((702269:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((702269:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((1413679:ℝ)/2000000) ((2854781:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((702269:ℝ)/1000000) ((2854781:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((1431961:ℝ)/2000000) ((720551:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((2854781:ℝ)/4000000) ((720551:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((702269:ℝ)/1000000) ((720551:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((720551:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((578269:ℝ)/800000) ((2909627:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node11_14 :
    ∀ r ∈ Set.Icc ((720551:ℝ)/1000000) ((2909627:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 node12_14
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((182423:ℝ)/250000) ((58741:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((2909627:ℝ)/4000000) ((58741:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node11_17 :
    ∀ r ∈ Set.Icc ((720551:ℝ)/1000000) ((58741:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_14 node14_17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((2946191:ℝ)/4000000) ((1486807:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node17_20 :
    ∀ r ∈ Set.Icc ((58741:ℝ)/80000) ((1486807:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 node18_20
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((373987:ℝ)/500000) ((47891:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node20_23 :
    ∀ r ∈ Set.Icc ((1486807:ℝ)/2000000) ((47891:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 node21_23
private theorem node17_23 :
    ∀ r ∈ Set.Icc ((58741:ℝ)/80000) ((47891:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_20 node20_23
private theorem node11_23 :
    ∀ r ∈ Set.Icc ((720551:ℝ)/1000000) ((47891:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_17 node17_23
private theorem node0_23 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((47891:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_23
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_23
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450FifthRadialC11
#check @N11Formalization.C450FifthRadialC11.bound
#print axioms N11Formalization.C450FifthRadialC11.params_valid
#print axioms N11Formalization.C450FifthRadialC11.bound
