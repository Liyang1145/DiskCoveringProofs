import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FourthRadialC03
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((677853:ℚ)/1000000),((1448549:ℚ)/2000000),((-29:ℚ)/15625)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((81817:ℚ)/125000),((1959621959:ℚ)/10000000000),((6124681867:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((81817:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((81817:ℚ)/125000),((167951:ℚ)/250000),((1171116997:ℚ)/5000000000),((132070807:ℚ)/250000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((81817:ℝ)/125000) ((167951:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((167951:ℚ)/250000),((340219:ℚ)/500000),((2499221383:ℚ)/10000000000),((300811317:ℚ)/625000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((167951:ℝ)/250000) ((340219:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((340219:ℚ)/500000),((43067:ℚ)/62500),((659836627:ℚ)/2500000000),((570186903:ℚ)/1250000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((340219:ℝ)/500000) ((43067:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((43067:ℚ)/62500),((693389:ℚ)/1000000),((2703997437:ℚ)/10000000000),((4296399397:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((43067:ℝ)/62500) ((693389:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((693389:ℚ)/1000000),((348853:ℚ)/500000),((2765423063:ℚ)/10000000000),((831587241:ℚ)/2000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((693389:ℝ)/1000000) ((348853:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((348853:ℚ)/500000),((702023:ℚ)/1000000),((2823862687:ℚ)/10000000000),((802997517:ℚ)/2000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((348853:ℝ)/500000) ((702023:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((702023:ℚ)/1000000),((35317:ℚ)/50000),((4499259:ℚ)/15625000),((1933527369:ℚ)/5000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((702023:ℝ)/1000000) ((35317:ℝ)/50000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((35317:ℚ)/50000),((1416997:ℚ)/2000000),((2906374649:ℚ)/10000000000),((3713540601:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((35317:ℝ)/50000) ((1416997:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((1416997:ℚ)/2000000),((710657:ℚ)/1000000),((2932596941:ℚ)/10000000000),((454308761:ℚ)/1250000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((1416997:ℝ)/2000000) ((710657:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((710657:ℚ)/1000000),((1425631:ℚ)/2000000),((236657:ℚ)/800000),((710744087:ℚ)/2000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((710657:ℝ)/1000000) ((1425631:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((1425631:ℚ)/2000000),((357487:ℚ)/500000),((93226253:ℚ)/312500000),((3471174269:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((1425631:ℝ)/2000000) ((357487:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((357487:ℚ)/500000),((286853:ℚ)/400000),((1503848743:ℚ)/5000000000),((13229297:ℚ)/39062500)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((357487:ℝ)/500000) ((286853:ℝ)/400000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((286853:ℚ)/400000),((719291:ℚ)/1000000),((1515800747:ℚ)/5000000000),((3300149471:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((286853:ℝ)/400000) ((719291:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((719291:ℚ)/1000000),((1442899:ℚ)/2000000),((3054968079:ℚ)/10000000000),((642270901:ℚ)/2000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((719291:ℝ)/1000000) ((1442899:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((1442899:ℚ)/2000000),((90451:ℚ)/125000),((615562479:ℚ)/2000000000),((3120123311:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((1442899:ℝ)/2000000) ((90451:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((90451:ℚ)/125000),((1451533:ℚ)/2000000),((62002977:ℚ)/200000000),((60524707:ℚ)/200000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((90451:ℝ)/125000) ((1451533:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((1451533:ℚ)/2000000),((29117:ℚ)/40000),((1560995579:ℚ)/5000000000),((1464717481:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((1451533:ℝ)/2000000) ((29117:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((29117:ℚ)/40000),((366121:ℚ)/500000),((395530623:ℚ)/1250000000),((353677877:ℚ)/1250000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((29117:ℝ)/40000) ((366121:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((366121:ℚ)/500000),((736559:ℚ)/1000000),((801167839:ℚ)/2500000000),((1309139991:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((366121:ℝ)/500000) ((736559:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((736559:ℚ)/1000000),((185219:ℚ)/250000),((3243359257:ℚ)/10000000000),((298625929:ℚ)/1250000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((736559:ℝ)/1000000) ((185219:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((185219:ℚ)/250000),((74951:ℚ)/100000),((3315839013:ℚ)/10000000000),((2135772407:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((185219:ℝ)/250000) ((74951:ℝ)/100000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((74951:ℚ)/100000),((11846:ℚ)/15625),((676452227:ℚ)/2000000000),((1508781099:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((74951:ℝ)/100000) ((11846:ℝ)/15625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((167951:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((340219:ℝ)/500000) ((693389:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((167951:ℝ)/250000) ((693389:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((693389:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((348853:ℝ)/500000) ((35317:ℝ)/50000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((693389:ℝ)/1000000) ((35317:ℝ)/50000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((1416997:ℝ)/2000000) ((1425631:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((35317:ℝ)/50000) ((1425631:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((693389:ℝ)/1000000) ((1425631:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1425631:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((357487:ℝ)/500000) ((719291:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node11_14 :
    ∀ r ∈ Set.Icc ((1425631:ℝ)/2000000) ((719291:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 node12_14
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((1442899:ℝ)/2000000) ((1451533:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((719291:ℝ)/1000000) ((1451533:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node11_17 :
    ∀ r ∈ Set.Icc ((1425631:ℝ)/2000000) ((1451533:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_14 node14_17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((29117:ℝ)/40000) ((736559:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node17_20 :
    ∀ r ∈ Set.Icc ((1451533:ℝ)/2000000) ((736559:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 node18_20
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((185219:ℝ)/250000) ((11846:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node20_23 :
    ∀ r ∈ Set.Icc ((736559:ℝ)/1000000) ((11846:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 node21_23
private theorem node17_23 :
    ∀ r ∈ Set.Icc ((1451533:ℝ)/2000000) ((11846:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_20 node20_23
private theorem node11_23 :
    ∀ r ∈ Set.Icc ((1425631:ℝ)/2000000) ((11846:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_17 node17_23
private theorem node0_23 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((11846:ℝ)/15625),
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
end N11Formalization.C450FourthRadialC03
#check @N11Formalization.C450FourthRadialC03.bound
#print axioms N11Formalization.C450FourthRadialC03.params_valid
#print axioms N11Formalization.C450FourthRadialC03.bound
