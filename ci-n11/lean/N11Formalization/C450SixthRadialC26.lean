import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC26
open C450RadialPacketKernel
def params : Params := ⟨((82239999:ℚ)/32000000),((21686657:ℚ)/32000000),((11793491:ℚ)/16000000),((-13:ℚ)/5000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((13087:ℚ)/20000),((488712739:ℚ)/2500000000),((6107632707:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((13087:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((13087:ℚ)/20000),((26861:ℚ)/40000),((146052437:ℚ)/625000000),((5268247867:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((13087:ℝ)/20000) ((26861:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((26861:ℚ)/40000),((54409:ℚ)/80000),((1246814781:ℚ)/5000000000),((2399873789:ℚ)/5000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((26861:ℝ)/40000) ((54409:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((54409:ℚ)/80000),((6887:ℚ)/10000),((5143781:ℚ)/19531250),((909795671:ℚ)/2000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((54409:ℝ)/80000) ((6887:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((6887:ℚ)/10000),((110879:ℚ)/160000),((337277029:ℚ)/1250000000),((856926689:ℚ)/2000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((6887:ℝ)/10000) ((110879:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((110879:ℚ)/160000),((55783:ℚ)/80000),((2759602609:ℚ)/10000000000),((2073280367:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((110879:ℝ)/160000) ((55783:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((55783:ℚ)/80000),((112253:ℚ)/160000),((2818013521:ℚ)/10000000000),((2002007027:ℚ)/5000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((55783:ℝ)/80000) ((112253:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((112253:ℚ)/160000),((225193:ℚ)/320000),((355771179:ℚ)/1250000000),((3856495939:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((112253:ℝ)/160000) ((225193:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((225193:ℚ)/320000),((5647:ℚ)/8000),((287365773:ℚ)/1000000000),((945172767:ℚ)/2500000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((225193:ℝ)/320000) ((5647:ℝ)/8000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((5647:ℚ)/8000),((226567:ℚ)/320000),((1450250343:ℚ)/5000000000),((3703410919:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((5647:ℝ)/8000) ((226567:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((226567:ℚ)/320000),((113627:ℚ)/160000),((2926719283:ℚ)/10000000000),((3624560947:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((226567:ℝ)/320000) ((113627:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((113627:ℚ)/160000),((227941:ℚ)/320000),((2952333319:ℚ)/10000000000),((354403619:ℚ)/1000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((113627:ℝ)/160000) ((227941:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((227941:ℚ)/320000),((456569:ℚ)/640000),((2964919513:ℚ)/10000000000),((865429897:ℚ)/2500000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((227941:ℝ)/320000) ((456569:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((456569:ℚ)/640000),((57157:ℚ)/80000),((5954723:ℚ)/20000000),((2671757:ℚ)/7812500)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((456569:ℝ)/640000) ((57157:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((57157:ℚ)/80000),((457943:ℚ)/640000),((373707683:ℚ)/1250000000),((675495987:ℚ)/2000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((57157:ℝ)/80000) ((457943:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((457943:ℚ)/640000),((45863:ℚ)/64000),((1500910763:ℚ)/5000000000),((333459349:ℚ)/1000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((457943:ℝ)/640000) ((45863:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((45863:ℚ)/64000),((115001:ℚ)/160000),((1512865081:ℚ)/5000000000),((1645584687:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((45863:ℝ)/64000) ((115001:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((115001:ℚ)/160000),((230689:ℚ)/320000),((609820663:ℚ)/2000000000),((1601310137:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((115001:ℝ)/160000) ((230689:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((230689:ℚ)/320000),((14461:ℚ)/20000),((1535978043:ℚ)/5000000000),((124465653:ℚ)/400000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((230689:ℝ)/320000) ((14461:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((14461:ℚ)/20000),((232063:ℚ)/320000),((3094302837:ℚ)/10000000000),((3018012579:ℚ)/10000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((14461:ℝ)/20000) ((232063:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((232063:ℚ)/320000),((931:ℚ)/1280),((3116157233:ℚ)/10000000000),((2921479061:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((232063:ℝ)/320000) ((931:ℝ)/1280),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((931:ℚ)/1280),((58531:ℚ)/80000),((3158440439:ℚ)/10000000000),((70543561:ℚ)/250000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((931:ℝ)/1280) ((58531:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((58531:ℚ)/80000),((117749:ℚ)/160000),((3198902859:ℚ)/10000000000),((1305589701:ℚ)/5000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((58531:ℝ)/80000) ((117749:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((117749:ℚ)/160000),((29609:ℚ)/40000),((809408293:ℚ)/2500000000),((1191267419:ℚ)/5000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((117749:ℝ)/160000) ((29609:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((29609:ℚ)/40000),((11981:ℚ)/16000),((827553939:ℚ)/2500000000),((1064995721:ℚ)/5000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((29609:ℝ)/40000) ((11981:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((11981:ℚ)/16000),((3787:ℚ)/5000),((3376763113:ℚ)/10000000000),((300941:ℚ)/2000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((11981:ℝ)/16000) ((3787:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((13087:ℝ)/20000) ((54409:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((54409:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((6887:ℝ)/10000) ((55783:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node3_6 :
    ∀ r ∈ Set.Icc ((54409:ℝ)/80000) ((55783:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 node4_6
private theorem node0_6 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((55783:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_6
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((112253:ℝ)/160000) ((5647:ℝ)/8000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node6_9 :
    ∀ r ∈ Set.Icc ((55783:ℝ)/80000) ((5647:ℝ)/8000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 node7_9
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((5647:ℝ)/8000) ((113627:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((113627:ℝ)/160000) ((456569:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node9_13 :
    ∀ r ∈ Set.Icc ((5647:ℝ)/8000) ((456569:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node9_11 node11_13
private theorem node6_13 :
    ∀ r ∈ Set.Icc ((55783:ℝ)/80000) ((456569:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node6_9 node9_13
private theorem node0_13 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((456569:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_6 node6_13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((57157:ℝ)/80000) ((45863:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node13_16 :
    ∀ r ∈ Set.Icc ((456569:ℝ)/640000) ((45863:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 node14_16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((115001:ℝ)/160000) ((14461:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((45863:ℝ)/64000) ((14461:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node13_19 :
    ∀ r ∈ Set.Icc ((456569:ℝ)/640000) ((14461:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node13_16 node16_19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((232063:ℝ)/320000) ((58531:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node19_22 :
    ∀ r ∈ Set.Icc ((14461:ℝ)/20000) ((58531:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 node20_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((58531:ℝ)/80000) ((29609:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((29609:ℝ)/40000) ((3787:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node22_26 :
    ∀ r ∈ Set.Icc ((58531:ℝ)/80000) ((3787:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_26
private theorem node19_26 :
    ∀ r ∈ Set.Icc ((14461:ℝ)/20000) ((3787:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_22 node22_26
private theorem node13_26 :
    ∀ r ∈ Set.Icc ((456569:ℝ)/640000) ((3787:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node13_19 node19_26
private theorem node0_26 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3787:ℝ)/5000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_13 node13_26
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_26
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC26
#check @N11Formalization.C450SixthRadialC26.bound
#print axioms N11Formalization.C450SixthRadialC26.params_valid
#print axioms N11Formalization.C450SixthRadialC26.params_sum
#print axioms N11Formalization.C450SixthRadialC26.bound
