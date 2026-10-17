import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FifthRadialC15
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((339853:ℚ)/500000),((382419:ℚ)/625000),((891:ℚ)/62500)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((164641:ℚ)/250000),((514752419:ℚ)/2500000000),((1296864573:ℚ)/2000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((164641:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((164641:ℚ)/250000),((338923:ℚ)/500000),((2454017393:ℚ)/10000000000),((2795114919:ℚ)/5000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((164641:ℝ)/250000) ((338923:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((338923:ℚ)/500000),((87141:ℚ)/125000),((1378688439:ℚ)/5000000000),((636474443:ℚ)/1250000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((338923:ℝ)/500000) ((87141:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((87141:ℚ)/125000),((706769:ℚ)/1000000),((1442456417:ℚ)/5000000000),((90883989:ℚ)/200000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((87141:ℝ)/125000) ((706769:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((706769:ℚ)/1000000),((1423179:ℚ)/2000000),((2943736511:ℚ)/10000000000),((16586153:ℚ)/39062500)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((706769:ℝ)/1000000) ((1423179:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((1423179:ℚ)/2000000),((2855999:ℚ)/4000000),((594403081:ℚ)/2000000000),((2044684339:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((1423179:ℝ)/2000000) ((2855999:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((2855999:ℚ)/4000000),((71641:ℚ)/100000),((2999573459:ℚ)/10000000000),((4008863779:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((2855999:ℝ)/4000000) ((71641:ℝ)/100000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((71641:ℚ)/100000),((2875281:ℚ)/4000000),((3026434601:ℚ)/10000000000),((1963399903:ℚ)/5000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((71641:ℝ)/100000) ((2875281:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2875281:ℚ)/4000000),((1442461:ℚ)/2000000),((1526310687:ℚ)/5000000000),((3843076641:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2875281:ℝ)/4000000) ((1442461:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((1442461:ℚ)/2000000),((1155897:ℚ)/1600000),((383183571:ℚ)/1250000000),((375758313:ℚ)/1000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((1442461:ℝ)/2000000) ((1155897:ℝ)/1600000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1155897:ℚ)/1600000),((2894563:ℚ)/4000000),((615631011:ℚ)/2000000000),((464266789:ℚ)/1250000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1155897:ℝ)/1600000) ((2894563:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((2894563:ℚ)/4000000),((5798767:ℚ)/8000000),((193167707:ℚ)/625000000),((734039061:ℚ)/2000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((2894563:ℝ)/4000000) ((5798767:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((5798767:ℚ)/8000000),((726051:ℚ)/1000000),((3103055749:ℚ)/10000000000),((1812874129:ℚ)/5000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((5798767:ℝ)/8000000) ((726051:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((726051:ℚ)/1000000),((5818049:ℚ)/8000000),((389409339:ℚ)/1250000000),((1790387109:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((726051:ℝ)/1000000) ((5818049:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((5818049:ℚ)/8000000),((582769:ℚ)/800000),((3127342483:ℚ)/10000000000),((1767626521:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((5818049:ℝ)/8000000) ((582769:ℝ)/800000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((582769:ℚ)/800000),((5837331:ℚ)/8000000),((627852257:ℚ)/2000000000),((3489163281:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((582769:ℝ)/800000) ((5837331:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((5837331:ℚ)/8000000),((1461743:ℚ)/2000000),((3151033283:ℚ)/10000000000),((688496413:ℚ)/2000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((5837331:ℝ)/8000000) ((1461743:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((1461743:ℚ)/2000000),((5856613:ℚ)/8000000),((1581330293:ℚ)/5000000000),((3395184963:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((1461743:ℝ)/2000000) ((5856613:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((5856613:ℚ)/8000000),((2933127:ℚ)/4000000),((12696581:ℚ)/40000000),((1673622917:ℚ)/5000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((5856613:ℝ)/8000000) ((2933127:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((2933127:ℚ)/4000000),((1175179:ℚ)/1600000),((1592744639:ℚ)/5000000000),((824659163:ℚ)/2500000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((2933127:ℝ)/4000000) ((1175179:ℝ)/1600000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1175179:ℚ)/1600000),((183923:ℚ)/250000),((1598347313:ℚ)/5000000000),((324932731:ℚ)/1000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1175179:ℝ)/1600000) ((183923:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((183923:ℚ)/250000),((5895177:ℚ)/8000000),((1603881599:ℚ)/5000000000),((1599642699:ℚ)/5000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((183923:ℝ)/250000) ((5895177:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((5895177:ℚ)/8000000),((2952409:ℚ)/4000000),((1609348427:ℚ)/5000000000),((62969519:ℚ)/200000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((5895177:ℝ)/8000000) ((2952409:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((2952409:ℚ)/4000000),((5914459:ℚ)/8000000),((322949741:ℚ)/1000000000),((96776911:ℚ)/312500000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((2952409:ℝ)/4000000) ((5914459:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((5914459:ℚ)/8000000),((59241:ℚ)/80000),((1620083317:ℚ)/5000000000),((608880001:ℚ)/2000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((5914459:ℝ)/8000000) ((59241:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((59241:ℚ)/80000),((5933741:ℚ)/8000000),((3250706259:ℚ)/10000000000),((1495523969:ℚ)/5000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((59241:ℝ)/80000) ((5933741:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((5933741:ℚ)/8000000),((2971691:ℚ)/4000000),((3261117971:ℚ)/10000000000),((2936756357:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((5933741:ℝ)/8000000) ((2971691:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((2971691:ℚ)/4000000),((745333:ℚ)/1000000),((3281564221:ℚ)/10000000000),((2881472117:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((2971691:ℝ)/4000000) ((745333:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((745333:ℚ)/1000000),((2990973:ℚ)/4000000),((1650759067:ℚ)/5000000000),((345960813:ℚ)/1250000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((745333:ℝ)/1000000) ((2990973:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((2990973:ℚ)/4000000),((1500307:ℚ)/2000000),((1660495947:ℚ)/5000000000),((1324574181:ℚ)/5000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((2990973:ℝ)/4000000) ((1500307:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((1500307:ℚ)/2000000),((377487:ℚ)/500000),((67170901:ℚ)/200000000),((2525188143:ℚ)/10000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((1500307:ℝ)/2000000) ((377487:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((377487:ℚ)/500000),((152923:ℚ)/200000),((3428370201:ℚ)/10000000000),((564347701:ℚ)/2500000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((377487:ℝ)/500000) ((152923:ℝ)/200000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((152923:ℚ)/200000),((48391:ℚ)/62500),((218228629:ℚ)/625000000),((199314747:ℚ)/1250000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((152923:ℝ)/200000) ((48391:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((338923:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((338923:ℝ)/500000) ((706769:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((706769:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((706769:ℝ)/1000000) ((2855999:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((2855999:ℝ)/4000000) ((2875281:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((706769:ℝ)/1000000) ((2875281:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((2875281:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((2875281:ℝ)/4000000) ((1155897:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((1155897:ℝ)/1600000) ((5798767:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((2875281:ℝ)/4000000) ((5798767:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((5798767:ℝ)/8000000) ((5818049:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((5818049:ℝ)/8000000) ((5837331:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((5798767:ℝ)/8000000) ((5837331:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((2875281:ℝ)/4000000) ((5837331:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((5837331:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((5837331:ℝ)/8000000) ((5856613:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((5856613:ℝ)/8000000) ((1175179:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((5837331:ℝ)/8000000) ((1175179:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((1175179:ℝ)/1600000) ((5895177:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((5895177:ℝ)/8000000) ((5914459:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((1175179:ℝ)/1600000) ((5914459:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((5837331:ℝ)/8000000) ((5914459:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((5914459:ℝ)/8000000) ((5933741:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((5933741:ℝ)/8000000) ((745333:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((5914459:ℝ)/8000000) ((745333:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((745333:ℝ)/1000000) ((1500307:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((377487:ℝ)/500000) ((48391:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((1500307:ℝ)/2000000) ((48391:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node28_33 :
    ∀ r ∈ Set.Icc ((745333:ℝ)/1000000) ((48391:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node28_30 node30_33
private theorem node24_33 :
    ∀ r ∈ Set.Icc ((5914459:ℝ)/8000000) ((48391:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_28 node28_33
private theorem node16_33 :
    ∀ r ∈ Set.Icc ((5837331:ℝ)/8000000) ((48391:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_24 node24_33
private theorem node0_33 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((48391:ℝ)/62500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_16 node16_33
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_33
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450FifthRadialC15
#check @N11Formalization.C450FifthRadialC15.bound
#print axioms N11Formalization.C450FifthRadialC15.params_valid
#print axioms N11Formalization.C450FifthRadialC15.bound
