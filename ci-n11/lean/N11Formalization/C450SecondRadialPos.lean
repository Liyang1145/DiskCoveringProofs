import N11Formalization.C450SecondRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SecondRadialPos
open C450SecondRadialKernel
def packet0 : Packet := ⟨((31:ℚ)/50),((262715041:ℚ)/400000000),((2016076269:ℚ)/10000000000),((1265578689:ℚ)/2000000000)⟩
theorem valid0 : Valid .pos packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((262715041:ℝ)/400000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((262715041:ℚ)/400000000),((540145123:ℚ)/800000000),((601468299:ℚ)/2500000000),((5456583991:ℚ)/10000000000)⟩
theorem valid1 : Valid .pos packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((262715041:ℝ)/400000000) ((540145123:ℝ)/800000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((540145123:ℚ)/800000000),((1095005287:ℚ)/1600000000),((2565071529:ℚ)/10000000000),((2485301349:ℚ)/5000000000)⟩
theorem valid2 : Valid .pos packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((540145123:ℝ)/800000000) ((1095005287:ℝ)/1600000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((1095005287:ℚ)/1600000000),((138715041:ℚ)/200000000),((270671163:ℚ)/1000000000),((2355282299:ℚ)/5000000000)⟩
theorem valid3 : Valid .pos packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((1095005287:ℝ)/1600000000) ((138715041:ℝ)/200000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((138715041:ℚ)/200000000),((2234155697:ℚ)/3200000000),((2771894001:ℚ)/10000000000),((4436510279:ℚ)/10000000000)⟩
theorem valid4 : Valid .pos packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((138715041:ℝ)/200000000) ((2234155697:ℝ)/3200000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((2234155697:ℚ)/3200000000),((1124435369:ℚ)/1600000000),((354214403:ℚ)/1250000000),((4293389773:ℚ)/10000000000)⟩
theorem valid5 : Valid .pos packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((2234155697:ℝ)/3200000000) ((1124435369:ℝ)/1600000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((1124435369:ℚ)/1600000000),((2263585779:ℚ)/3200000000),((180776499:ℚ)/625000000),((64775749:ℚ)/156250000)⟩
theorem valid6 : Valid .pos packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((1124435369:ℝ)/1600000000) ((2263585779:ℝ)/3200000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((2263585779:ℚ)/3200000000),((4541886599:ℚ)/6400000000),((584136057:ℚ)/2000000000),((1996385071:ℚ)/5000000000)⟩
theorem valid7 : Valid .pos packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((2263585779:ℝ)/3200000000) ((4541886599:ℝ)/6400000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((4541886599:ℚ)/6400000000),((113915041:ℚ)/160000000),((1474119:ℚ)/5000000),((3822478:ℚ)/9765625)⟩
theorem valid8 : Valid .pos packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((4541886599:ℝ)/6400000000) ((113915041:ℝ)/160000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((113915041:ℚ)/160000000),((4571316681:ℚ)/6400000000),((2975120363:ℚ)/10000000000),((3834140371:ℚ)/10000000000)⟩
theorem valid9 : Valid .pos packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((113915041:ℝ)/160000000) ((4571316681:ℝ)/6400000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((4571316681:ℚ)/6400000000),((2293015861:ℚ)/3200000000),((3001349267:ℚ)/10000000000),((375244103:ℚ)/1000000000)⟩
theorem valid10 : Valid .pos packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((4571316681:ℝ)/6400000000) ((2293015861:ℝ)/3200000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((2293015861:ℚ)/3200000000),((4600746763:ℚ)/6400000000),((302694537:ℚ)/1000000000),((183450543:ℚ)/500000000)⟩
theorem valid11 : Valid .pos packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((2293015861:ℝ)/3200000000) ((4600746763:ℝ)/6400000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((4600746763:ℚ)/6400000000),((9216208567:ℚ)/12800000000),((379939033:ℚ)/1250000000),((3583728757:ℚ)/10000000000)⟩
theorem valid12 : Valid .pos packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((4600746763:ℝ)/6400000000) ((9216208567:ℝ)/12800000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((9216208567:ℚ)/12800000000),((1153865451:ℚ)/1600000000),((610385639:ℚ)/2000000000),((70807029:ℚ)/200000000)⟩
theorem valid13 : Valid .pos packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((9216208567:ℝ)/12800000000) ((1153865451:ℝ)/1600000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1153865451:ℚ)/1600000000),((9245638649:ℚ)/12800000000),((3064195439:ℚ)/10000000000),((174822949:ℚ)/500000000)⟩
theorem valid14 : Valid .pos packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1153865451:ℝ)/1600000000) ((9245638649:ℝ)/12800000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((9245638649:ℚ)/12800000000),((926035369:ℚ)/1280000000),((769079053:ℚ)/2500000000),((3452031667:ℚ)/10000000000)⟩
theorem valid15 : Valid .pos packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((9245638649:ℝ)/12800000000) ((926035369:ℝ)/1280000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((926035369:ℚ)/1280000000),((9275068731:ℚ)/12800000000),((3088292673:ℚ)/10000000000),((3407048559:ℚ)/10000000000)⟩
theorem valid16 : Valid .pos packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((926035369:ℝ)/1280000000) ((9275068731:ℝ)/12800000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((9275068731:ℚ)/12800000000),((2322445943:ℚ)/3200000000),((3100126923:ℚ)/10000000000),((1680743657:ℚ)/5000000000)⟩
theorem valid17 : Valid .pos packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((9275068731:ℝ)/12800000000) ((2322445943:ℝ)/3200000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((2322445943:ℚ)/3200000000),((9304498813:ℚ)/12800000000),((3111821011:ℚ)/10000000000),((1657662033:ℚ)/5000000000)⟩
theorem valid18 : Valid .pos packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((2322445943:ℝ)/3200000000) ((9304498813:ℝ)/12800000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((9304498813:ℚ)/12800000000),((4659606927:ℚ)/6400000000),((3123376931:ℚ)/10000000000),((1634266639:ℚ)/5000000000)⟩
theorem valid19 : Valid .pos packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((9304498813:ℝ)/12800000000) ((4659606927:ℝ)/6400000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((4659606927:ℚ)/6400000000),((1866785779:ℚ)/2560000000),((783699157:ℚ)/2500000000),((805271893:ℚ)/2500000000)⟩
theorem valid20 : Valid .pos packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((4659606927:ℝ)/6400000000) ((1866785779:ℝ)/2560000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((1866785779:ℚ)/2560000000),((292145123:ℚ)/400000000),((3146082001:ℚ)/10000000000),((3172957537:ℚ)/10000000000)⟩
theorem valid21 : Valid .pos packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((1866785779:ℝ)/2560000000) ((292145123:ℝ)/400000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((292145123:ℚ)/400000000),((4689037009:ℚ)/6400000000),((25346057:ℚ)/80000000),((3124111513:ℚ)/10000000000)⟩
theorem valid22 : Valid .pos packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((292145123:ℝ)/400000000) ((4689037009:ℝ)/6400000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((4689037009:ℚ)/6400000000),((94075041:ℚ)/128000000),((3189916571:ℚ)/10000000000),((302413209:ℚ)/1000000000)⟩
theorem valid23 : Valid .pos packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((4689037009:ℝ)/6400000000) ((94075041:ℝ)/128000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((94075041:ℚ)/128000000),((4718467091:ℚ)/6400000000),((1605536967:ℚ)/5000000000),((2920840637:ℚ)/10000000000)⟩
theorem valid24 : Valid .pos packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((94075041:ℝ)/128000000) ((4718467091:ℝ)/6400000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((4718467091:ℚ)/6400000000),((1183295533:ℚ)/1600000000),((161587109:ℚ)/500000000),((1406936083:ℚ)/5000000000)⟩
theorem valid25 : Valid .pos packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((4718467091:ℝ)/6400000000) ((1183295533:ℝ)/1600000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((1183295533:ℚ)/1600000000),((2381306107:ℚ)/3200000000),((3271660271:ℚ)/10000000000),((337848731:ℚ)/1250000000)⟩
theorem valid26 : Valid .pos packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((1183295533:ℝ)/1600000000) ((2381306107:ℝ)/3200000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((2381306107:ℚ)/3200000000),((599005287:ℚ)/800000000),((3309763443:ℚ)/10000000000),((1233019579:ℚ)/5000000000)⟩
theorem valid27 : Valid .pos packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((2381306107:ℝ)/3200000000) ((599005287:ℝ)/800000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((599005287:ℚ)/800000000),((242545123:ℚ)/320000000),((845214347:ℚ)/2500000000),((551142347:ℚ)/2500000000)⟩
theorem valid28 : Valid .pos packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((599005287:ℝ)/800000000) ((242545123:ℝ)/320000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((242545123:ℚ)/320000000),((76715041:ℚ)/100000000),((3445624339:ℚ)/10000000000),((389321053:ℚ)/2500000000)⟩
theorem valid29 : Valid .pos packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((242545123:ℝ)/320000000) ((76715041:ℝ)/100000000),
    model .pos r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .pos packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((262715041:ℝ)/400000000) ((1095005287:ℝ)/1600000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1095005287:ℝ)/1600000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((1095005287:ℝ)/1600000000) ((2234155697:ℝ)/3200000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((2234155697:ℝ)/3200000000) ((2263585779:ℝ)/3200000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node3_7 :
    ∀ r ∈ Set.Icc ((1095005287:ℝ)/1600000000) ((2263585779:ℝ)/3200000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node3_5 node5_7
private theorem node0_7 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((2263585779:ℝ)/3200000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_7
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((2263585779:ℝ)/3200000000) ((113915041:ℝ)/160000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((113915041:ℝ)/160000000) ((2293015861:ℝ)/3200000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node7_11 :
    ∀ r ∈ Set.Icc ((2263585779:ℝ)/3200000000) ((2293015861:ℝ)/3200000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node7_9 node9_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((2293015861:ℝ)/3200000000) ((9216208567:ℝ)/12800000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((9216208567:ℝ)/12800000000) ((9245638649:ℝ)/12800000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node11_15 :
    ∀ r ∈ Set.Icc ((2293015861:ℝ)/3200000000) ((9245638649:ℝ)/12800000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_15
private theorem node7_15 :
    ∀ r ∈ Set.Icc ((2263585779:ℝ)/3200000000) ((9245638649:ℝ)/12800000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node7_11 node11_15
private theorem node0_15 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((9245638649:ℝ)/12800000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_7 node7_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((926035369:ℝ)/1280000000) ((2322445943:ℝ)/3200000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((9245638649:ℝ)/12800000000) ((2322445943:ℝ)/3200000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((2322445943:ℝ)/3200000000) ((4659606927:ℝ)/6400000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((4659606927:ℝ)/6400000000) ((292145123:ℝ)/400000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node18_22 :
    ∀ r ∈ Set.Icc ((2322445943:ℝ)/3200000000) ((292145123:ℝ)/400000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node18_20 node20_22
private theorem node15_22 :
    ∀ r ∈ Set.Icc ((9245638649:ℝ)/12800000000) ((292145123:ℝ)/400000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node15_18 node18_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((292145123:ℝ)/400000000) ((94075041:ℝ)/128000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((94075041:ℝ)/128000000) ((1183295533:ℝ)/1600000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node22_26 :
    ∀ r ∈ Set.Icc ((292145123:ℝ)/400000000) ((1183295533:ℝ)/1600000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_26
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((1183295533:ℝ)/1600000000) ((599005287:ℝ)/800000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((599005287:ℝ)/800000000) ((76715041:ℝ)/100000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node26_30 :
    ∀ r ∈ Set.Icc ((1183295533:ℝ)/1600000000) ((76715041:ℝ)/100000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node26_28 node28_30
private theorem node22_30 :
    ∀ r ∈ Set.Icc ((292145123:ℝ)/400000000) ((76715041:ℝ)/100000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node22_26 node26_30
private theorem node15_30 :
    ∀ r ∈ Set.Icc ((9245638649:ℝ)/12800000000) ((76715041:ℝ)/100000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node15_22 node22_30
private theorem node0_30 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((76715041:ℝ)/100000000),
      model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_15 node15_30
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish .pos:ℝ),
    model .pos r < (cap:ℝ) := by
  have hh := node0_30
  norm_num [finish,F,E,R] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model .pos r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join near_bound (fun r hr => far_bound .pos r hr)
end N11Formalization.C450SecondRadialPos
#check @N11Formalization.C450SecondRadialPos.bound
#print axioms N11Formalization.C450SecondRadialPos.bound
