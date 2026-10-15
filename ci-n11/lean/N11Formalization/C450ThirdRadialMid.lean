import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450ThirdRadialMid
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((338529:ℚ)/500000),((678927:ℚ)/1000000),((127:ℚ)/31250)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((41001:ℚ)/62500),((399398927:ℚ)/2000000000),((6258899261:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((41001:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((41001:ℚ)/62500),((84253:ℚ)/125000),((2384404593:ℚ)/10000000000),((1079521831:ℚ)/2000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((41001:ℝ)/62500) ((84253:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((84253:ℚ)/125000),((170757:ℚ)/250000),((635720067:ℚ)/2500000000),((4917110231:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((84253:ℝ)/125000) ((170757:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((170757:ℚ)/250000),((10813:ℚ)/15625),((2684034947:ℚ)/10000000000),((582497251:ℚ)/1250000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((170757:ℝ)/250000) ((10813:ℝ)/15625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((10813:ℚ)/15625),((348267:ℚ)/500000),((1374525833:ℚ)/5000000000),((175558679:ℚ)/400000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((10813:ℝ)/15625) ((348267:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((348267:ℚ)/500000),((175259:ℚ)/250000),((702688387:ℚ)/2500000000),((1061857091:ℚ)/2500000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((348267:ℝ)/500000) ((175259:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((175259:ℚ)/250000),((352769:ℚ)/500000),((17933663:ℚ)/62500000),((2050657209:ℚ)/5000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((175259:ℝ)/250000) ((352769:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((352769:ℚ)/500000),((17751:ℚ)/25000),((2925164163:ℚ)/10000000000),((3950115879:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((352769:ℝ)/500000) ((17751:ℝ)/25000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((17751:ℚ)/25000),((712291:ℚ)/1000000),((1476021439:ℚ)/5000000000),((758644631:ℚ)/2000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((17751:ℝ)/25000) ((712291:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((712291:ℚ)/1000000),((357271:ℚ)/500000),((2978277293:ℚ)/10000000000),((3712416383:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((712291:ℝ)/1000000) ((357271:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((357271:ℚ)/500000),((716793:ℚ)/1000000),((600777559:ℚ)/2000000000),((113434259:ℚ)/312500000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((357271:ℝ)/500000) ((716793:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((716793:ℚ)/1000000),((179761:ℚ)/250000),((60577873:ℚ)/200000000),((3545543029:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((716793:ℝ)/1000000) ((179761:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((179761:ℚ)/250000),((144259:ℚ)/200000),((1526656543:ℚ)/5000000000),((1729611143:ℚ)/5000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((179761:ℝ)/250000) ((144259:ℝ)/200000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((144259:ℚ)/200000),((361773:ℚ)/500000),((1538581687:ℚ)/5000000000),((3370782687:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((144259:ℝ)/200000) ((361773:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((361773:ℚ)/500000),((725797:ℚ)/1000000),((3100460897:ℚ)/10000000000),((410006577:ℚ)/1250000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((361773:ℝ)/500000) ((725797:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((725797:ℚ)/1000000),((45503:ℚ)/62500),((780805303:ℚ)/2500000000),((398354527:ℚ)/1250000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((725797:ℝ)/1000000) ((45503:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((45503:ℚ)/62500),((730299:ℚ)/1000000),((3145459113:ℚ)/10000000000),((1545454153:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((45503:ℝ)/62500) ((730299:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((730299:ℚ)/1000000),((14651:ℚ)/20000),((1583594339:ℚ)/5000000000),((748001961:ℚ)/2500000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((730299:ℝ)/1000000) ((14651:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((14651:ℚ)/20000),((734801:ℚ)/1000000),((1594211661:ℚ)/5000000000),((2889829399:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((14651:ℝ)/20000) ((734801:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((734801:ℚ)/1000000),((184263:ℚ)/250000),((3209175839:ℚ)/10000000000),((1392005903:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((734801:ℝ)/1000000) ((184263:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((184263:ℚ)/250000),((370777:ℚ)/500000),((324928279:ℚ)/1000000000),((2674122813:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((184263:ℝ)/250000) ((370777:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((370777:ℚ)/500000),((93257:ℚ)/125000),((3287600901:ℚ)/10000000000),((48798193:ℚ)/200000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((370777:ℝ)/500000) ((93257:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((93257:ℚ)/125000),((37753:ℚ)/50000),((3359198541:ℚ)/10000000000),((545308469:ℚ)/2500000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((93257:ℝ)/125000) ((37753:ℝ)/50000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((37753:ℚ)/50000),((23877:ℚ)/31250),((3424561117:ℚ)/10000000000),((1540833281:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((37753:ℝ)/50000) ((23877:ℝ)/31250),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((41001:ℝ)/62500) ((170757:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((170757:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((10813:ℝ)/15625) ((175259:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node3_6 :
    ∀ r ∈ Set.Icc ((170757:ℝ)/250000) ((175259:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 node4_6
private theorem node0_6 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((175259:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_6
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((352769:ℝ)/500000) ((712291:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node6_9 :
    ∀ r ∈ Set.Icc ((175259:ℝ)/250000) ((712291:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 node7_9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((357271:ℝ)/500000) ((179761:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node9_12 :
    ∀ r ∈ Set.Icc ((712291:ℝ)/1000000) ((179761:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 node10_12
private theorem node6_12 :
    ∀ r ∈ Set.Icc ((175259:ℝ)/250000) ((179761:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node6_9 node9_12
private theorem node0_12 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((179761:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_6 node6_12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((144259:ℝ)/200000) ((725797:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((179761:ℝ)/250000) ((725797:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((45503:ℝ)/62500) ((14651:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((725797:ℝ)/1000000) ((14651:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node12_18 :
    ∀ r ∈ Set.Icc ((179761:ℝ)/250000) ((14651:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_15 node15_18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((734801:ℝ)/1000000) ((370777:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node18_21 :
    ∀ r ∈ Set.Icc ((14651:ℝ)/20000) ((370777:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 node19_21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((93257:ℝ)/125000) ((23877:ℝ)/31250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node21_24 :
    ∀ r ∈ Set.Icc ((370777:ℝ)/500000) ((23877:ℝ)/31250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 node22_24
private theorem node18_24 :
    ∀ r ∈ Set.Icc ((14651:ℝ)/20000) ((23877:ℝ)/31250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node18_21 node21_24
private theorem node12_24 :
    ∀ r ∈ Set.Icc ((179761:ℝ)/250000) ((23877:ℝ)/31250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_18 node18_24
private theorem node0_24 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((23877:ℝ)/31250),
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
end N11Formalization.C450ThirdRadialMid
#check @N11Formalization.C450ThirdRadialMid.bound
#print axioms N11Formalization.C450ThirdRadialMid.params_valid
#print axioms N11Formalization.C450ThirdRadialMid.bound
