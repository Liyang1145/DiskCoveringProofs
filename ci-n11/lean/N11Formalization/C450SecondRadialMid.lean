import N11Formalization.C450SecondRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SecondRadialMid
open C450SecondRadialKernel
def packet0 : Packet := ⟨((31:ℚ)/50),((262360041:ℚ)/400000000),((1994105083:ℚ)/10000000000),((1562119799:ℚ)/2500000000)⟩
theorem valid0 : Valid .mid packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((262360041:ℝ)/400000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((262360041:ℚ)/400000000),((539080123:ℚ)/800000000),((595287461:ℚ)/2500000000),((5388700747:ℚ)/10000000000)⟩
theorem valid1 : Valid .mid packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((262360041:ℝ)/400000000) ((539080123:ℝ)/800000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((539080123:ℚ)/800000000),((1092520287:ℚ)/1600000000),((2539513869:ℚ)/10000000000),((981805857:ℚ)/2000000000)⟩
theorem valid2 : Valid .mid packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((539080123:ℝ)/800000000) ((1092520287:ℝ)/1600000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((1092520287:ℚ)/1600000000),((138360041:ℚ)/200000000),((1340296323:ℚ)/5000000000),((1163083933:ℚ)/2500000000)⟩
theorem valid3 : Valid .mid packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((1092520287:ℝ)/1600000000) ((138360041:ℝ)/200000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((138360041:ℚ)/200000000),((1121240369:ℚ)/1600000000),((1403632771:ℚ)/5000000000),((4381784167:ℚ)/10000000000)⟩
theorem valid4 : Valid .mid packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((138360041:ℝ)/200000000) ((1121240369:ℝ)/1600000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((1121240369:ℚ)/1600000000),((2256840779:ℚ)/3200000000),((573177041:ℚ)/2000000000),((163784651:ℚ)/400000000)⟩
theorem valid5 : Valid .mid packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((1121240369:ℝ)/1600000000) ((2256840779:ℝ)/3200000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((2256840779:ℚ)/3200000000),((113560041:ℚ)/160000000),((2921656491:ℚ)/10000000000),((3943671319:ℚ)/10000000000)⟩
theorem valid6 : Valid .mid packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((2256840779:ℝ)/3200000000) ((113560041:ℝ)/160000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((113560041:ℚ)/160000000),((4556761681:ℚ)/6400000000),((589706793:ℚ)/2000000000),((94676023:ℚ)/250000000)⟩
theorem valid7 : Valid .mid packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((113560041:ℝ)/160000000) ((4556761681:ℝ)/6400000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((4556761681:ℚ)/6400000000),((2285560861:ℚ)/3200000000),((1487384259:ℚ)/5000000000),((3706368949:ℚ)/10000000000)⟩
theorem valid8 : Valid .mid packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((4556761681:ℝ)/6400000000) ((2285560861:ℝ)/3200000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((2285560861:ℚ)/3200000000),((4585481763:ℚ)/6400000000),((3000380497:ℚ)/10000000000),((1811993151:ℚ)/5000000000)⟩
theorem valid9 : Valid .mid packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((2285560861:ℝ)/3200000000) ((4585481763:ℝ)/6400000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((4585481763:ℚ)/6400000000),((1149960451:ℚ)/1600000000),((302538913:ℚ)/1000000000),((353977333:ℚ)/1000000000)⟩
theorem valid10 : Valid .mid packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((4585481763:ℝ)/6400000000) ((1149960451:ℝ)/1600000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((1149960451:ℚ)/1600000000),((922840369:ℚ)/1280000000),((23826661:ℚ)/78125000),((3453595927:ℚ)/10000000000)⟩
theorem valid11 : Valid .mid packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((1149960451:ℝ)/1600000000) ((922840369:ℝ)/1280000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((922840369:ℚ)/1280000000),((2314280943:ℚ)/3200000000),((1536834083:ℚ)/5000000000),((3365302963:ℚ)/10000000000)⟩
theorem valid12 : Valid .mid packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((922840369:ℝ)/1280000000) ((2314280943:ℝ)/3200000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((2314280943:ℚ)/3200000000),((4642921927:ℚ)/6400000000),((1548486077:ℚ)/5000000000),((1637361549:ℚ)/5000000000)⟩
theorem valid13 : Valid .mid packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((2314280943:ℝ)/3200000000) ((4642921927:ℝ)/6400000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((4642921927:ℚ)/6400000000),((291080123:ℚ)/400000000),((31197401:ℚ)/100000000),((636332157:ℚ)/2000000000)⟩
theorem valid14 : Valid .mid packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((4642921927:ℝ)/6400000000) ((291080123:ℝ)/400000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((291080123:ℚ)/400000000),((4671642009:ℚ)/6400000000),((1570993383:ℚ)/5000000000),((1542945601:ℚ)/5000000000)⟩
theorem valid15 : Valid .mid packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((291080123:ℝ)/400000000) ((4671642009:ℝ)/6400000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((4671642009:ℚ)/6400000000),((93720041:ℚ)/128000000),((3163726203:ℚ)/10000000000),((2987153729:ℚ)/10000000000)⟩
theorem valid16 : Valid .mid packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((4671642009:ℝ)/6400000000) ((93720041:ℝ)/128000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((93720041:ℚ)/128000000),((1178680533:ℚ)/1600000000),((3205736317:ℚ)/10000000000),((2885143419:ℚ)/10000000000)⟩
theorem valid17 : Valid .mid packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((93720041:ℝ)/128000000) ((1178680533:ℝ)/1600000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((1178680533:ℚ)/1600000000),((2371721107:ℚ)/3200000000),((1622935167:ℚ)/5000000000),((106791639:ℚ)/400000000)⟩
theorem valid18 : Valid .mid packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((1178680533:ℝ)/1600000000) ((2371721107:ℝ)/3200000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((2371721107:ℚ)/3200000000),((596520287:ℚ)/800000000),((3284219439:ℚ)/10000000000),((2435961179:ℚ)/10000000000)⟩
theorem valid19 : Valid .mid packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((2371721107:ℝ)/3200000000) ((596520287:ℝ)/800000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((596520287:ℚ)/800000000),((241480123:ℚ)/320000000),((1677945091:ℚ)/5000000000),((435541509:ℚ)/2000000000)⟩
theorem valid20 : Valid .mid packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((596520287:ℝ)/800000000) ((241480123:ℝ)/320000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((241480123:ℚ)/320000000),((76360041:ℚ)/100000000),((3421339703:ℚ)/10000000000),((1538347217:ℚ)/10000000000)⟩
theorem valid21 : Valid .mid packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((241480123:ℝ)/320000000) ((76360041:ℝ)/100000000),
    model .mid r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .mid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((539080123:ℝ)/800000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((1092520287:ℝ)/1600000000) ((1121240369:ℝ)/1600000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((539080123:ℝ)/800000000) ((1121240369:ℝ)/1600000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1121240369:ℝ)/1600000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((2256840779:ℝ)/3200000000) ((4556761681:ℝ)/6400000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((1121240369:ℝ)/1600000000) ((4556761681:ℝ)/6400000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((2285560861:ℝ)/3200000000) ((1149960451:ℝ)/1600000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((4556761681:ℝ)/6400000000) ((1149960451:ℝ)/1600000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((1121240369:ℝ)/1600000000) ((1149960451:ℝ)/1600000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1149960451:ℝ)/1600000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((1149960451:ℝ)/1600000000) ((2314280943:ℝ)/3200000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((4642921927:ℝ)/6400000000) ((4671642009:ℝ)/6400000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node13_16 :
    ∀ r ∈ Set.Icc ((2314280943:ℝ)/3200000000) ((4671642009:ℝ)/6400000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 node14_16
private theorem node11_16 :
    ∀ r ∈ Set.Icc ((1149960451:ℝ)/1600000000) ((4671642009:ℝ)/6400000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((93720041:ℝ)/128000000) ((2371721107:ℝ)/3200000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((4671642009:ℝ)/6400000000) ((2371721107:ℝ)/3200000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((596520287:ℝ)/800000000) ((76360041:ℝ)/100000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node19_22 :
    ∀ r ∈ Set.Icc ((2371721107:ℝ)/3200000000) ((76360041:ℝ)/100000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 node20_22
private theorem node16_22 :
    ∀ r ∈ Set.Icc ((4671642009:ℝ)/6400000000) ((76360041:ℝ)/100000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node16_19 node19_22
private theorem node11_22 :
    ∀ r ∈ Set.Icc ((1149960451:ℝ)/1600000000) ((76360041:ℝ)/100000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node11_16 node16_22
private theorem node0_22 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((76360041:ℝ)/100000000),
      model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_22
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish .mid:ℝ),
    model .mid r < (cap:ℝ) := by
  have hh := node0_22
  norm_num [finish,F,E,R] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model .mid r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join near_bound (fun r hr => far_bound .mid r hr)
end N11Formalization.C450SecondRadialMid
#check @N11Formalization.C450SecondRadialMid.bound
#print axioms N11Formalization.C450SecondRadialMid.bound
