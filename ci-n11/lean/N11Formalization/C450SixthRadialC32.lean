import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC32
open C450RadialPacketKernel
def params : Params := ⟨((82181001:ℚ)/32000000),((4349131:ℚ)/6400000),((11350421:ℚ)/16000000),((1:ℚ)/2500)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((6551:ℚ)/10000),((493496599:ℚ)/2500000000),((1544032111:ℚ)/2500000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((6551:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((6551:ℚ)/10000),((13453:ℚ)/20000),((589615387:ℚ)/2500000000),((5326834971:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((6551:ℝ)/10000) ((13453:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((13453:ℚ)/20000),((27257:ℚ)/40000),((2516032251:ℚ)/10000000000),((48529051:ℚ)/100000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((13453:ℝ)/20000) ((27257:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((27257:ℚ)/40000),((3451:ℚ)/5000),((265656529:ℚ)/1000000000),((143726749:ℚ)/312500000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((27257:ℝ)/40000) ((3451:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((3451:ℚ)/5000),((55567:ℚ)/80000),((2721363213:ℚ)/10000000000),((4331893577:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((3451:ℝ)/5000) ((55567:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((55567:ℚ)/80000),((27959:ℚ)/40000),((1391450801:ℚ)/5000000000),((4192251849:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((55567:ℝ)/80000) ((27959:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((27959:ℚ)/40000),((56269:ℚ)/80000),((2841422123:ℚ)/10000000000),((809618033:ℚ)/2000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((27959:ℝ)/40000) ((56269:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((56269:ℚ)/80000),((112889:ℚ)/160000),((2869617817:ℚ)/10000000000),((1949452857:ℚ)/5000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((56269:ℝ)/80000) ((112889:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((112889:ℚ)/160000),((2831:ℚ)/4000),((2897136311:ℚ)/10000000000),((152889859:ℚ)/400000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((112889:ℝ)/160000) ((2831:ℝ)/4000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((2831:ℚ)/4000),((113591:ℚ)/160000),((116960007:ℚ)/400000000),((1872048313:ℚ)/5000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((2831:ℝ)/4000) ((113591:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((113591:ℚ)/160000),((56971:ℚ)/80000),((118009227:ℚ)/400000000),((3664360607:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((113591:ℝ)/160000) ((56971:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((56971:ℚ)/80000),((114293:ℚ)/160000),((1487923937:ℚ)/5000000000),((143317293:ℚ)/400000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((56971:ℝ)/80000) ((114293:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((114293:ℚ)/160000),((28661:ℚ)/40000),((3000870731:ℚ)/10000000000),((174984673:ℚ)/500000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((114293:ℝ)/160000) ((28661:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((28661:ℚ)/40000),((22999:ℚ)/32000),((47270581:ℚ)/156250000),((853627849:ℚ)/2500000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((28661:ℝ)/40000) ((22999:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((22999:ℚ)/32000),((57673:ℚ)/80000),((3049204229:ℚ)/10000000000),((3327236681:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((22999:ℝ)/32000) ((57673:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((57673:ℚ)/80000),((115697:ℚ)/160000),((614509597:ℚ)/2000000000),((80942497:ℚ)/250000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((57673:ℝ)/80000) ((115697:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((115697:ℚ)/160000),((7253:ℚ)/10000),((1547681881:ℚ)/5000000000),((3145707623:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((115697:ℝ)/160000) ((7253:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((7253:ℚ)/10000),((116399:ℚ)/160000),((623533223:ℚ)/2000000000),((3051037587:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((7253:ℝ)/10000) ((116399:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((116399:ℚ)/160000),((467:ℚ)/640),((1569734449:ℚ)/5000000000),((2953432051:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((116399:ℝ)/160000) ((467:ℝ)/640),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((467:ℚ)/640),((29363:ℚ)/40000),((3181627931:ℚ)/10000000000),((1426294733:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((467:ℝ)/640) ((29363:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((29363:ℚ)/40000),((59077:ℚ)/80000),((805484837:ℚ)/2500000000),((2639696681:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((29363:ℝ)/40000) ((59077:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((59077:ℚ)/80000),((14857:ℚ)/20000),((3260493043:ℚ)/10000000000),((1204264849:ℚ)/5000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((59077:ℝ)/80000) ((14857:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((14857:ℚ)/20000),((6013:ℚ)/8000),((833162479:ℚ)/2500000000),((1076604173:ℚ)/5000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((14857:ℝ)/20000) ((6013:ℝ)/8000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((6013:ℚ)/8000),((1901:ℚ)/2500),((1699340681:ℚ)/5000000000),((1521074613:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((6013:ℝ)/8000) ((1901:ℝ)/2500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((6551:ℝ)/10000) ((27257:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((27257:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((3451:ℝ)/5000) ((27959:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node3_6 :
    ∀ r ∈ Set.Icc ((27257:ℝ)/40000) ((27959:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 node4_6
private theorem node0_6 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((27959:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_6
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((56269:ℝ)/80000) ((2831:ℝ)/4000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node6_9 :
    ∀ r ∈ Set.Icc ((27959:ℝ)/40000) ((2831:ℝ)/4000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 node7_9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((113591:ℝ)/160000) ((114293:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node9_12 :
    ∀ r ∈ Set.Icc ((2831:ℝ)/4000) ((114293:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 node10_12
private theorem node6_12 :
    ∀ r ∈ Set.Icc ((27959:ℝ)/40000) ((114293:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node6_9 node9_12
private theorem node0_12 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((114293:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_6 node6_12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((28661:ℝ)/40000) ((57673:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((114293:ℝ)/160000) ((57673:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((115697:ℝ)/160000) ((116399:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((57673:ℝ)/80000) ((116399:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node12_18 :
    ∀ r ∈ Set.Icc ((114293:ℝ)/160000) ((116399:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_15 node15_18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((467:ℝ)/640) ((59077:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node18_21 :
    ∀ r ∈ Set.Icc ((116399:ℝ)/160000) ((59077:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 node19_21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((14857:ℝ)/20000) ((1901:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node21_24 :
    ∀ r ∈ Set.Icc ((59077:ℝ)/80000) ((1901:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 node22_24
private theorem node18_24 :
    ∀ r ∈ Set.Icc ((116399:ℝ)/160000) ((1901:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node18_21 node21_24
private theorem node12_24 :
    ∀ r ∈ Set.Icc ((114293:ℝ)/160000) ((1901:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_18 node18_24
private theorem node0_24 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1901:ℝ)/2500),
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
end N11Formalization.C450SixthRadialC32
#check @N11Formalization.C450SixthRadialC32.bound
#print axioms N11Formalization.C450SixthRadialC32.params_valid
#print axioms N11Formalization.C450SixthRadialC32.params_sum
#print axioms N11Formalization.C450SixthRadialC32.bound
