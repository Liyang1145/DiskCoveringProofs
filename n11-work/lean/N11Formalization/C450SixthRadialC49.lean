import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC49
open C450RadialPacketKernel
def params : Params := ⟨((512011499:ℚ)/200000000),((137530101:ℚ)/200000000),((64571:ℚ)/100000),((441:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((105241:ℚ)/160000),((2039655897:ℚ)/10000000000),((641359893:ℚ)/1000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((105241:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((105241:ℚ)/160000),((216523:ℚ)/320000),((2432342421:ℚ)/10000000000),((138245457:ℚ)/250000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((105241:ℝ)/160000) ((216523:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((216523:ℚ)/320000),((439087:ℚ)/640000),((2592398173:ℚ)/10000000000),((1007403627:ℚ)/2000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((216523:ℝ)/320000) ((439087:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((439087:ℚ)/640000),((55641:ℚ)/80000),((2734599661:ℚ)/10000000000),((4773367083:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((439087:ℝ)/640000) ((55641:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55641:ℚ)/80000),((896297:ℚ)/1280000),((699991641:ℚ)/2500000000),((4495529879:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55641:ℝ)/80000) ((896297:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((896297:ℚ)/1280000),((451169:ℚ)/640000),((715478631:ℚ)/2500000000),((4350443383:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((896297:ℝ)/1280000) ((451169:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((451169:ℚ)/640000),((908379:ℚ)/1280000),((584139243:ℚ)/2000000000),((420067863:ℚ)/1000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((451169:ℝ)/640000) ((908379:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((908379:ℚ)/1280000),((1822799:ℚ)/2560000),((2948969921:ℚ)/10000000000),((2022857169:ℚ)/5000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((908379:ℝ)/1280000) ((1822799:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1822799:ℚ)/2560000),((45721:ℚ)/64000),((2976532873:ℚ)/10000000000),((247880759:ℚ)/625000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1822799:ℝ)/2560000) ((45721:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45721:ℚ)/64000),((1834881:ℚ)/2560000),((600681737:ℚ)/2000000000),((242807907:ℚ)/625000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45721:ℝ)/64000) ((1834881:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1834881:ℚ)/2560000),((3675803:ℚ)/5120000),((3016595917:ℚ)/10000000000),((1901059183:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1834881:ℝ)/2560000) ((3675803:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((3675803:ℚ)/5120000),((920461:ℚ)/1280000),((378702451:ℚ)/1250000000),((3760064449:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((3675803:ℝ)/5120000) ((920461:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((920461:ℚ)/1280000),((737577:ℚ)/1024000),((1521241171:ℚ)/5000000000),((371755771:ℚ)/1000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((920461:ℝ)/1280000) ((737577:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((737577:ℚ)/1024000),((1846963:ℚ)/2560000),((763796659:ℚ)/2500000000),((1837291203:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((737577:ℝ)/1024000) ((1846963:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1846963:ℚ)/2560000),((3699967:ℚ)/5120000),((3067734933:ℚ)/10000000000),((363112187:ℚ)/1000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1846963:ℝ)/2560000) ((3699967:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((3699967:ℚ)/5120000),((463251:ℚ)/640000),((3080129611:ℚ)/10000000000),((717431687:ℚ)/2000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((3699967:ℝ)/5120000) ((463251:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((463251:ℚ)/640000),((7418057:ℚ)/10240000),((3086270069:ℚ)/10000000000),((3542673347:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((463251:ℝ)/640000) ((7418057:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((7418057:ℚ)/10240000),((3712049:ℚ)/5120000),((618474597:ℚ)/2000000000),((3520229003:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((7418057:ℝ)/10240000) ((3712049:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((3712049:ℚ)/5120000),((7430139:ℚ)/10240000),((38730483:ℚ)/125000000),((3497646673:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((3712049:ℝ)/5120000) ((7430139:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((7430139:ℚ)/10240000),((371809:ℚ)/512000),((776116827:ℚ)/2500000000),((1737461831:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((7430139:ℝ)/10240000) ((371809:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((371809:ℚ)/512000),((7442221:ℚ)/10240000),((3110459263:ℚ)/10000000000),((863014297:ℚ)/2500000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((371809:ℝ)/512000) ((7442221:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((7442221:ℚ)/10240000),((3724131:ℚ)/5120000),((3116414773:ℚ)/10000000000),((3429044377:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((7442221:ℝ)/10240000) ((3724131:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((3724131:ℚ)/5120000),((7454303:ℚ)/10240000),((3122334103:ℚ)/10000000000),((170294113:ℚ)/500000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((3724131:ℝ)/5120000) ((7454303:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((7454303:ℚ)/10240000),((932543:ℚ)/1280000),((782054379:ℚ)/2500000000),((845641941:ℚ)/2500000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((7454303:ℝ)/10240000) ((932543:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((932543:ℚ)/1280000),((1493277:ℚ)/2048000),((3134065269:ℚ)/10000000000),((1679548857:ℚ)/5000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((932543:ℝ)/1280000) ((1493277:ℝ)/2048000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((1493277:ℚ)/2048000),((3736213:ℚ)/5120000),((3139877619:ℚ)/10000000000),((3335468821:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((1493277:ℝ)/2048000) ((3736213:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((3736213:ℚ)/5120000),((7478467:ℚ)/10240000),((98301713:ℚ)/312500000),((3311677681:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((3736213:ℝ)/5120000) ((7478467:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((7478467:ℚ)/10240000),((1871127:ℚ)/2560000),((3151397109:ℚ)/10000000000),((3287720769:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((7478467:ℝ)/10240000) ((1871127:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((1871127:ℚ)/2560000),((7490549:ℚ)/10240000),((631420949:ℚ)/2000000000),((815898607:ℚ)/2500000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((1871127:ℝ)/2560000) ((7490549:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((7490549:ℚ)/10240000),((749659:ℚ)/1024000),((1581388983:ℚ)/5000000000),((3239294871:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((7490549:ℝ)/10240000) ((749659:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((749659:ℚ)/1024000),((117323:ℚ)/160000),((634804423:ℚ)/2000000000),((803704541:ℚ)/2500000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((749659:ℝ)/1024000) ((117323:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((117323:ℚ)/160000),((3760377:ℚ)/5120000),((3185131439:ℚ)/10000000000),((197832301:ℚ)/625000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((117323:ℝ)/160000) ((3760377:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((3760377:ℚ)/5120000),((1883209:ℚ)/2560000),((799026943:ℚ)/2500000000),((389381973:ℚ)/1250000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((3760377:ℝ)/5120000) ((1883209:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((1883209:ℚ)/2560000),((3772459:ℚ)/5120000),((641390581:ℚ)/2000000000),((61279953:ℚ)/200000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((1883209:ℝ)/2560000) ((3772459:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((3772459:ℚ)/5120000),((7557:ℚ)/10240),((402208573:ℚ)/1250000000),((1506050921:ℚ)/5000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((3772459:ℝ)/5120000) ((7557:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((7557:ℚ)/10240),((1895291:ℚ)/2560000),((3238718371:ℚ)/10000000000),((92478883:ℚ)/312500000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((7557:ℝ)/10240) ((1895291:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((1895291:ℚ)/2560000),((475333:ℚ)/640000),((3259270311:ℚ)/10000000000),((570185381:ℚ)/2000000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((1895291:ℝ)/2560000) ((475333:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((475333:ℚ)/640000),((1907373:ℚ)/2560000),((655867397:ℚ)/2000000000),((171147693:ℚ)/625000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((475333:ℝ)/640000) ((1907373:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((1907373:ℚ)/2560000),((956707:ℚ)/1280000),((206183151:ℚ)/625000000),((10484383:ℚ)/40000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((1907373:ℝ)/2560000) ((956707:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((956707:ℚ)/1280000),((240687:ℚ)/320000),((3336743031:ℚ)/10000000000),((2498462353:ℚ)/10000000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((956707:ℝ)/1280000) ((240687:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((240687:ℚ)/320000),((97483:ℚ)/128000),((1703581821:ℚ)/5000000000),((446704909:ℚ)/2000000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((240687:ℝ)/320000) ((97483:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((97483:ℚ)/128000),((30841:ℚ)/40000),((1735571183:ℚ)/5000000000),((1577695361:ℚ)/10000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((97483:ℝ)/128000) ((30841:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((216523:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((439087:ℝ)/640000) ((896297:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((216523:ℝ)/320000) ((896297:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((896297:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((896297:ℝ)/1280000) ((908379:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((1822799:ℝ)/2560000) ((1834881:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((908379:ℝ)/1280000) ((1834881:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node5_10 :
    ∀ r ∈ Set.Icc ((896297:ℝ)/1280000) ((1834881:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_7 node7_10
private theorem node0_10 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1834881:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((1834881:ℝ)/2560000) ((920461:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((737577:ℝ)/1024000) ((3699967:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((920461:ℝ)/1280000) ((3699967:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node10_15 :
    ∀ r ∈ Set.Icc ((1834881:ℝ)/2560000) ((3699967:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((463251:ℝ)/640000) ((3712049:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((3699967:ℝ)/5120000) ((3712049:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((7430139:ℝ)/10240000) ((7442221:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node18_21 :
    ∀ r ∈ Set.Icc ((3712049:ℝ)/5120000) ((7442221:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 node19_21
private theorem node15_21 :
    ∀ r ∈ Set.Icc ((3699967:ℝ)/5120000) ((7442221:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_18 node18_21
private theorem node10_21 :
    ∀ r ∈ Set.Icc ((1834881:ℝ)/2560000) ((7442221:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_15 node15_21
private theorem node0_21 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7442221:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_10 node10_21
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((7442221:ℝ)/10240000) ((7454303:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((932543:ℝ)/1280000) ((3736213:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node23_26 :
    ∀ r ∈ Set.Icc ((7454303:ℝ)/10240000) ((3736213:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 node24_26
private theorem node21_26 :
    ∀ r ∈ Set.Icc ((7442221:ℝ)/10240000) ((3736213:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_23 node23_26
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((3736213:ℝ)/5120000) ((1871127:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node29_31 :
    ∀ r ∈ Set.Icc ((7490549:ℝ)/10240000) ((117323:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf29 leaf30
private theorem node28_31 :
    ∀ r ∈ Set.Icc ((1871127:ℝ)/2560000) ((117323:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 node29_31
private theorem node26_31 :
    ∀ r ∈ Set.Icc ((3736213:ℝ)/5120000) ((117323:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node26_28 node28_31
private theorem node21_31 :
    ∀ r ∈ Set.Icc ((7442221:ℝ)/10240000) ((117323:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_26 node26_31
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((117323:ℝ)/160000) ((1883209:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((3772459:ℝ)/5120000) ((1895291:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 leaf35
private theorem node33_36 :
    ∀ r ∈ Set.Icc ((1883209:ℝ)/2560000) ((1895291:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 node34_36
private theorem node31_36 :
    ∀ r ∈ Set.Icc ((117323:ℝ)/160000) ((1895291:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node31_33 node33_36
private theorem node37_39 :
    ∀ r ∈ Set.Icc ((475333:ℝ)/640000) ((956707:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 leaf38
private theorem node36_39 :
    ∀ r ∈ Set.Icc ((1895291:ℝ)/2560000) ((956707:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 node37_39
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((240687:ℝ)/320000) ((30841:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 leaf41
private theorem node39_42 :
    ∀ r ∈ Set.Icc ((956707:ℝ)/1280000) ((30841:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 node40_42
private theorem node36_42 :
    ∀ r ∈ Set.Icc ((1895291:ℝ)/2560000) ((30841:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node36_39 node39_42
private theorem node31_42 :
    ∀ r ∈ Set.Icc ((117323:ℝ)/160000) ((30841:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node31_36 node36_42
private theorem node21_42 :
    ∀ r ∈ Set.Icc ((7442221:ℝ)/10240000) ((30841:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_31 node31_42
private theorem node0_42 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((30841:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_21 node21_42
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_42
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC49
#check @N11Formalization.C450SixthRadialC49.bound
#print axioms N11Formalization.C450SixthRadialC49.params_valid
#print axioms N11Formalization.C450SixthRadialC49.params_sum
#print axioms N11Formalization.C450SixthRadialC49.bound
