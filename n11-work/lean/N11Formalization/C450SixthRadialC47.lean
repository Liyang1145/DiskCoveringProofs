import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC47
open C450RadialPacketKernel
def params : Params := ⟨((8196358461:ℚ)/3200000000),((2196307139:ℚ)/3200000000),((1306189:ℚ)/2000000),((391:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((105191:ℚ)/160000),((40641871:ℚ)/200000000),((638605727:ℚ)/1000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((105191:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((105191:ℚ)/160000),((216373:ℚ)/320000),((605965161:ℚ)/2500000000),((5506287317:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((105191:ℝ)/160000) ((216373:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((216373:ℚ)/320000),((438737:ℚ)/640000),((1291822869:ℚ)/5000000000),((501567947:ℚ)/1000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((216373:ℝ)/320000) ((438737:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((438737:ℚ)/640000),((55591:ℚ)/80000),((2725671859:ℚ)/10000000000),((2376594921:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((438737:ℝ)/640000) ((55591:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55591:ℚ)/80000),((895447:ℚ)/1280000),((174436377:ℚ)/625000000),((4476568577:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55591:ℝ)/80000) ((895447:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((895447:ℚ)/1280000),((450719:ℚ)/640000),((713222967:ℚ)/2500000000),((4332113971:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((895447:ℝ)/1280000) ((450719:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((450719:ℚ)/640000),((907429:ℚ)/1280000),((582330551:ℚ)/2000000000),((6692799:ℚ)/16000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((450719:ℝ)/640000) ((907429:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((907429:ℚ)/1280000),((1820849:ℚ)/2560000),((1469961097:ℚ)/5000000000),((805741129:ℚ)/2000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((907429:ℝ)/1280000) ((1820849:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1820849:ℚ)/2560000),((45671:ℚ)/64000),((2967484797:ℚ)/10000000000),((1974713583:ℚ)/5000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1820849:ℝ)/2560000) ((45671:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45671:ℚ)/64000),((1832831:ℚ)/2560000),((598872811:ℚ)/2000000000),((967152837:ℚ)/2500000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45671:ℝ)/64000) ((1832831:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1832831:ℚ)/2560000),((3671653:ℚ)/5120000),((3007554397:ℚ)/10000000000),((151446381:ℚ)/400000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1832831:ℝ)/2560000) ((3671653:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((3671653:ℚ)/5120000),((919411:ℚ)/1280000),((3020582103:ℚ)/10000000000),((936071587:ℚ)/2500000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((3671653:ℝ)/5120000) ((919411:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((919411:ℚ)/1280000),((736727:ℚ)/1024000),((1516724873:ℚ)/5000000000),((3701962151:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((919411:ℝ)/1280000) ((736727:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((736727:ℚ)/1024000),((1844813:ℚ)/2560000),((761539957:ℚ)/2500000000),((3659171253:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((736727:ℝ)/1024000) ((1844813:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1844813:ℚ)/2560000),((3695617:ℚ)/5120000),((152935739:ℚ)/500000000),((112996783:ℚ)/312500000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1844813:ℝ)/2560000) ((3695617:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((3695617:ℚ)/5120000),((462701:ℚ)/640000),((3071116969:ℚ)/10000000000),((1786060983:ℚ)/5000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((3695617:ℝ)/5120000) ((462701:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((462701:ℚ)/640000),((3707599:ℚ)/5120000),((385421087:ℚ)/1250000000),((3527827307:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((462701:ℝ)/640000) ((3707599:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((3707599:ℚ)/5120000),((7421189:ℚ)/10240000),((3089438839:ℚ)/10000000000),((139319729:ℚ)/400000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((3707599:ℝ)/5120000) ((7421189:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((7421189:ℚ)/10240000),((371359:ℚ)/512000),((1547736101:ℚ)/5000000000),((69207347:ℚ)/200000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((7421189:ℝ)/10240000) ((371359:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((371359:ℚ)/512000),((7433171:ℚ)/10240000),((3101469057:ℚ)/10000000000),((1718799293:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((371359:ℝ)/512000) ((7433171:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((7433171:ℚ)/10240000),((3719581:ℚ)/5120000),((310742967:ℚ)/1000000000),((426835509:ℚ)/1250000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((7433171:ℝ)/10240000) ((3719581:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((3719581:ℚ)/5120000),((7445153:ℚ)/10240000),((1556677153:ℚ)/5000000000),((3391620849:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((3719581:ℝ)/5120000) ((7445153:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((7445153:ℚ)/10240000),((931393:ℚ)/1280000),((389905403:ℚ)/1250000000),((3368405859:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((7445153:ℝ)/10240000) ((931393:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((931393:ℚ)/1280000),((1491427:ℚ)/2048000),((3125096683:ℚ)/10000000000),((3345035939:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((931393:ℝ)/1280000) ((1491427:ℝ)/2048000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((1491427:ℚ)/2048000),((3731563:ℚ)/5120000),((391364367:ℚ)/1250000000),((3321507813:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((1491427:ℝ)/2048000) ((3731563:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((3731563:ℚ)/5120000),((1868777:ℚ)/2560000),((3142446823:ℚ)/10000000000),((3297818093:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((3731563:ℝ)/5120000) ((1868777:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((1868777:ℚ)/2560000),((748709:ℚ)/1024000),((788460213:ℚ)/2500000000),((3249939693:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((1868777:ℝ)/2560000) ((748709:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((748709:ℚ)/1024000),((117173:ℚ)/160000),((3165098941:ℚ)/10000000000),((800342767:ℚ)/2500000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((748709:ℝ)/1024000) ((117173:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((117173:ℚ)/160000),((3755527:ℚ)/5120000),((3176222961:ℚ)/10000000000),((3152080281:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((117173:ℝ)/160000) ((3755527:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((3755527:ℚ)/5120000),((1880759:ℚ)/2560000),((1593607369:ℚ)/5000000000),((387754109:ℚ)/1250000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((3755527:ℝ)/5120000) ((1880759:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((1880759:ℚ)/2560000),((3767509:ℚ)/5120000),((3198076051:ℚ)/10000000000),((381398947:ℚ)/1250000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((1880759:ℝ)/2560000) ((3767509:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((3767509:ℚ)/5120000),((7547:ℚ)/10240),((3208808641:ℚ)/10000000000),((2999515991:ℚ)/10000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((3767509:ℝ)/5120000) ((7547:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((7547:ℚ)/10240),((1892741:ℚ)/2560000),((3229894397:ℚ)/10000000000),((2946962193:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((7547:ℝ)/10240) ((1892741:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((1892741:ℚ)/2560000),((474683:ℚ)/640000),((1625242559:ℚ)/5000000000),((2839023923:ℚ)/10000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((1892741:ℝ)/2560000) ((474683:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((474683:ℚ)/640000),((1904723:ℚ)/2560000),((1635296659:ℚ)/5000000000),((681734021:ℚ)/2500000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((474683:ℝ)/640000) ((1904723:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((1904723:ℚ)/2560000),((955357:ℚ)/1280000),((658046191:ℚ)/2000000000),((1305081917:ℚ)/5000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((1904723:ℝ)/2560000) ((955357:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((955357:ℚ)/1280000),((240337:ℚ)/320000),((3328139791:ℚ)/10000000000),((311005921:ℚ)/1250000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((955357:ℝ)/1280000) ((240337:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((240337:ℚ)/320000),((97333:ℚ)/128000),((1699391271:ℚ)/5000000000),((2224223693:ℚ)/10000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((240337:ℝ)/320000) ((97333:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((97333:ℚ)/128000),((30791:ℚ)/40000),((3463020411:ℚ)/10000000000),((1571139159:ℚ)/10000000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((97333:ℝ)/128000) ((30791:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((216373:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((216373:ℝ)/320000) ((55591:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((55591:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((55591:ℝ)/80000) ((450719:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((907429:ℝ)/1280000) ((45671:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node6_9 :
    ∀ r ∈ Set.Icc ((450719:ℝ)/640000) ((45671:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 node7_9
private theorem node4_9 :
    ∀ r ∈ Set.Icc ((55591:ℝ)/80000) ((45671:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_9
private theorem node0_9 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((45671:ℝ)/64000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_9
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((45671:ℝ)/64000) ((3671653:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((919411:ℝ)/1280000) ((1844813:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node11_14 :
    ∀ r ∈ Set.Icc ((3671653:ℝ)/5120000) ((1844813:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 node12_14
private theorem node9_14 :
    ∀ r ∈ Set.Icc ((45671:ℝ)/64000) ((1844813:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node9_11 node11_14
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((1844813:ℝ)/2560000) ((462701:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((3707599:ℝ)/5120000) ((371359:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((462701:ℝ)/640000) ((371359:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node14_19 :
    ∀ r ∈ Set.Icc ((1844813:ℝ)/2560000) ((371359:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_16 node16_19
private theorem node9_19 :
    ∀ r ∈ Set.Icc ((45671:ℝ)/64000) ((371359:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node9_14 node14_19
private theorem node0_19 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((371359:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_9 node9_19
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((371359:ℝ)/512000) ((3719581:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((7445153:ℝ)/10240000) ((1491427:ℝ)/2048000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node21_24 :
    ∀ r ∈ Set.Icc ((3719581:ℝ)/5120000) ((1491427:ℝ)/2048000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 node22_24
private theorem node19_24 :
    ∀ r ∈ Set.Icc ((371359:ℝ)/512000) ((1491427:ℝ)/2048000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_21 node21_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((1491427:ℝ)/2048000) ((1868777:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((748709:ℝ)/1024000) ((3755527:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node26_29 :
    ∀ r ∈ Set.Icc ((1868777:ℝ)/2560000) ((3755527:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 node27_29
private theorem node24_29 :
    ∀ r ∈ Set.Icc ((1491427:ℝ)/2048000) ((3755527:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_26 node26_29
private theorem node19_29 :
    ∀ r ∈ Set.Icc ((371359:ℝ)/512000) ((3755527:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_24 node24_29
private theorem node29_31 :
    ∀ r ∈ Set.Icc ((3755527:ℝ)/5120000) ((3767509:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf29 leaf30
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((7547:ℝ)/10240) ((474683:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 leaf33
private theorem node31_34 :
    ∀ r ∈ Set.Icc ((3767509:ℝ)/5120000) ((474683:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 node32_34
private theorem node29_34 :
    ∀ r ∈ Set.Icc ((3755527:ℝ)/5120000) ((474683:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node29_31 node31_34
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((474683:ℝ)/640000) ((955357:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 leaf35
private theorem node37_39 :
    ∀ r ∈ Set.Icc ((240337:ℝ)/320000) ((30791:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 leaf38
private theorem node36_39 :
    ∀ r ∈ Set.Icc ((955357:ℝ)/1280000) ((30791:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 node37_39
private theorem node34_39 :
    ∀ r ∈ Set.Icc ((474683:ℝ)/640000) ((30791:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node34_36 node36_39
private theorem node29_39 :
    ∀ r ∈ Set.Icc ((3755527:ℝ)/5120000) ((30791:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node29_34 node34_39
private theorem node19_39 :
    ∀ r ∈ Set.Icc ((371359:ℝ)/512000) ((30791:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_29 node29_39
private theorem node0_39 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((30791:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_19 node19_39
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_39
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC47
#check @N11Formalization.C450SixthRadialC47.bound
#print axioms N11Formalization.C450SixthRadialC47.params_valid
#print axioms N11Formalization.C450SixthRadialC47.params_sum
#print axioms N11Formalization.C450SixthRadialC47.bound
