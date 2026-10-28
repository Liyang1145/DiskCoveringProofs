import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC54
open C450RadialPacketKernel
def params : Params := ⟨((261735818703:ℚ)/102400000000),((70829480497:ℚ)/102400000000),((501799:ℚ)/800000),((283:ℚ)/20000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((52683:ℚ)/80000),((1029189549:ℚ)/5000000000),((6482013107:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((52683:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((52683:ℚ)/80000),((108449:ℚ)/160000),((490662383:ℚ)/2000000000),((698532147:ℚ)/1250000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((52683:ℝ)/80000) ((108449:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((108449:ℚ)/160000),((219981:ℚ)/320000),((653504989:ℚ)/2500000000),((5090006991:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((108449:ℝ)/160000) ((219981:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((219981:ℚ)/320000),((27883:ℚ)/40000),((2756636383:ℚ)/10000000000),((18841677:ℚ)/39062500)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((219981:ℝ)/320000) ((27883:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((27883:ℚ)/40000),((449211:ℚ)/640000),((56442673:ℚ)/200000000),((113565261:ℚ)/250000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((27883:ℝ)/40000) ((449211:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((449211:ℚ)/640000),((226147:ℚ)/320000),((2884165631:ℚ)/10000000000),((2197976923:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((449211:ℝ)/640000) ((226147:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((226147:ℚ)/320000),((455377:ℚ)/640000),((735747049:ℚ)/2500000000),((169782949:ℚ)/400000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((226147:ℝ)/320000) ((455377:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((455377:ℚ)/640000),((913837:ℚ)/1280000),((742816763:ℚ)/2500000000),((2043971743:ℚ)/5000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((455377:ℝ)/640000) ((913837:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((913837:ℚ)/1280000),((22923:ℚ)/32000),((1499412699:ℚ)/5000000000),((500933427:ℚ)/1250000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((913837:ℝ)/1280000) ((22923:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((22923:ℚ)/32000),((920003:ℚ)/1280000),((3025687151:ℚ)/10000000000),((245339549:ℚ)/625000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((22923:ℝ)/32000) ((920003:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((920003:ℚ)/1280000),((1843089:ℚ)/2560000),((3038863899:ℚ)/10000000000),((3841739503:ℚ)/10000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((920003:ℝ)/1280000) ((1843089:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((1843089:ℚ)/2560000),((461543:ℚ)/640000),((3051874847:ℚ)/10000000000),((3799236623:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((1843089:ℝ)/2560000) ((461543:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((461543:ℚ)/640000),((369851:ℚ)/512000),((612944523:ℚ)/2000000000),((3756276457:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((461543:ℝ)/640000) ((369851:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((369851:ℚ)/512000),((926169:ℚ)/1280000),((12309639:ℚ)/40000000),((3712843103:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((369851:ℝ)/512000) ((926169:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((926169:ℚ)/1280000),((1855421:ℚ)/2560000),((3089938729:ℚ)/10000000000),((1834459861:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((926169:ℝ)/1280000) ((1855421:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((1855421:ℚ)/2560000),((148557:ℚ)/204800),((619228933:ℚ)/2000000000),((906122117:ℚ)/2500000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((1855421:ℝ)/2560000) ((148557:ℝ)/204800),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((148557:ℚ)/204800),((232313:ℚ)/320000),((77557799:ℚ)/250000000),((3602076513:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((148557:ℝ)/204800) ((232313:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((232313:ℚ)/320000),((3720091:ℚ)/5120000),((621688181:ℚ)/2000000000),((894882599:ℚ)/2500000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((232313:ℝ)/320000) ((3720091:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((3720091:ℚ)/5120000),((1861587:ℚ)/2560000),((3114531787:ℚ)/10000000000),((88921189:ℚ)/250000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((3720091:ℝ)/5120000) ((1861587:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((1861587:ℚ)/2560000),((3726257:ℚ)/5120000),((312058489:ℚ)/1000000000),((441753171:ℚ)/1250000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((1861587:ℝ)/2560000) ((3726257:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((3726257:ℚ)/5120000),((186467:ℚ)/256000),((3126600493:ℚ)/10000000000),((35110611:ℚ)/100000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((3726257:ℝ)/5120000) ((186467:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((186467:ℚ)/256000),((3732423:ℚ)/5120000),((391572359:ℚ)/1250000000),((435993993:ℚ)/1250000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((186467:ℝ)/256000) ((3732423:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((3732423:ℚ)/5120000),((1867753:ℚ)/2560000),((3138520299:ℚ)/10000000000),((1732347499:ℚ)/5000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((3732423:ℝ)/5120000) ((1867753:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((1867753:ℚ)/2560000),((3738589:ℚ)/5120000),((1572212521:ℚ)/5000000000),((3441287261:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((1867753:ℝ)/2560000) ((3738589:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((3738589:ℚ)/5120000),((467709:ℚ)/640000),((393786671:ℚ)/1250000000),((341772563:ℚ)/1000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((3738589:ℝ)/5120000) ((467709:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((467709:ℚ)/640000),((748951:ℚ)/1024000),((1578062769:ℚ)/5000000000),((3394006897:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((467709:ℝ)/640000) ((748951:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((748951:ℚ)/1024000),((1873919:ℚ)/2560000),((3161921811:ℚ)/10000000000),((3370127739:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((748951:ℝ)/1024000) ((1873919:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((1873919:ℚ)/2560000),((3750921:ℚ)/5120000),((3167682441:ℚ)/10000000000),((3346084719:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((1873919:ℝ)/2560000) ((3750921:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((3750921:ℚ)/5120000),((938501:ℚ)/1280000),((9916899:ℚ)/31250000),((3321874273:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((3750921:ℝ)/5120000) ((938501:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((938501:ℚ)/1280000),((3757087:ℚ)/5120000),((1589548889:ℚ)/5000000000),((329749271:ℚ)/1000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((938501:ℝ)/1280000) ((3757087:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((3757087:ℚ)/5120000),((376017:ℚ)/512000),((159237649:ℚ)/500000000),((3272936201:ℚ)/10000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((3757087:ℝ)/5120000) ((376017:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((376017:ℚ)/512000),((3763253:ℚ)/5120000),((398796691:ℚ)/1250000000),((1624100387:ℚ)/5000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((376017:ℝ)/512000) ((3763253:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((3763253:ℚ)/5120000),((58849:ℚ)/80000),((3195959663:ℚ)/10000000000),((1611641153:ℚ)/5000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((3763253:ℝ)/5120000) ((58849:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((58849:ℚ)/80000),((3769419:ℚ)/5120000),((3201511621:ℚ)/10000000000),((1599088257:ℚ)/5000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((58849:ℝ)/80000) ((3769419:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((3769419:ℚ)/5120000),((1886251:ℚ)/2560000),((641405927:ℚ)/2000000000),((1586439473:ℚ)/5000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((3769419:ℝ)/5120000) ((1886251:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((1886251:ℚ)/2560000),((944667:ℚ)/1280000),((1608982377:ℚ)/5000000000),((1573692487:ℚ)/5000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((1886251:ℝ)/2560000) ((944667:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((944667:ℚ)/1280000),((1892417:ℚ)/2560000),((3228766833:ℚ)/10000000000),((48371693:ℚ)/156250000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((944667:ℝ)/1280000) ((1892417:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((1892417:ℚ)/2560000),((3791:ℚ)/5120),((809859411:ℚ)/2500000000),((11888069:ℚ)/39062500)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((1892417:ℝ)/2560000) ((3791:ℝ)/5120),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((3791:ℚ)/5120),((1898583:ℚ)/2560000),((649995783:ℚ)/2000000000),((598002471:ℚ)/2000000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((3791:ℝ)/5120) ((1898583:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((1898583:ℚ)/2560000),((950833:ℚ)/1280000),((1630196167:ℚ)/5000000000),((1467869923:ℚ)/5000000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((1898583:ℝ)/2560000) ((950833:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((950833:ℚ)/1280000),((238479:ℚ)/320000),((131233687:ℚ)/400000000),((720118753:ℚ)/2500000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((950833:ℝ)/1280000) ((238479:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((238479:ℚ)/320000),((956999:ℚ)/1280000),((330079991:ℚ)/1000000000),((2766729291:ℚ)/10000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((238479:ℝ)/320000) ((956999:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((956999:ℚ)/1280000),((480041:ℚ)/640000),((1660138859:ℚ)/5000000000),((8275727:ℚ)/31250000)⟩
theorem valid42 : Valid params packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((956999:ℝ)/1280000) ((480041:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((480041:ℚ)/640000),((120781:ℚ)/160000),((335783963:ℚ)/1000000000),((2524315739:ℚ)/10000000000)⟩
theorem valid43 : Valid params packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((480041:ℝ)/640000) ((120781:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((120781:ℚ)/160000),((48929:ℚ)/64000),((1713842399:ℚ)/5000000000),((564152939:ℚ)/2500000000)⟩
theorem valid44 : Valid params packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((120781:ℝ)/160000) ((48929:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((48929:ℚ)/64000),((15483:ℚ)/20000),((3490995801:ℚ)/10000000000),((1593968867:ℚ)/10000000000)⟩
theorem valid45 : Valid params packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((48929:ℝ)/64000) ((15483:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((108449:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((219981:ℝ)/320000) ((449211:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((108449:ℝ)/160000) ((449211:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((449211:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((226147:ℝ)/320000) ((913837:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((449211:ℝ)/640000) ((913837:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((22923:ℝ)/32000) ((1843089:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((913837:ℝ)/1280000) ((1843089:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((449211:ℝ)/640000) ((1843089:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1843089:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((461543:ℝ)/640000) ((926169:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node11_14 :
    ∀ r ∈ Set.Icc ((1843089:ℝ)/2560000) ((926169:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 node12_14
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((1855421:ℝ)/2560000) ((232313:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node14_17 :
    ∀ r ∈ Set.Icc ((926169:ℝ)/1280000) ((232313:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 node15_17
private theorem node11_17 :
    ∀ r ∈ Set.Icc ((1843089:ℝ)/2560000) ((232313:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_14 node14_17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((3720091:ℝ)/5120000) ((3726257:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node17_20 :
    ∀ r ∈ Set.Icc ((232313:ℝ)/320000) ((3726257:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 node18_20
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((186467:ℝ)/256000) ((1867753:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node20_23 :
    ∀ r ∈ Set.Icc ((3726257:ℝ)/5120000) ((1867753:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 node21_23
private theorem node17_23 :
    ∀ r ∈ Set.Icc ((232313:ℝ)/320000) ((1867753:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node17_20 node20_23
private theorem node11_23 :
    ∀ r ∈ Set.Icc ((1843089:ℝ)/2560000) ((1867753:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_17 node17_23
private theorem node0_23 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1867753:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_23
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((1867753:ℝ)/2560000) ((467709:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((748951:ℝ)/1024000) ((3750921:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node25_28 :
    ∀ r ∈ Set.Icc ((467709:ℝ)/640000) ((3750921:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 node26_28
private theorem node23_28 :
    ∀ r ∈ Set.Icc ((1867753:ℝ)/2560000) ((3750921:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node23_25 node25_28
private theorem node29_31 :
    ∀ r ∈ Set.Icc ((938501:ℝ)/1280000) ((376017:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf29 leaf30
private theorem node28_31 :
    ∀ r ∈ Set.Icc ((3750921:ℝ)/5120000) ((376017:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 node29_31
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((3763253:ℝ)/5120000) ((3769419:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 leaf33
private theorem node31_34 :
    ∀ r ∈ Set.Icc ((376017:ℝ)/512000) ((3769419:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 node32_34
private theorem node28_34 :
    ∀ r ∈ Set.Icc ((3750921:ℝ)/5120000) ((3769419:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node28_31 node31_34
private theorem node23_34 :
    ∀ r ∈ Set.Icc ((1867753:ℝ)/2560000) ((3769419:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node23_28 node28_34
private theorem node35_37 :
    ∀ r ∈ Set.Icc ((1886251:ℝ)/2560000) ((1892417:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf35 leaf36
private theorem node34_37 :
    ∀ r ∈ Set.Icc ((3769419:ℝ)/5120000) ((1892417:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 node35_37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((3791:ℝ)/5120) ((950833:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf38 leaf39
private theorem node37_40 :
    ∀ r ∈ Set.Icc ((1892417:ℝ)/2560000) ((950833:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 node38_40
private theorem node34_40 :
    ∀ r ∈ Set.Icc ((3769419:ℝ)/5120000) ((950833:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node34_37 node37_40
private theorem node41_43 :
    ∀ r ∈ Set.Icc ((238479:ℝ)/320000) ((480041:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf41 leaf42
private theorem node40_43 :
    ∀ r ∈ Set.Icc ((950833:ℝ)/1280000) ((480041:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 node41_43
private theorem node44_46 :
    ∀ r ∈ Set.Icc ((120781:ℝ)/160000) ((15483:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf44 leaf45
private theorem node43_46 :
    ∀ r ∈ Set.Icc ((480041:ℝ)/640000) ((15483:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf43 node44_46
private theorem node40_46 :
    ∀ r ∈ Set.Icc ((950833:ℝ)/1280000) ((15483:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node40_43 node43_46
private theorem node34_46 :
    ∀ r ∈ Set.Icc ((3769419:ℝ)/5120000) ((15483:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node34_40 node40_46
private theorem node23_46 :
    ∀ r ∈ Set.Icc ((1867753:ℝ)/2560000) ((15483:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node23_34 node34_46
private theorem node0_46 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((15483:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_23 node23_46
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_46
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC54
#check @N11Formalization.C450SixthRadialC54.bound
#print axioms N11Formalization.C450SixthRadialC54.params_valid
#print axioms N11Formalization.C450SixthRadialC54.params_sum
#print axioms N11Formalization.C450SixthRadialC54.bound
