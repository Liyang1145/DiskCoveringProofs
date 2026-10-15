import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC57
open C450RadialPacketKernel
def params : Params := ⟨((1021219047:ℚ)/400000000),((277864153:ℚ)/400000000),((154043:ℚ)/250000),((641:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((105441:ℚ)/160000),((2069490119:ℚ)/10000000000),((1304553273:ℚ)/2000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((105441:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((105441:ℚ)/160000),((217123:ℚ)/320000),((154108467:ℚ)/625000000),((5623059693:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((105441:ℝ)/160000) ((217123:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((217123:ℚ)/320000),((440487:ℚ)/640000),((2626818471:ℚ)/10000000000),((256078003:ℚ)/500000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((217123:ℝ)/320000) ((440487:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((440487:ℚ)/640000),((55841:ℚ)/80000),((1384834017:ℚ)/5000000000),((1213325439:ℚ)/2500000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((440487:ℝ)/640000) ((55841:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55841:ℚ)/80000),((899697:ℚ)/1280000),((567047159:ℚ)/2000000000),((2285321039:ℚ)/5000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55841:ℝ)/80000) ((899697:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((899697:ℚ)/1280000),((452969:ℚ)/640000),((181081911:ℚ)/625000000),((4423049881:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((899697:ℝ)/1280000) ((452969:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((452969:ℚ)/640000),((912179:ℚ)/1280000),((2956150159:ℚ)/10000000000),((4270707263:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((452969:ℝ)/640000) ((912179:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((912179:ℚ)/1280000),((1830599:ℚ)/2560000),((2984428387:ℚ)/10000000000),((164523379:ℚ)/400000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((912179:ℝ)/1280000) ((1830599:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1830599:ℚ)/2560000),((45921:ℚ)/64000),((752995069:ℚ)/2500000000),((4032099709:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1830599:ℝ)/2560000) ((45921:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45921:ℚ)/64000),((1843081:ℚ)/2560000),((1519414961:ℚ)/5000000000),((3949547391:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45921:ℝ)/64000) ((1843081:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1843081:ℚ)/2560000),((3692403:ℚ)/5120000),((3051998551:ℚ)/10000000000),((966331709:ℚ)/2500000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1843081:ℝ)/2560000) ((3692403:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((3692403:ℚ)/5120000),((924661:ℚ)/1280000),((3065000031:ℚ)/10000000000),((3822556517:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((3692403:ℝ)/5120000) ((924661:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((924661:ℚ)/1280000),((740977:ℚ)/1024000),((3077837003:ℚ)/10000000000),((3779326259:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((924661:ℝ)/1280000) ((740977:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((740977:ℚ)/1024000),((1855563:ℚ)/2560000),((96578501:ℚ)/312500000),((116738127:ℚ)/312500000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((740977:ℝ)/1024000) ((1855563:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1855563:ℚ)/2560000),((3717367:ℚ)/5120000),((775756903:ℚ)/2500000000),((57678453:ℚ)/156250000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1855563:ℝ)/2560000) ((3717367:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((3717367:ℚ)/5120000),((465451:ℚ)/640000),((3115386173:ℚ)/10000000000),((364671109:ℚ)/1000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((3717367:ℝ)/5120000) ((465451:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((465451:ℚ)/640000),((7453457:ℚ)/10240000),((3121507311:ℚ)/10000000000),((3601471299:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((465451:ℝ)/640000) ((7453457:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((7453457:ℚ)/10240000),((3729849:ℚ)/5120000),((125103603:ℚ)/400000000),((715729283:ℚ)/2000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((7453457:ℝ)/10240000) ((3729849:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((3729849:ℚ)/5120000),((7465939:ℚ)/10240000),((12534539:ℚ)/40000000),((3555681361:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((3729849:ℝ)/5120000) ((7465939:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((7465939:ℚ)/10240000),((373609:ℚ)/512000),((1569820809:ℚ)/5000000000),((17662867:ℚ)/50000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((7465939:ℝ)/10240000) ((373609:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((373609:ℚ)/512000),((7478421:ℚ)/10240000),((3145610957:ℚ)/10000000000),((701863941:ℚ)/2000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((373609:ℝ)/512000) ((7478421:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((7478421:ℚ)/10240000),((3742331:ℚ)/5120000),((3151543041:ℚ)/10000000000),((697183471:ℚ)/2000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((7478421:ℝ)/10240000) ((3742331:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((3742331:ℚ)/5120000),((7490903:ℚ)/10240000),((157871907:ℚ)/500000000),((865590833:ℚ)/2500000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((3742331:ℝ)/5120000) ((7490903:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((7490903:ℚ)/10240000),((937143:ℚ)/1280000),((3163296523:ℚ)/10000000000),((1719327257:ℚ)/5000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((7490903:ℝ)/10240000) ((937143:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((937143:ℚ)/1280000),((1500677:ℚ)/2048000),((3169118453:ℚ)/10000000000),((3414787673:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((937143:ℝ)/1280000) ((1500677:ℝ)/2048000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((1500677:ℚ)/2048000),((3754813:ℚ)/5120000),((3174904191:ℚ)/10000000000),((3390759467:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((1500677:ℝ)/2048000) ((3754813:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((3754813:ℚ)/5120000),((7515867:ℚ)/10240000),((3180653993:ℚ)/10000000000),((1683283219:ℚ)/5000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((3754813:ℝ)/5120000) ((7515867:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((7515867:ℚ)/10240000),((1880527:ℚ)/2560000),((1593184057:ℚ)/5000000000),((3342205001:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((7515867:ℝ)/10240000) ((1880527:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((1880527:ℚ)/2560000),((7528349:ℚ)/10240000),((3192046803:ℚ)/10000000000),((3317671441:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((1880527:ℝ)/2560000) ((7528349:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((7528349:ℚ)/10240000),((753459:ℚ)/1024000),((319769031:ℚ)/1000000000),((3292961909:ℚ)/10000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((7528349:ℝ)/10240000) ((753459:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((753459:ℚ)/1024000),((7540831:ℚ)/10240000),((3203298877:ℚ)/10000000000),((1634036203:ℚ)/5000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((753459:ℝ)/1024000) ((7540831:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((7540831:ℚ)/10240000),((117923:ℚ)/160000),((3208872747:ℚ)/10000000000),((1621499393:ℚ)/5000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((7540831:ℝ)/10240000) ((117923:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((117923:ℚ)/160000),((7553313:ℚ)/10240000),((3214412159:ℚ)/10000000000),((3217736739:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((117923:ℝ)/160000) ((7553313:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((7553313:ℚ)/10240000),((3779777:ℚ)/5120000),((3219917347:ℚ)/10000000000),((798070447:ℚ)/2500000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((7553313:ℝ)/10240000) ((3779777:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((3779777:ℚ)/5120000),((1893009:ℚ)/2560000),((161541299:ℚ)/500000000),((126665171:ℚ)/400000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((3779777:ℝ)/5120000) ((1893009:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((1893009:ℚ)/2560000),((3792259:ℚ)/5120000),((129664019:ℚ)/400000000),((1557355993:ℚ)/5000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((1893009:ℝ)/2560000) ((3792259:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((3792259:ℚ)/5120000),((7597:ℚ)/10240),((406530327:ℚ)/1250000000),((3061943639:ℚ)/10000000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((3792259:ℝ)/5120000) ((7597:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((7597:ℚ)/10240),((3804741:ℚ)/5120000),((101961067:ℚ)/312500000),((300827941:ℚ)/1000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((7597:ℝ)/10240) ((3804741:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((3804741:ℚ)/5120000),((1905491:ℚ)/2560000),((3273136761:ℚ)/10000000000),((2953670431:ℚ)/10000000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((3804741:ℝ)/5120000) ((1905491:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((1905491:ℚ)/2560000),((477933:ℚ)/640000),((329352187:ℚ)/1000000000),((2898063253:ℚ)/10000000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((1905491:ℝ)/2560000) ((477933:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((477933:ℚ)/640000),((1917973:ℚ)/2560000),((103544087:ℚ)/312500000),((2783613789:ℚ)/10000000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((477933:ℝ)/640000) ((1917973:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((1917973:ℚ)/2560000),((962107:ℚ)/1280000),((133312631:ℚ)/400000000),((1332192597:ℚ)/5000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((1917973:ℝ)/2560000) ((962107:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((962107:ℚ)/1280000),((242087:ℚ)/320000),((26329847:ℚ)/78125000),((634926029:ℚ)/2500000000)⟩
theorem valid42 : Valid params packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((962107:ℝ)/1280000) ((242087:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((242087:ℚ)/320000),((98083:ℚ)/128000),((3439706759:ℚ)/10000000000),((1135176647:ℚ)/5000000000)⟩
theorem valid43 : Valid params packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((242087:ℝ)/320000) ((98083:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((98083:ℚ)/128000),((31041:ℚ)/40000),((350260373:ℚ)/1000000000),((1603654371:ℚ)/10000000000)⟩
theorem valid44 : Valid params packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((98083:ℝ)/128000) ((31041:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((217123:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((440487:ℝ)/640000) ((899697:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((217123:ℝ)/320000) ((899697:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((899697:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((452969:ℝ)/640000) ((1830599:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((899697:ℝ)/1280000) ((1830599:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((45921:ℝ)/64000) ((3692403:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((1830599:ℝ)/2560000) ((3692403:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((899697:ℝ)/1280000) ((3692403:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3692403:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((3692403:ℝ)/5120000) ((740977:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((1855563:ℝ)/2560000) ((465451:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node13_16 :
    ∀ r ∈ Set.Icc ((740977:ℝ)/1024000) ((465451:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 node14_16
private theorem node11_16 :
    ∀ r ∈ Set.Icc ((3692403:ℝ)/5120000) ((465451:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((7453457:ℝ)/10240000) ((7465939:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((465451:ℝ)/640000) ((7465939:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((373609:ℝ)/512000) ((3742331:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node19_22 :
    ∀ r ∈ Set.Icc ((7465939:ℝ)/10240000) ((3742331:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 node20_22
private theorem node16_22 :
    ∀ r ∈ Set.Icc ((465451:ℝ)/640000) ((3742331:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_19 node19_22
private theorem node11_22 :
    ∀ r ∈ Set.Icc ((3692403:ℝ)/5120000) ((3742331:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_16 node16_22
private theorem node0_22 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3742331:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((3742331:ℝ)/5120000) ((937143:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((1500677:ℝ)/2048000) ((7515867:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node24_27 :
    ∀ r ∈ Set.Icc ((937143:ℝ)/1280000) ((7515867:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 node25_27
private theorem node22_27 :
    ∀ r ∈ Set.Icc ((3742331:ℝ)/5120000) ((7515867:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((1880527:ℝ)/2560000) ((753459:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((7515867:ℝ)/10240000) ((753459:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((7540831:ℝ)/10240000) ((7553313:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((753459:ℝ)/1024000) ((7553313:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node27_33 :
    ∀ r ∈ Set.Icc ((7515867:ℝ)/10240000) ((7553313:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node27_30 node30_33
private theorem node22_33 :
    ∀ r ∈ Set.Icc ((3742331:ℝ)/5120000) ((7553313:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_27 node27_33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((3779777:ℝ)/5120000) ((3792259:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 leaf35
private theorem node33_36 :
    ∀ r ∈ Set.Icc ((7553313:ℝ)/10240000) ((3792259:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 node34_36
private theorem node37_39 :
    ∀ r ∈ Set.Icc ((7597:ℝ)/10240) ((1905491:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 leaf38
private theorem node36_39 :
    ∀ r ∈ Set.Icc ((3792259:ℝ)/5120000) ((1905491:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 node37_39
private theorem node33_39 :
    ∀ r ∈ Set.Icc ((7553313:ℝ)/10240000) ((1905491:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_36 node36_39
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((477933:ℝ)/640000) ((962107:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 leaf41
private theorem node39_42 :
    ∀ r ∈ Set.Icc ((1905491:ℝ)/2560000) ((962107:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 node40_42
private theorem node43_45 :
    ∀ r ∈ Set.Icc ((242087:ℝ)/320000) ((31041:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf43 leaf44
private theorem node42_45 :
    ∀ r ∈ Set.Icc ((962107:ℝ)/1280000) ((31041:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf42 node43_45
private theorem node39_45 :
    ∀ r ∈ Set.Icc ((1905491:ℝ)/2560000) ((31041:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node39_42 node42_45
private theorem node33_45 :
    ∀ r ∈ Set.Icc ((7553313:ℝ)/10240000) ((31041:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_39 node39_45
private theorem node22_45 :
    ∀ r ∈ Set.Icc ((3742331:ℝ)/5120000) ((31041:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_33 node33_45
private theorem node0_45 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((31041:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_22 node22_45
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_45
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC57
#check @N11Formalization.C450SixthRadialC57.bound
#print axioms N11Formalization.C450SixthRadialC57.params_valid
#print axioms N11Formalization.C450SixthRadialC57.params_sum
#print axioms N11Formalization.C450SixthRadialC57.bound
