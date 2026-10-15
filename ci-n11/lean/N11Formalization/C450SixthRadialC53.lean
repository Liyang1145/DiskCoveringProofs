import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC53
open C450RadialPacketKernel
def params : Params := ⟨((818218663:ℚ)/320000000),((221047897:ℚ)/320000000),((630941:ℚ)/1000000),((541:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((105341:ℚ)/160000),((256831887:ℚ)/1250000000),((6468379903:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((105341:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((105341:ℚ)/160000),((216823:ℚ)/320000),((306143071:ℚ)/1250000000),((5576613233:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((105341:ℝ)/160000) ((216823:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((216823:ℚ)/320000),((439787:ℚ)/640000),((521944981:ℚ)/2000000000),((1269862399:ℚ)/2500000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((216823:ℝ)/320000) ((439787:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((439787:ℚ)/640000),((55741:ℚ)/80000),((2752261:ℚ)/10000000),((2406743667:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((439787:ℝ)/640000) ((55741:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55741:ℚ)/80000),((897997:ℚ)/1280000),((2817733491:ℚ)/10000000000),((906646149:ℚ)/2000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55741:ℝ)/80000) ((897997:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((897997:ℚ)/1280000),((452069:ℚ)/640000),((575949989:ℚ)/2000000000),((877377417:ℚ)/2000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((897997:ℝ)/1280000) ((452069:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((452069:ℚ)/640000),((910279:ℚ)/1280000),((587713119:ℚ)/2000000000),((4235828907:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((452069:ℝ)/640000) ((910279:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((910279:ℚ)/1280000),((1826699:ℚ)/2560000),((593368809:ℚ)/2000000000),((4079530677:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((910279:ℝ)/1280000) ((1826699:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1826699:ℚ)/2560000),((45821:ℚ)/64000),((748600983:ℚ)/2500000000),((3999224773:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1826699:ℝ)/2560000) ((45821:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45821:ℚ)/64000),((1838981:ℚ)/2560000),((3021269113:ℚ)/10000000000),((979340829:ℚ)/2500000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45821:ℝ)/64000) ((1838981:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1838981:ℚ)/2560000),((3684103:ℚ)/5120000),((379306033:ℚ)/1250000000),((1916923211:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1838981:ℝ)/2560000) ((3684103:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((3684103:ℚ)/5120000),((922561:ℚ)/1280000),((1523731033:ℚ)/5000000000),((3791433009:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((3684103:ℝ)/5120000) ((922561:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((922561:ℚ)/1280000),((739277:ℚ)/1024000),((3060313133:ℚ)/10000000000),((3748563199:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((922561:ℝ)/1280000) ((739277:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((739277:ℚ)/1024000),((1851263:ℚ)/2560000),((768251001:ℚ)/2500000000),((723676:ℚ)/1953125)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((739277:ℝ)/1024000) ((1851263:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1851263:ℚ)/2560000),((3708667:ℚ)/5120000),((3085537149:ℚ)/10000000000),((3661389969:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1851263:ℝ)/2560000) ((3708667:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((3708667:ℚ)/5120000),((296939:ℚ)/409600),((193234083:ℚ)/625000000),((723410387:ℚ)/2000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((3708667:ℝ)/5120000) ((296939:ℝ)/409600),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((296939:ℚ)/409600),((464351:ℚ)/640000),((774478743:ℚ)/2500000000),((1797343487:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((296939:ℝ)/409600) ((464351:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((464351:ℚ)/640000),((7435757:ℚ)/10240000),((310404637:ℚ)/1000000000),((223261757:ℚ)/625000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((464351:ℝ)/640000) ((7435757:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((7435757:ℚ)/10240000),((3720949:ℚ)/5120000),((311013981:ℚ)/1000000000),((1774776399:ℚ)/5000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((7435757:ℝ)/10240000) ((3720949:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((3720949:ℚ)/5120000),((7448039:ℚ)/10240000),((1558097787:ℚ)/5000000000),((1763389201:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((3720949:ℝ)/5120000) ((7448039:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((7448039:ℚ)/10240000),((372709:ℚ)/512000),((156110697:ℚ)/500000000),((1751931103:ℚ)/5000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((7448039:ℝ)/10240000) ((372709:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((372709:ℚ)/512000),((7460321:ℚ)/10240000),((195512199:ℚ)/625000000),((3480801407:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((372709:ℝ)/512000) ((7460321:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((7460321:ℚ)/10240000),((3733231:ℚ)/5120000),((3134139577:ℚ)/10000000000),((3457593107:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((7460321:ℝ)/10240000) ((3733231:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((3733231:ℚ)/5120000),((7472603:ℚ)/10240000),((785011847:ℚ)/2500000000),((3434234311:ℚ)/10000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((3733231:ℝ)/5120000) ((7472603:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((7472603:ℚ)/10240000),((934843:ℚ)/1280000),((3145918881:ℚ)/10000000000),((852680481:ℚ)/2500000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((7472603:ℝ)/10240000) ((934843:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((934843:ℚ)/1280000),((1496977:ℚ)/2048000),((3151754317:ℚ)/10000000000),((1693526371:ℚ)/5000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((934843:ℝ)/1280000) ((1496977:ℝ)/2048000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((1496977:ℚ)/2048000),((3745513:ℚ)/5120000),((3157553953:ℚ)/10000000000),((67264469:ℚ)/200000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((1496977:ℝ)/2048000) ((3745513:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((3745513:ℚ)/5120000),((7497167:ℚ)/10240000),((1581659023:ℚ)/5000000000),((1669615309:ℚ)/5000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((3745513:ℝ)/5120000) ((7497167:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((7497167:ℚ)/10240000),((1875827:ℚ)/2560000),((633809369:ℚ)/2000000000),((3315070689:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((7497167:ℝ)/10240000) ((1875827:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((1875827:ℚ)/2560000),((7509449:ℚ)/10240000),((3174740599:ℚ)/10000000000),((164536999:ℚ)/500000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((1875827:ℝ)/2560000) ((7509449:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((7509449:ℚ)/10240000),((751559:ℚ)/1024000),((3180399553:ℚ)/10000000000),((816558667:ℚ)/2500000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((7509449:ℝ)/10240000) ((751559:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((751559:ℚ)/1024000),((7521731:ℚ)/10240000),((3186023949:ℚ)/10000000000),((3241550791:ℚ)/10000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((751559:ℝ)/1024000) ((7521731:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((7521731:ℚ)/10240000),((117623:ℚ)/160000),((1595807013:ℚ)/5000000000),((3216684233:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((7521731:ℝ)/10240000) ((117623:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((117623:ℚ)/160000),((3770077:ℚ)/5120000),((3202692163:ℚ)/10000000000),((3191630719:ℚ)/10000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((117623:ℝ)/160000) ((3770077:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((3770077:ℚ)/5120000),((1888109:ℚ)/2560000),((160681791:ℚ)/500000000),((3140944881:ℚ)/10000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((3770077:ℝ)/5120000) ((1888109:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((1888109:ℚ)/2560000),((3782359:ℚ)/5120000),((806111701:ℚ)/2500000000),((3089455549:ℚ)/10000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((1888109:ℝ)/2560000) ((3782359:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((3782359:ℚ)/5120000),((7577:ℚ)/10240),((1617563441:ℚ)/5000000000),((1518560911:ℚ)/5000000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((3782359:ℝ)/5120000) ((7577:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((7577:ℚ)/10240),((3794641:ℚ)/5120000),((3245677779:ℚ)/10000000000),((596779847:ℚ)/2000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((7577:ℝ)/10240) ((3794641:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((3794641:ℚ)/5120000),((1900391:ℚ)/2560000),((3256101177:ℚ)/10000000000),((2929739307:ℚ)/10000000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((3794641:ℝ)/5120000) ((1900391:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((1900391:ℚ)/2560000),((476633:ℚ)/640000),((3276572019:ℚ)/10000000000),((143729451:ℚ)/500000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((1900391:ℝ)/2560000) ((476633:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((476633:ℚ)/640000),((1912673:ℚ)/2560000),((3296552123:ℚ)/10000000000),((2761078773:ℚ)/10000000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((476633:ℝ)/640000) ((1912673:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((1912673:ℚ)/2560000),((959407:ℚ)/1280000),((3316053633:ℚ)/10000000000),((528565407:ℚ)/2000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((1912673:ℝ)/2560000) ((959407:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((959407:ℚ)/1280000),((241387:ℚ)/320000),((1676833417:ℚ)/5000000000),((31489573:ℚ)/125000000)⟩
theorem valid42 : Valid params packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((959407:ℝ)/1280000) ((241387:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((241387:ℚ)/320000),((97783:ℚ)/128000),((684725873:ℚ)/2000000000),((225201293:ℚ)/1000000000)⟩
theorem valid43 : Valid params packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((241387:ℝ)/320000) ((97783:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((97783:ℚ)/128000),((30941:ℚ)/40000),((10897113:ℚ)/31250000),((397681843:ℚ)/2500000000)⟩
theorem valid44 : Valid params packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((97783:ℝ)/128000) ((30941:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((216823:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((439787:ℝ)/640000) ((897997:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((216823:ℝ)/320000) ((897997:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((897997:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((452069:ℝ)/640000) ((1826699:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node5_8 :
    ∀ r ∈ Set.Icc ((897997:ℝ)/1280000) ((1826699:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 node6_8
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((45821:ℝ)/64000) ((3684103:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node8_11 :
    ∀ r ∈ Set.Icc ((1826699:ℝ)/2560000) ((3684103:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 node9_11
private theorem node5_11 :
    ∀ r ∈ Set.Icc ((897997:ℝ)/1280000) ((3684103:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_8 node8_11
private theorem node0_11 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3684103:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_11
private theorem node11_13 :
    ∀ r ∈ Set.Icc ((3684103:ℝ)/5120000) ((739277:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 leaf12
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((1851263:ℝ)/2560000) ((296939:ℝ)/409600),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node13_16 :
    ∀ r ∈ Set.Icc ((739277:ℝ)/1024000) ((296939:ℝ)/409600),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 node14_16
private theorem node11_16 :
    ∀ r ∈ Set.Icc ((3684103:ℝ)/5120000) ((296939:ℝ)/409600),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_13 node13_16
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((464351:ℝ)/640000) ((3720949:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((296939:ℝ)/409600) ((3720949:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((7448039:ℝ)/10240000) ((7460321:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node19_22 :
    ∀ r ∈ Set.Icc ((3720949:ℝ)/5120000) ((7460321:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 node20_22
private theorem node16_22 :
    ∀ r ∈ Set.Icc ((296939:ℝ)/409600) ((7460321:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_19 node19_22
private theorem node11_22 :
    ∀ r ∈ Set.Icc ((3684103:ℝ)/5120000) ((7460321:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node11_16 node16_22
private theorem node0_22 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7460321:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_11 node11_22
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((7460321:ℝ)/10240000) ((7472603:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((934843:ℝ)/1280000) ((3745513:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node24_27 :
    ∀ r ∈ Set.Icc ((7472603:ℝ)/10240000) ((3745513:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 node25_27
private theorem node22_27 :
    ∀ r ∈ Set.Icc ((7460321:ℝ)/10240000) ((3745513:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_24 node24_27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((7497167:ℝ)/10240000) ((7509449:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((3745513:ℝ)/5120000) ((7509449:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((751559:ℝ)/1024000) ((117623:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((7509449:ℝ)/10240000) ((117623:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node27_33 :
    ∀ r ∈ Set.Icc ((3745513:ℝ)/5120000) ((117623:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node27_30 node30_33
private theorem node22_33 :
    ∀ r ∈ Set.Icc ((7460321:ℝ)/10240000) ((117623:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_27 node27_33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((3770077:ℝ)/5120000) ((3782359:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 leaf35
private theorem node33_36 :
    ∀ r ∈ Set.Icc ((117623:ℝ)/160000) ((3782359:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 node34_36
private theorem node37_39 :
    ∀ r ∈ Set.Icc ((7577:ℝ)/10240) ((1900391:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 leaf38
private theorem node36_39 :
    ∀ r ∈ Set.Icc ((3782359:ℝ)/5120000) ((1900391:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 node37_39
private theorem node33_39 :
    ∀ r ∈ Set.Icc ((117623:ℝ)/160000) ((1900391:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_36 node36_39
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((476633:ℝ)/640000) ((959407:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 leaf41
private theorem node39_42 :
    ∀ r ∈ Set.Icc ((1900391:ℝ)/2560000) ((959407:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 node40_42
private theorem node43_45 :
    ∀ r ∈ Set.Icc ((241387:ℝ)/320000) ((30941:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf43 leaf44
private theorem node42_45 :
    ∀ r ∈ Set.Icc ((959407:ℝ)/1280000) ((30941:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf42 node43_45
private theorem node39_45 :
    ∀ r ∈ Set.Icc ((1900391:ℝ)/2560000) ((30941:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node39_42 node42_45
private theorem node33_45 :
    ∀ r ∈ Set.Icc ((117623:ℝ)/160000) ((30941:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_39 node39_45
private theorem node22_45 :
    ∀ r ∈ Set.Icc ((7460321:ℝ)/10240000) ((30941:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node22_33 node33_45
private theorem node0_45 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((30941:ℝ)/40000),
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
end N11Formalization.C450SixthRadialC53
#check @N11Formalization.C450SixthRadialC53.bound
#print axioms N11Formalization.C450SixthRadialC53.params_valid
#print axioms N11Formalization.C450SixthRadialC53.params_sum
#print axioms N11Formalization.C450SixthRadialC53.bound
