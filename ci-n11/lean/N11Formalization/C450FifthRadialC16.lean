import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FifthRadialC16
open C450RadialPacketKernel
def params : Params := ⟨((641363:ℚ)/250000),((339853:ℚ)/500000),((2998179:ℚ)/5000000),((254:ℚ)/15625)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((82383:ℚ)/125000),((2070852719:ℚ)/10000000000),((3263886059:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((82383:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((82383:ℚ)/125000),((169649:ℚ)/250000),((1233628987:ℚ)/5000000000),((1125466813:ℚ)/2000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((82383:ℝ)/125000) ((169649:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((169649:ℚ)/250000),((43633:ℚ)/62500),((692815951:ℚ)/2500000000),((5125435147:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((169649:ℝ)/250000) ((43633:ℝ)/62500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((43633:ℚ)/62500),((353947:ℚ)/500000),((2898919519:ℚ)/10000000000),((1143521131:ℚ)/2500000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((43633:ℝ)/62500) ((353947:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((353947:ℚ)/500000),((712777:ℚ)/1000000),((1478880407:ℚ)/5000000000),((854783307:ℚ)/2000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((353947:ℝ)/500000) ((712777:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((712777:ℚ)/1000000),((1430437:ℚ)/2000000),((119441551:ℚ)/400000000),((4116171823:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((712777:ℝ)/1000000) ((1430437:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((1430437:ℚ)/2000000),((35883:ℚ)/50000),((3013589679:ℚ)/10000000000),((403512457:ℚ)/1000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((1430437:ℝ)/2000000) ((35883:ℝ)/50000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((35883:ℚ)/50000),((1440203:ℚ)/2000000),((1520218823:ℚ)/5000000000),((3952508663:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((35883:ℝ)/50000) ((1440203:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1440203:ℚ)/2000000),((722543:ℚ)/1000000),((3066605401:ℚ)/10000000000),((1934111671:ℚ)/5000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1440203:ℝ)/2000000) ((722543:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((722543:ℚ)/1000000),((579011:ℚ)/800000),((61588819:ℚ)/200000000),((189107837:ℚ)/500000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((722543:ℝ)/1000000) ((579011:ℝ)/800000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((579011:ℚ)/800000),((1449969:ℚ)/2000000),((1546057197:ℚ)/5000000000),((467302129:ℚ)/1250000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((579011:ℝ)/800000) ((1449969:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((1449969:ℚ)/2000000),((2904821:ℚ)/4000000),((388078529:ℚ)/1250000000),((1847092049:ℚ)/5000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((1449969:ℝ)/2000000) ((2904821:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((2904821:ℚ)/4000000),((363713:ℚ)/500000),((3116984893:ℚ)/10000000000),((3649439971:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((2904821:ℝ)/4000000) ((363713:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((363713:ℚ)/500000),((2914587:ℚ)/4000000),((3129186741:ℚ)/10000000000),((1802082789:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((363713:ℝ)/500000) ((2914587:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((2914587:ℚ)/4000000),((291947:ℚ)/400000),((1570618039:ℚ)/5000000000),((711668129:ℚ)/2000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((2914587:ℝ)/4000000) ((291947:ℝ)/400000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((291947:ℚ)/400000),((5843823:ℚ)/8000000),((3147204257:ℚ)/10000000000),((877985897:ℚ)/2500000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((291947:ℝ)/400000) ((5843823:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((5843823:ℚ)/8000000),((2924353:ℚ)/4000000),((394141893:ℚ)/1250000000),((174426169:ℚ)/500000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((5843823:ℝ)/8000000) ((2924353:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((2924353:ℚ)/4000000),((5853589:ℚ)/8000000),((315902901:ℚ)/1000000000),((3464951389:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((2924353:ℝ)/4000000) ((5853589:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((5853589:ℚ)/8000000),((732309:ℚ)/1000000),((3164886123:ℚ)/10000000000),((1720612247:ℚ)/5000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((5853589:ℝ)/8000000) ((732309:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((732309:ℚ)/1000000),((1172671:ℚ)/1600000),((1585353373:ℚ)/5000000000),((1708669731:ℚ)/5000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((732309:ℝ)/1000000) ((1172671:ℝ)/1600000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1172671:ℚ)/1600000),((2934119:ℚ)/4000000),((158824557:ℚ)/500000000),((67865859:ℚ)/200000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1172671:ℝ)/1600000) ((2934119:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((2934119:ℚ)/4000000),((5873121:ℚ)/8000000),((3182239563:ℚ)/10000000000),((3369081497:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((2934119:ℝ)/4000000) ((5873121:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((5873121:ℚ)/8000000),((1469501:ℚ)/2000000),((796988067:ℚ)/2500000000),((668940303:ℚ)/2000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((5873121:ℝ)/8000000) ((1469501:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((1469501:ℚ)/2000000),((5882887:ℚ)/8000000),((3193629507:ℚ)/10000000000),((415018661:ℚ)/1250000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((1469501:ℝ)/2000000) ((5882887:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((5882887:ℚ)/8000000),((588777:ℚ)/800000),((3199271527:ℚ)/10000000000),((3295420961:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((5882887:ℝ)/8000000) ((588777:ℝ)/800000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((588777:ℚ)/800000),((5892653:ℚ)/8000000),((3204878573:ℚ)/10000000000),((654102507:ℚ)/2000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((588777:ℝ)/800000) ((5892653:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((5892653:ℚ)/8000000),((92149:ℚ)/125000),((3210450887:ℚ)/10000000000),((162270993:ℚ)/500000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((5892653:ℝ)/8000000) ((92149:ℝ)/125000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((92149:ℚ)/125000),((5902419:ℚ)/8000000),((803997177:ℚ)/2500000000),((1610069311:ℚ)/5000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((92149:ℝ)/125000) ((5902419:ℝ)/8000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((5902419:ℚ)/8000000),((2953651:ℚ)/4000000),((3221492271:ℚ)/10000000000),((1597332171:ℚ)/5000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((5902419:ℝ)/8000000) ((2953651:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((2953651:ℚ)/4000000),((1479267:ℚ)/2000000),((3232397551:ℚ)/10000000000),((1584496179:ℚ)/5000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((2953651:ℝ)/4000000) ((1479267:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((1479267:ℚ)/2000000),((2963417:ℚ)/4000000),((1621584279:ℚ)/5000000000),((1558517843:ℚ)/5000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((1479267:ℝ)/2000000) ((2963417:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((2963417:ℚ)/4000000),((29683:ℚ)/40000),((3253807077:ℚ)/10000000000),((3064227343:ℚ)/10000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((2963417:ℝ)/4000000) ((29683:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((29683:ℚ)/40000),((2973183:ℚ)/4000000),((816078713:ℚ)/2500000000),((1505261237:ℚ)/5000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((29683:ℝ)/40000) ((2973183:ℝ)/4000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((2973183:ℚ)/4000000),((1489033:ℚ)/2000000),((654938717:ℚ)/2000000000),((738968043:ℚ)/2500000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((2973183:ℝ)/4000000) ((1489033:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((1489033:ℚ)/2000000),((373479:ℚ)/500000),((3295070541:ℚ)/10000000000),((2900222951:ℚ)/10000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((1489033:ℝ)/2000000) ((373479:ℝ)/500000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((373479:ℚ)/500000),((1498799:ℚ)/2000000),((8287377:ℚ)/25000000),((2785687061:ℚ)/10000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((373479:ℝ)/500000) ((1498799:ℝ)/2000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((1498799:ℚ)/2000000),((751841:ℚ)/1000000),((3334346643:ℚ)/10000000000),((2666368579:ℚ)/10000000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((1498799:ℝ)/2000000) ((751841:ℝ)/1000000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((751841:ℚ)/1000000),((189181:ℚ)/250000),((3371731557:ℚ)/10000000000),((508318731:ℚ)/2000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((751841:ℝ)/1000000) ((189181:ℝ)/250000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((189181:ℚ)/250000),((76649:ℚ)/100000),((3441173:ℚ)/10000000),((11360203:ℚ)/50000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((189181:ℝ)/250000) ((76649:ℝ)/100000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((76649:ℚ)/100000),((12129:ℚ)/15625),((1752009137:ℚ)/5000000000),((50151363:ℚ)/312500000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((76649:ℝ)/100000) ((12129:ℝ)/15625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((169649:ℝ)/250000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((43633:ℝ)/62500) ((712777:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((169649:ℝ)/250000) ((712777:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((712777:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((712777:ℝ)/1000000) ((35883:ℝ)/50000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((1440203:ℝ)/2000000) ((579011:ℝ)/800000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((35883:ℝ)/50000) ((579011:ℝ)/800000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node5_10 :
    ∀ r ∈ Set.Icc ((712777:ℝ)/1000000) ((579011:ℝ)/800000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_7 node7_10
private theorem node0_10 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((579011:ℝ)/800000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((579011:ℝ)/800000) ((2904821:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((363713:ℝ)/500000) ((291947:ℝ)/400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((2904821:ℝ)/4000000) ((291947:ℝ)/400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node10_15 :
    ∀ r ∈ Set.Icc ((579011:ℝ)/800000) ((291947:ℝ)/400000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_15
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((291947:ℝ)/400000) ((2924353:ℝ)/4000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((5853589:ℝ)/8000000) ((1172671:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node17_20 :
    ∀ r ∈ Set.Icc ((2924353:ℝ)/4000000) ((1172671:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 node18_20
private theorem node15_20 :
    ∀ r ∈ Set.Icc ((291947:ℝ)/400000) ((1172671:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_17 node17_20
private theorem node10_20 :
    ∀ r ∈ Set.Icc ((579011:ℝ)/800000) ((1172671:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_15 node15_20
private theorem node0_20 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1172671:ℝ)/1600000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_10 node10_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((1172671:ℝ)/1600000) ((5873121:ℝ)/8000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((1469501:ℝ)/2000000) ((588777:ℝ)/800000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node22_25 :
    ∀ r ∈ Set.Icc ((5873121:ℝ)/8000000) ((588777:ℝ)/800000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 node23_25
private theorem node20_25 :
    ∀ r ∈ Set.Icc ((1172671:ℝ)/1600000) ((588777:ℝ)/800000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_22 node22_25
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((588777:ℝ)/800000) ((92149:ℝ)/125000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((5902419:ℝ)/8000000) ((1479267:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((92149:ℝ)/125000) ((1479267:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node25_30 :
    ∀ r ∈ Set.Icc ((588777:ℝ)/800000) ((1479267:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node25_27 node27_30
private theorem node20_30 :
    ∀ r ∈ Set.Icc ((1172671:ℝ)/1600000) ((1479267:ℝ)/2000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_25 node25_30
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((1479267:ℝ)/2000000) ((29683:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node33_35 :
    ∀ r ∈ Set.Icc ((2973183:ℝ)/4000000) ((373479:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 leaf34
private theorem node32_35 :
    ∀ r ∈ Set.Icc ((29683:ℝ)/40000) ((373479:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 node33_35
private theorem node30_35 :
    ∀ r ∈ Set.Icc ((1479267:ℝ)/2000000) ((373479:ℝ)/500000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node30_32 node32_35
private theorem node35_37 :
    ∀ r ∈ Set.Icc ((373479:ℝ)/500000) ((751841:ℝ)/1000000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf35 leaf36
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((189181:ℝ)/250000) ((12129:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf38 leaf39
private theorem node37_40 :
    ∀ r ∈ Set.Icc ((751841:ℝ)/1000000) ((12129:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 node38_40
private theorem node35_40 :
    ∀ r ∈ Set.Icc ((373479:ℝ)/500000) ((12129:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node35_37 node37_40
private theorem node30_40 :
    ∀ r ∈ Set.Icc ((1479267:ℝ)/2000000) ((12129:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node30_35 node35_40
private theorem node20_40 :
    ∀ r ∈ Set.Icc ((1172671:ℝ)/1600000) ((12129:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_30 node30_40
private theorem node0_40 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((12129:ℝ)/15625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_20 node20_40
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_40
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450FifthRadialC16
#check @N11Formalization.C450FifthRadialC16.bound
#print axioms N11Formalization.C450FifthRadialC16.params_valid
#print axioms N11Formalization.C450FifthRadialC16.bound
