import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC48
open C450RadialPacketKernel
def params : Params := ⟨((6555447203:ℚ)/2560000000),((1758685277:ℚ)/2560000000),((2597609:ℚ)/4000000),((13:ℚ)/1250)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((411:ℚ)/625),((1017940001:ℚ)/5000000000),((1599960209:ℚ)/2500000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((411:ℝ)/625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((411:ℚ)/625),((1691:ℚ)/2500),((2428108321:ℚ)/10000000000),((2759032021:ℚ)/5000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((411:ℝ)/625) ((1691:ℝ)/2500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((1691:ℚ)/2500),((3429:ℚ)/5000),((2588029447:ℚ)/10000000000),((1256589789:ℚ)/2500000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((1691:ℝ)/2500) ((3429:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((3429:ℚ)/5000),((869:ℚ)/1250),((2730143929:ℚ)/10000000000),((2381644163:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((3429:ℝ)/5000) ((869:ℝ)/1250),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((869:ℚ)/1250),((6999:ℚ)/10000),((1397741399:ℚ)/5000000000),((897211713:ℚ)/2000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((869:ℝ)/1250) ((6999:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((6999:ℚ)/10000),((3523:ℚ)/5000),((1428706011:ℚ)/5000000000),((868257547:ℚ)/2000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((6999:ℝ)/10000) ((3523:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((3523:ℚ)/5000),((7093:ℚ)/10000),((2916183633:ℚ)/10000000000),((4191847771:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((3523:ℝ)/5000) ((7093:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((7093:ℚ)/10000),((14233:ℚ)/20000),((588891073:ℚ)/2000000000),((4037218457:ℚ)/10000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((7093:ℝ)/10000) ((14233:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((14233:ℚ)/20000),((357:ℚ)/500),((29720183:ℚ)/100000000),((3957767963:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((14233:ℝ)/20000) ((357:ℝ)/500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((357:ℚ)/500),((14327:ℚ)/20000),((2998895993:ℚ)/10000000000),((3876777079:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((357:ℝ)/500) ((14327:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((14327:ℚ)/20000),((28701:ℚ)/40000),((1506042429:ℚ)/5000000000),((379414693:ℚ)/1000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((14327:ℝ)/20000) ((28701:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((28701:ℚ)/40000),((7187:ℚ)/10000),((1512555317:ℚ)/5000000000),((3752183299:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((28701:ℝ)/40000) ((7187:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((7187:ℚ)/10000),((5759:ℚ)/8000),((3037975901:ℚ)/10000000000),((1854883873:ℚ)/5000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((7187:ℝ)/10000) ((5759:ℝ)/8000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((5759:ℚ)/8000),((14421:ℚ)/20000),((1525341583:ℚ)/5000000000),((3666884559:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((5759:ℝ)/8000) ((14421:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((14421:ℚ)/20000),((28889:ℚ)/40000),((765808717:ℚ)/2500000000),((1811758553:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((14421:ℝ)/20000) ((28889:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((28889:ℚ)/40000),((3617:ℚ)/5000),((1537816689:ℚ)/5000000000),((715929551:ℚ)/2000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((28889:ℝ)/40000) ((3617:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((3617:ℚ)/5000),((57919:ℚ)/80000),((3081775911:ℚ)/10000000000),((3535257793:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((3617:ℝ)/5000) ((57919:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((57919:ℚ)/80000),((28983:ℚ)/40000),((1543940503:ℚ)/5000000000),((1756430707:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((57919:ℝ)/80000) ((28983:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((28983:ℚ)/40000),((58013:ℚ)/80000),((3093948943:ℚ)/10000000000),((872581831:ℚ)/2500000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((28983:ℝ)/40000) ((58013:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((58013:ℚ)/80000),((2903:ℚ)/4000),((3099979997:ℚ)/10000000000),((693530567:ℚ)/2000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((58013:ℝ)/80000) ((2903:ℝ)/4000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((2903:ℚ)/4000),((58107:ℚ)/80000),((77649361:ℚ)/250000000),((344483517:ℚ)/1000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((58107:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((58107:ℚ)/80000),((29077:ℚ)/40000),((155596627:ℚ)/500000000),((3421871461:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((58107:ℝ)/80000) ((29077:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((29077:ℚ)/40000),((58201:ℚ)/80000),((3117854561:ℚ)/10000000000),((424844843:ℚ)/1250000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((29077:ℝ)/40000) ((58201:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((58201:ℚ)/80000),((7281:ℚ)/10000),((624748153:ℚ)/2000000000),((1687746977:ℚ)/5000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((58201:ℝ)/80000) ((7281:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((7281:ℚ)/10000),((11659:ℚ)/16000),((312959141:ℚ)/1000000000),((3352073921:ℚ)/10000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((7281:ℝ)/10000) ((11659:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((11659:ℚ)/16000),((29171:ℚ)/40000),((3135406749:ℚ)/10000000000),((832123841:ℚ)/2500000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((11659:ℝ)/16000) ((29171:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((29171:ℚ)/40000),((58389:ℚ)/80000),((1570593517:ℚ)/5000000000),((1652377443:ℚ)/5000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((29171:ℝ)/40000) ((58389:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((58389:ℚ)/80000),((14609:ℚ)/20000),((3146932513:ℚ)/10000000000),((410106121:ℚ)/1250000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((58389:ℝ)/80000) ((14609:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((14609:ℚ)/20000),((5853:ℚ)/8000),((98697501:ℚ)/312500000),((1628386981:ℚ)/5000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((14609:ℝ)/20000) ((5853:ℝ)/8000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((5853:ℚ)/8000),((458:ℚ)/625),((3169571227:ℚ)/10000000000),((1604050709:ℚ)/5000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((5853:ℝ)/8000) ((458:ℝ)/625),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((458:ℚ)/625),((29359:ℚ)/40000),((1590343987:ℚ)/5000000000),((12634821:ℚ)/40000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((458:ℝ)/625) ((29359:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((29359:ℚ)/40000),((14703:ℚ)/20000),((398959013:ℚ)/1250000000),((3108550927:ℚ)/10000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((29359:ℝ)/40000) ((14703:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((14703:ℚ)/20000),((29453:ℚ)/40000),((1601262701:ℚ)/5000000000),((3057601107:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((14703:ℝ)/20000) ((29453:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((29453:ℚ)/40000),((59:ℚ)/80),((3213249611:ℚ)/10000000000),((375726913:ℚ)/1250000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((29453:ℝ)/40000) ((59:ℝ)/80),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((59:ℚ)/80),((14797:ℚ)/20000),((808579383:ℚ)/2500000000),((46142961:ℚ)/156250000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((59:ℝ)/80) ((14797:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((14797:ℚ)/20000),((3711:ℚ)/5000),((3254889011:ℚ)/10000000000),((284498147:ℚ)/1000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((14797:ℝ)/20000) ((3711:ℝ)/5000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((3711:ℚ)/5000),((14891:ℚ)/20000),((818744149:ℚ)/2500000000),((273265541:ℚ)/1000000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((3711:ℝ)/5000) ((14891:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((14891:ℚ)/20000),((7469:ℚ)/10000),((1647296139:ℚ)/5000000000),((653908843:ℚ)/2500000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((14891:ℝ)/20000) ((7469:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((7469:ℚ)/10000),((1879:ℚ)/2500),((208278331:ℚ)/625000000),((1246630093:ℚ)/5000000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((7469:ℝ)/10000) ((1879:ℝ)/2500),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((1879:ℚ)/2500),((761:ℚ)/1000),((3402985557:ℚ)/10000000000),((222887889:ℚ)/1000000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((1879:ℝ)/2500) ((761:ℝ)/1000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((761:ℚ)/1000),((963:ℚ)/1250),((1733547213:ℚ)/5000000000),((393605161:ℚ)/2500000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((761:ℝ)/1000) ((963:ℝ)/1250),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1691:ℝ)/2500),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((3429:ℝ)/5000) ((6999:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((1691:ℝ)/2500) ((6999:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((6999:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((6999:ℝ)/10000) ((7093:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((14233:ℝ)/20000) ((14327:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((7093:ℝ)/10000) ((14327:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node5_10 :
    ∀ r ∈ Set.Icc ((6999:ℝ)/10000) ((14327:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_7 node7_10
private theorem node0_10 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((14327:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((14327:ℝ)/20000) ((7187:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((5759:ℝ)/8000) ((28889:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((7187:ℝ)/10000) ((28889:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node10_15 :
    ∀ r ∈ Set.Icc ((14327:ℝ)/20000) ((28889:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_15
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((28889:ℝ)/40000) ((57919:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((28983:ℝ)/40000) ((2903:ℝ)/4000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node17_20 :
    ∀ r ∈ Set.Icc ((57919:ℝ)/80000) ((2903:ℝ)/4000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 node18_20
private theorem node15_20 :
    ∀ r ∈ Set.Icc ((28889:ℝ)/40000) ((2903:ℝ)/4000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_17 node17_20
private theorem node10_20 :
    ∀ r ∈ Set.Icc ((14327:ℝ)/20000) ((2903:ℝ)/4000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_15 node15_20
private theorem node0_20 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((2903:ℝ)/4000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_10 node10_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((29077:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((58201:ℝ)/80000) ((11659:ℝ)/16000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node22_25 :
    ∀ r ∈ Set.Icc ((29077:ℝ)/40000) ((11659:ℝ)/16000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 node23_25
private theorem node20_25 :
    ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((11659:ℝ)/16000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_22 node22_25
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((11659:ℝ)/16000) ((58389:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((14609:ℝ)/20000) ((458:ℝ)/625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((58389:ℝ)/80000) ((458:ℝ)/625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node25_30 :
    ∀ r ∈ Set.Icc ((11659:ℝ)/16000) ((458:ℝ)/625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node25_27 node27_30
private theorem node20_30 :
    ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((458:ℝ)/625),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_25 node25_30
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((458:ℝ)/625) ((14703:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node33_35 :
    ∀ r ∈ Set.Icc ((29453:ℝ)/40000) ((14797:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 leaf34
private theorem node32_35 :
    ∀ r ∈ Set.Icc ((14703:ℝ)/20000) ((14797:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 node33_35
private theorem node30_35 :
    ∀ r ∈ Set.Icc ((458:ℝ)/625) ((14797:ℝ)/20000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node30_32 node32_35
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((3711:ℝ)/5000) ((7469:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 leaf37
private theorem node35_38 :
    ∀ r ∈ Set.Icc ((14797:ℝ)/20000) ((7469:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf35 node36_38
private theorem node39_41 :
    ∀ r ∈ Set.Icc ((1879:ℝ)/2500) ((963:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 leaf40
private theorem node38_41 :
    ∀ r ∈ Set.Icc ((7469:ℝ)/10000) ((963:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf38 node39_41
private theorem node35_41 :
    ∀ r ∈ Set.Icc ((14797:ℝ)/20000) ((963:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node35_38 node38_41
private theorem node30_41 :
    ∀ r ∈ Set.Icc ((458:ℝ)/625) ((963:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node30_35 node35_41
private theorem node20_41 :
    ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((963:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_30 node30_41
private theorem node0_41 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((963:ℝ)/1250),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_20 node20_41
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_41
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC48
#check @N11Formalization.C450SixthRadialC48.bound
#print axioms N11Formalization.C450SixthRadialC48.params_valid
#print axioms N11Formalization.C450SixthRadialC48.params_sum
#print axioms N11Formalization.C450SixthRadialC48.bound
