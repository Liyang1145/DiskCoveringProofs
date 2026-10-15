import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC59
open C450RadialPacketKernel
def params : Params := ⟨((32651387671:ℚ)/12800000000),((8919274729:ℚ)/12800000000),((48703:ℚ)/80000),((691:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((105491:ℚ)/160000),((207684721:ℚ)/1000000000),((6549814787:ℚ)/10000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((105491:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((105491:ℚ)/160000),((217273:ℚ)/320000),((1236976577:ℚ)/5000000000),((1129230991:ℚ)/2000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((105491:ℝ)/160000) ((217273:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((217273:ℚ)/320000),((440837:ℚ)/640000),((13176397:ℚ)/50000000),((5142497401:ℚ)/10000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((217273:ℝ)/320000) ((440837:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((440837:ℚ)/640000),((55891:ℚ)/80000),((173642369:ℚ)/625000000),((2436548319:ℚ)/5000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((440837:ℝ)/640000) ((55891:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55891:ℚ)/80000),((900547:ℚ)/1280000),((568777899:ℚ)/2000000000),((2294620697:ℚ)/5000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55891:ℝ)/80000) ((900547:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((900547:ℚ)/1280000),((453419:ℚ)/640000),((2905989691:ℚ)/10000000000),((2220514047:ℚ)/5000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((900547:ℝ)/1280000) ((453419:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((453419:ℚ)/640000),((913129:ℚ)/1280000),((1482418771:ℚ)/5000000000),((536005819:ℚ)/1250000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((453419:ℝ)/640000) ((913129:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((913129:ℚ)/1280000),((1832549:ℚ)/2560000),((299311383:ℚ)/1000000000),((64527577:ℚ)/156250000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((913129:ℝ)/1280000) ((1832549:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1832549:ℚ)/2560000),((45971:ℚ)/64000),((30206599:ℚ)/100000000),((4048442511:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1832549:ℝ)/2560000) ((45971:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45971:ℚ)/64000),((1845131:ℚ)/2560000),((304749997:ℚ)/1000000000),((793109317:ℚ)/2000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45971:ℝ)/64000) ((1845131:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1845131:ℚ)/2560000),((3696553:ℚ)/5120000),((1530331219:ℚ)/5000000000),((1940488033:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1845131:ℝ)/2560000) ((3696553:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((3696553:ℚ)/5120000),((925711:ℚ)/1280000),((153682843:ℚ)/500000000),((767605649:ℚ)/2000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((3696553:ℝ)/5120000) ((925711:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((925711:ℚ)/1280000),((741827:ℚ)/1024000),((3086485889:ℚ)/10000000000),((3794618727:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((925711:ℝ)/1280000) ((741827:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((741827:ℚ)/1024000),((1857713:ℚ)/2560000),((387394013:ℚ)/1250000000),((3750731449:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((741827:ℝ)/1024000) ((1857713:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((1857713:ℚ)/2560000),((3721717:ℚ)/5120000),((3111658013:ℚ)/10000000000),((1853174703:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((1857713:ℝ)/2560000) ((3721717:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((3721717:ℚ)/5120000),((466001:ℚ)/640000),((624801211:ℚ)/2000000000),((915363643:ℚ)/2500000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((3721717:ℝ)/5120000) ((466001:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((466001:ℚ)/640000),((3734299:ℚ)/5120000),((784049651:ℚ)/2500000000),((1808013907:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((466001:ℝ)/640000) ((3734299:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((3734299:ℚ)/5120000),((7474889:ℚ)/10240000),((3142237293:ℚ)/10000000000),((3570048793:ℚ)/10000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((3734299:ℝ)/5120000) ((7474889:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((7474889:ℚ)/10240000),((374059:ℚ)/512000),((314823797:ℚ)/1000000000),((354684547:ℚ)/1000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((7474889:ℝ)/10240000) ((374059:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((374059:ℚ)/512000),((7487471:ℚ)/10240000),((788550229:ℚ)/2500000000),((880873963:ℚ)/2500000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((374059:ℝ)/512000) ((7487471:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((7487471:ℚ)/10240000),((3746881:ℚ)/5120000),((632025281:ℚ)/2000000000),((1749998503:ℚ)/5000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((7487471:ℝ)/10240000) ((3746881:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((3746881:ℚ)/5120000),((7500053:ℚ)/10240000),((316601471:ℚ)/1000000000),((1738172951:ℚ)/5000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((3746881:ℝ)/5120000) ((7500053:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((7500053:ℚ)/10240000),((938293:ℚ)/1280000),((3171866099:ℚ)/10000000000),((690507881:ℚ)/2000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((7500053:ℝ)/10240000) ((938293:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((938293:ℚ)/1280000),((1502527:ℚ)/2048000),((1588840419:ℚ)/5000000000),((857143569:ℚ)/2500000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((938293:ℝ)/1280000) ((1502527:ℝ)/2048000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((1502527:ℚ)/2048000),((3759463:ℚ)/5120000),((795864797:ℚ)/2500000000),((1702223579:ℚ)/5000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((1502527:ℝ)/2048000) ((3759463:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((3759463:ℚ)/5120000),((7525217:ℚ)/10240000),((6228909:ℚ)/19531250),((3380154579:ℚ)/10000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((3759463:ℝ)/5120000) ((7525217:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((7525217:ℚ)/10240000),((1882877:ℚ)/2560000),((399363469:ℚ)/1250000000),((3355692941:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((7525217:ℝ)/10240000) ((1882877:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((1882877:ℚ)/2560000),((7537799:ℚ)/10240000),((1600289237:ℚ)/5000000000),((666211703:ℚ)/2000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((1882877:ℝ)/2560000) ((7537799:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((7537799:ℚ)/10240000),((754409:ℚ)/1024000),((3206213821:ℚ)/10000000000),((1653123717:ℚ)/5000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((7537799:ℝ)/10240000) ((754409:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((754409:ℚ)/1024000),((7550381:ℚ)/10240000),((3211814039:ℚ)/10000000000),((1640627843:ℚ)/5000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((754409:ℝ)/1024000) ((7550381:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((7550381:ℚ)/10240000),((118073:ℚ)/160000),((804344843:ℚ)/2500000000),((3256079107:ℚ)/10000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((7550381:ℝ)/10240000) ((118073:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((118073:ℚ)/160000),((3784627:ℚ)/5120000),((1614203167:ℚ)/5000000000),((323071337:ℚ)/1000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((118073:ℝ)/160000) ((3784627:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((3784627:ℚ)/5120000),((1895459:ℚ)/2560000),((323929659:ℚ)/1000000000),((3179396263:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((3784627:ℝ)/5120000) ((1895459:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((1895459:ℚ)/2560000),((3797209:ℚ)/5120000),((406256497:ℚ)/1250000000),((390908273:ℚ)/1250000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((1895459:ℝ)/2560000) ((3797209:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((3797209:ℚ)/5120000),((7607:ℚ)/10240),((3260674287:ℚ)/10000000000),((1537140869:ℚ)/5000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((3797209:ℝ)/5120000) ((7607:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((7607:ℚ)/10240),((3809791:ℚ)/5120000),((408895659:ℚ)/1250000000),((3020397923:ℚ)/10000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((7607:ℝ)/10240) ((3809791:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((3809791:ℚ)/5120000),((1908041:ℚ)/2560000),((41019083:ℚ)/125000000),((741391419:ℚ)/2500000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((3809791:ℝ)/5120000) ((1908041:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((1908041:ℚ)/2560000),((478583:ℚ)/640000),((825466793:ℚ)/2500000000),((1454865669:ℚ)/5000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((1908041:ℝ)/2560000) ((478583:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((478583:ℚ)/640000),((1920623:ℚ)/2560000),((830427197:ℚ)/2500000000),((1397407457:ℚ)/5000000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((478583:ℝ)/640000) ((1920623:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((1920623:ℚ)/2560000),((963457:ℚ)/1280000),((1670531911:ℚ)/5000000000),((2675100661:ℚ)/10000000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((1920623:ℝ)/2560000) ((963457:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((963457:ℚ)/1280000),((242437:ℚ)/320000),((422295101:ℚ)/1250000000),((637478137:ℚ)/2500000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((963457:ℝ)/1280000) ((242437:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((242437:ℚ)/320000),((98233:ℚ)/128000),((430950297:ℚ)/1250000000),((2279469087:ℚ)/10000000000)⟩
theorem valid41 : Valid params packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((242437:ℝ)/320000) ((98233:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((98233:ℚ)/128000),((31091:ℚ)/40000),((1755108913:ℚ)/5000000000),((805039641:ℚ)/5000000000)⟩
theorem valid42 : Valid params packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((98233:ℝ)/128000) ((31091:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((217273:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((440837:ℝ)/640000) ((900547:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((217273:ℝ)/320000) ((900547:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((900547:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((900547:ℝ)/1280000) ((913129:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((1832549:ℝ)/2560000) ((1845131:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((913129:ℝ)/1280000) ((1845131:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node5_10 :
    ∀ r ∈ Set.Icc ((900547:ℝ)/1280000) ((1845131:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_7 node7_10
private theorem node0_10 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1845131:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((1845131:ℝ)/2560000) ((925711:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((741827:ℝ)/1024000) ((3721717:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((925711:ℝ)/1280000) ((3721717:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node10_15 :
    ∀ r ∈ Set.Icc ((1845131:ℝ)/2560000) ((3721717:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((466001:ℝ)/640000) ((7474889:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((3721717:ℝ)/5120000) ((7474889:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((374059:ℝ)/512000) ((3746881:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node18_21 :
    ∀ r ∈ Set.Icc ((7474889:ℝ)/10240000) ((3746881:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 node19_21
private theorem node15_21 :
    ∀ r ∈ Set.Icc ((3721717:ℝ)/5120000) ((3746881:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_18 node18_21
private theorem node10_21 :
    ∀ r ∈ Set.Icc ((1845131:ℝ)/2560000) ((3746881:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_15 node15_21
private theorem node0_21 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3746881:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_10 node10_21
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((3746881:ℝ)/5120000) ((938293:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((1502527:ℝ)/2048000) ((7525217:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node23_26 :
    ∀ r ∈ Set.Icc ((938293:ℝ)/1280000) ((7525217:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 node24_26
private theorem node21_26 :
    ∀ r ∈ Set.Icc ((3746881:ℝ)/5120000) ((7525217:ℝ)/10240000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_23 node23_26
private theorem node27_29 :
    ∀ r ∈ Set.Icc ((1882877:ℝ)/2560000) ((754409:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 leaf28
private theorem node26_29 :
    ∀ r ∈ Set.Icc ((7525217:ℝ)/10240000) ((754409:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 node27_29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((7550381:ℝ)/10240000) ((3784627:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node29_32 :
    ∀ r ∈ Set.Icc ((754409:ℝ)/1024000) ((3784627:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf29 node30_32
private theorem node26_32 :
    ∀ r ∈ Set.Icc ((7525217:ℝ)/10240000) ((3784627:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node26_29 node29_32
private theorem node21_32 :
    ∀ r ∈ Set.Icc ((3746881:ℝ)/5120000) ((3784627:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_26 node26_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((3784627:ℝ)/5120000) ((3797209:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 leaf33
private theorem node35_37 :
    ∀ r ∈ Set.Icc ((7607:ℝ)/10240) ((1908041:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf35 leaf36
private theorem node34_37 :
    ∀ r ∈ Set.Icc ((3797209:ℝ)/5120000) ((1908041:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 node35_37
private theorem node32_37 :
    ∀ r ∈ Set.Icc ((3784627:ℝ)/5120000) ((1908041:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node32_34 node34_37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((478583:ℝ)/640000) ((963457:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf38 leaf39
private theorem node37_40 :
    ∀ r ∈ Set.Icc ((1908041:ℝ)/2560000) ((963457:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 node38_40
private theorem node41_43 :
    ∀ r ∈ Set.Icc ((242437:ℝ)/320000) ((31091:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf41 leaf42
private theorem node40_43 :
    ∀ r ∈ Set.Icc ((963457:ℝ)/1280000) ((31091:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 node41_43
private theorem node37_43 :
    ∀ r ∈ Set.Icc ((1908041:ℝ)/2560000) ((31091:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node37_40 node40_43
private theorem node32_43 :
    ∀ r ∈ Set.Icc ((3784627:ℝ)/5120000) ((31091:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node32_37 node37_43
private theorem node21_43 :
    ∀ r ∈ Set.Icc ((3746881:ℝ)/5120000) ((31091:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node21_32 node32_43
private theorem node0_43 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((31091:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_21 node21_43
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_43
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC59
#check @N11Formalization.C450SixthRadialC59.bound
#print axioms N11Formalization.C450SixthRadialC59.params_valid
#print axioms N11Formalization.C450SixthRadialC59.params_sum
#print axioms N11Formalization.C450SixthRadialC59.bound
