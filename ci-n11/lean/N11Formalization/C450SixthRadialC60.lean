import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC60
open C450RadialPacketKernel
def params : Params := ⟨((261091123161:ℚ)/102400000000),((71474176039:ℚ)/102400000000),((2420381:ℚ)/4000000),((179:ℚ)/10000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((26379:ℚ)/40000),((1040255423:ℚ)/5000000000),((656330333:ℚ)/1000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((26379:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((26379:ℚ)/40000),((54337:ℚ)/80000),((2478042799:ℚ)/10000000000),((5657671057:ℚ)/10000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((26379:ℝ)/40000) ((54337:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((54337:ℚ)/80000),((110253:ℚ)/160000),((82484021:ℚ)/312500000),((2576468511:ℚ)/5000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((54337:ℝ)/80000) ((110253:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((110253:ℚ)/160000),((13979:ℚ)/20000),((2782559719:ℚ)/10000000000),((4882966399:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((110253:ℝ)/160000) ((13979:ℝ)/20000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((13979:ℚ)/20000),((225243:ℚ)/320000),((1424096143:ℚ)/5000000000),((2299257421:ℚ)/5000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((13979:ℝ)/20000) ((225243:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((225243:ℚ)/320000),((113411:ℚ)/160000),((2910304263:ℚ)/10000000000),((4449991771:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((225243:ℝ)/320000) ((113411:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((113411:ℚ)/160000),((228401:ℚ)/320000),((1484577667:ℚ)/5000000000),((214834579:ℚ)/500000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((113411:ℝ)/160000) ((228401:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((228401:ℚ)/320000),((458381:ℚ)/640000),((2997430199:ℚ)/10000000000),((517260173:ℚ)/1250000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((228401:ℝ)/320000) ((458381:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((458381:ℚ)/640000),((11499:ℚ)/16000),((3024972911:ℚ)/10000000000),((202829529:ℚ)/500000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((458381:ℝ)/640000) ((11499:ℝ)/16000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((11499:ℚ)/16000),((461539:ℚ)/640000),((1525903873:ℚ)/5000000000),((3973523299:ℚ)/10000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((11499:ℝ)/16000) ((461539:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((461539:ℚ)/640000),((231559:ℚ)/320000),((1538978791:ℚ)/5000000000),((1944389129:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((461539:ℝ)/640000) ((231559:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((231559:ℚ)/320000),((185563:ℚ)/256000),((3090782419:ℚ)/10000000000),((380224301:ℚ)/1000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((231559:ℝ)/320000) ((185563:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((185563:ℚ)/256000),((464697:ℚ)/640000),((1551722003:ℚ)/5000000000),((3758265431:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((185563:ℝ)/256000) ((464697:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((464697:ℚ)/640000),((930973:ℚ)/1280000),((3115944859:ℚ)/10000000000),((1856896073:ℚ)/5000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((464697:ℝ)/640000) ((930973:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((930973:ℚ)/1280000),((116569:ℚ)/160000),((1564143711:ℚ)/5000000000),((3668805093:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((930973:ℝ)/1280000) ((116569:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((116569:ℚ)/160000),((934131:ℚ)/1280000),((785118519:ℚ)/2500000000),((1811642551:ℚ)/5000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((116569:ℝ)/160000) ((934131:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((934131:ℚ)/1280000),((93571:ℚ)/128000),((12314481:ℚ)/39062500),((3577211793:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((934131:ℝ)/1280000) ((93571:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((93571:ℚ)/128000),((1872999:ℚ)/2560000),((394808347:ℚ)/1250000000),((882640867:ℚ)/2500000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((93571:ℝ)/128000) ((1872999:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((1872999:ℚ)/2560000),((937289:ℚ)/1280000),((3164388859:ℚ)/10000000000),((438377063:ℚ)/1250000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((1872999:ℝ)/2560000) ((937289:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((937289:ℚ)/1280000),((1876157:ℚ)/2560000),((1585136829:ℚ)/5000000000),((348331699:ℚ)/1000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((937289:ℝ)/1280000) ((1876157:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1876157:ℚ)/2560000),((234717:ℚ)/320000),((1588060721:ℚ)/5000000000),((3459461787:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1876157:ℝ)/2560000) ((234717:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((234717:ℚ)/320000),((375863:ℚ)/512000),((3181932477:ℚ)/10000000000),((1717723823:ℚ)/5000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((234717:ℝ)/320000) ((375863:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((375863:ℚ)/512000),((940447:ℚ)/1280000),((127508281:ℚ)/400000000),((1705635603:ℚ)/5000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((375863:ℝ)/512000) ((940447:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((940447:ℚ)/1280000),((1882473:ℚ)/2560000),((1596722673:ℚ)/5000000000),((846732247:ℚ)/2500000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((940447:ℝ)/1280000) ((1882473:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((1882473:ℚ)/2560000),((471013:ℚ)/640000),((639829539:ℚ)/2000000000),((1681208693:ℚ)/5000000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((1882473:ℝ)/2560000) ((471013:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((471013:ℚ)/640000),((1885631:ℚ)/2560000),((801203581:ℚ)/2500000000),((417216583:ℚ)/1250000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((471013:ℝ)/640000) ((1885631:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((1885631:ℚ)/2560000),((188721:ℚ)/256000),((802611371:ℚ)/2500000000),((828217737:ℚ)/2500000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((1885631:ℝ)/2560000) ((188721:ℝ)/256000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((188721:ℚ)/256000),((1888789:ℚ)/2560000),((160802071:ℚ)/500000000),((3287828217:ℚ)/10000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((188721:ℝ)/256000) ((1888789:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((1888789:ℚ)/2560000),((29537:ℚ)/40000),((402700297:ℚ)/1250000000),((3262600299:ℚ)/10000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((1888789:ℝ)/2560000) ((29537:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((29537:ℚ)/40000),((946763:ℚ)/1280000),((646524061:ℚ)/2000000000),((161859143:ℚ)/500000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((29537:ℝ)/40000) ((946763:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((946763:ℚ)/1280000),((474171:ℚ)/640000),((3243501159:ℚ)/10000000000),((3185761219:ℚ)/10000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((946763:ℝ)/1280000) ((474171:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((474171:ℚ)/640000),((949921:ℚ)/1280000),((1627123389:ℚ)/5000000000),((1566762519:ℚ)/5000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((474171:ℝ)/640000) ((949921:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((949921:ℚ)/1280000),((1903:ℚ)/2560),((40810737:ℚ)/125000000),((3080432841:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((949921:ℝ)/1280000) ((1903:ℝ)/2560),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((1903:ℚ)/2560),((953079:ℚ)/1280000),((163766973:ℚ)/500000000),((1513219769:ℚ)/5000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((1903:ℝ)/2560) ((953079:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((953079:ℚ)/1280000),((477329:ℚ)/640000),((3285689993:ℚ)/10000000000),((2971495967:ℚ)/10000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((953079:ℝ)/1280000) ((477329:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((477329:ℚ)/640000),((119727:ℚ)/160000),((3306007813:ℚ)/10000000000),((728887091:ℚ)/2500000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((477329:ℝ)/640000) ((119727:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((119727:ℚ)/160000),((480487:ℚ)/640000),((3325825359:ℚ)/10000000000),((2800399113:ℚ)/10000000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((119727:ℝ)/160000) ((480487:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((480487:ℚ)/640000),((241033:ℚ)/320000),((669030999:ℚ)/2000000000),((1340221357:ℚ)/5000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((480487:ℝ)/640000) ((241033:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((241033:ℚ)/320000),((60653:ℚ)/80000),((3382397319:ℚ)/10000000000),((2555001801:ℚ)/10000000000)⟩
theorem valid38 : Valid params packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((241033:ℝ)/320000) ((60653:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((60653:ℚ)/80000),((24577:ℚ)/32000),((3451514847:ℚ)/10000000000),((285501697:ℚ)/1250000000)⟩
theorem valid39 : Valid params packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((60653:ℝ)/80000) ((24577:ℝ)/32000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((24577:ℚ)/32000),((7779:ℚ)/10000),((54906061:ℚ)/156250000),((64531289:ℚ)/400000000)⟩
theorem valid40 : Valid params packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((24577:ℝ)/32000) ((7779:ℝ)/10000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((54337:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node3_5 :
    ∀ r ∈ Set.Icc ((110253:ℝ)/160000) ((225243:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 leaf4
private theorem node2_5 :
    ∀ r ∈ Set.Icc ((54337:ℝ)/80000) ((225243:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 node3_5
private theorem node0_5 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((225243:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_5
private theorem node5_7 :
    ∀ r ∈ Set.Icc ((225243:ℝ)/320000) ((228401:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf5 leaf6
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((458381:ℝ)/640000) ((461539:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node7_10 :
    ∀ r ∈ Set.Icc ((228401:ℝ)/320000) ((461539:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 node8_10
private theorem node5_10 :
    ∀ r ∈ Set.Icc ((225243:ℝ)/320000) ((461539:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node5_7 node7_10
private theorem node0_10 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((461539:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_5 node5_10
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((461539:ℝ)/640000) ((185563:ℝ)/256000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((464697:ℝ)/640000) ((116569:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((185563:ℝ)/256000) ((116569:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node10_15 :
    ∀ r ∈ Set.Icc ((461539:ℝ)/640000) ((116569:ℝ)/160000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_12 node12_15
private theorem node15_17 :
    ∀ r ∈ Set.Icc ((116569:ℝ)/160000) ((93571:ℝ)/128000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 leaf16
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((1872999:ℝ)/2560000) ((1876157:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node17_20 :
    ∀ r ∈ Set.Icc ((93571:ℝ)/128000) ((1876157:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 node18_20
private theorem node15_20 :
    ∀ r ∈ Set.Icc ((116569:ℝ)/160000) ((1876157:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node15_17 node17_20
private theorem node10_20 :
    ∀ r ∈ Set.Icc ((461539:ℝ)/640000) ((1876157:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node10_15 node15_20
private theorem node0_20 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1876157:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_10 node10_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((1876157:ℝ)/2560000) ((375863:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((940447:ℝ)/1280000) ((471013:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node22_25 :
    ∀ r ∈ Set.Icc ((375863:ℝ)/512000) ((471013:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 node23_25
private theorem node20_25 :
    ∀ r ∈ Set.Icc ((1876157:ℝ)/2560000) ((471013:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_22 node22_25
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((471013:ℝ)/640000) ((188721:ℝ)/256000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((1888789:ℝ)/2560000) ((946763:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((188721:ℝ)/256000) ((946763:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node25_30 :
    ∀ r ∈ Set.Icc ((471013:ℝ)/640000) ((946763:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node25_27 node27_30
private theorem node20_30 :
    ∀ r ∈ Set.Icc ((1876157:ℝ)/2560000) ((946763:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_25 node25_30
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((946763:ℝ)/1280000) ((949921:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node33_35 :
    ∀ r ∈ Set.Icc ((1903:ℝ)/2560) ((477329:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 leaf34
private theorem node32_35 :
    ∀ r ∈ Set.Icc ((949921:ℝ)/1280000) ((477329:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf32 node33_35
private theorem node30_35 :
    ∀ r ∈ Set.Icc ((946763:ℝ)/1280000) ((477329:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node30_32 node32_35
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((119727:ℝ)/160000) ((241033:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 leaf37
private theorem node35_38 :
    ∀ r ∈ Set.Icc ((477329:ℝ)/640000) ((241033:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf35 node36_38
private theorem node39_41 :
    ∀ r ∈ Set.Icc ((60653:ℝ)/80000) ((7779:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 leaf40
private theorem node38_41 :
    ∀ r ∈ Set.Icc ((241033:ℝ)/320000) ((7779:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf38 node39_41
private theorem node35_41 :
    ∀ r ∈ Set.Icc ((477329:ℝ)/640000) ((7779:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node35_38 node38_41
private theorem node30_41 :
    ∀ r ∈ Set.Icc ((946763:ℝ)/1280000) ((7779:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node30_35 node35_41
private theorem node20_41 :
    ∀ r ∈ Set.Icc ((1876157:ℝ)/2560000) ((7779:ℝ)/10000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_30 node30_41
private theorem node0_41 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((7779:ℝ)/10000),
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
end N11Formalization.C450SixthRadialC60
#check @N11Formalization.C450SixthRadialC60.bound
#print axioms N11Formalization.C450SixthRadialC60.params_valid
#print axioms N11Formalization.C450SixthRadialC60.params_sum
#print axioms N11Formalization.C450SixthRadialC60.bound
