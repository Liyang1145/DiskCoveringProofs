import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC61
open C450RadialPacketKernel
def params : Params := ⟨((16310486519:ℚ)/6400000000),((4474844681:ℚ)/6400000000),((601403:ℚ)/1000000),((741:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((105541:ℚ)/160000),((416832923:ℚ)/2000000000),((1644192073:ℚ)/2500000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((105541:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((105541:ℚ)/160000),((217423:ℚ)/320000),((1241059869:ℚ)/5000000000),((708645789:ℚ)/1250000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((105541:ℝ)/160000) ((217423:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((217423:ℚ)/320000),((441187:ℚ)/640000),((528736783:ℚ)/2000000000),((2581678717:ℚ)/5000000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((217423:ℝ)/320000) ((441187:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((441187:ℚ)/640000),((55941:ℚ)/80000),((2786826231:ℚ)/10000000000),((978563571:ℚ)/2000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((441187:ℝ)/640000) ((55941:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55941:ℚ)/80000),((453869:ℚ)/640000),((582920459:ℚ)/2000000000),((57597137:ℚ)/125000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55941:ℝ)/80000) ((453869:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((453869:ℚ)/640000),((914079:ℚ)/1280000),((1486727991:ℚ)/5000000000),((4305320327:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((453869:ℝ)/640000) ((914079:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((914079:ℚ)/1280000),((1834499:ℚ)/2560000),((24013833:ℚ)/80000000),((4146382121:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((914079:ℝ)/1280000) ((1834499:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((1834499:ℚ)/2560000),((46021:ℚ)/64000),((151463409:ℚ)/500000000),((203236161:ℚ)/500000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((1834499:ℝ)/2560000) ((46021:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((46021:ℚ)/64000),((1847181:ℚ)/2560000),((764024371:ℚ)/2500000000),((3981484881:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((46021:ℝ)/64000) ((1847181:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((1847181:ℚ)/2560000),((926761:ℚ)/1280000),((770559993:ℚ)/2500000000),((1948282811:ℚ)/5000000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((1847181:ℝ)/2560000) ((926761:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((926761:ℚ)/1280000),((742677:ℚ)/1024000),((309506047:ℚ)/1000000000),((476231597:ℚ)/1250000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((926761:ℝ)/1280000) ((742677:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((742677:ℚ)/1024000),((1859863:ℚ)/2560000),((776929321:ℚ)/2500000000),((117680783:ℚ)/312500000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((742677:ℝ)/1024000) ((1859863:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((1859863:ℚ)/2560000),((3726067:ℚ)/5120000),((624042587:ℚ)/2000000000),((3721220689:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((1859863:ℝ)/2560000) ((3726067:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((3726067:ℚ)/5120000),((466551:ℚ)/640000),((1566274937:ℚ)/5000000000),((3676141581:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((3726067:ℝ)/5120000) ((466551:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((466551:ℚ)/640000),((3738749:ℚ)/5120000),((393091311:ℚ)/1250000000),((1815264261:ℚ)/5000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((466551:ℝ)/640000) ((3738749:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((3738749:ℚ)/5120000),((374509:ℚ)/512000),((3156757097:ℚ)/10000000000),((3584361093:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((3738749:ℝ)/5120000) ((374509:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((374509:ℚ)/512000),((3751431:ℚ)/5120000),((633726393:ℚ)/2000000000),((1768808777:ℚ)/5000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((374509:ℝ)/512000) ((3751431:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((3751431:ℚ)/5120000),((7509203:ℚ)/10240000),((1587256593:ℚ)/5000000000),((1745137361:ℚ)/5000000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((3751431:ℝ)/5120000) ((7509203:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((7509203:ℚ)/10240000),((939443:ℚ)/1280000),((795089323:ℚ)/2500000000),((3466370899:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((7509203:ℝ)/10240000) ((939443:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((939443:ℚ)/1280000),((1504377:ℚ)/2048000),((398270569:ℚ)/1250000000),((688461567:ℚ)/2000000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((939443:ℝ)/1280000) ((1504377:ℝ)/2048000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1504377:ℚ)/2048000),((3764113:ℚ)/5120000),((1595967613:ℚ)/5000000000),((1709041081:ℚ)/5000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1504377:ℝ)/2048000) ((3764113:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((3764113:ℚ)/5120000),((7534567:ℚ)/10240000),((399708697:ℚ)/1250000000),((1696845197:ℚ)/5000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((3764113:ℝ)/5120000) ((7534567:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((7534567:ℚ)/10240000),((1885227:ℚ)/2560000),((3203367857:ℚ)/10000000000),((3369128919:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((7534567:ℝ)/10240000) ((1885227:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((1885227:ℚ)/2560000),((7547249:ℚ)/10240000),((3209030323:ℚ)/10000000000),((418049249:ℚ)/1250000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((1885227:ℝ)/2560000) ((7547249:ℝ)/10240000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((7547249:ℚ)/10240000),((755359:ℚ)/1024000),((128586289:ℚ)/400000000),((829870433:ℚ)/2500000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((7547249:ℝ)/10240000) ((755359:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((755359:ℚ)/1024000),((118223:ℚ)/160000),((806451329:ℚ)/2500000000),((329438811:ℚ)/1000000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((755359:ℝ)/1024000) ((118223:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((118223:ℚ)/160000),((3789477:ℚ)/5120000),((323681407:ℚ)/1000000000),((3243639899:ℚ)/10000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((118223:ℝ)/160000) ((3789477:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((3789477:ℚ)/5120000),((1897909:ℚ)/2560000),((3247685379:ℚ)/10000000000),((638422783:ℚ)/2000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((3789477:ℝ)/5120000) ((1897909:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((1897909:ℚ)/2560000),((3802159:ℚ)/5120000),((325842109:ℚ)/1000000000),((1569885913:ℚ)/5000000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((1897909:ℝ)/2560000) ((3802159:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((3802159:ℚ)/5120000),((7617:ℚ)/10240),((3269023003:ℚ)/10000000000),((771643019:ℚ)/2500000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((3802159:ℝ)/5120000) ((7617:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((7617:ℚ)/10240),((3814841:ℚ)/5120000),((1639746439:ℚ)/5000000000),((758117371:ℚ)/2500000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((7617:ℝ)/10240) ((3814841:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((3814841:ℚ)/5120000),((1910591:ℚ)/2560000),((1644916217:ℚ)/5000000000),((595482959:ℚ)/2000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((3814841:ℝ)/5120000) ((1910591:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((1910591:ℚ)/2560000),((479233:ℚ)/640000),((1655063631:ℚ)/5000000000),((2921354137:ℚ)/10000000000)⟩
theorem valid32 : Valid params packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((1910591:ℝ)/2560000) ((479233:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((479233:ℚ)/640000),((1923273:ℚ)/2560000),((3329920459:ℚ)/10000000000),((2805972491:ℚ)/10000000000)⟩
theorem valid33 : Valid params packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((479233:ℝ)/640000) ((1923273:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((1923273:ℚ)/2560000),((964807:ℚ)/1280000),((3349224419:ℚ)/10000000000),((2685774397:ℚ)/10000000000)⟩
theorem valid34 : Valid params packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((1923273:ℝ)/2560000) ((964807:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((964807:ℚ)/1280000),((242787:ℚ)/320000),((3386411529:ℚ)/10000000000),((2560081157:ℚ)/10000000000)⟩
theorem valid35 : Valid params packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((964807:ℝ)/1280000) ((242787:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((242787:ℚ)/320000),((98383:ℚ)/128000),((3455403923:ℚ)/10000000000),((1144274599:ℚ)/5000000000)⟩
theorem valid36 : Valid params packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((242787:ℝ)/320000) ((98383:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((98383:ℚ)/128000),((31141:ℚ)/40000),((1758866751:ℚ)/5000000000),((1616478877:ℚ)/10000000000)⟩
theorem valid37 : Valid params packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((98383:ℝ)/128000) ((31141:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((217423:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((217423:ℝ)/320000) ((55941:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((55941:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((55941:ℝ)/80000) ((914079:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((1834499:ℝ)/2560000) ((1847181:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node6_9 :
    ∀ r ∈ Set.Icc ((914079:ℝ)/1280000) ((1847181:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 node7_9
private theorem node4_9 :
    ∀ r ∈ Set.Icc ((55941:ℝ)/80000) ((1847181:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_9
private theorem node0_9 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1847181:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_9
private theorem node9_11 :
    ∀ r ∈ Set.Icc ((1847181:ℝ)/2560000) ((742677:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 leaf10
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((1859863:ℝ)/2560000) ((466551:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node11_14 :
    ∀ r ∈ Set.Icc ((742677:ℝ)/1024000) ((466551:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf11 node12_14
private theorem node9_14 :
    ∀ r ∈ Set.Icc ((1847181:ℝ)/2560000) ((466551:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node9_11 node11_14
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((466551:ℝ)/640000) ((374509:ℝ)/512000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node17_19 :
    ∀ r ∈ Set.Icc ((3751431:ℝ)/5120000) ((939443:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf17 leaf18
private theorem node16_19 :
    ∀ r ∈ Set.Icc ((374509:ℝ)/512000) ((939443:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 node17_19
private theorem node14_19 :
    ∀ r ∈ Set.Icc ((466551:ℝ)/640000) ((939443:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node14_16 node16_19
private theorem node9_19 :
    ∀ r ∈ Set.Icc ((1847181:ℝ)/2560000) ((939443:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node9_14 node14_19
private theorem node0_19 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((939443:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_9 node9_19
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((939443:ℝ)/1280000) ((3764113:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node21_23 :
    ∀ r ∈ Set.Icc ((3764113:ℝ)/5120000) ((1885227:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 leaf22
private theorem node19_23 :
    ∀ r ∈ Set.Icc ((939443:ℝ)/1280000) ((1885227:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_21 node21_23
private theorem node23_25 :
    ∀ r ∈ Set.Icc ((1885227:ℝ)/2560000) ((755359:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf23 leaf24
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((118223:ℝ)/160000) ((1897909:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node25_28 :
    ∀ r ∈ Set.Icc ((755359:ℝ)/1024000) ((1897909:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 node26_28
private theorem node23_28 :
    ∀ r ∈ Set.Icc ((1885227:ℝ)/2560000) ((1897909:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node23_25 node25_28
private theorem node19_28 :
    ∀ r ∈ Set.Icc ((939443:ℝ)/1280000) ((1897909:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_23 node23_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((1897909:ℝ)/2560000) ((7617:ℝ)/10240),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((3814841:ℝ)/5120000) ((479233:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((7617:ℝ)/10240) ((479233:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node28_33 :
    ∀ r ∈ Set.Icc ((1897909:ℝ)/2560000) ((479233:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node28_30 node30_33
private theorem node33_35 :
    ∀ r ∈ Set.Icc ((479233:ℝ)/640000) ((964807:ℝ)/1280000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 leaf34
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((242787:ℝ)/320000) ((31141:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 leaf37
private theorem node35_38 :
    ∀ r ∈ Set.Icc ((964807:ℝ)/1280000) ((31141:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf35 node36_38
private theorem node33_38 :
    ∀ r ∈ Set.Icc ((479233:ℝ)/640000) ((31141:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node33_35 node35_38
private theorem node28_38 :
    ∀ r ∈ Set.Icc ((1897909:ℝ)/2560000) ((31141:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node28_33 node33_38
private theorem node19_38 :
    ∀ r ∈ Set.Icc ((939443:ℝ)/1280000) ((31141:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node19_28 node28_38
private theorem node0_38 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((31141:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_19 node19_38
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_38
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC61
#check @N11Formalization.C450SixthRadialC61.bound
#print axioms N11Formalization.C450SixthRadialC61.params_valid
#print axioms N11Formalization.C450SixthRadialC61.params_sum
#print axioms N11Formalization.C450SixthRadialC61.bound
