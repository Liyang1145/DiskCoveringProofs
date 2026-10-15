import N11Formalization.C450RadialPacketKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SixthRadialC41
open C450RadialPacketKernel
def params : Params := ⟨((1025883549:ℚ)/400000000),((273199651:ℚ)/400000000),((42203:ℚ)/62500),((241:ℚ)/40000)⟩
theorem params_valid : ValidParams params := by
  constructor <;> decide +kernel
theorem params_sum : params.A+params.B = ((811927:ℚ)/250000) := by
  decide +kernel
def packet0 : Packet := ⟨((31:ℚ)/50),((105041:ℚ)/160000),((100457481:ℚ)/500000000),((3151405719:ℚ)/5000000000)⟩
theorem valid0 : Valid params packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((105041:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((105041:ℚ)/160000),((215923:ℚ)/320000),((2398085053:ℚ)/10000000000),((2717573231:ℚ)/5000000000)⟩
theorem valid1 : Valid params packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((105041:ℝ)/160000) ((215923:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((215923:ℚ)/320000),((437687:ℚ)/640000),((2557024013:ℚ)/10000000000),((309447433:ℚ)/625000000)⟩
theorem valid2 : Valid params packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((215923:ℝ)/320000) ((437687:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((437687:ℚ)/640000),((55441:ℚ)/80000),((337311387:ℚ)/1250000000),((4692177491:ℚ)/10000000000)⟩
theorem valid3 : Valid params packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((437687:ℝ)/640000) ((55441:ℝ)/80000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((55441:ℚ)/80000),((892897:ℚ)/1280000),((2763615009:ℚ)/10000000000),((4419229727:ℚ)/10000000000)⟩
theorem valid4 : Valid params packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((55441:ℝ)/80000) ((892897:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((892897:ℚ)/1280000),((449369:ℚ)/640000),((2825394631:ℚ)/10000000000),((4276684377:ℚ)/10000000000)⟩
theorem valid5 : Valid params packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((892897:ℝ)/1280000) ((449369:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((449369:ℚ)/640000),((904579:ℚ)/1280000),((576815497:ℚ)/2000000000),((4129534401:ℚ)/10000000000)⟩
theorem valid6 : Valid params packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((449369:ℝ)/640000) ((904579:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((904579:ℚ)/1280000),((1814999:ℚ)/2560000),((2912326393:ℚ)/10000000000),((1988633561:ℚ)/5000000000)⟩
theorem valid7 : Valid params packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((904579:ℝ)/1280000) ((1814999:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((1814999:ℚ)/2560000),((45521:ℚ)/64000),((2939880263:ℚ)/10000000000),((3899027417:ℚ)/10000000000)⟩
theorem valid8 : Valid params packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((1814999:ℝ)/2560000) ((45521:ℝ)/64000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((45521:ℚ)/64000),((1826681:ℚ)/2560000),((2966762219:ℚ)/10000000000),((477408607:ℚ)/1250000000)⟩
theorem valid9 : Valid params packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((45521:ℝ)/64000) ((1826681:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1826681:ℚ)/2560000),((916261:ℚ)/1280000),((2992994051:ℚ)/10000000000),((1868947001:ℚ)/5000000000)⟩
theorem valid10 : Valid params packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1826681:ℝ)/2560000) ((916261:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((916261:ℚ)/1280000),((734177:ℚ)/1024000),((1174169:ℚ)/3906250),((3654794677:ℚ)/10000000000)⟩
theorem valid11 : Valid params packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((916261:ℝ)/1280000) ((734177:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((734177:ℚ)/1024000),((1838363:ℚ)/2560000),((3018596317:ℚ)/10000000000),((3612561179:ℚ)/10000000000)⟩
theorem valid12 : Valid params packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((734177:ℝ)/1024000) ((1838363:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((1838363:ℚ)/2560000),((3682567:ℚ)/5120000),((3031167477:ℚ)/10000000000),((3569850237:ℚ)/10000000000)⟩
theorem valid13 : Valid params packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((1838363:ℝ)/2560000) ((3682567:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((3682567:ℚ)/5120000),((461051:ℚ)/640000),((3043588447:ℚ)/10000000000),((3526644477:ℚ)/10000000000)⟩
theorem valid14 : Valid params packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((3682567:ℝ)/5120000) ((461051:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((461051:ℚ)/640000),((3694249:ℚ)/5120000),((1527930747:ℚ)/5000000000),((3482925457:ℚ)/10000000000)⟩
theorem valid15 : Valid params packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((461051:ℝ)/640000) ((3694249:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((3694249:ℚ)/5120000),((370009:ℚ)/512000),((3067988823:ℚ)/10000000000),((3438673571:ℚ)/10000000000)⟩
theorem valid16 : Valid params packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((3694249:ℝ)/5120000) ((370009:ℝ)/512000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((370009:ℚ)/512000),((3705931:ℚ)/5120000),((3079972583:ℚ)/10000000000),((848466987:ℚ)/2500000000)⟩
theorem valid17 : Valid params packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((370009:ℝ)/512000) ((3705931:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((3705931:ℚ)/5120000),((927943:ℚ)/1280000),((3091814863:ℚ)/10000000000),((3348486329:ℚ)/10000000000)⟩
theorem valid18 : Valid params packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((3705931:ℝ)/5120000) ((927943:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((927943:ℚ)/1280000),((3717613:ℚ)/5120000),((387939713:ℚ)/1250000000),((165125247:ℚ)/500000000)⟩
theorem valid19 : Valid params packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((927943:ℝ)/1280000) ((3717613:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((3717613:ℚ)/5120000),((1861727:ℚ)/2560000),((3115083089:ℚ)/10000000000),((3255898341:ℚ)/10000000000)⟩
theorem valid20 : Valid params packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((3717613:ℝ)/5120000) ((1861727:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((1861727:ℚ)/2560000),((745859:ℚ)/1024000),((3126512957:ℚ)/10000000000),((3208639257:ℚ)/10000000000)⟩
theorem valid21 : Valid params packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((1861727:ℝ)/2560000) ((745859:ℝ)/1024000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((745859:ℚ)/1024000),((116723:ℚ)/160000),((3137809193:ℚ)/10000000000),((3160698391:ℚ)/10000000000)⟩
theorem valid22 : Valid params packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((745859:ℝ)/1024000) ((116723:ℝ)/160000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((116723:ℚ)/160000),((3740977:ℚ)/5120000),((3148973639:ℚ)/10000000000),((1556022101:ℚ)/5000000000)⟩
theorem valid23 : Valid params packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((116723:ℝ)/160000) ((3740977:ℝ)/5120000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((3740977:ℚ)/5120000),((1873409:ℚ)/2560000),((790002023:ℚ)/2500000000),((382830333:ℚ)/1250000000)⟩
theorem valid24 : Valid params packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((3740977:ℝ)/5120000) ((1873409:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((1873409:ℚ)/2560000),((7517:ℚ)/10240),((1590846993:ℚ)/5000000000),((188278561:ℚ)/625000000)⟩
theorem valid25 : Valid params packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((1873409:ℝ)/2560000) ((7517:ℝ)/10240),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((7517:ℚ)/10240),((1885091:ℚ)/2560000),((640576081:ℚ)/2000000000),((290957009:ℚ)/1000000000)⟩
theorem valid26 : Valid params packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((7517:ℝ)/10240) ((1885091:ℝ)/2560000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((1885091:ℚ)/2560000),((472733:ℚ)/640000),((12894321:ℚ)/40000000),((560603989:ℚ)/2000000000)⟩
theorem valid27 : Valid params packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((1885091:ℝ)/2560000) ((472733:ℝ)/640000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((472733:ℚ)/640000),((951307:ℚ)/1280000),((163178447:ℚ)/500000000),((21538971:ℚ)/80000000)⟩
theorem valid28 : Valid params packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((472733:ℝ)/640000) ((951307:ℝ)/1280000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((951307:ℚ)/1280000),((239287:ℚ)/320000),((660350441:ℚ)/2000000000),((1228271499:ℚ)/5000000000)⟩
theorem valid29 : Valid params packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((951307:ℝ)/1280000) ((239287:ℝ)/320000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((239287:ℚ)/320000),((96883:ℚ)/128000),((13175911:ℚ)/39062500),((2196088729:ℚ)/10000000000)⟩
theorem valid30 : Valid params packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((239287:ℝ)/320000) ((96883:ℝ)/128000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((96883:ℚ)/128000),((30641:ℚ)/40000),((3438020711:ℚ)/10000000000),((155130569:ℚ)/1000000000)⟩
theorem valid31 : Valid params packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((96883:ℝ)/128000) ((30641:ℝ)/40000),
    model params r < (cap params:ℝ) := by
  intro r hr
  exact packet_bound params params_valid packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((215923:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((215923:ℝ)/320000) ((55441:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((55441:ℝ)/80000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((55441:ℝ)/80000) ((449369:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((449369:ℝ)/640000) ((1814999:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((55441:ℝ)/80000) ((1814999:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1814999:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((1814999:ℝ)/2560000) ((1826681:ℝ)/2560000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((1826681:ℝ)/2560000) ((734177:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((1814999:ℝ)/2560000) ((734177:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((734177:ℝ)/1024000) ((3682567:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((3682567:ℝ)/5120000) ((3694249:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((734177:ℝ)/1024000) ((3694249:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((1814999:ℝ)/2560000) ((3694249:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((3694249:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((3694249:ℝ)/5120000) ((3705931:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((3705931:ℝ)/5120000) ((3717613:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((3694249:ℝ)/5120000) ((3717613:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((3717613:ℝ)/5120000) ((745859:ℝ)/1024000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((745859:ℝ)/1024000) ((3740977:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((3717613:ℝ)/5120000) ((3740977:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((3694249:ℝ)/5120000) ((3740977:ℝ)/5120000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((3740977:ℝ)/5120000) ((7517:ℝ)/10240),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((7517:ℝ)/10240) ((472733:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((3740977:ℝ)/5120000) ((472733:ℝ)/640000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((472733:ℝ)/640000) ((239287:ℝ)/320000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((239287:ℝ)/320000) ((30641:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((472733:ℝ)/640000) ((30641:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((3740977:ℝ)/5120000) ((30641:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((3694249:ℝ)/5120000) ((30641:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((30641:ℝ)/40000),
      model params r < (cap params:ℝ) :=
  C450FirstRadialKernel.interval_join node0_16 node16_32
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish params:ℝ),
    model params r < (cap params:ℝ) := by
  have hh := node0_32
  norm_num [finish,params] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model params r < (cap params:ℝ) :=
  closed_of_near params params_valid near_bound
end N11Formalization.C450SixthRadialC41
#check @N11Formalization.C450SixthRadialC41.bound
#print axioms N11Formalization.C450SixthRadialC41.params_valid
#print axioms N11Formalization.C450SixthRadialC41.params_sum
#print axioms N11Formalization.C450SixthRadialC41.bound
