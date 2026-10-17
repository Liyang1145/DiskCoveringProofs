import N11Formalization.C450FirstRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstRadialG02
open C450FirstRadialKernel
def packet0 : Packet := ⟨((319:ℚ)/500),((817:ℚ)/1280),((729409987:ℚ)/5000000000),((1168193477:ℚ)/2000000000)⟩
theorem valid0 : Valid packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((319:ℝ)/500) ((817:ℝ)/1280), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((817:ℚ)/1280),((10217:ℚ)/16000),((1469415409:ℚ)/10000000000),((116685063:ℚ)/200000000)⟩
theorem valid1 : Valid packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((817:ℝ)/1280) ((10217:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((10217:ℚ)/16000),((20443:ℚ)/32000),((295983581:ℚ)/2000000000),((5827532079:ℚ)/10000000000)⟩
theorem valid2 : Valid packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((10217:ℝ)/16000) ((20443:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((20443:ℚ)/32000),((5113:ℚ)/8000),((745164723:ℚ)/5000000000),((5820804147:ℚ)/10000000000)⟩
theorem valid3 : Valid packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((20443:ℝ)/32000) ((5113:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((5113:ℚ)/8000),((20461:ℚ)/32000),((1500651947:ℚ)/10000000000),((581406933:ℚ)/1000000000)⟩
theorem valid4 : Valid packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((5113:ℝ)/8000) ((20461:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((20461:ℚ)/32000),((2047:ℚ)/3200),((377721813:ℚ)/2500000000),((1451831901:ℚ)/2500000000)⟩
theorem valid5 : Valid packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((20461:ℝ)/32000) ((2047:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((2047:ℚ)/3200),((20479:ℚ)/32000),((1521037141:ℚ)/10000000000),((1160115789:ℚ)/2000000000)⟩
theorem valid6 : Valid packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((2047:ℝ)/3200) ((20479:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((20479:ℚ)/32000),((2561:ℚ)/4000),((1531103333:ℚ)/10000000000),((5793823329:ℚ)/10000000000)⟩
theorem valid7 : Valid packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((20479:ℝ)/32000) ((2561:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2561:ℚ)/4000),((20497:ℚ)/32000),((6019873:ℚ)/39062500),((5787060729:ℚ)/10000000000)⟩
theorem valid8 : Valid packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2561:ℝ)/4000) ((20497:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((20497:ℚ)/32000),((10253:ℚ)/16000),((1550991209:ℚ)/10000000000),((5780291123:ℚ)/10000000000)⟩
theorem valid9 : Valid packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((20497:ℝ)/32000) ((10253:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((10253:ℚ)/16000),((4103:ℚ)/6400),((1560816047:ℚ)/10000000000),((1443378621:ℚ)/2500000000)⟩
theorem valid10 : Valid packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((10253:ℝ)/16000) ((4103:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((4103:ℚ)/6400),((5131:ℚ)/8000),((1570563501:ℚ)/10000000000),((1441682697:ℚ)/2500000000)⟩
theorem valid11 : Valid packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((4103:ℝ)/6400) ((5131:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((5131:ℚ)/8000),((20533:ℚ)/32000),((1580235023:ℚ)/10000000000),((5759940009:ℚ)/10000000000)⟩
theorem valid12 : Valid packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((5131:ℝ)/8000) ((20533:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((20533:ℚ)/32000),((10271:ℚ)/16000),((1589832017:ℚ)/10000000000),((5753142123:ℚ)/10000000000)⟩
theorem valid13 : Valid packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((20533:ℝ)/32000) ((10271:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((10271:ℚ)/16000),((20551:ℚ)/32000),((399838961:ℚ)/2500000000),((2873168551:ℚ)/5000000000)⟩
theorem valid14 : Valid packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((10271:ℝ)/16000) ((20551:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((20551:ℚ)/32000),((257:ℚ)/400),((1608807821:ℚ)/10000000000),((5739524923:ℚ)/10000000000)⟩
theorem valid15 : Valid packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((20551:ℝ)/32000) ((257:ℝ)/400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((257:ℚ)/400),((20569:ℚ)/32000),((809094613:ℚ)/5000000000),((5732705559:ℚ)/10000000000)⟩
theorem valid16 : Valid packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((257:ℝ)/400) ((20569:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((20569:ℚ)/32000),((10289:ℚ)/16000),((813750649:ℚ)/5000000000),((715734873:ℚ)/1250000000)⟩
theorem valid17 : Valid packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((20569:ℝ)/32000) ((10289:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((10289:ℚ)/16000),((20587:ℚ)/32000),((818372619:ℚ)/5000000000),((1429761293:ℚ)/2500000000)⟩
theorem valid18 : Valid packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((10289:ℝ)/16000) ((20587:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((20587:ℚ)/32000),((5149:ℚ)/8000),((411480553:ℚ)/2500000000),((5712204097:ℚ)/10000000000)⟩
theorem valid19 : Valid packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((20587:ℝ)/32000) ((5149:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((5149:ℚ)/8000),((4121:ℚ)/6400),((1655033353:ℚ)/10000000000),((1426338933:ℚ)/2500000000)⟩
theorem valid20 : Valid packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((5149:ℝ)/8000) ((4121:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((4121:ℚ)/6400),((10307:ℚ)/16000),((1664079759:ℚ)/10000000000),((5698500051:ℚ)/10000000000)⟩
theorem valid21 : Valid packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((4121:ℝ)/6400) ((10307:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((10307:ℚ)/16000),((20623:ℚ)/32000),((836531249:ℚ)/5000000000),((5691637027:ℚ)/10000000000)⟩
theorem valid22 : Valid packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((10307:ℝ)/16000) ((20623:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((20623:ℚ)/32000),((2579:ℚ)/4000),((105123913:ℚ)/625000000),((710595829:ℚ)/1250000000)⟩
theorem valid23 : Valid packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((20623:ℝ)/32000) ((2579:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((2579:ℚ)/4000),((20641:ℚ)/32000),((1690841097:ℚ)/10000000000),((5677888841:ℚ)/10000000000)⟩
theorem valid24 : Valid packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((2579:ℝ)/4000) ((20641:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((20641:ℚ)/32000),((413:ℚ)/640),((1699638947:ℚ)/10000000000),((2835501813:ℚ)/5000000000)⟩
theorem valid25 : Valid packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((20641:ℝ)/32000) ((413:ℝ)/640), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((413:ℚ)/640),((20659:ℚ)/32000),((170837711:ℚ)/1000000000),((70801387:ℚ)/125000000)⟩
theorem valid26 : Valid packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((413:ℝ)/640) ((20659:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((20659:ℚ)/32000),((5167:ℚ)/8000),((1717056517:ℚ)/10000000000),((2828605407:ℚ)/5000000000)⟩
theorem valid27 : Valid packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((20659:ℝ)/32000) ((5167:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((5167:ℚ)/8000),((20677:ℚ)/32000),((172567807:ℚ)/1000000000),((2825151581:ℚ)/5000000000)⟩
theorem valid28 : Valid packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((5167:ℝ)/8000) ((20677:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((20677:ℚ)/32000),((10343:ℚ)/16000),((1734242649:ℚ)/10000000000),((225735519:ℚ)/400000000)⟩
theorem valid29 : Valid packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((20677:ℝ)/32000) ((10343:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((10343:ℚ)/16000),((4139:ℚ)/6400),((1742751111:ℚ)/10000000000),((225458609:ℚ)/400000000)⟩
theorem valid30 : Valid packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((10343:ℝ)/16000) ((4139:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((4139:ℚ)/6400),((647:ℚ)/1000),((175120429:ℚ)/1000000000),((1407383721:ℚ)/2500000000)⟩
theorem valid31 : Valid packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((4139:ℝ)/6400) ((647:ℝ)/1000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((647:ℚ)/1000),((20713:ℚ)/32000),((1759603:ℚ)/10000000),((224903877:ℚ)/400000000)⟩
theorem valid32 : Valid packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((647:ℝ)/1000) ((20713:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((20713:ℚ)/32000),((10361:ℚ)/16000),((1767948033:ℚ)/10000000000),((2807825659:ℚ)/5000000000)⟩
theorem valid33 : Valid packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((20713:ℝ)/32000) ((10361:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((10361:ℚ)/16000),((20731:ℚ)/32000),((888120081:ℚ)/5000000000),((2804349017:ℚ)/5000000000)⟩
theorem valid34 : Valid packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((10361:ℝ)/16000) ((20731:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((20731:ℚ)/32000),((1037:ℚ)/1600),((892240071:ℚ)/5000000000),((1120347409:ℚ)/2000000000)⟩
theorem valid35 : Valid packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((20731:ℝ)/32000) ((1037:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((1037:ℚ)/1600),((20749:ℚ)/32000),((1792668707:ℚ)/10000000000),((5594768321:ℚ)/10000000000)⟩
theorem valid36 : Valid packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((1037:ℝ)/1600) ((20749:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((20749:ℚ)/32000),((10379:ℚ)/16000),((900403287:ℚ)/5000000000),((2793895917:ℚ)/5000000000)⟩
theorem valid37 : Valid packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((20749:ℝ)/32000) ((10379:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((10379:ℚ)/16000),((20767:ℚ)/32000),((361778889:ℚ)/2000000000),((2790403777:ℚ)/5000000000)⟩
theorem valid38 : Valid packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((10379:ℝ)/16000) ((20767:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((20767:ℚ)/32000),((2597:ℚ)/4000),((908466501:ℚ)/5000000000),((1393453863:ℚ)/2500000000)⟩
theorem valid39 : Valid packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((20767:ℝ)/32000) ((2597:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((2597:ℚ)/4000),((4157:ℚ)/6400),((1824922913:ℚ)/10000000000),((5566815497:ℚ)/10000000000)⟩
theorem valid40 : Valid packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((2597:ℝ)/4000) ((4157:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((4157:ℚ)/6400),((10397:ℚ)/16000),((183286483:ℚ)/1000000000),((5559807659:ℚ)/10000000000)⟩
theorem valid41 : Valid packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((4157:ℝ)/6400) ((10397:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((10397:ℚ)/16000),((20803:ℚ)/32000),((184075939:ℚ)/1000000000),((555279191:ℚ)/1000000000)⟩
theorem valid42 : Valid packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((10397:ℝ)/16000) ((20803:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((20803:ℚ)/32000),((5203:ℚ)/8000),((369721443:ℚ)/2000000000),((5545768217:ℚ)/10000000000)⟩
theorem valid43 : Valid packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((20803:ℝ)/32000) ((5203:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((5203:ℚ)/8000),((20821:ℚ)/32000),((116025557:ℚ)/625000000),((5538736551:ℚ)/10000000000)⟩
theorem valid44 : Valid packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((5203:ℝ)/8000) ((20821:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((20821:ℚ)/32000),((2083:ℚ)/3200),((1864165077:ℚ)/10000000000),((5531696881:ℚ)/10000000000)⟩
theorem valid45 : Valid packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((20821:ℝ)/32000) ((2083:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet46 : Packet := ⟨((2083:ℚ)/3200),((20839:ℚ)/32000),((1871876291:ℚ)/10000000000),((690581147:ℚ)/1250000000)⟩
theorem valid46 : Valid packet46 := by
  constructor <;> decide +kernel
private theorem leaf46 : ∀ r ∈ Set.Icc ((2083:ℝ)/3200) ((20839:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet46 valid46 r
    (by simpa only [packet46,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet47 : Packet := ⟨((20839:ℚ)/32000),((1303:ℚ)/2000),((1879543121:ℚ)/10000000000),((2758796703:ℚ)/5000000000)⟩
theorem valid47 : Valid packet47 := by
  constructor <;> decide +kernel
private theorem leaf47 : ∀ r ∈ Set.Icc ((20839:ℝ)/32000) ((1303:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet47 valid47 r
    (by simpa only [packet47,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet48 : Packet := ⟨((1303:ℚ)/2000),((20857:ℚ)/32000),((15097329:ℚ)/80000000),((2755264769:ℚ)/5000000000)⟩
theorem valid48 : Valid packet48 := by
  constructor <;> decide +kernel
private theorem leaf48 : ∀ r ∈ Set.Icc ((1303:ℝ)/2000) ((20857:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet48 valid48 r
    (by simpa only [packet48,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet49 : Packet := ⟨((20857:ℚ)/32000),((10433:ℚ)/16000),((947372923:ℚ)/5000000000),((5503457541:ℚ)/10000000000)⟩
theorem valid49 : Valid packet49 := by
  constructor <;> decide +kernel
private theorem leaf49 : ∀ r ∈ Set.Icc ((20857:ℝ)/32000) ((10433:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet49 valid49 r
    (by simpa only [packet49,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet50 : Packet := ⟨((10433:ℚ)/16000),((167:ℚ)/256),((1902282817:ℚ)/10000000000),((5496377383:ℚ)/10000000000)⟩
theorem valid50 : Valid packet50 := by
  constructor <;> decide +kernel
private theorem leaf50 : ∀ r ∈ Set.Icc ((10433:ℝ)/16000) ((167:ℝ)/256), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet50 valid50 r
    (by simpa only [packet50,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet51 : Packet := ⟨((167:ℚ)/256),((5221:ℚ)/8000),((1909777557:ℚ)/10000000000),((2744644517:ℚ)/5000000000)⟩
theorem valid51 : Valid packet51 := by
  constructor <;> decide +kernel
private theorem leaf51 : ∀ r ∈ Set.Icc ((167:ℝ)/256) ((5221:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet51 valid51 r
    (by simpa only [packet51,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet52 : Packet := ⟨((5221:ℚ)/8000),((20893:ℚ)/32000),((958615289:ℚ)/5000000000),((274109623:ℚ)/500000000)⟩
theorem valid52 : Valid packet52 := by
  constructor <;> decide +kernel
private theorem leaf52 : ∀ r ∈ Set.Icc ((5221:ℝ)/8000) ((20893:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet52 valid52 r
    (by simpa only [packet52,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet53 : Packet := ⟨((20893:ℚ)/32000),((10451:ℚ)/16000),((1924642379:ℚ)/10000000000),((5475087629:ℚ)/10000000000)⟩
theorem valid53 : Valid packet53 := by
  constructor <;> decide +kernel
private theorem leaf53 : ∀ r ∈ Set.Icc ((20893:ℝ)/32000) ((10451:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet53 valid53 r
    (by simpa only [packet53,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet54 : Packet := ⟨((10451:ℚ)/16000),((20911:ℚ)/32000),((241501681:ℚ)/1250000000),((5467974509:ℚ)/10000000000)⟩
theorem valid54 : Valid packet54 := by
  constructor <;> decide +kernel
private theorem leaf54 : ∀ r ∈ Set.Icc ((10451:ℝ)/16000) ((20911:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet54 valid54 r
    (by simpa only [packet54,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet55 : Packet := ⟨((20911:ℚ)/32000),((523:ℚ)/800),((387868853:ℚ)/2000000000),((1365213267:ℚ)/2500000000)⟩
theorem valid55 : Valid packet55 := by
  constructor <;> decide +kernel
private theorem leaf55 : ∀ r ∈ Set.Icc ((20911:ℝ)/32000) ((523:ℝ)/800), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet55 valid55 r
    (by simpa only [packet55,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet56 : Packet := ⟨((523:ℚ)/800),((20929:ℚ)/32000),((973317649:ℚ)/5000000000),((5453723271:ℚ)/10000000000)⟩
theorem valid56 : Valid packet56 := by
  constructor <;> decide +kernel
private theorem leaf56 : ∀ r ∈ Set.Icc ((523:ℝ)/800) ((20929:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet56 valid56 r
    (by simpa only [packet56,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet57 : Packet := ⟨((20929:ℚ)/32000),((10469:ℚ)/16000),((61058969:ℚ)/312500000),((5446585087:ℚ)/10000000000)⟩
theorem valid57 : Valid packet57 := by
  constructor <;> decide +kernel
private theorem leaf57 : ∀ r ∈ Set.Icc ((20929:ℝ)/32000) ((10469:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet57 valid57 r
    (by simpa only [packet57,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet58 : Packet := ⟨((10469:ℚ)/16000),((20947:ℚ)/32000),((392219969:ℚ)/2000000000),((5439438481:ℚ)/10000000000)⟩
theorem valid58 : Valid packet58 := by
  constructor <;> decide +kernel
private theorem leaf58 : ∀ r ∈ Set.Icc ((10469:ℝ)/16000) ((20947:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet58 valid58 r
    (by simpa only [packet58,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet59 : Packet := ⟨((20947:ℚ)/32000),((5239:ℚ)/8000),((1968274251:ℚ)/10000000000),((5432283421:ℚ)/10000000000)⟩
theorem valid59 : Valid packet59 := by
  constructor <;> decide +kernel
private theorem leaf59 : ∀ r ∈ Set.Icc ((20947:ℝ)/32000) ((5239:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet59 valid59 r
    (by simpa only [packet59,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet60 : Packet := ⟨((5239:ℚ)/8000),((4193:ℚ)/6400),((987705329:ℚ)/5000000000),((5425119873:ℚ)/10000000000)⟩
theorem valid60 : Valid packet60 := by
  constructor <;> decide +kernel
private theorem leaf60 : ∀ r ∈ Set.Icc ((5239:ℝ)/8000) ((4193:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet60 valid60 r
    (by simpa only [packet60,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet61 : Packet := ⟨((4193:ℚ)/6400),((10487:ℚ)/16000),((1982509491:ℚ)/10000000000),((2708973901:ℚ)/5000000000)⟩
theorem valid61 : Valid packet61 := by
  constructor <;> decide +kernel
private theorem leaf61 : ∀ r ∈ Set.Icc ((4193:ℝ)/6400) ((10487:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet61 valid61 r
    (by simpa only [packet61,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet62 : Packet := ⟨((10487:ℚ)/16000),((20983:ℚ)/32000),((994785583:ℚ)/5000000000),((2705383587:ℚ)/5000000000)⟩
theorem valid62 : Valid packet62 := by
  constructor <;> decide +kernel
private theorem leaf62 : ∀ r ∈ Set.Icc ((10487:ℝ)/16000) ((20983:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet62 valid62 r
    (by simpa only [packet62,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet63 : Packet := ⟨((20983:ℚ)/32000),((82:ℚ)/125),((1996596091:ℚ)/10000000000),((1080715591:ℚ)/2000000000)⟩
theorem valid63 : Valid packet63 := by
  constructor <;> decide +kernel
private theorem leaf63 : ∀ r ∈ Set.Icc ((20983:ℝ)/32000) ((82:ℝ)/125), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet63 valid63 r
    (by simpa only [packet63,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((319:ℝ)/500) ((10217:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((10217:ℝ)/16000) ((5113:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((319:ℝ)/500) ((5113:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((5113:ℝ)/8000) ((2047:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((2047:ℝ)/3200) ((2561:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((5113:ℝ)/8000) ((2561:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((319:ℝ)/500) ((2561:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((2561:ℝ)/4000) ((10253:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((10253:ℝ)/16000) ((5131:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((2561:ℝ)/4000) ((5131:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((5131:ℝ)/8000) ((10271:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((10271:ℝ)/16000) ((257:ℝ)/400), model r < (cap:ℝ) :=
  interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((5131:ℝ)/8000) ((257:ℝ)/400), model r < (cap:ℝ) :=
  interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((2561:ℝ)/4000) ((257:ℝ)/400), model r < (cap:ℝ) :=
  interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((319:ℝ)/500) ((257:ℝ)/400), model r < (cap:ℝ) :=
  interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((257:ℝ)/400) ((10289:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((10289:ℝ)/16000) ((5149:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((257:ℝ)/400) ((5149:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((5149:ℝ)/8000) ((10307:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((10307:ℝ)/16000) ((2579:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((5149:ℝ)/8000) ((2579:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((257:ℝ)/400) ((2579:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((2579:ℝ)/4000) ((413:ℝ)/640), model r < (cap:ℝ) :=
  interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((413:ℝ)/640) ((5167:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((2579:ℝ)/4000) ((5167:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((5167:ℝ)/8000) ((10343:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((10343:ℝ)/16000) ((647:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((5167:ℝ)/8000) ((647:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((2579:ℝ)/4000) ((647:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((257:ℝ)/400) ((647:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((319:ℝ)/500) ((647:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node0_16 node16_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((647:ℝ)/1000) ((10361:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf32 leaf33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((10361:ℝ)/16000) ((1037:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf34 leaf35
private theorem node32_36 :
    ∀ r ∈ Set.Icc ((647:ℝ)/1000) ((1037:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node32_34 node34_36
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((1037:ℝ)/1600) ((10379:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf36 leaf37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((10379:ℝ)/16000) ((2597:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf38 leaf39
private theorem node36_40 :
    ∀ r ∈ Set.Icc ((1037:ℝ)/1600) ((2597:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node36_38 node38_40
private theorem node32_40 :
    ∀ r ∈ Set.Icc ((647:ℝ)/1000) ((2597:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node32_36 node36_40
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((2597:ℝ)/4000) ((10397:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf40 leaf41
private theorem node42_44 :
    ∀ r ∈ Set.Icc ((10397:ℝ)/16000) ((5203:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf42 leaf43
private theorem node40_44 :
    ∀ r ∈ Set.Icc ((2597:ℝ)/4000) ((5203:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node40_42 node42_44
private theorem node44_46 :
    ∀ r ∈ Set.Icc ((5203:ℝ)/8000) ((2083:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf44 leaf45
private theorem node46_48 :
    ∀ r ∈ Set.Icc ((2083:ℝ)/3200) ((1303:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf46 leaf47
private theorem node44_48 :
    ∀ r ∈ Set.Icc ((5203:ℝ)/8000) ((1303:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node44_46 node46_48
private theorem node40_48 :
    ∀ r ∈ Set.Icc ((2597:ℝ)/4000) ((1303:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node40_44 node44_48
private theorem node32_48 :
    ∀ r ∈ Set.Icc ((647:ℝ)/1000) ((1303:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node32_40 node40_48
private theorem node48_50 :
    ∀ r ∈ Set.Icc ((1303:ℝ)/2000) ((10433:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf48 leaf49
private theorem node50_52 :
    ∀ r ∈ Set.Icc ((10433:ℝ)/16000) ((5221:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf50 leaf51
private theorem node48_52 :
    ∀ r ∈ Set.Icc ((1303:ℝ)/2000) ((5221:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node48_50 node50_52
private theorem node52_54 :
    ∀ r ∈ Set.Icc ((5221:ℝ)/8000) ((10451:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf52 leaf53
private theorem node54_56 :
    ∀ r ∈ Set.Icc ((10451:ℝ)/16000) ((523:ℝ)/800), model r < (cap:ℝ) :=
  interval_join leaf54 leaf55
private theorem node52_56 :
    ∀ r ∈ Set.Icc ((5221:ℝ)/8000) ((523:ℝ)/800), model r < (cap:ℝ) :=
  interval_join node52_54 node54_56
private theorem node48_56 :
    ∀ r ∈ Set.Icc ((1303:ℝ)/2000) ((523:ℝ)/800), model r < (cap:ℝ) :=
  interval_join node48_52 node52_56
private theorem node56_58 :
    ∀ r ∈ Set.Icc ((523:ℝ)/800) ((10469:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf56 leaf57
private theorem node58_60 :
    ∀ r ∈ Set.Icc ((10469:ℝ)/16000) ((5239:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf58 leaf59
private theorem node56_60 :
    ∀ r ∈ Set.Icc ((523:ℝ)/800) ((5239:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node56_58 node58_60
private theorem node60_62 :
    ∀ r ∈ Set.Icc ((5239:ℝ)/8000) ((10487:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf60 leaf61
private theorem node62_64 :
    ∀ r ∈ Set.Icc ((10487:ℝ)/16000) ((82:ℝ)/125), model r < (cap:ℝ) :=
  interval_join leaf62 leaf63
private theorem node60_64 :
    ∀ r ∈ Set.Icc ((5239:ℝ)/8000) ((82:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node60_62 node62_64
private theorem node56_64 :
    ∀ r ∈ Set.Icc ((523:ℝ)/800) ((82:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node56_60 node60_64
private theorem node48_64 :
    ∀ r ∈ Set.Icc ((1303:ℝ)/2000) ((82:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node48_56 node56_64
private theorem node32_64 :
    ∀ r ∈ Set.Icc ((647:ℝ)/1000) ((82:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node32_48 node48_64
private theorem node0_64 :
    ∀ r ∈ Set.Icc ((319:ℝ)/500) ((82:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node0_32 node32_64
theorem bound : ∀ r ∈ Set.Icc ((319:ℝ)/500) ((82:ℝ)/125), model r < (cap:ℝ) := node0_64
end N11Formalization.C450FirstRadialG02
#check @N11Formalization.C450FirstRadialG02.bound
#print axioms N11Formalization.C450FirstRadialG02.bound
