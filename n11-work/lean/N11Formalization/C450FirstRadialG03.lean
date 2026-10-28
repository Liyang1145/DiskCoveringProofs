import N11Formalization.C450FirstRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstRadialG03
open C450FirstRadialKernel
def packet0 : Packet := ⟨((82:ℚ)/125),((21001:ℚ)/32000),((2003584667:ℚ)/10000000000),((539638011:ℚ)/1000000000)⟩
theorem valid0 : Valid packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((82:ℝ)/125) ((21001:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((21001:ℚ)/32000),((2101:ℚ)/3200),((1005268643:ℚ)/5000000000),((1077834721:ℚ)/2000000000)⟩
theorem valid1 : Valid packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((21001:ℝ)/32000) ((2101:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((2101:ℚ)/3200),((21019:ℚ)/32000),((1008727167:ℚ)/5000000000),((1076391681:ℚ)/2000000000)⟩
theorem valid2 : Valid packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((2101:ℝ)/3200) ((21019:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((21019:ℚ)/32000),((5257:ℚ)/8000),((202433619:ℚ)/1000000000),((5374734473:ℚ)/10000000000)⟩
theorem valid3 : Valid packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((21019:ℝ)/32000) ((5257:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((5257:ℚ)/8000),((21037:ℚ)/32000),((2031183223:ℚ)/10000000000),((214700071:ℚ)/400000000)⟩
theorem valid4 : Valid packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((5257:ℝ)/8000) ((21037:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((21037:ℚ)/32000),((10523:ℚ)/16000),((10189979:ℚ)/50000000),((2680130137:ℚ)/5000000000)⟩
theorem valid5 : Valid packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((21037:ℝ)/32000) ((10523:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((10523:ℚ)/16000),((4211:ℚ)/6400),((1022387139:ℚ)/5000000000),((1070601987:ℚ)/2000000000)⟩
theorem valid6 : Valid packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((10523:ℝ)/16000) ((4211:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((4211:ℚ)/6400),((2633:ℚ)/4000),((2051519007:ℚ)/10000000000),((2672875361:ℚ)/5000000000)⟩
theorem valid7 : Valid packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((4211:ℝ)/6400) ((2633:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2633:ℚ)/4000),((21073:ℚ)/32000),((1029115167:ℚ)/5000000000),((5338482597:ℚ)/10000000000)⟩
theorem valid8 : Valid packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2633:ℝ)/4000) ((21073:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((21073:ℚ)/32000),((10541:ℚ)/16000),((1032454299:ℚ)/5000000000),((213248221:ℚ)/400000000)⟩
theorem valid9 : Valid packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((21073:ℝ)/32000) ((10541:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((10541:ℚ)/16000),((21091:ℚ)/32000),((207155413:ℚ)/1000000000),((5323919467:ℚ)/10000000000)⟩
theorem valid10 : Valid packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((10541:ℝ)/16000) ((21091:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((21091:ℚ)/32000),((211:ℚ)/320),((2078167259:ℚ)/10000000000),((1329156097:ℚ)/2500000000)⟩
theorem valid11 : Valid packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((21091:ℝ)/32000) ((211:ℝ)/320), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((211:ℚ)/320),((21109:ℚ)/32000),((1042374153:ℚ)/5000000000),((5309320249:ℚ)/10000000000)⟩
theorem valid12 : Valid packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((211:ℝ)/320) ((21109:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((21109:ℚ)/32000),((10559:ℚ)/16000),((1045648793:ℚ)/5000000000),((1325501753:ℚ)/2500000000)⟩
theorem valid13 : Valid packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((21109:ℝ)/32000) ((10559:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((10559:ℚ)/16000),((21127:ℚ)/32000),((209781541:ℚ)/1000000000),((33091779:ℚ)/62500000)⟩
theorem valid14 : Valid packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((10559:ℝ)/16000) ((21127:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((21127:ℚ)/32000),((1321:ℚ)/2000),((526075521:ℚ)/2500000000),((1057470619:ℚ)/2000000000)⟩
theorem valid15 : Valid packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((21127:ℝ)/32000) ((1321:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((1321:ℚ)/2000),((4229:ℚ)/6400),((2110757907:ℚ)/10000000000),((5280012337:ℚ)/10000000000)⟩
theorem valid16 : Valid packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((1321:ℝ)/2000) ((4229:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((4229:ℚ)/6400),((10577:ℚ)/16000),((1058591587:ℚ)/5000000000),((5272662329:ℚ)/10000000000)⟩
theorem valid17 : Valid packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((4229:ℝ)/6400) ((10577:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((10577:ℚ)/16000),((21163:ℚ)/32000),((33180909:ℚ)/156250000),((526530303:ℚ)/1000000000)⟩
theorem valid18 : Valid packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((10577:ℝ)/16000) ((21163:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((21163:ℚ)/32000),((5293:ℚ)/8000),((2129943197:ℚ)/10000000000),((2628967201:ℚ)/5000000000)⟩
theorem valid19 : Valid packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((21163:ℝ)/32000) ((5293:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((5293:ℚ)/8000),((21181:ℚ)/32000),((2136278519:ℚ)/10000000000),((2625278203:ℚ)/5000000000)⟩
theorem valid20 : Valid packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((5293:ℝ)/8000) ((21181:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((21181:ℚ)/32000),((2119:ℚ)/3200),((2142584417:ℚ)/10000000000),((5243169:ℚ)/10000000)⟩
theorem valid21 : Valid packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((21181:ℝ)/32000) ((2119:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((2119:ℚ)/3200),((21199:ℚ)/32000),((1074430581:ℚ)/5000000000),((2617886073:ℚ)/5000000000)⟩
theorem valid22 : Valid packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((2119:ℝ)/3200) ((21199:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((21199:ℚ)/32000),((2651:ℚ)/4000),((2155109023:ℚ)/10000000000),((2614182901:ℚ)/5000000000)⟩
theorem valid23 : Valid packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((21199:ℝ)/32000) ((2651:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((2651:ℚ)/4000),((21217:ℚ)/32000),((2161328261:ℚ)/10000000000),((5220949929:ℚ)/10000000000)⟩
theorem valid24 : Valid packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((2651:ℝ)/4000) ((21217:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((21217:ℚ)/32000),((10613:ℚ)/16000),((67734973:ℚ)/312500000),((1303381121:ℚ)/2500000000)⟩
theorem valid25 : Valid packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((21217:ℝ)/32000) ((10613:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((10613:ℚ)/16000),((4247:ℚ)/6400),((1086840951:ℚ)/5000000000),((5206089427:ℚ)/10000000000)⟩
theorem valid26 : Valid packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((10613:ℝ)/16000) ((4247:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((4247:ℚ)/6400),((5311:ℚ)/8000),((217981681:ℚ)/1000000000),((5198644717:ℚ)/10000000000)⟩
theorem valid27 : Valid packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((4247:ℝ)/6400) ((5311:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((5311:ℚ)/8000),((21253:ℚ)/32000),((1092962053:ℚ)/5000000000),((5191190311:ℚ)/10000000000)⟩
theorem valid28 : Valid packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((5311:ℝ)/8000) ((21253:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((21253:ℚ)/32000),((10631:ℚ)/16000),((2192004033:ℚ)/10000000000),((5183726167:ℚ)/10000000000)⟩
theorem valid29 : Valid packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((21253:ℝ)/32000) ((10631:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((10631:ℚ)/16000),((21271:ℚ)/32000),((2198056831:ℚ)/10000000000),((5176252243:ℚ)/10000000000)⟩
theorem valid30 : Valid packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((10631:ℝ)/16000) ((21271:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((21271:ℚ)/32000),((133:ℚ)/200),((440816547:ℚ)/2000000000),((323048031:ℚ)/625000000)⟩
theorem valid31 : Valid packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((21271:ℝ)/32000) ((133:ℝ)/200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((133:ℚ)/200),((21289:ℚ)/32000),((2210081977:ℚ)/10000000000),((5161274883:ℚ)/10000000000)⟩
theorem valid32 : Valid packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((133:ℝ)/200) ((21289:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((21289:ℚ)/32000),((10649:ℚ)/16000),((1108027393:ℚ)/5000000000),((32211071:ℚ)/62500000)⟩
theorem valid33 : Valid packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((21289:ℝ)/32000) ((10649:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((10649:ℚ)/16000),((21307:ℚ)/32000),((1111000693:ℚ)/5000000000),((1029251577:ℚ)/2000000000)⟩
theorem valid34 : Valid packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((10649:ℝ)/16000) ((21307:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((21307:ℚ)/32000),((5329:ℚ)/8000),((2227921999:ℚ)/10000000000),((5138734413:ℚ)/10000000000)⟩
theorem valid35 : Valid packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((21307:ℝ)/32000) ((5329:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((5329:ℚ)/8000),((853:ℚ)/1280),((558454211:ℚ)/2500000000),((5131200899:ℚ)/10000000000)⟩
theorem valid36 : Valid packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((5329:ℝ)/8000) ((853:ℝ)/1280), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((853:ℚ)/1280),((10667:ℚ)/16000),((447937227:ℚ)/2000000000),((51236573:ℚ)/100000000)⟩
theorem valid37 : Valid packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((853:ℝ)/1280) ((10667:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((10667:ℚ)/16000),((21343:ℚ)/32000),((449106017:ℚ)/2000000000),((511610357:ℚ)/1000000000)⟩
theorem valid38 : Valid packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((10667:ℝ)/16000) ((21343:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((21343:ℚ)/32000),((2669:ℚ)/4000),((2251348903:ℚ)/10000000000),((319283729:ℚ)/625000000)⟩
theorem valid39 : Valid packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((21343:ℝ)/32000) ((2669:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((2669:ℚ)/4000),((21361:ℚ)/32000),((451428559:ℚ)/2000000000),((159405173:ℚ)/312500000)⟩
theorem valid40 : Valid packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((2669:ℝ)/4000) ((21361:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((21361:ℚ)/32000),((2137:ℚ)/3200),((2262911963:ℚ)/10000000000),((5093381141:ℚ)/10000000000)⟩
theorem valid41 : Valid packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((21361:ℝ)/32000) ((2137:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((2137:ℚ)/3200),((21379:ℚ)/32000),((70895519:ℚ)/312500000),((79465413:ℚ)/156250000)⟩
theorem valid42 : Valid packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((2137:ℝ)/3200) ((21379:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((21379:ℚ)/32000),((5347:ℚ)/8000),((2274376927:ℚ)/10000000000),((5078181363:ℚ)/10000000000)⟩
theorem valid43 : Valid packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((21379:ℝ)/32000) ((5347:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((5347:ℚ)/8000),((21397:ℚ)/32000),((1140036557:ℚ)/5000000000),((2535282943:ℚ)/5000000000)⟩
theorem valid44 : Valid packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((5347:ℝ)/8000) ((21397:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((21397:ℚ)/32000),((10703:ℚ)/16000),((1142872681:ℚ)/5000000000),((1012587991:ℚ)/2000000000)⟩
theorem valid45 : Valid packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((21397:ℝ)/32000) ((10703:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet46 : Packet := ⟨((10703:ℚ)/16000),((4283:ℚ)/6400),((1145696929:ℚ)/5000000000),((2527651761:ℚ)/5000000000)⟩
theorem valid46 : Valid packet46 := by
  constructor <;> decide +kernel
private theorem leaf46 : ∀ r ∈ Set.Icc ((10703:ℝ)/16000) ((4283:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet46 valid46 r
    (by simpa only [packet46,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet47 : Packet := ⟨((4283:ℚ)/6400),((1339:ℚ)/2000),((2297018791:ℚ)/10000000000),((2523828269:ℚ)/5000000000)⟩
theorem valid47 : Valid packet47 := by
  constructor <;> decide +kernel
private theorem leaf47 : ∀ r ∈ Set.Icc ((4283:ℝ)/6400) ((1339:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet47 valid47 r
    (by simpa only [packet47,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet48 : Packet := ⟨((1339:ℚ)/2000),((21433:ℚ)/32000),((287827543:ℚ)/1250000000),((1259999739:ℚ)/2500000000)⟩
theorem valid48 : Valid packet48 := by
  constructor <;> decide +kernel
private theorem leaf48 : ∀ r ∈ Set.Icc ((1339:ℝ)/2000) ((21433:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet48 valid48 r
    (by simpa only [packet48,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet49 : Packet := ⟨((21433:ℚ)/32000),((10721:ℚ)/16000),((2308198697:ℚ)/10000000000),((5032330727:ℚ)/10000000000)⟩
theorem valid49 : Valid packet49 := by
  constructor <;> decide +kernel
private theorem leaf49 : ∀ r ∈ Set.Icc ((21433:ℝ)/32000) ((10721:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet49 valid49 r
    (by simpa only [packet49,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet50 : Packet := ⟨((10721:ℚ)/16000),((21451:ℚ)/32000),((231375403:ℚ)/1000000000),((5024651801:ℚ)/10000000000)⟩
theorem valid50 : Valid packet50 := by
  constructor <;> decide +kernel
private theorem leaf50 : ∀ r ∈ Set.Icc ((10721:ℝ)/16000) ((21451:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet50 valid50 r
    (by simpa only [packet50,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet51 : Packet := ⟨((21451:ℚ)/32000),((1073:ℚ)/1600),((57982163:ℚ)/250000000),((501696213:ℚ)/1000000000)⟩
theorem valid51 : Valid packet51 := by
  constructor <;> decide +kernel
private theorem leaf51 : ∀ r ∈ Set.Icc ((21451:ℝ)/32000) ((1073:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet51 valid51 r
    (by simpa only [packet51,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet52 : Packet := ⟨((1073:ℚ)/1600),((21469:ℚ)/32000),((2324796341:ℚ)/10000000000),((5009261663:ℚ)/10000000000)⟩
theorem valid52 : Valid packet52 := by
  constructor <;> decide +kernel
private theorem leaf52 : ∀ r ∈ Set.Icc ((1073:ℝ)/1600) ((21469:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet52 valid52 r
    (by simpa only [packet52,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet53 : Packet := ⟨((21469:ℚ)/32000),((10739:ℚ)/16000),((2330283663:ℚ)/10000000000),((5001550351:ℚ)/10000000000)⟩
theorem valid53 : Valid packet53 := by
  constructor <;> decide +kernel
private theorem leaf53 : ∀ r ∈ Set.Icc ((21469:ℝ)/32000) ((10739:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet53 valid53 r
    (by simpa only [packet53,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet54 : Packet := ⟨((10739:ℚ)/16000),((21487:ℚ)/32000),((1167874329:ℚ)/5000000000),((2496914071:ℚ)/5000000000)⟩
theorem valid54 : Valid packet54 := by
  constructor <;> decide +kernel
private theorem leaf54 : ∀ r ∈ Set.Icc ((10739:ℝ)/16000) ((21487:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet54 valid54 r
    (by simpa only [packet54,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet55 : Packet := ⟨((21487:ℚ)/32000),((2687:ℚ)/4000),((585297873:ℚ)/2500000000),((2493047493:ℚ)/5000000000)⟩
theorem valid55 : Valid packet55 := by
  constructor <;> decide +kernel
private theorem leaf55 : ∀ r ∈ Set.Icc ((21487:ℝ)/32000) ((2687:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet55 valid55 r
    (by simpa only [packet55,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet56 : Packet := ⟨((2687:ℚ)/4000),((4301:ℚ)/6400),((234661233:ℚ)/1000000000),((311146927:ℚ)/625000000)⟩
theorem valid56 : Valid packet56 := by
  constructor <;> decide +kernel
private theorem leaf56 : ∀ r ∈ Set.Icc ((2687:ℝ)/4000) ((4301:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet56 valid56 r
    (by simpa only [packet56,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet57 : Packet := ⟨((4301:ℚ)/6400),((10757:ℚ)/16000),((470402267:ℚ)/2000000000),((4970595627:ℚ)/10000000000)⟩
theorem valid57 : Valid packet57 := by
  constructor <;> decide +kernel
private theorem leaf57 : ∀ r ∈ Set.Icc ((4301:ℝ)/6400) ((10757:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet57 valid57 r
    (by simpa only [packet57,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet58 : Packet := ⟨((10757:ℚ)/16000),((21523:ℚ)/32000),((589347167:ℚ)/2500000000),((124070733:ℚ)/250000000)⟩
theorem valid58 : Valid packet58 := by
  constructor <;> decide +kernel
private theorem leaf58 : ∀ r ∈ Set.Icc ((10757:ℝ)/16000) ((21523:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet58 valid58 r
    (by simpa only [packet58,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet59 : Packet := ⟨((21523:ℚ)/32000),((5383:ℚ)/8000),((295343061:ℚ)/1250000000),((2477525929:ℚ)/5000000000)⟩
theorem valid59 : Valid packet59 := by
  constructor <;> decide +kernel
private theorem leaf59 : ∀ r ∈ Set.Icc ((21523:ℝ)/32000) ((5383:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet59 valid59 r
    (by simpa only [packet59,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet60 : Packet := ⟨((5383:ℚ)/8000),((21541:ℚ)/32000),((2368078951:ℚ)/10000000000),((1236815797:ℚ)/2500000000)⟩
theorem valid60 : Valid packet60 := by
  constructor <;> decide +kernel
private theorem leaf60 : ∀ r ∈ Set.Icc ((5383:ℝ)/8000) ((21541:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet60 valid60 r
    (by simpa only [packet60,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet61 : Packet := ⟨((21541:ℚ)/32000),((431:ℚ)/640),((593348053:ℚ)/2500000000),((4939463257:ℚ)/10000000000)⟩
theorem valid61 : Valid packet61 := by
  constructor <;> decide +kernel
private theorem leaf61 : ∀ r ∈ Set.Icc ((21541:ℝ)/32000) ((431:ℝ)/640), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet61 valid61 r
    (by simpa only [packet61,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet62 : Packet := ⟨((431:ℚ)/640),((21559:ℚ)/32000),((297335553:ℚ)/1250000000),((1232913003:ℚ)/2500000000)⟩
theorem valid62 : Valid packet62 := by
  constructor <;> decide +kernel
private theorem leaf62 : ∀ r ∈ Set.Icc ((431:ℝ)/640) ((21559:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet62 valid62 r
    (by simpa only [packet62,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet63 : Packet := ⟨((21559:ℚ)/32000),((337:ℚ)/500),((2383955737:ℚ)/10000000000),((4923829397:ℚ)/10000000000)⟩
theorem valid63 : Valid packet63 := by
  constructor <;> decide +kernel
private theorem leaf63 : ∀ r ∈ Set.Icc ((21559:ℝ)/32000) ((337:ℝ)/500), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet63 valid63 r
    (by simpa only [packet63,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((82:ℝ)/125) ((2101:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((2101:ℝ)/3200) ((5257:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((82:ℝ)/125) ((5257:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((5257:ℝ)/8000) ((10523:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((10523:ℝ)/16000) ((2633:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((5257:ℝ)/8000) ((2633:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((82:ℝ)/125) ((2633:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((2633:ℝ)/4000) ((10541:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((10541:ℝ)/16000) ((211:ℝ)/320), model r < (cap:ℝ) :=
  interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((2633:ℝ)/4000) ((211:ℝ)/320), model r < (cap:ℝ) :=
  interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((211:ℝ)/320) ((10559:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((10559:ℝ)/16000) ((1321:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((211:ℝ)/320) ((1321:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((2633:ℝ)/4000) ((1321:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((82:ℝ)/125) ((1321:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((1321:ℝ)/2000) ((10577:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((10577:ℝ)/16000) ((5293:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((1321:ℝ)/2000) ((5293:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((5293:ℝ)/8000) ((2119:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((2119:ℝ)/3200) ((2651:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((5293:ℝ)/8000) ((2651:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((1321:ℝ)/2000) ((2651:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((2651:ℝ)/4000) ((10613:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((10613:ℝ)/16000) ((5311:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((2651:ℝ)/4000) ((5311:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((5311:ℝ)/8000) ((10631:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((10631:ℝ)/16000) ((133:ℝ)/200), model r < (cap:ℝ) :=
  interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((5311:ℝ)/8000) ((133:ℝ)/200), model r < (cap:ℝ) :=
  interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((2651:ℝ)/4000) ((133:ℝ)/200), model r < (cap:ℝ) :=
  interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((1321:ℝ)/2000) ((133:ℝ)/200), model r < (cap:ℝ) :=
  interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((82:ℝ)/125) ((133:ℝ)/200), model r < (cap:ℝ) :=
  interval_join node0_16 node16_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((133:ℝ)/200) ((10649:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf32 leaf33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((10649:ℝ)/16000) ((5329:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf34 leaf35
private theorem node32_36 :
    ∀ r ∈ Set.Icc ((133:ℝ)/200) ((5329:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node32_34 node34_36
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((5329:ℝ)/8000) ((10667:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf36 leaf37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((10667:ℝ)/16000) ((2669:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf38 leaf39
private theorem node36_40 :
    ∀ r ∈ Set.Icc ((5329:ℝ)/8000) ((2669:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node36_38 node38_40
private theorem node32_40 :
    ∀ r ∈ Set.Icc ((133:ℝ)/200) ((2669:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node32_36 node36_40
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((2669:ℝ)/4000) ((2137:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf40 leaf41
private theorem node42_44 :
    ∀ r ∈ Set.Icc ((2137:ℝ)/3200) ((5347:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf42 leaf43
private theorem node40_44 :
    ∀ r ∈ Set.Icc ((2669:ℝ)/4000) ((5347:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node40_42 node42_44
private theorem node44_46 :
    ∀ r ∈ Set.Icc ((5347:ℝ)/8000) ((10703:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf44 leaf45
private theorem node46_48 :
    ∀ r ∈ Set.Icc ((10703:ℝ)/16000) ((1339:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf46 leaf47
private theorem node44_48 :
    ∀ r ∈ Set.Icc ((5347:ℝ)/8000) ((1339:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node44_46 node46_48
private theorem node40_48 :
    ∀ r ∈ Set.Icc ((2669:ℝ)/4000) ((1339:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node40_44 node44_48
private theorem node32_48 :
    ∀ r ∈ Set.Icc ((133:ℝ)/200) ((1339:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node32_40 node40_48
private theorem node48_50 :
    ∀ r ∈ Set.Icc ((1339:ℝ)/2000) ((10721:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf48 leaf49
private theorem node50_52 :
    ∀ r ∈ Set.Icc ((10721:ℝ)/16000) ((1073:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf50 leaf51
private theorem node48_52 :
    ∀ r ∈ Set.Icc ((1339:ℝ)/2000) ((1073:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node48_50 node50_52
private theorem node52_54 :
    ∀ r ∈ Set.Icc ((1073:ℝ)/1600) ((10739:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf52 leaf53
private theorem node54_56 :
    ∀ r ∈ Set.Icc ((10739:ℝ)/16000) ((2687:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf54 leaf55
private theorem node52_56 :
    ∀ r ∈ Set.Icc ((1073:ℝ)/1600) ((2687:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node52_54 node54_56
private theorem node48_56 :
    ∀ r ∈ Set.Icc ((1339:ℝ)/2000) ((2687:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node48_52 node52_56
private theorem node56_58 :
    ∀ r ∈ Set.Icc ((2687:ℝ)/4000) ((10757:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf56 leaf57
private theorem node58_60 :
    ∀ r ∈ Set.Icc ((10757:ℝ)/16000) ((5383:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf58 leaf59
private theorem node56_60 :
    ∀ r ∈ Set.Icc ((2687:ℝ)/4000) ((5383:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node56_58 node58_60
private theorem node60_62 :
    ∀ r ∈ Set.Icc ((5383:ℝ)/8000) ((431:ℝ)/640), model r < (cap:ℝ) :=
  interval_join leaf60 leaf61
private theorem node62_64 :
    ∀ r ∈ Set.Icc ((431:ℝ)/640) ((337:ℝ)/500), model r < (cap:ℝ) :=
  interval_join leaf62 leaf63
private theorem node60_64 :
    ∀ r ∈ Set.Icc ((5383:ℝ)/8000) ((337:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node60_62 node62_64
private theorem node56_64 :
    ∀ r ∈ Set.Icc ((2687:ℝ)/4000) ((337:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node56_60 node60_64
private theorem node48_64 :
    ∀ r ∈ Set.Icc ((1339:ℝ)/2000) ((337:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node48_56 node56_64
private theorem node32_64 :
    ∀ r ∈ Set.Icc ((133:ℝ)/200) ((337:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node32_48 node48_64
private theorem node0_64 :
    ∀ r ∈ Set.Icc ((82:ℝ)/125) ((337:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node0_32 node32_64
theorem bound : ∀ r ∈ Set.Icc ((82:ℝ)/125) ((337:ℝ)/500), model r < (cap:ℝ) := node0_64
end N11Formalization.C450FirstRadialG03
#check @N11Formalization.C450FirstRadialG03.bound
#print axioms N11Formalization.C450FirstRadialG03.bound
