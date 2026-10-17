import N11Formalization.C450FirstRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstRadialG04
open C450FirstRadialKernel
def packet0 : Packet := ⟨((337:ℚ)/500),((21577:ℚ)/32000),((2389206301:ℚ)/10000000000),((2457997679:ℚ)/5000000000)⟩
theorem valid0 : Valid packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((337:ℝ)/500) ((21577:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((21577:ℚ)/32000),((10793:ℚ)/16000),((2394436261:ℚ)/10000000000),((61351873:ℚ)/125000000)⟩
theorem valid1 : Valid packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((21577:ℝ)/32000) ((10793:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((10793:ℚ)/16000),((4319:ℚ)/6400),((479929153:ℚ)/2000000000),((4900292789:ℚ)/10000000000)⟩
theorem valid2 : Valid packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((10793:ℝ)/16000) ((4319:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((4319:ℚ)/6400),((5401:ℚ)/8000),((1202417477:ℚ)/5000000000),((4892424147:ℚ)/10000000000)⟩
theorem valid3 : Valid packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((4319:ℝ)/6400) ((5401:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((5401:ℚ)/8000),((21613:ℚ)/32000),((2410003971:ℚ)/10000000000),((4884543859:ℚ)/10000000000)⟩
theorem valid4 : Valid packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((5401:ℝ)/8000) ((21613:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((21613:ℚ)/32000),((10811:ℚ)/16000),((483030591:ℚ)/2000000000),((1219162967:ℚ)/2500000000)⟩
theorem valid5 : Valid packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((21613:ℝ)/32000) ((10811:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((10811:ℚ)/16000),((21631:ℚ)/32000),((484056409:ℚ)/2000000000),((1217187029:ℚ)/2500000000)⟩
theorem valid6 : Valid packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((10811:ℝ)/16000) ((21631:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((21631:ℚ)/32000),((541:ℚ)/800),((2425391377:ℚ)/10000000000),((2430416273:ℚ)/5000000000)⟩
theorem valid7 : Valid packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((21631:ℝ)/32000) ((541:ℝ)/800), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((541:ℚ)/800),((21649:ℚ)/32000),((486096217:ℚ)/2000000000),((48529051:ℚ)/100000000)⟩
theorem valid8 : Valid packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((541:ℝ)/800) ((21649:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((21649:ℚ)/32000),((10829:ℚ)/16000),((304443913:ℚ)/1250000000),((121124143:ℚ)/250000000)⟩
theorem valid9 : Valid packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((21649:ℝ)/32000) ((10829:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((10829:ℚ)/16000),((21667:ℚ)/32000),((488120433:ℚ)/2000000000),((967402869:ℚ)/2000000000)⟩
theorem valid10 : Valid packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((10829:ℝ)/16000) ((21667:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((21667:ℚ)/32000),((5419:ℚ)/8000),((2445633797:ℚ)/10000000000),((1207262729:ℚ)/2500000000)⟩
theorem valid11 : Valid packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((21667:ℝ)/32000) ((5419:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((5419:ℚ)/8000),((4337:ℚ)/6400),((245064633:ℚ)/1000000000),((2410537687:ℚ)/5000000000)⟩
theorem valid12 : Valid packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((5419:ℝ)/8000) ((4337:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((4337:ℚ)/6400),((10847:ℚ)/16000),((245563989:ℚ)/1000000000),((2406543829:ℚ)/5000000000)⟩
theorem valid13 : Valid packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((4337:ℝ)/6400) ((10847:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((10847:ℚ)/16000),((21703:ℚ)/32000),((2460614603:ℚ)/10000000000),((2402543853:ℚ)/5000000000)⟩
theorem valid14 : Valid packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((10847:ℝ)/16000) ((21703:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((21703:ℚ)/32000),((1357:ℚ)/2000),((2465570593:ℚ)/10000000000),((2398537729:ℚ)/5000000000)⟩
theorem valid15 : Valid packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((21703:ℝ)/32000) ((1357:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((1357:ℚ)/2000),((21721:ℚ)/32000),((2470507983:ℚ)/10000000000),((4789050851:ℚ)/10000000000)⟩
theorem valid16 : Valid packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((1357:ℝ)/2000) ((21721:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((21721:ℚ)/32000),((2173:ℚ)/3200),((1237713447:ℚ)/5000000000),((4781013823:ℚ)/10000000000)⟩
theorem valid17 : Valid packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((21721:ℝ)/32000) ((2173:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((2173:ℚ)/3200),((21739:ℚ)/32000),((1240163723:ℚ)/5000000000),((477296431:ℚ)/1000000000)⟩
theorem valid18 : Valid packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((2173:ℝ)/3200) ((21739:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((21739:ℚ)/32000),((5437:ℚ)/8000),((621302439:ℚ)/2500000000),((4764902249:ℚ)/10000000000)⟩
theorem valid19 : Valid packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((21739:ℝ)/32000) ((5437:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((5437:ℚ)/8000),((21757:ℚ)/32000),((2490073943:ℚ)/10000000000),((4756827577:ℚ)/10000000000)⟩
theorem valid20 : Valid packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((5437:ℝ)/8000) ((21757:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((21757:ℚ)/32000),((10883:ℚ)/16000),((1247460061:ℚ)/5000000000),((4748740227:ℚ)/10000000000)⟩
theorem valid21 : Valid packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((21757:ℝ)/32000) ((10883:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((10883:ℚ)/16000),((871:ℚ)/1280),((312468551:ℚ)/1250000000),((948128027:ℚ)/2000000000)⟩
theorem valid22 : Valid packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((10883:ℝ)/16000) ((871:ℝ)/1280), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((871:ℚ)/1280),((2723:ℚ)/4000),((2504558913:ℚ)/10000000000),((1183131809:ℚ)/2500000000)⟩
theorem valid23 : Valid packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((871:ℝ)/1280) ((2723:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((2723:ℚ)/4000),((21793:ℚ)/32000),((2509351751:ℚ)/10000000000),((2362200731:ℚ)/5000000000)⟩
theorem valid24 : Valid packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((2723:ℝ)/4000) ((21793:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((21793:ℚ)/32000),((10901:ℚ)/16000),((251412703:ℚ)/1000000000),((1179065687:ℚ)/2500000000)⟩
theorem valid25 : Valid packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((21793:ℝ)/32000) ((10901:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((10901:ℚ)/16000),((21811:ℚ)/32000),((1259442431:ℚ)/5000000000),((188324441:ℚ)/400000000)⟩
theorem valid26 : Valid packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((10901:ℝ)/16000) ((21811:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((21811:ℚ)/32000),((1091:ℚ)/1600),((1261812677:ℚ)/5000000000),((187997849:ℚ)/400000000)⟩
theorem valid27 : Valid packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((21811:ℝ)/32000) ((1091:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((1091:ℚ)/1600),((21829:ℚ)/32000),((2528348613:ℚ)/10000000000),((4691768281:ℚ)/10000000000)⟩
theorem valid28 : Valid packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((1091:ℝ)/1600) ((21829:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((21829:ℚ)/32000),((10919:ℚ)/16000),((506610949:ℚ)/2000000000),((2341788561:ℚ)/5000000000)⟩
theorem valid29 : Valid packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((21829:ℝ)/32000) ((10919:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((10919:ℚ)/16000),((21847:ℚ)/32000),((507548771:ℚ)/2000000000),((4675372679:ℚ)/10000000000)⟩
theorem valid30 : Valid packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((10919:ℝ)/16000) ((21847:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((21847:ℚ)/32000),((683:ℚ)/1000),((2542416047:ℚ)/10000000000),((2333577441:ℚ)/5000000000)⟩
theorem valid31 : Valid packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((21847:ℝ)/32000) ((683:ℝ)/1000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((683:ℚ)/1000),((4373:ℚ)/6400),((2547071423:ℚ)/10000000000),((232946183:ℚ)/500000000)⟩
theorem valid32 : Valid packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((683:ℝ)/1000) ((4373:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((4373:ℚ)/6400),((10937:ℚ)/16000),((510342017:ℚ)/2000000000),((232533947:ℚ)/500000000)⟩
theorem valid33 : Valid packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((4373:ℝ)/6400) ((10937:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((10937:ℚ)/16000),((21883:ℚ)/32000),((2556332133:ℚ)/10000000000),((1160605163:ℚ)/2500000000)⟩
theorem valid34 : Valid packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((10937:ℝ)/16000) ((21883:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((21883:ℚ)/32000),((5473:ℚ)/8000),((1280468833:ℚ)/5000000000),((4634148721:ℚ)/10000000000)⟩
theorem valid35 : Valid packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((21883:ℝ)/32000) ((5473:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((5473:ℚ)/8000),((21901:ℚ)/32000),((2565526783:ℚ)/10000000000),((2312931537:ℚ)/5000000000)⟩
theorem valid36 : Valid packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((5473:ℝ)/8000) ((21901:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((21901:ℚ)/32000),((2191:ℚ)/3200),((128504979:ℚ)/500000000),((2308781819:ℚ)/5000000000)⟩
theorem valid37 : Valid packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((21901:ℝ)/32000) ((2191:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((2191:ℚ)/3200),((21919:ℚ)/32000),((1287328077:ℚ)/5000000000),((4609250337:ℚ)/10000000000)⟩
theorem valid38 : Valid packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((2191:ℝ)/3200) ((21919:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((21919:ℚ)/32000),((2741:ℚ)/4000),((2579196601:ℚ)/10000000000),((575115387:ℚ)/1250000000)⟩
theorem valid39 : Valid packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((21919:ℝ)/32000) ((2741:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((2741:ℚ)/4000),((21937:ℚ)/32000),((1291860507:ℚ)/5000000000),((2296290919:ℚ)/5000000000)⟩
theorem valid40 : Valid packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((2741:ℝ)/4000) ((21937:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((21937:ℚ)/32000),((10973:ℚ)/16000),((1294114743:ℚ)/5000000000),((573028311:ℚ)/1250000000)⟩
theorem valid41 : Valid packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((21937:ℝ)/32000) ((10973:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((10973:ℚ)/16000),((4391:ℚ)/6400),((2592722111:ℚ)/10000000000),((2287928483:ℚ)/5000000000)⟩
theorem valid42 : Valid packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((10973:ℝ)/16000) ((4391:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((4391:ℚ)/6400),((5491:ℚ)/8000),((2597198979:ℚ)/10000000000),((1141868299:ℚ)/2500000000)⟩
theorem valid43 : Valid packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((4391:ℝ)/6400) ((5491:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((5491:ℚ)/8000),((21973:ℚ)/32000),((130083009:ℚ)/500000000),((2279537549:ℚ)/5000000000)⟩
theorem valid44 : Valid packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((5491:ℝ)/8000) ((21973:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((21973:ℚ)/32000),((10991:ℚ)/16000),((521221161:ℚ)/2000000000),((71104103:ℚ)/156250000)⟩
theorem valid45 : Valid packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((21973:ℝ)/32000) ((10991:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet46 : Packet := ⟨((10991:ℚ)/16000),((21991:ℚ)/32000),((2610535941:ℚ)/10000000000),((2271117799:ℚ)/5000000000)⟩
theorem valid46 : Valid packet46 := by
  constructor <;> decide +kernel
private theorem leaf46 : ∀ r ∈ Set.Icc ((10991:ℝ)/16000) ((21991:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet46 valid46 r
    (by simpa only [packet46,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet47 : Packet := ⟨((21991:ℚ)/32000),((11:ℚ)/16),((2614950677:ℚ)/10000000000),((1133448509:ℚ)/2500000000)⟩
theorem valid47 : Valid packet47 := by
  constructor <;> decide +kernel
private theorem leaf47 : ∀ r ∈ Set.Icc ((21991:ℝ)/32000) ((11:ℝ)/16), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet47 valid47 r
    (by simpa only [packet47,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet48 : Packet := ⟨((11:ℚ)/16),((22009:ℚ)/32000),((26193501:ℚ)/100000000),((2262668911:ℚ)/5000000000)⟩
theorem valid48 : Valid packet48 := by
  constructor <;> decide +kernel
private theorem leaf48 : ∀ r ∈ Set.Icc ((11:ℝ)/16) ((22009:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet48 valid48 r
    (by simpa only [packet48,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet49 : Packet := ⟨((22009:ℚ)/32000),((11009:ℚ)/16000),((1311867147:ℚ)/5000000000),((7226987:ℚ)/16000000)⟩
theorem valid49 : Valid packet49 := by
  constructor <;> decide +kernel
private theorem leaf49 : ∀ r ∈ Set.Icc ((22009:ℝ)/32000) ((11009:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet49 valid49 r
    (by simpa only [packet49,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet50 : Packet := ⟨((11009:ℚ)/16000),((22027:ℚ)/32000),((1314051673:ℚ)/5000000000),((450838111:ℚ)/1000000000)⟩
theorem valid50 : Valid packet50 := by
  constructor <;> decide +kernel
private theorem leaf50 : ∀ r ∈ Set.Icc ((11009:ℝ)/16000) ((22027:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet50 valid50 r
    (by simpa only [packet50,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet51 : Packet := ⟨((22027:ℚ)/32000),((5509:ℚ)/8000),((131622867:ℚ)/500000000),((899976089:ℚ)/2000000000)⟩
theorem valid51 : Valid packet51 := by
  constructor <;> decide +kernel
private theorem leaf51 : ∀ r ∈ Set.Icc ((22027:ℝ)/32000) ((5509:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet51 valid51 r
    (by simpa only [packet51,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet52 : Packet := ⟨((5509:ℚ)/8000),((4409:ℚ)/6400),((2636796359:ℚ)/10000000000),((4491364793:ℚ)/10000000000)⟩
theorem valid52 : Valid packet52 := by
  constructor <;> decide +kernel
private theorem leaf52 : ∀ r ∈ Set.Icc ((5509:ℝ)/8000) ((4409:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet52 valid52 r
    (by simpa only [packet52,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet53 : Packet := ⟨((4409:ℚ)/6400),((11027:ℚ)/16000),((528224097:ℚ)/2000000000),((448283407:ℚ)/1000000000)⟩
theorem valid53 : Valid packet53 := by
  constructor <;> decide +kernel
private theorem leaf53 : ∀ r ∈ Set.Icc ((4409:ℝ)/6400) ((11027:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet53 valid53 r
    (by simpa only [packet53,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet54 : Packet := ⟨((11027:ℚ)/16000),((22063:ℚ)/32000),((1322714901:ℚ)/5000000000),((1118572047:ℚ)/2500000000)⟩
theorem valid54 : Valid packet54 := by
  constructor <;> decide +kernel
private theorem leaf54 : ∀ r ∈ Set.Icc ((11027:ℝ)/16000) ((22063:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet54 valid54 r
    (by simpa only [packet54,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet55 : Packet := ⟨((22063:ℚ)/32000),((2759:ℚ)/4000),((662431097:ℚ)/2500000000),((4465727061:ℚ)/10000000000)⟩
theorem valid55 : Valid packet55 := by
  constructor <;> decide +kernel
private theorem leaf55 : ∀ r ∈ Set.Icc ((22063:ℝ)/32000) ((2759:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet55 valid55 r
    (by simpa only [packet55,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet56 : Packet := ⟨((2759:ℚ)/4000),((22081:ℚ)/32000),((1327002163:ℚ)/5000000000),((22285753:ℚ)/50000000)⟩
theorem valid56 : Valid packet56 := by
  constructor <;> decide +kernel
private theorem leaf56 : ∀ r ∈ Set.Icc ((2759:ℝ)/4000) ((22081:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet56 valid56 r
    (by simpa only [packet56,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet57 : Packet := ⟨((22081:ℚ)/32000),((2209:ℚ)/3200),((1329134847:ℚ)/5000000000),((889711743:ℚ)/2000000000)⟩
theorem valid57 : Valid packet57 := by
  constructor <;> decide +kernel
private theorem leaf57 : ∀ r ∈ Set.Icc ((22081:ℝ)/32000) ((2209:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet57 valid57 r
    (by simpa only [packet57,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet58 : Packet := ⟨((2209:ℚ)/3200),((22099:ℚ)/32000),((2662520571:ℚ)/10000000000),((2219975659:ℚ)/5000000000)⟩
theorem valid58 : Valid packet58 := by
  constructor <;> decide +kernel
private theorem leaf58 : ∀ r ∈ Set.Icc ((2209:ℝ)/3200) ((22099:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet58 valid58 r
    (by simpa only [packet58,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet59 : Packet := ⟨((22099:ℚ)/32000),((5527:ℚ)/8000),((533351407:ℚ)/2000000000),((4431328317:ℚ)/10000000000)⟩
theorem valid59 : Valid packet59 := by
  constructor <;> decide +kernel
private theorem leaf59 : ∀ r ∈ Set.Icc ((22099:ℝ)/32000) ((5527:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet59 valid59 r
    (by simpa only [packet59,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet60 : Packet := ⟨((5527:ℚ)/8000),((22117:ℚ)/32000),((667744791:ℚ)/2500000000),((4422689621:ℚ)/10000000000)⟩
theorem valid60 : Valid packet60 := by
  constructor <;> decide +kernel
private theorem leaf60 : ∀ r ∈ Set.Icc ((5527:ℝ)/8000) ((22117:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet60 valid60 r
    (by simpa only [packet60,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet61 : Packet := ⟨((22117:ℚ)/32000),((11063:ℚ)/16000),((2675187033:ℚ)/10000000000),((4414035137:ℚ)/10000000000)⟩
theorem valid61 : Valid packet61 := by
  constructor <;> decide +kernel
private theorem leaf61 : ∀ r ∈ Set.Icc ((22117:ℝ)/32000) ((11063:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet61 valid61 r
    (by simpa only [packet61,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet62 : Packet := ⟨((11063:ℚ)/16000),((4427:ℚ)/6400),((1339690359:ℚ)/5000000000),((1101341193:ℚ)/2500000000)⟩
theorem valid62 : Valid packet62 := by
  constructor <;> decide +kernel
private theorem leaf62 : ∀ r ∈ Set.Icc ((11063:ℝ)/16000) ((4427:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet62 valid62 r
    (by simpa only [packet62,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet63 : Packet := ⟨((4427:ℚ)/6400),((173:ℚ)/250),((536712059:ℚ)/2000000000),((137396201:ℚ)/312500000)⟩
theorem valid63 : Valid packet63 := by
  constructor <;> decide +kernel
private theorem leaf63 : ∀ r ∈ Set.Icc ((4427:ℝ)/6400) ((173:ℝ)/250), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet63 valid63 r
    (by simpa only [packet63,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((337:ℝ)/500) ((10793:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((10793:ℝ)/16000) ((5401:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((337:ℝ)/500) ((5401:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((5401:ℝ)/8000) ((10811:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((10811:ℝ)/16000) ((541:ℝ)/800), model r < (cap:ℝ) :=
  interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((5401:ℝ)/8000) ((541:ℝ)/800), model r < (cap:ℝ) :=
  interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((337:ℝ)/500) ((541:ℝ)/800), model r < (cap:ℝ) :=
  interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((541:ℝ)/800) ((10829:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((10829:ℝ)/16000) ((5419:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((541:ℝ)/800) ((5419:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((5419:ℝ)/8000) ((10847:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((10847:ℝ)/16000) ((1357:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((5419:ℝ)/8000) ((1357:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((541:ℝ)/800) ((1357:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((337:ℝ)/500) ((1357:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((1357:ℝ)/2000) ((2173:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((2173:ℝ)/3200) ((5437:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((1357:ℝ)/2000) ((5437:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((5437:ℝ)/8000) ((10883:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((10883:ℝ)/16000) ((2723:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((5437:ℝ)/8000) ((2723:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((1357:ℝ)/2000) ((2723:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((2723:ℝ)/4000) ((10901:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((10901:ℝ)/16000) ((1091:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((2723:ℝ)/4000) ((1091:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((1091:ℝ)/1600) ((10919:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((10919:ℝ)/16000) ((683:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((1091:ℝ)/1600) ((683:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((2723:ℝ)/4000) ((683:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((1357:ℝ)/2000) ((683:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((337:ℝ)/500) ((683:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node0_16 node16_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((683:ℝ)/1000) ((10937:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf32 leaf33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((10937:ℝ)/16000) ((5473:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf34 leaf35
private theorem node32_36 :
    ∀ r ∈ Set.Icc ((683:ℝ)/1000) ((5473:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node32_34 node34_36
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((5473:ℝ)/8000) ((2191:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf36 leaf37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((2191:ℝ)/3200) ((2741:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf38 leaf39
private theorem node36_40 :
    ∀ r ∈ Set.Icc ((5473:ℝ)/8000) ((2741:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node36_38 node38_40
private theorem node32_40 :
    ∀ r ∈ Set.Icc ((683:ℝ)/1000) ((2741:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node32_36 node36_40
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((2741:ℝ)/4000) ((10973:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf40 leaf41
private theorem node42_44 :
    ∀ r ∈ Set.Icc ((10973:ℝ)/16000) ((5491:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf42 leaf43
private theorem node40_44 :
    ∀ r ∈ Set.Icc ((2741:ℝ)/4000) ((5491:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node40_42 node42_44
private theorem node44_46 :
    ∀ r ∈ Set.Icc ((5491:ℝ)/8000) ((10991:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf44 leaf45
private theorem node46_48 :
    ∀ r ∈ Set.Icc ((10991:ℝ)/16000) ((11:ℝ)/16), model r < (cap:ℝ) :=
  interval_join leaf46 leaf47
private theorem node44_48 :
    ∀ r ∈ Set.Icc ((5491:ℝ)/8000) ((11:ℝ)/16), model r < (cap:ℝ) :=
  interval_join node44_46 node46_48
private theorem node40_48 :
    ∀ r ∈ Set.Icc ((2741:ℝ)/4000) ((11:ℝ)/16), model r < (cap:ℝ) :=
  interval_join node40_44 node44_48
private theorem node32_48 :
    ∀ r ∈ Set.Icc ((683:ℝ)/1000) ((11:ℝ)/16), model r < (cap:ℝ) :=
  interval_join node32_40 node40_48
private theorem node48_50 :
    ∀ r ∈ Set.Icc ((11:ℝ)/16) ((11009:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf48 leaf49
private theorem node50_52 :
    ∀ r ∈ Set.Icc ((11009:ℝ)/16000) ((5509:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf50 leaf51
private theorem node48_52 :
    ∀ r ∈ Set.Icc ((11:ℝ)/16) ((5509:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node48_50 node50_52
private theorem node52_54 :
    ∀ r ∈ Set.Icc ((5509:ℝ)/8000) ((11027:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf52 leaf53
private theorem node54_56 :
    ∀ r ∈ Set.Icc ((11027:ℝ)/16000) ((2759:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf54 leaf55
private theorem node52_56 :
    ∀ r ∈ Set.Icc ((5509:ℝ)/8000) ((2759:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node52_54 node54_56
private theorem node48_56 :
    ∀ r ∈ Set.Icc ((11:ℝ)/16) ((2759:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node48_52 node52_56
private theorem node56_58 :
    ∀ r ∈ Set.Icc ((2759:ℝ)/4000) ((2209:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf56 leaf57
private theorem node58_60 :
    ∀ r ∈ Set.Icc ((2209:ℝ)/3200) ((5527:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf58 leaf59
private theorem node56_60 :
    ∀ r ∈ Set.Icc ((2759:ℝ)/4000) ((5527:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node56_58 node58_60
private theorem node60_62 :
    ∀ r ∈ Set.Icc ((5527:ℝ)/8000) ((11063:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf60 leaf61
private theorem node62_64 :
    ∀ r ∈ Set.Icc ((11063:ℝ)/16000) ((173:ℝ)/250), model r < (cap:ℝ) :=
  interval_join leaf62 leaf63
private theorem node60_64 :
    ∀ r ∈ Set.Icc ((5527:ℝ)/8000) ((173:ℝ)/250), model r < (cap:ℝ) :=
  interval_join node60_62 node62_64
private theorem node56_64 :
    ∀ r ∈ Set.Icc ((2759:ℝ)/4000) ((173:ℝ)/250), model r < (cap:ℝ) :=
  interval_join node56_60 node60_64
private theorem node48_64 :
    ∀ r ∈ Set.Icc ((11:ℝ)/16) ((173:ℝ)/250), model r < (cap:ℝ) :=
  interval_join node48_56 node56_64
private theorem node32_64 :
    ∀ r ∈ Set.Icc ((683:ℝ)/1000) ((173:ℝ)/250), model r < (cap:ℝ) :=
  interval_join node32_48 node48_64
private theorem node0_64 :
    ∀ r ∈ Set.Icc ((337:ℝ)/500) ((173:ℝ)/250), model r < (cap:ℝ) :=
  interval_join node0_32 node32_64
theorem bound : ∀ r ∈ Set.Icc ((337:ℝ)/500) ((173:ℝ)/250), model r < (cap:ℝ) := node0_64
end N11Formalization.C450FirstRadialG04
#check @N11Formalization.C450FirstRadialG04.bound
#print axioms N11Formalization.C450FirstRadialG04.bound
