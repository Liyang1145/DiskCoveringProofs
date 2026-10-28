import N11Formalization.C450FirstRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstRadialG01
open C450FirstRadialKernel
def packet0 : Packet := ⟨((31:ℚ)/50),((19849:ℚ)/32000),((185602833:ℚ)/10000000000),((3128730817:ℚ)/5000000000)⟩
theorem valid0 : Valid packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((19849:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((19849:ℚ)/32000),((9929:ℚ)/16000),((32797217:ℚ)/1250000000),((3125570271:ℚ)/5000000000)⟩
theorem valid1 : Valid packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((19849:ℝ)/32000) ((9929:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((9929:ℚ)/16000),((19867:ℚ)/32000),((321218091:ℚ)/10000000000),((6244813909:ℚ)/10000000000)⟩
theorem valid2 : Valid packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((9929:ℝ)/16000) ((19867:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((19867:ℚ)/32000),((4969:ℚ)/8000),((92690829:ℚ)/2500000000),((6238481717:ℚ)/10000000000)⟩
theorem valid3 : Valid packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((19867:ℝ)/32000) ((4969:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((4969:ℚ)/8000),((3977:ℚ)/6400),((103590319:ℚ)/2500000000),((6232143949:ℚ)/10000000000)⟩
theorem valid4 : Valid packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((4969:ℝ)/8000) ((3977:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((3977:ℚ)/6400),((9947:ℚ)/16000),((226864839:ℚ)/5000000000),((1556450147:ℚ)/2500000000)⟩
theorem valid5 : Valid packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((3977:ℝ)/6400) ((9947:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((9947:ℚ)/16000),((19903:ℚ)/32000),((24494467:ℚ)/500000000),((194357863:ℚ)/312500000)⟩
theorem valid6 : Valid packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((9947:ℝ)/16000) ((19903:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((19903:ℚ)/32000),((2489:ℚ)/4000),((130876413:ℚ)/2500000000),((776637127:ℚ)/1250000000)⟩
theorem valid7 : Valid packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((19903:ℝ)/32000) ((2489:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2489:ℚ)/4000),((19921:ℚ)/32000),((69380123:ℚ)/1250000000),((620673677:ℚ)/1000000000)⟩
theorem valid8 : Valid packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2489:ℝ)/4000) ((19921:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((19921:ℚ)/32000),((1993:ℚ)/3200),((584832123:ℚ)/10000000000),((6200370861:ℚ)/10000000000)⟩
theorem valid9 : Valid packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((19921:ℝ)/32000) ((1993:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((1993:ℚ)/3200),((19939:ℚ)/32000),((306566709:ℚ)/5000000000),((6193999271:ℚ)/10000000000)⟩
theorem valid10 : Valid packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((1993:ℝ)/3200) ((19939:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((19939:ℚ)/32000),((4987:ℚ)/8000),((320071277:ℚ)/5000000000),((3093810991:ℚ)/5000000000)⟩
theorem valid11 : Valid packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((19939:ℝ)/32000) ((4987:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((4987:ℚ)/8000),((19957:ℚ)/32000),((666016803:ℚ)/10000000000),((6181238977:ℚ)/10000000000)⟩
theorem valid12 : Valid packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((4987:ℝ)/8000) ((19957:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((19957:ℚ)/32000),((9983:ℚ)/16000),((690883733:ℚ)/10000000000),((1543712559:ℚ)/2500000000)⟩
theorem valid13 : Valid packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((19957:ℝ)/32000) ((9983:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((9983:ℚ)/16000),((799:ℚ)/1280),((17871213:ℚ)/250000000),((3084227871:ℚ)/5000000000)⟩
theorem valid14 : Valid packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((9983:ℝ)/16000) ((799:ℝ)/1280), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((799:ℚ)/1280),((1249:ℚ)/2000),((7379991:ℚ)/100000000),((3081027739:ℚ)/5000000000)⟩
theorem valid15 : Valid packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((799:ℝ)/1280) ((1249:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((1249:ℚ)/2000),((19993:ℚ)/32000),((152081977:ℚ)/2000000000),((6155649423:ℚ)/10000000000)⟩
theorem valid16 : Valid packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((1249:ℝ)/2000) ((19993:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((19993:ℚ)/32000),((10001:ℚ)/16000),((782144511:ℚ)/10000000000),((6149237561:ℚ)/10000000000)⟩
theorem valid17 : Valid packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((19993:ℝ)/32000) ((10001:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((10001:ℚ)/16000),((20011:ℚ)/32000),((803257909:ℚ)/10000000000),((6142819873:ℚ)/10000000000)⟩
theorem valid18 : Valid packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((10001:ℝ)/16000) ((20011:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((20011:ℚ)/32000),((1001:ℚ)/1600),((164759577:ℚ)/2000000000),((306819817:ℚ)/500000000)⟩
theorem valid19 : Valid packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((20011:ℝ)/32000) ((1001:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((1001:ℚ)/1600),((20029:ℚ)/32000),((843806353:ℚ)/10000000000),((191561467:ℚ)/312500000)⟩
theorem valid20 : Valid packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((1001:ℝ)/1600) ((20029:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((20029:ℚ)/32000),((10019:ℚ)/16000),((863320307:ℚ)/10000000000),((1224706333:ℚ)/2000000000)⟩
theorem valid21 : Valid packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((20029:ℝ)/32000) ((10019:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((10019:ℚ)/16000),((20047:ℚ)/32000),((441186297:ℚ)/5000000000),((1223418097:ℚ)/2000000000)⟩
theorem valid22 : Valid packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((10019:ℝ)/16000) ((20047:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((20047:ℚ)/32000),((2507:ℚ)/4000),((450496269:ℚ)/5000000000),((1222128677:ℚ)/2000000000)⟩
theorem valid23 : Valid packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((20047:ℝ)/32000) ((2507:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((2507:ℚ)/4000),((4013:ℚ)/6400),((57450403:ℚ)/625000000),((3052095173:ℚ)/5000000000)⟩
theorem valid24 : Valid packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((2507:ℝ)/4000) ((4013:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((4013:ℚ)/6400),((10037:ℚ)/16000),((234259509:ℚ)/2500000000),((6097731349:ℚ)/10000000000)⟩
theorem valid25 : Valid packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((4013:ℝ)/6400) ((10037:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((10037:ℚ)/16000),((20083:ℚ)/32000),((238627191:ℚ)/2500000000),((3045633187:ℚ)/5000000000)⟩
theorem valid26 : Valid packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((10037:ℝ)/16000) ((20083:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((20083:ℚ)/32000),((5023:ℚ)/8000),((97163813:ℚ)/1000000000),((6084795403:ℚ)/10000000000)⟩
theorem valid27 : Valid packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((20083:ℝ)/32000) ((5023:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((5023:ℚ)/8000),((20101:ℚ)/32000),((197688783:ℚ)/2000000000),((1215663683:ℚ)/2000000000)⟩
theorem valid28 : Valid packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((5023:ℝ)/8000) ((20101:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((20101:ℚ)/32000),((2011:ℚ)/3200),((200988477:ℚ)/2000000000),((23718107:ℚ)/39062500)⟩
theorem valid29 : Valid packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((20101:ℝ)/32000) ((2011:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((2011:ℚ)/3200),((20119:ℚ)/32000),((1021148467:ℚ)/10000000000),((6065346313:ℚ)/10000000000)⟩
theorem valid30 : Valid packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((2011:ℝ)/3200) ((20119:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((20119:ℚ)/32000),((629:ℚ)/1000),((10370759:ℚ)/100000000),((151471279:ℚ)/250000000)⟩
theorem valid31 : Valid packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((20119:ℝ)/32000) ((629:ℝ)/1000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((629:ℚ)/1000),((20137:ℚ)/32000),((526368681:ℚ)/5000000000),((6052349911:ℚ)/10000000000)⟩
theorem valid32 : Valid packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((629:ℝ)/1000) ((20137:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((20137:ℚ)/32000),((10073:ℚ)/16000),((534072291:ℚ)/5000000000),((6045842547:ℚ)/10000000000)⟩
theorem valid33 : Valid packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((20137:ℝ)/32000) ((10073:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((10073:ℚ)/16000),((4031:ℚ)/6400),((1083308437:ℚ)/10000000000),((754916131:ℚ)/1250000000)⟩
theorem valid34 : Valid packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((10073:ℝ)/16000) ((4031:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((4031:ℚ)/6400),((5041:ℚ)/8000),((1098239039:ℚ)/10000000000),((1206561879:ℚ)/2000000000)⟩
theorem valid35 : Valid packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((4031:ℝ)/6400) ((5041:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((5041:ℚ)/8000),((20173:ℚ)/32000),((1112945803:ℚ)/10000000000),((1205256713:ℚ)/2000000000)⟩
theorem valid36 : Valid packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((5041:ℝ)/8000) ((20173:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((20173:ℚ)/32000),((10091:ℚ)/16000),((281859379:ℚ)/2500000000),((300987577:ℚ)/500000000)⟩
theorem valid37 : Valid packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((20173:ℝ)/32000) ((10091:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((10091:ℚ)/16000),((20191:ℚ)/32000),((1141722397:ℚ)/10000000000),((6013213299:ℚ)/10000000000)⟩
theorem valid38 : Valid packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((10091:ℝ)/16000) ((20191:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((20191:ℚ)/32000),((101:ℚ)/160),((1155808141:ℚ)/10000000000),((6006668821:ℚ)/10000000000)⟩
theorem valid39 : Valid packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((20191:ℝ)/32000) ((101:ℝ)/160), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((101:ℚ)/160),((20209:ℚ)/32000),((1169701969:ℚ)/10000000000),((3000059043:ℚ)/5000000000)⟩
theorem valid40 : Valid packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((101:ℝ)/160) ((20209:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((20209:ℚ)/32000),((10109:ℚ)/16000),((1183410669:ℚ)/10000000000),((374597567:ℚ)/625000000)⟩
theorem valid41 : Valid packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((20209:ℝ)/32000) ((10109:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((10109:ℚ)/16000),((20227:ℚ)/32000),((1196940627:ℚ)/10000000000),((5986997759:ℚ)/10000000000)⟩
theorem valid42 : Valid packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((10109:ℝ)/16000) ((20227:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((20227:ℚ)/32000),((5059:ℚ)/8000),((151287233:ℚ)/1250000000),((2990214063:ℚ)/5000000000)⟩
theorem valid43 : Valid packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((20227:ℝ)/32000) ((5059:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((5059:ℚ)/8000),((4049:ℚ)/6400),((1223488063:ℚ)/10000000000),((5973852151:ℚ)/10000000000)⟩
theorem valid44 : Valid packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((5059:ℝ)/8000) ((4049:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((4049:ℚ)/6400),((10127:ℚ)/16000),((247303319:ℚ)/2000000000),((2983634907:ℚ)/5000000000)⟩
theorem valid45 : Valid packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((4049:ℝ)/6400) ((10127:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet46 : Packet := ⟨((10127:ℚ)/16000),((20263:ℚ)/32000),((1249388543:ℚ)/10000000000),((5960681093:ℚ)/10000000000)⟩
theorem valid46 : Valid packet46 := by
  constructor <;> decide +kernel
private theorem leaf46 : ∀ r ∈ Set.Icc ((10127:ℝ)/16000) ((20263:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet46 valid46 r
    (by simpa only [packet46,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet47 : Packet := ⟨((20263:ℚ)/32000),((1267:ℚ)/2000),((631054361:ℚ)/5000000000),((2977042983:ℚ)/5000000000)⟩
theorem valid47 : Valid packet47 := by
  constructor <;> decide +kernel
private theorem leaf47 : ∀ r ∈ Set.Icc ((20263:ℝ)/32000) ((1267:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet47 valid47 r
    (by simpa only [packet47,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet48 : Packet := ⟨((1267:ℚ)/2000),((20281:ℚ)/32000),((1274681701:ℚ)/10000000000),((1486871103:ℚ)/2500000000)⟩
theorem valid48 : Valid packet48 := by
  constructor <;> decide +kernel
private theorem leaf48 : ∀ r ∈ Set.Icc ((1267:ℝ)/2000) ((20281:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet48 valid48 r
    (by simpa only [packet48,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet49 : Packet := ⟨((20281:ℚ)/32000),((2029:ℚ)/3200),((643555909:ℚ)/5000000000),((5940876409:ℚ)/10000000000)⟩
theorem valid49 : Valid packet49 := by
  constructor <;> decide +kernel
private theorem leaf49 : ∀ r ∈ Set.Icc ((20281:ℝ)/32000) ((2029:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet49 valid49 r
    (by simpa only [packet49,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet50 : Packet := ⟨((2029:ℚ)/3200),((20299:ℚ)/32000),((1299403197:ℚ)/10000000000),((370891371:ℚ)/625000000)⟩
theorem valid50 : Valid packet50 := by
  constructor <;> decide +kernel
private theorem leaf50 : ∀ r ∈ Set.Icc ((2029:ℝ)/3200) ((20299:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet50 valid50 r
    (by simpa only [packet50,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet51 : Packet := ⟨((20299:ℚ)/32000),((5077:ℚ)/8000),((655779881:ℚ)/5000000000),((592764097:ℚ)/1000000000)⟩
theorem valid51 : Valid packet51 := by
  constructor <;> decide +kernel
private theorem leaf51 : ∀ r ∈ Set.Icc ((20299:ℝ)/32000) ((5077:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet51 valid51 r
    (by simpa only [packet51,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet52 : Packet := ⟨((5077:ℚ)/8000),((20317:ℚ)/32000),((330896313:ℚ)/2500000000),((592101349:ℚ)/1000000000)⟩
theorem valid52 : Valid packet52 := by
  constructor <;> decide +kernel
private theorem leaf52 : ∀ r ∈ Set.Icc ((5077:ℝ)/8000) ((20317:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet52 valid52 r
    (by simpa only [packet52,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet53 : Packet := ⟨((20317:ℚ)/32000),((10163:ℚ)/16000),((1335483231:ℚ)/10000000000),((5914379473:ℚ)/10000000000)⟩
theorem valid53 : Valid packet53 := by
  constructor <;> decide +kernel
private theorem leaf53 : ∀ r ∈ Set.Icc ((20317:ℝ)/32000) ((10163:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet53 valid53 r
    (by simpa only [packet53,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet54 : Packet := ⟨((10163:ℚ)/16000),((4067:ℚ)/6400),((1347257099:ℚ)/10000000000),((369233681:ℚ)/625000000)⟩
theorem valid54 : Valid packet54 := by
  constructor <;> decide +kernel
private theorem leaf54 : ∀ r ∈ Set.Icc ((10163:ℝ)/16000) ((4067:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet54 valid54 r
    (by simpa only [packet54,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet55 : Packet := ⟨((4067:ℚ)/6400),((2543:ℚ)/4000),((679455053:ℚ)/5000000000),((5901091739:ℚ)/10000000000)⟩
theorem valid55 : Valid packet55 := by
  constructor <;> decide +kernel
private theorem leaf55 : ∀ r ∈ Set.Icc ((4067:ℝ)/6400) ((2543:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet55 valid55 r
    (by simpa only [packet55,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet56 : Packet := ⟨((2543:ℚ)/4000),((20353:ℚ)/32000),((685222679:ℚ)/5000000000),((5894437977:ℚ)/10000000000)⟩
theorem valid56 : Valid packet56 := by
  constructor <;> decide +kernel
private theorem leaf56 : ∀ r ∈ Set.Icc ((2543:ℝ)/4000) ((20353:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet56 valid56 r
    (by simpa only [packet56,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet57 : Packet := ⟨((20353:ℚ)/32000),((10181:ℚ)/16000),((690932913:ℚ)/5000000000),((1471944397:ℚ)/2500000000)⟩
theorem valid57 : Valid packet57 := by
  constructor <;> decide +kernel
private theorem leaf57 : ∀ r ∈ Set.Icc ((20353:ℝ)/32000) ((10181:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet57 valid57 r
    (by simpa only [packet57,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet58 : Packet := ⟨((10181:ℚ)/16000),((20371:ℚ)/32000),((278634871:ℚ)/2000000000),((5881110549:ℚ)/10000000000)⟩
theorem valid58 : Valid packet58 := by
  constructor <;> decide +kernel
private theorem leaf58 : ∀ r ∈ Set.Icc ((10181:ℝ)/16000) ((20371:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet58 valid58 r
    (by simpa only [packet58,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet59 : Packet := ⟨((20371:ℚ)/32000),((1019:ℚ)/1600),((1404373671:ℚ)/10000000000),((2937218419:ℚ)/5000000000)⟩
theorem valid59 : Valid packet59 := by
  constructor <;> decide +kernel
private theorem leaf59 : ∀ r ∈ Set.Icc ((20371:ℝ)/32000) ((1019:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet59 valid59 r
    (by simpa only [packet59,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet60 : Packet := ⟨((1019:ℚ)/1600),((20389:ℚ)/32000),((353866597:ℚ)/2500000000),((366734777:ℚ)/625000000)⟩
theorem valid60 : Valid packet60 := by
  constructor <;> decide +kernel
private theorem leaf60 : ∀ r ∈ Set.Icc ((1019:ℝ)/1600) ((20389:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet60 valid60 r
    (by simpa only [packet60,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet61 : Packet := ⟨((20389:ℚ)/32000),((10199:ℚ)/16000),((285291003:ℚ)/2000000000),((5861069307:ℚ)/10000000000)⟩
theorem valid61 : Valid packet61 := by
  constructor <;> decide +kernel
private theorem leaf61 : ∀ r ∈ Set.Icc ((20389:ℝ)/32000) ((10199:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet61 valid61 r
    (by simpa only [packet61,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet62 : Packet := ⟨((10199:ℚ)/16000),((20407:ℚ)/32000),((35933549:ℚ)/250000000),((5854375439:ℚ)/10000000000)⟩
theorem valid62 : Valid packet62 := by
  constructor <;> decide +kernel
private theorem leaf62 : ∀ r ∈ Set.Icc ((10199:ℝ)/16000) ((20407:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet62 valid62 r
    (by simpa only [packet62,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet63 : Packet := ⟨((20407:ℚ)/32000),((319:ℚ)/500),((724064769:ℚ)/5000000000),((5847674807:ℚ)/10000000000)⟩
theorem valid63 : Valid packet63 := by
  constructor <;> decide +kernel
private theorem leaf63 : ∀ r ∈ Set.Icc ((20407:ℝ)/32000) ((319:ℝ)/500), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet63 valid63 r
    (by simpa only [packet63,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((9929:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((9929:ℝ)/16000) ((4969:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((4969:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((4969:ℝ)/8000) ((9947:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((9947:ℝ)/16000) ((2489:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((4969:ℝ)/8000) ((2489:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((2489:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((2489:ℝ)/4000) ((1993:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((1993:ℝ)/3200) ((4987:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((2489:ℝ)/4000) ((4987:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((4987:ℝ)/8000) ((9983:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((9983:ℝ)/16000) ((1249:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((4987:ℝ)/8000) ((1249:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((2489:ℝ)/4000) ((1249:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1249:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((1249:ℝ)/2000) ((10001:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((10001:ℝ)/16000) ((1001:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((1249:ℝ)/2000) ((1001:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((1001:ℝ)/1600) ((10019:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((10019:ℝ)/16000) ((2507:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((1001:ℝ)/1600) ((2507:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((1249:ℝ)/2000) ((2507:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((2507:ℝ)/4000) ((10037:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((10037:ℝ)/16000) ((5023:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((2507:ℝ)/4000) ((5023:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((5023:ℝ)/8000) ((2011:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((2011:ℝ)/3200) ((629:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((5023:ℝ)/8000) ((629:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((2507:ℝ)/4000) ((629:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((1249:ℝ)/2000) ((629:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((629:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node0_16 node16_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((629:ℝ)/1000) ((10073:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf32 leaf33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((10073:ℝ)/16000) ((5041:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf34 leaf35
private theorem node32_36 :
    ∀ r ∈ Set.Icc ((629:ℝ)/1000) ((5041:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node32_34 node34_36
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((5041:ℝ)/8000) ((10091:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf36 leaf37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((10091:ℝ)/16000) ((101:ℝ)/160), model r < (cap:ℝ) :=
  interval_join leaf38 leaf39
private theorem node36_40 :
    ∀ r ∈ Set.Icc ((5041:ℝ)/8000) ((101:ℝ)/160), model r < (cap:ℝ) :=
  interval_join node36_38 node38_40
private theorem node32_40 :
    ∀ r ∈ Set.Icc ((629:ℝ)/1000) ((101:ℝ)/160), model r < (cap:ℝ) :=
  interval_join node32_36 node36_40
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((101:ℝ)/160) ((10109:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf40 leaf41
private theorem node42_44 :
    ∀ r ∈ Set.Icc ((10109:ℝ)/16000) ((5059:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf42 leaf43
private theorem node40_44 :
    ∀ r ∈ Set.Icc ((101:ℝ)/160) ((5059:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node40_42 node42_44
private theorem node44_46 :
    ∀ r ∈ Set.Icc ((5059:ℝ)/8000) ((10127:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf44 leaf45
private theorem node46_48 :
    ∀ r ∈ Set.Icc ((10127:ℝ)/16000) ((1267:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf46 leaf47
private theorem node44_48 :
    ∀ r ∈ Set.Icc ((5059:ℝ)/8000) ((1267:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node44_46 node46_48
private theorem node40_48 :
    ∀ r ∈ Set.Icc ((101:ℝ)/160) ((1267:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node40_44 node44_48
private theorem node32_48 :
    ∀ r ∈ Set.Icc ((629:ℝ)/1000) ((1267:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node32_40 node40_48
private theorem node48_50 :
    ∀ r ∈ Set.Icc ((1267:ℝ)/2000) ((2029:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf48 leaf49
private theorem node50_52 :
    ∀ r ∈ Set.Icc ((2029:ℝ)/3200) ((5077:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf50 leaf51
private theorem node48_52 :
    ∀ r ∈ Set.Icc ((1267:ℝ)/2000) ((5077:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node48_50 node50_52
private theorem node52_54 :
    ∀ r ∈ Set.Icc ((5077:ℝ)/8000) ((10163:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf52 leaf53
private theorem node54_56 :
    ∀ r ∈ Set.Icc ((10163:ℝ)/16000) ((2543:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf54 leaf55
private theorem node52_56 :
    ∀ r ∈ Set.Icc ((5077:ℝ)/8000) ((2543:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node52_54 node54_56
private theorem node48_56 :
    ∀ r ∈ Set.Icc ((1267:ℝ)/2000) ((2543:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node48_52 node52_56
private theorem node56_58 :
    ∀ r ∈ Set.Icc ((2543:ℝ)/4000) ((10181:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf56 leaf57
private theorem node58_60 :
    ∀ r ∈ Set.Icc ((10181:ℝ)/16000) ((1019:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf58 leaf59
private theorem node56_60 :
    ∀ r ∈ Set.Icc ((2543:ℝ)/4000) ((1019:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node56_58 node58_60
private theorem node60_62 :
    ∀ r ∈ Set.Icc ((1019:ℝ)/1600) ((10199:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf60 leaf61
private theorem node62_64 :
    ∀ r ∈ Set.Icc ((10199:ℝ)/16000) ((319:ℝ)/500), model r < (cap:ℝ) :=
  interval_join leaf62 leaf63
private theorem node60_64 :
    ∀ r ∈ Set.Icc ((1019:ℝ)/1600) ((319:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node60_62 node62_64
private theorem node56_64 :
    ∀ r ∈ Set.Icc ((2543:ℝ)/4000) ((319:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node56_60 node60_64
private theorem node48_64 :
    ∀ r ∈ Set.Icc ((1267:ℝ)/2000) ((319:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node48_56 node56_64
private theorem node32_64 :
    ∀ r ∈ Set.Icc ((629:ℝ)/1000) ((319:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node32_48 node48_64
private theorem node0_64 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((319:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node0_32 node32_64
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((319:ℝ)/500), model r < (cap:ℝ) := node0_64
end N11Formalization.C450FirstRadialG01
#check @N11Formalization.C450FirstRadialG01.bound
#print axioms N11Formalization.C450FirstRadialG01.bound
