import N11Formalization.C450FirstRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstRadialG05
open C450FirstRadialKernel
def packet0 : Packet := ⟨((173:ℚ)/250),((22153:ℚ)/32000),((1343862919:ℚ)/5000000000),((4387976021:ℚ)/10000000000)⟩
theorem valid0 : Valid packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((173:ℝ)/250) ((22153:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((22153:ℚ)/32000),((11081:ℚ)/16000),((134593871:ℚ)/500000000),((4379257443:ℚ)/10000000000)⟩
theorem valid1 : Valid packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((22153:ℝ)/32000) ((11081:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((11081:ℚ)/16000),((22171:ℚ)/32000),((539203023:ℚ)/2000000000),((2185261301:ℚ)/5000000000)⟩
theorem valid2 : Valid packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((11081:ℝ)/16000) ((22171:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((22171:ℚ)/32000),((1109:ℚ)/1600),((540027799:ℚ)/2000000000),((2180885699:ℚ)/5000000000)⟩
theorem valid3 : Valid packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((22171:ℝ)/32000) ((1109:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((1109:ℚ)/1600),((22189:ℚ)/32000),((2704249131:ℚ)/10000000000),((4353003733:ℚ)/10000000000)⟩
theorem valid4 : Valid packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((1109:ℝ)/1600) ((22189:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((22189:ℚ)/32000),((11099:ℚ)/16000),((541669119:ℚ)/2000000000),((1086054877:ℚ)/2500000000)⟩
theorem valid5 : Valid packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((22189:ℝ)/32000) ((11099:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((11099:ℚ)/16000),((22207:ℚ)/32000),((339053557:ℚ)/1250000000),((216770931:ℚ)/500000000)⟩
theorem valid6 : Valid packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((11099:ℝ)/16000) ((22207:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((22207:ℚ)/32000),((2777:ℚ)/4000),((543299557:ℚ)/2000000000),((540825121:ℚ)/1250000000)⟩
theorem valid7 : Valid packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((22207:ℝ)/32000) ((2777:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2777:ℚ)/4000),((889:ℚ)/1280),((54411073:ℚ)/200000000),((4317766449:ℚ)/10000000000)⟩
theorem valid8 : Valid packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2777:ℝ)/4000) ((889:ℝ)/1280), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((889:ℚ)/1280),((11117:ℚ)/16000),((68114903:ℚ)/250000000),((4308914959:ℚ)/10000000000)⟩
theorem valid9 : Valid packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((889:ℝ)/1280) ((11117:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((11117:ℚ)/16000),((22243:ℚ)/32000),((2728625263:ℚ)/10000000000),((4300046393:ℚ)/10000000000)⟩
theorem valid10 : Valid packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((11117:ℝ)/16000) ((22243:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((22243:ℚ)/32000),((5563:ℚ)/8000),((1366320573:ℚ)/5000000000),((1072790161:ℚ)/2500000000)⟩
theorem valid11 : Valid packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((22243:ℝ)/32000) ((5563:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((5563:ℚ)/8000),((22261:ℚ)/32000),((547328767:ℚ)/2000000000),((856451521:ℚ)/2000000000)⟩
theorem valid12 : Valid packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((5563:ℝ)/8000) ((22261:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((22261:ℚ)/32000),((2227:ℚ)/3200),((2740633397:ℚ)/10000000000),((4273337167:ℚ)/10000000000)⟩
theorem valid13 : Valid packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((22261:ℝ)/32000) ((2227:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((2227:ℚ)/3200),((22279:ℚ)/32000),((2744609897:ℚ)/10000000000),((2132199611:ℚ)/5000000000)⟩
theorem valid14 : Valid packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((2227:ℝ)/3200) ((22279:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((22279:ℚ)/32000),((1393:ℚ)/2000),((13742867:ℚ)/50000000),((2127721829:ℚ)/5000000000)⟩
theorem valid15 : Valid packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((22279:ℝ)/32000) ((1393:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((1393:ℚ)/2000),((22297:ℚ)/32000),((2752523971:ℚ)/10000000000),((1061617591:ℚ)/2500000000)⟩
theorem valid16 : Valid packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((1393:ℝ)/2000) ((22297:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((22297:ℚ)/32000),((11153:ℚ)/16000),((2756461671:ℚ)/10000000000),((4237479227:ℚ)/10000000000)⟩
theorem valid17 : Valid packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((22297:ℝ)/32000) ((11153:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((11153:ℚ)/16000),((4463:ℚ)/6400),((2760386567:ℚ)/10000000000),((4228470131:ℚ)/10000000000)⟩
theorem valid18 : Valid packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((11153:ℝ)/16000) ((4463:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((4463:ℚ)/6400),((5581:ℚ)/8000),((1382149359:ℚ)/5000000000),((4219442963:ℚ)/10000000000)⟩
theorem valid19 : Valid packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((4463:ℝ)/6400) ((5581:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((5581:ℚ)/8000),((22333:ℚ)/32000),((2768198189:ℚ)/10000000000),((2105198803:ℚ)/5000000000)⟩
theorem valid20 : Valid packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((5581:ℝ)/8000) ((22333:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((22333:ℚ)/32000),((11171:ℚ)/16000),((2772085039:ℚ)/10000000000),((210066697:ℚ)/500000000)⟩
theorem valid21 : Valid packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((22333:ℝ)/32000) ((11171:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((11171:ℚ)/16000),((22351:ℚ)/32000),((2775959331:ℚ)/10000000000),((4192251849:ℚ)/10000000000)⟩
theorem valid22 : Valid packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((11171:ℝ)/16000) ((22351:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((22351:ℚ)/32000),((559:ℚ)/800),((22238569:ℚ)/80000000),((418315121:ℚ)/1000000000)⟩
theorem valid23 : Valid packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((22351:ℝ)/32000) ((559:ℝ)/800), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((559:ℚ)/800),((22369:ℚ)/32000),((2783670481:ℚ)/10000000000),((4174031903:ℚ)/10000000000)⟩
theorem valid24 : Valid packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((559:ℝ)/800) ((22369:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((22369:ℚ)/32000),((11189:ℚ)/16000),((1393753729:ℚ)/5000000000),((832978761:ℚ)/2000000000)⟩
theorem valid25 : Valid packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((22369:ℝ)/32000) ((11189:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((11189:ℚ)/16000),((22387:ℚ)/32000),((558266423:ℚ)/2000000000),((415573679:ℚ)/1000000000)⟩
theorem valid26 : Valid packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((11189:ℝ)/16000) ((22387:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((22387:ℚ)/32000),((5599:ℚ)/8000),((279514451:ℚ)/1000000000),((2073280367:ℚ)/5000000000)⟩
theorem valid27 : Valid packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((22387:ℝ)/32000) ((5599:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((5599:ℚ)/8000),((4481:ℚ)/6400),((2798944703:ℚ)/10000000000),((4137365509:ℚ)/10000000000)⟩
theorem valid28 : Valid packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((5599:ℝ)/8000) ((4481:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((4481:ℚ)/6400),((11207:ℚ)/16000),((2802732749:ℚ)/10000000000),((1032037747:ℚ)/2500000000)⟩
theorem valid29 : Valid packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((4481:ℝ)/6400) ((11207:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((11207:ℚ)/16000),((22423:ℚ)/32000),((1403254353:ℚ)/5000000000),((4118917039:ℚ)/10000000000)⟩
theorem valid30 : Valid packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((11207:ℝ)/16000) ((22423:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((22423:ℚ)/32000),((701:ℚ)/1000),((351284079:ℚ)/1250000000),((1027415883:ℚ)/2500000000)⟩
theorem valid31 : Valid packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((22423:ℝ)/32000) ((701:ℝ)/1000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((701:ℚ)/1000),((22441:ℚ)/32000),((140701229:ℚ)/500000000),((2050195167:ℚ)/5000000000)⟩
theorem valid32 : Valid packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((701:ℝ)/1000) ((22441:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((22441:ℚ)/32000),((449:ℚ)/640),((11006893:ℚ)/39062500),((409109731:ℚ)/1000000000)⟩
theorem valid33 : Valid packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((22441:ℝ)/32000) ((449:ℝ)/640), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((449:ℚ)/640),((22459:ℚ)/32000),((2821492771:ℚ)/10000000000),((2040892163:ℚ)/5000000000)⟩
theorem valid34 : Valid packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((449:ℝ)/640) ((22459:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((22459:ℚ)/32000),((5617:ℚ)/8000),((2825209123:ℚ)/10000000000),((4072451243:ℚ)/10000000000)⟩
theorem valid35 : Valid packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((22459:ℝ)/32000) ((5617:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((5617:ℚ)/8000),((22477:ℚ)/32000),((1414456859:ℚ)/5000000000),((2031548961:ℚ)/5000000000)⟩
theorem valid36 : Valid packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((5617:ℝ)/8000) ((22477:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((22477:ℚ)/32000),((11243:ℚ)/16000),((283260661:ℚ)/1000000000),((63339441:ℚ)/156250000)⟩
theorem valid37 : Valid packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((22477:ℝ)/32000) ((11243:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((11243:ℚ)/16000),((4499:ℚ)/6400),((2836287853:ℚ)/10000000000),((2022165003:ℚ)/5000000000)⟩
theorem valid38 : Valid packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((11243:ℝ)/16000) ((4499:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((4499:ℚ)/6400),((2813:ℚ)/4000),((2839957499:ℚ)/10000000000),((32279321:ℚ)/80000000)⟩
theorem valid39 : Valid packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((4499:ℝ)/6400) ((2813:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((2813:ℚ)/4000),((22513:ℚ)/32000),((1421807801:ℚ)/5000000000),((805095887:ℚ)/2000000000)⟩
theorem valid40 : Valid packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((2813:ℝ)/4000) ((22513:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((22513:ℚ)/32000),((11261:ℚ)/16000),((711815553:ℚ)/2500000000),((4016022789:ℚ)/10000000000)⟩
theorem valid41 : Valid packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((22513:ℝ)/32000) ((11261:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((11261:ℚ)/16000),((22531:ℚ)/32000),((1425448691:ℚ)/5000000000),((2003272519:ℚ)/5000000000)⟩
theorem valid42 : Valid packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((11261:ℝ)/16000) ((22531:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((22531:ℚ)/32000),((1127:ℚ)/1600),((2854521163:ℚ)/10000000000),((249815377:ℚ)/625000000)⟩
theorem valid43 : Valid packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((22531:ℝ)/32000) ((1127:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((1127:ℚ)/1600),((22549:ℚ)/32000),((1429066803:ℚ)/5000000000),((3987525619:ℚ)/10000000000)⟩
theorem valid44 : Valid packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((1127:ℝ)/1600) ((22549:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((22549:ℚ)/32000),((11279:ℚ)/16000),((1430867381:ℚ)/5000000000),((994495911:ℚ)/2500000000)⟩
theorem valid45 : Valid packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((22549:ℝ)/32000) ((11279:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet46 : Packet := ⟨((11279:ℚ)/16000),((22567:ℚ)/32000),((2865324679:ℚ)/10000000000),((3968419951:ℚ)/10000000000)⟩
theorem valid46 : Valid packet46 := by
  constructor <;> decide +kernel
private theorem leaf46 : ∀ r ∈ Set.Icc ((11279:ℝ)/16000) ((22567:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet46 valid46 r
    (by simpa only [packet46,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet47 : Packet := ⟨((22567:ℚ)/32000),((1411:ℚ)/2000),((2868903409:ℚ)/10000000000),((247427149:ℚ)/625000000)⟩
theorem valid47 : Valid packet47 := by
  constructor <;> decide +kernel
private theorem leaf47 : ∀ r ∈ Set.Icc ((22567:ℝ)/32000) ((1411:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet47 valid47 r
    (by simpa only [packet47,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet48 : Packet := ⟨((1411:ℚ)/2000),((4517:ℚ)/6400),((2872471:ℚ)/10000000),((3949226781:ℚ)/10000000000)⟩
theorem valid48 : Valid packet48 := by
  constructor <;> decide +kernel
private theorem leaf48 : ∀ r ∈ Set.Icc ((1411:ℝ)/2000) ((4517:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet48 valid48 r
    (by simpa only [packet48,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet49 : Packet := ⟨((4517:ℚ)/6400),((11297:ℚ)/16000),((2876027501:ℚ)/10000000000),((1969798491:ℚ)/5000000000)⟩
theorem valid49 : Valid packet49 := by
  constructor <;> decide +kernel
private theorem leaf49 : ∀ r ∈ Set.Icc ((4517:ℝ)/6400) ((11297:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet49 valid49 r
    (by simpa only [packet49,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet50 : Packet := ⟨((11297:ℚ)/16000),((22603:ℚ)/32000),((2879572961:ℚ)/10000000000),((3929944823:ℚ)/10000000000)⟩
theorem valid50 : Valid packet50 := by
  constructor <;> decide +kernel
private theorem leaf50 : ∀ r ∈ Set.Icc ((11297:ℝ)/16000) ((22603:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet50 valid50 r
    (by simpa only [packet50,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet51 : Packet := ⟨((22603:ℚ)/32000),((5653:ℚ)/8000),((2883107427:ℚ)/10000000000),((3920270139:ℚ)/10000000000)⟩
theorem valid51 : Valid packet51 := by
  constructor <;> decide +kernel
private theorem leaf51 : ∀ r ∈ Set.Icc ((22603:ℝ)/32000) ((5653:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet51 valid51 r
    (by simpa only [packet51,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet52 : Packet := ⟨((5653:ℚ)/8000),((22621:ℚ)/32000),((721657737:ℚ)/2500000000),((3910572761:ℚ)/10000000000)⟩
theorem valid52 : Valid packet52 := by
  constructor <;> decide +kernel
private theorem leaf52 : ∀ r ∈ Set.Icc ((5653:ℝ)/8000) ((22621:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet52 valid52 r
    (by simpa only [packet52,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet53 : Packet := ⟨((22621:ℚ)/32000),((2263:ℚ)/3200),((2890143571:ℚ)/10000000000),((3900852521:ℚ)/10000000000)⟩
theorem valid53 : Valid packet53 := by
  constructor <;> decide +kernel
private theorem leaf53 : ∀ r ∈ Set.Icc ((22621:ℝ)/32000) ((2263:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet53 valid53 r
    (by simpa only [packet53,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet54 : Packet := ⟨((2263:ℚ)/3200),((22639:ℚ)/32000),((2893645343:ℚ)/10000000000),((1945554623:ℚ)/5000000000)⟩
theorem valid54 : Valid packet54 := by
  constructor <;> decide +kernel
private theorem leaf54 : ∀ r ∈ Set.Icc ((2263:ℝ)/3200) ((22639:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet54 valid54 r
    (by simpa only [packet54,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet55 : Packet := ⟨((22639:ℚ)/32000),((2831:ℚ)/4000),((2897136311:ℚ)/10000000000),((3881342763:ℚ)/10000000000)⟩
theorem valid55 : Valid packet55 := by
  constructor <;> decide +kernel
private theorem leaf55 : ∀ r ∈ Set.Icc ((22639:ℝ)/32000) ((2831:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet55 valid55 r
    (by simpa only [packet55,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet56 : Packet := ⟨((2831:ℚ)/4000),((22657:ℚ)/32000),((72515413:ℚ)/250000000),((774310579:ℚ)/2000000000)⟩
theorem valid56 : Valid packet56 := by
  constructor <;> decide +kernel
private theorem leaf56 : ∀ r ∈ Set.Icc ((2831:ℝ)/4000) ((22657:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet56 valid56 r
    (by simpa only [packet56,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet57 : Packet := ⟨((22657:ℚ)/32000),((11333:ℚ)/16000),((2904086017:ℚ)/10000000000),((772347893:ℚ)/2000000000)⟩
theorem valid57 : Valid packet57 := by
  constructor <;> decide +kernel
private theorem leaf57 : ∀ r ∈ Set.Icc ((22657:ℝ)/32000) ((11333:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet57 valid57 r
    (by simpa only [packet57,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet58 : Packet := ⟨((11333:ℚ)/16000),((907:ℚ)/1280),((181721553:ℚ)/625000000),((962975573:ℚ)/2500000000)⟩
theorem valid58 : Valid packet58 := by
  constructor <;> decide +kernel
private theorem leaf58 : ∀ r ∈ Set.Icc ((11333:ℝ)/16000) ((907:ℝ)/1280), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet58 valid58 r
    (by simpa only [packet58,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet59 : Packet := ⟨((907:ℚ)/1280),((5671:ℚ)/8000),((1455496529:ℚ)/5000000000),((3842041193:ℚ)/10000000000)⟩
theorem valid59 : Valid packet59 := by
  constructor <;> decide +kernel
private theorem leaf59 : ∀ r ∈ Set.Icc ((907:ℝ)/1280) ((5671:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet59 valid59 r
    (by simpa only [packet59,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet60 : Packet := ⟨((5671:ℚ)/8000),((22693:ℚ)/32000),((2914430691:ℚ)/10000000000),((3832155983:ℚ)/10000000000)⟩
theorem valid60 : Valid packet60 := by
  constructor <;> decide +kernel
private theorem leaf60 : ∀ r ∈ Set.Icc ((5671:ℝ)/8000) ((22693:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet60 valid60 r
    (by simpa only [packet60,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet61 : Packet := ⟨((22693:ℚ)/32000),((11351:ℚ)/16000),((5698941:ℚ)/19531250),((152889859:ℚ)/400000000)⟩
theorem valid61 : Valid packet61 := by
  constructor <;> decide +kernel
private theorem leaf61 : ∀ r ∈ Set.Icc ((22693:ℝ)/32000) ((11351:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet61 valid61 r
    (by simpa only [packet61,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet62 : Packet := ⟨((11351:ℚ)/16000),((22711:ℚ)/32000),((1460637203:ℚ)/5000000000),((1906156239:ℚ)/5000000000)⟩
theorem valid62 : Valid packet62 := by
  constructor <;> decide +kernel
private theorem leaf62 : ∀ r ∈ Set.Icc ((11351:ℝ)/16000) ((22711:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet62 valid62 r
    (by simpa only [packet62,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet63 : Packet := ⟨((22711:ℚ)/32000),((71:ℚ)/100),((22849067:ℚ)/78125000),((3802353801:ℚ)/10000000000)⟩
theorem valid63 : Valid packet63 := by
  constructor <;> decide +kernel
private theorem leaf63 : ∀ r ∈ Set.Icc ((22711:ℝ)/32000) ((71:ℝ)/100), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet63 valid63 r
    (by simpa only [packet63,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((173:ℝ)/250) ((11081:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((11081:ℝ)/16000) ((1109:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((173:ℝ)/250) ((1109:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((1109:ℝ)/1600) ((11099:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((11099:ℝ)/16000) ((2777:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((1109:ℝ)/1600) ((2777:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((173:ℝ)/250) ((2777:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((2777:ℝ)/4000) ((11117:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((11117:ℝ)/16000) ((5563:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((2777:ℝ)/4000) ((5563:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((5563:ℝ)/8000) ((2227:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((2227:ℝ)/3200) ((1393:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((5563:ℝ)/8000) ((1393:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((2777:ℝ)/4000) ((1393:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((173:ℝ)/250) ((1393:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((1393:ℝ)/2000) ((11153:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((11153:ℝ)/16000) ((5581:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((1393:ℝ)/2000) ((5581:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((5581:ℝ)/8000) ((11171:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((11171:ℝ)/16000) ((559:ℝ)/800), model r < (cap:ℝ) :=
  interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((5581:ℝ)/8000) ((559:ℝ)/800), model r < (cap:ℝ) :=
  interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((1393:ℝ)/2000) ((559:ℝ)/800), model r < (cap:ℝ) :=
  interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((559:ℝ)/800) ((11189:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((11189:ℝ)/16000) ((5599:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((559:ℝ)/800) ((5599:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((5599:ℝ)/8000) ((11207:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((11207:ℝ)/16000) ((701:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((5599:ℝ)/8000) ((701:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((559:ℝ)/800) ((701:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((1393:ℝ)/2000) ((701:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((173:ℝ)/250) ((701:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node0_16 node16_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((701:ℝ)/1000) ((449:ℝ)/640), model r < (cap:ℝ) :=
  interval_join leaf32 leaf33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((449:ℝ)/640) ((5617:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf34 leaf35
private theorem node32_36 :
    ∀ r ∈ Set.Icc ((701:ℝ)/1000) ((5617:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node32_34 node34_36
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((5617:ℝ)/8000) ((11243:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf36 leaf37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((11243:ℝ)/16000) ((2813:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf38 leaf39
private theorem node36_40 :
    ∀ r ∈ Set.Icc ((5617:ℝ)/8000) ((2813:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node36_38 node38_40
private theorem node32_40 :
    ∀ r ∈ Set.Icc ((701:ℝ)/1000) ((2813:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node32_36 node36_40
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((2813:ℝ)/4000) ((11261:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf40 leaf41
private theorem node42_44 :
    ∀ r ∈ Set.Icc ((11261:ℝ)/16000) ((1127:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf42 leaf43
private theorem node40_44 :
    ∀ r ∈ Set.Icc ((2813:ℝ)/4000) ((1127:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node40_42 node42_44
private theorem node44_46 :
    ∀ r ∈ Set.Icc ((1127:ℝ)/1600) ((11279:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf44 leaf45
private theorem node46_48 :
    ∀ r ∈ Set.Icc ((11279:ℝ)/16000) ((1411:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf46 leaf47
private theorem node44_48 :
    ∀ r ∈ Set.Icc ((1127:ℝ)/1600) ((1411:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node44_46 node46_48
private theorem node40_48 :
    ∀ r ∈ Set.Icc ((2813:ℝ)/4000) ((1411:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node40_44 node44_48
private theorem node32_48 :
    ∀ r ∈ Set.Icc ((701:ℝ)/1000) ((1411:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node32_40 node40_48
private theorem node48_50 :
    ∀ r ∈ Set.Icc ((1411:ℝ)/2000) ((11297:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf48 leaf49
private theorem node50_52 :
    ∀ r ∈ Set.Icc ((11297:ℝ)/16000) ((5653:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf50 leaf51
private theorem node48_52 :
    ∀ r ∈ Set.Icc ((1411:ℝ)/2000) ((5653:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node48_50 node50_52
private theorem node52_54 :
    ∀ r ∈ Set.Icc ((5653:ℝ)/8000) ((2263:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf52 leaf53
private theorem node54_56 :
    ∀ r ∈ Set.Icc ((2263:ℝ)/3200) ((2831:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf54 leaf55
private theorem node52_56 :
    ∀ r ∈ Set.Icc ((5653:ℝ)/8000) ((2831:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node52_54 node54_56
private theorem node48_56 :
    ∀ r ∈ Set.Icc ((1411:ℝ)/2000) ((2831:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node48_52 node52_56
private theorem node56_58 :
    ∀ r ∈ Set.Icc ((2831:ℝ)/4000) ((11333:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf56 leaf57
private theorem node58_60 :
    ∀ r ∈ Set.Icc ((11333:ℝ)/16000) ((5671:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf58 leaf59
private theorem node56_60 :
    ∀ r ∈ Set.Icc ((2831:ℝ)/4000) ((5671:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node56_58 node58_60
private theorem node60_62 :
    ∀ r ∈ Set.Icc ((5671:ℝ)/8000) ((11351:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf60 leaf61
private theorem node62_64 :
    ∀ r ∈ Set.Icc ((11351:ℝ)/16000) ((71:ℝ)/100), model r < (cap:ℝ) :=
  interval_join leaf62 leaf63
private theorem node60_64 :
    ∀ r ∈ Set.Icc ((5671:ℝ)/8000) ((71:ℝ)/100), model r < (cap:ℝ) :=
  interval_join node60_62 node62_64
private theorem node56_64 :
    ∀ r ∈ Set.Icc ((2831:ℝ)/4000) ((71:ℝ)/100), model r < (cap:ℝ) :=
  interval_join node56_60 node60_64
private theorem node48_64 :
    ∀ r ∈ Set.Icc ((1411:ℝ)/2000) ((71:ℝ)/100), model r < (cap:ℝ) :=
  interval_join node48_56 node56_64
private theorem node32_64 :
    ∀ r ∈ Set.Icc ((701:ℝ)/1000) ((71:ℝ)/100), model r < (cap:ℝ) :=
  interval_join node32_48 node48_64
private theorem node0_64 :
    ∀ r ∈ Set.Icc ((173:ℝ)/250) ((71:ℝ)/100), model r < (cap:ℝ) :=
  interval_join node0_32 node32_64
theorem bound : ∀ r ∈ Set.Icc ((173:ℝ)/250) ((71:ℝ)/100), model r < (cap:ℝ) := node0_64
end N11Formalization.C450FirstRadialG05
#check @N11Formalization.C450FirstRadialG05.bound
#print axioms N11Formalization.C450FirstRadialG05.bound
