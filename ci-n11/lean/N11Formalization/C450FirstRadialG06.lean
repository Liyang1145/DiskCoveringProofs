import N11Formalization.C450FirstRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstRadialG06
open C450FirstRadialKernel
def packet0 : Packet := ⟨((71:ℚ)/100),((22729:ℚ)/32000),((1464038173:ℚ)/5000000000),((3792370249:ℚ)/10000000000)⟩
theorem valid0 : Valid packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((71:ℝ)/100) ((22729:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((22729:ℚ)/32000),((11369:ℚ)/16000),((2931461759:ℚ)/10000000000),((472795203:ℚ)/1250000000)⟩
theorem valid1 : Valid packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((22729:ℝ)/32000) ((11369:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((11369:ℚ)/16000),((22747:ℚ)/32000),((2934836859:ℚ)/10000000000),((1886163863:ℚ)/5000000000)⟩
theorem valid2 : Valid packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((11369:ℝ)/16000) ((22747:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((22747:ℚ)/32000),((5689:ℚ)/8000),((2938201687:ℚ)/10000000000),((3762268353:ℚ)/10000000000)⟩
theorem valid3 : Valid packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((22747:ℝ)/32000) ((5689:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((5689:ℚ)/8000),((4553:ℚ)/6400),((2941556287:ℚ)/10000000000),((3752183299:ℚ)/10000000000)⟩
theorem valid4 : Valid packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((5689:ℝ)/8000) ((4553:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((4553:ℚ)/6400),((11387:ℚ)/16000),((2944900699:ℚ)/10000000000),((3742072357:ℚ)/10000000000)⟩
theorem valid5 : Valid packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((4553:ℝ)/6400) ((11387:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((11387:ℚ)/16000),((22783:ℚ)/32000),((2948234967:ℚ)/10000000000),((746387063:ℚ)/2000000000)⟩
theorem valid6 : Valid packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((11387:ℝ)/16000) ((22783:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((22783:ℚ)/32000),((2849:ℚ)/4000),((295155913:ℚ)/1000000000),((93044299:ℚ)/250000000)⟩
theorem valid7 : Valid packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((22783:ℝ)/32000) ((2849:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2849:ℚ)/4000),((22801:ℚ)/32000),((2954873231:ℚ)/10000000000),((148463283:ℚ)/400000000)⟩
theorem valid8 : Valid packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2849:ℝ)/4000) ((22801:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((22801:ℚ)/32000),((2281:ℚ)/3200),((2958177311:ℚ)/10000000000),((1850682721:ℚ)/5000000000)⟩
theorem valid9 : Valid packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((22801:ℝ)/32000) ((2281:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((2281:ℚ)/3200),((22819:ℚ)/32000),((185091963:ℚ)/625000000),((922780459:ℚ)/2500000000)⟩
theorem valid10 : Valid packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((2281:ℝ)/3200) ((22819:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((22819:ℚ)/32000),((5707:ℚ)/8000),((592951113:ℚ)/2000000000),((1840425517:ℚ)/5000000000)⟩
theorem valid11 : Valid packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((22819:ℝ)/32000) ((5707:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((5707:ℚ)/8000),((22837:ℚ)/32000),((2968029821:ℚ)/10000000000),((734110561:ℚ)/2000000000)⟩
theorem valid12 : Valid packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((5707:ℝ)/8000) ((22837:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((22837:ℚ)/32000),((11423:ℚ)/16000),((594258843:ℚ)/2000000000),((1830113459:ℚ)/5000000000)⟩
theorem valid13 : Valid packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((22837:ℝ)/32000) ((11423:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((11423:ℚ)/16000),((4571:ℚ)/6400),((1487274393:ℚ)/5000000000),((3649873139:ℚ)/10000000000)⟩
theorem valid14 : Valid packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((11423:ℝ)/16000) ((4571:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((4571:ℚ)/6400),((1429:ℚ)/2000),((119111743:ℚ)/400000000),((909872807:ℚ)/2500000000)⟩
theorem valid15 : Valid packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((4571:ℝ)/6400) ((1429:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((1429:ℚ)/2000),((22873:ℚ)/32000),((2981028619:ℚ)/10000000000),((226817559:ℚ)/625000000)⟩
theorem valid16 : Valid packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((1429:ℝ)/2000) ((22873:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((22873:ℚ)/32000),((11441:ℚ)/16000),((1492126979:ℚ)/5000000000),((3618642041:ℚ)/10000000000)⟩
theorem valid17 : Valid packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((22873:ℝ)/32000) ((11441:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((11441:ℚ)/16000),((22891:ℚ)/32000),((2987469629:ℚ)/10000000000),((3608174271:ℚ)/10000000000)⟩
theorem valid18 : Valid packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((11441:ℝ)/16000) ((22891:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((22891:ℚ)/32000),((229:ℚ)/320),((2990675671:ℚ)/10000000000),((3597677381:ℚ)/10000000000)⟩
theorem valid19 : Valid packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((22891:ℝ)/32000) ((229:ℝ)/320), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((229:ℚ)/320),((22909:ℚ)/32000),((74846803:ℚ)/250000000),((717430223:ℚ)/2000000000)⟩
theorem valid20 : Valid packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((229:ℝ)/320) ((22909:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((22909:ℚ)/32000),((11459:ℚ)/16000),((374632377:ℚ)/1250000000),((3576595213:ℚ)/10000000000)⟩
theorem valid21 : Valid packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((22909:ℝ)/32000) ((11459:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((11459:ℚ)/16000),((22927:ℚ)/32000),((1500118197:ℚ)/5000000000),((3566009413:ℚ)/10000000000)⟩
theorem valid22 : Valid packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((11459:ℝ)/16000) ((22927:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((22927:ℚ)/32000),((2867:ℚ)/4000),((750851073:ℚ)/2500000000),((711078689:ℚ)/2000000000)⟩
theorem valid23 : Valid packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((22927:ℝ)/32000) ((2867:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((2867:ℚ)/4000),((4589:ℚ)/6400),((3006562747:ℚ)/10000000000),((22154669:ℚ)/62500000)⟩
theorem valid24 : Valid packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((2867:ℝ)/4000) ((4589:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((4589:ℚ)/6400),((11477:ℚ)/16000),((1504855897:ℚ)/5000000000),((3534069921:ℚ)/10000000000)⟩
theorem valid25 : Valid packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((4589:ℝ)/6400) ((11477:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((11477:ℚ)/16000),((22963:ℚ)/32000),((3012851471:ℚ)/10000000000),((220210113:ℚ)/625000000)⟩
theorem valid26 : Valid packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((11477:ℝ)/16000) ((22963:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((22963:ℚ)/32000),((5743:ℚ)/8000),((3015981813:ℚ)/10000000000),((3512622419:ℚ)/10000000000)⟩
theorem valid27 : Valid packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((22963:ℝ)/32000) ((5743:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((5743:ℚ)/8000),((22981:ℚ)/32000),((603820571:ℚ)/2000000000),((437731433:ℚ)/1250000000)⟩
theorem valid28 : Valid packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((5743:ℝ)/8000) ((22981:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((22981:ℚ)/32000),((2299:ℚ)/3200),((1511107317:ℚ)/5000000000),((872762163:ℚ)/2500000000)⟩
theorem valid29 : Valid packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((22981:ℝ)/32000) ((2299:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((2299:ℚ)/3200),((22999:ℚ)/32000),((47270581:ℚ)/156250000),((870053421:ℚ)/2500000000)⟩
theorem valid30 : Valid packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((2299:ℝ)/3200) ((22999:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((22999:ℚ)/32000),((719:ℚ)/1000),((3028410541:ℚ)/10000000000),((173467313:ℚ)/500000000)⟩
theorem valid31 : Valid packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((22999:ℝ)/32000) ((719:ℝ)/1000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((719:ℚ)/1000),((23017:ℚ)/32000),((3031494739:ℚ)/10000000000),((3458446073:ℚ)/10000000000)⟩
theorem valid32 : Valid packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((719:ℝ)/1000) ((23017:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((23017:ℚ)/32000),((11513:ℚ)/16000),((758642453:ℚ)/2500000000),((3447512811:ℚ)/10000000000)⟩
theorem valid33 : Valid packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((23017:ℝ)/32000) ((11513:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((11513:ℚ)/16000),((4607:ℚ)/6400),((759408949:ℚ)/2500000000),((42956827:ℚ)/125000000)⟩
theorem valid34 : Valid packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((11513:ℝ)/16000) ((4607:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((4607:ℚ)/6400),((5761:ℚ)/8000),((3040692723:ℚ)/10000000000),((856386449:ℚ)/2500000000)⟩
theorem valid35 : Valid packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((4607:ℝ)/6400) ((5761:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((5761:ℚ)/8000),((23053:ℚ)/32000),((760935157:ℚ)/2500000000),((853627849:ℚ)/2500000000)⟩
theorem valid36 : Valid packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((5761:ℝ)/8000) ((23053:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((23053:ℚ)/32000),((11531:ℚ)/16000),((609355909:ℚ)/2000000000),((27227541:ℚ)/80000000)⟩
theorem valid37 : Valid packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((23053:ℝ)/32000) ((11531:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((11531:ℚ)/16000),((23071:ℚ)/32000),((1524904753:ℚ)/5000000000),((3392339149:ℚ)/10000000000)⟩
theorem valid38 : Valid packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((11531:ℝ)/16000) ((23071:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((23071:ℚ)/32000),((577:ℚ)/800),((1526415273:ℚ)/5000000000),((5409921:ℚ)/16000000)⟩
theorem valid39 : Valid packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((23071:ℝ)/32000) ((577:ℝ)/800), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((577:ℚ)/800),((23089:ℚ)/32000),((381980337:ℚ)/1250000000),((210626669:ℚ)/625000000)⟩
theorem valid40 : Valid packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((577:ℝ)/800) ((23089:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((23089:ℚ)/32000),((11549:ℚ)/16000),((305884599:ℚ)/1000000000),((3358817033:ℚ)/10000000000)⟩
theorem valid41 : Valid packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((23089:ℝ)/32000) ((11549:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((11549:ℚ)/16000),((23107:ℚ)/32000),((3061840459:ℚ)/10000000000),((3347571253:ℚ)/10000000000)⟩
theorem valid42 : Valid packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((11549:ℝ)/16000) ((23107:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((23107:ℚ)/32000),((5779:ℚ)/8000),((3064826137:ℚ)/10000000000),((3336288997:ℚ)/10000000000)⟩
theorem valid43 : Valid packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((23107:ℝ)/32000) ((5779:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((5779:ℚ)/8000),((185:ℚ)/256),((191737691:ℚ)/625000000),((664993979:ℚ)/2000000000)⟩
theorem valid44 : Valid packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((5779:ℝ)/8000) ((185:ℝ)/256), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((185:ℚ)/256),((11567:ℚ)/16000),((3070771247:ℚ)/10000000000),((3313613567:ℚ)/10000000000)⟩
theorem valid45 : Valid packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((185:ℝ)/256) ((11567:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet46 : Packet := ⟨((11567:ℚ)/16000),((23143:ℚ)/32000),((1536865371:ℚ)/5000000000),((330221963:ℚ)/1000000000)⟩
theorem valid46 : Valid packet46 := by
  constructor <;> decide +kernel
private theorem leaf46 : ∀ r ∈ Set.Icc ((11567:ℝ)/16000) ((23143:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet46 valid46 r
    (by simpa only [packet46,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet47 : Packet := ⟨((23143:ℚ)/32000),((1447:ℚ)/2000),((769170393:ℚ)/2500000000),((3290787693:ℚ)/10000000000)⟩
theorem valid47 : Valid packet47 := by
  constructor <;> decide +kernel
private theorem leaf47 : ∀ r ∈ Set.Icc ((23143:ℝ)/32000) ((1447:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet47 valid47 r
    (by simpa only [packet47,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet48 : Packet := ⟨((1447:ℚ)/2000),((23161:ℚ)/32000),((3079623769:ℚ)/10000000000),((3279317357:ℚ)/10000000000)⟩
theorem valid48 : Valid packet48 := by
  constructor <;> decide +kernel
private theorem leaf48 : ∀ r ∈ Set.Icc ((1447:ℝ)/2000) ((23161:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet48 valid48 r
    (by simpa only [packet48,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet49 : Packet := ⟨((23161:ℚ)/32000),((2317:ℚ)/3200),((3082557363:ℚ)/10000000000),((1633904109:ℚ)/5000000000)⟩
theorem valid49 : Valid packet49 := by
  constructor <;> decide +kernel
private theorem leaf49 : ∀ r ∈ Set.Icc ((23161:ℝ)/32000) ((2317:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet49 valid49 r
    (by simpa only [packet49,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet50 : Packet := ⟨((2317:ℚ)/3200),((23179:ℚ)/32000),((1542741193:ℚ)/5000000000),((3256259863:ℚ)/10000000000)⟩
theorem valid50 : Valid packet50 := by
  constructor <;> decide +kernel
private theorem leaf50 : ∀ r ∈ Set.Icc ((2317:ℝ)/3200) ((23179:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet50 valid50 r
    (by simpa only [packet50,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet51 : Packet := ⟨((23179:ℚ)/32000),((5797:ℚ)/8000),((3088398869:ℚ)/10000000000),((207659:ℚ)/640000)⟩
theorem valid51 : Valid packet51 := by
  constructor <;> decide +kernel
private theorem leaf51 : ∀ r ∈ Set.Icc ((23179:ℝ)/32000) ((5797:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet51 valid51 r
    (by simpa only [packet51,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet52 : Packet := ⟨((5797:ℚ)/8000),((23197:ℚ)/32000),((3091306841:ℚ)/10000000000),((1616521913:ℚ)/5000000000)⟩
theorem valid52 : Valid packet52 := by
  constructor <;> decide +kernel
private theorem leaf52 : ∀ r ∈ Set.Icc ((5797:ℝ)/8000) ((23197:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet52 valid52 r
    (by simpa only [packet52,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet53 : Packet := ⟨((23197:ℚ)/32000),((11603:ℚ)/16000),((3094206333:ℚ)/10000000000),((3221375281:ℚ)/10000000000)⟩
theorem valid53 : Valid packet53 := by
  constructor <;> decide +kernel
private theorem leaf53 : ∀ r ∈ Set.Icc ((23197:ℝ)/32000) ((11603:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet53 valid53 r
    (by simpa only [packet53,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet54 : Packet := ⟨((11603:ℚ)/16000),((4643:ℚ)/6400),((24776779:ℚ)/80000000),((16048329:ℚ)/50000000)⟩
theorem valid54 : Valid packet54 := by
  constructor <;> decide +kernel
private theorem leaf54 : ∀ r ∈ Set.Icc ((11603:ℝ)/16000) ((4643:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet54 valid54 r
    (by simpa only [packet54,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet55 : Packet := ⟨((4643:ℚ)/6400),((2903:ℚ)/4000),((3099979997:ℚ)/10000000000),((319791493:ℚ)/1000000000)⟩
theorem valid55 : Valid packet55 := by
  constructor <;> decide +kernel
private theorem leaf55 : ∀ r ∈ Set.Icc ((4643:ℝ)/6400) ((2903:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet55 valid55 r
    (by simpa only [packet55,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet56 : Packet := ⟨((2903:ℚ)/4000),((23233:ℚ)/32000),((3102854229:ℚ)/10000000000),((398265277:ℚ)/1250000000)⟩
theorem valid56 : Valid packet56 := by
  constructor <;> decide +kernel
private theorem leaf56 : ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((23233:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet56 valid56 r
    (by simpa only [packet56,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet57 : Packet := ⟨((23233:ℚ)/32000),((11621:ℚ)/16000),((31057201:ℚ)/100000000),((793571797:ℚ)/2500000000)⟩
theorem valid57 : Valid packet57 := by
  constructor <;> decide +kernel
private theorem leaf57 : ∀ r ∈ Set.Icc ((23233:ℝ)/32000) ((11621:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet57 valid57 r
    (by simpa only [packet57,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet58 : Packet := ⟨((11621:ℚ)/16000),((23251:ℚ)/32000),((3108577639:ℚ)/10000000000),((3162409373:ℚ)/10000000000)⟩
theorem valid58 : Valid packet58 := by
  constructor <;> decide +kernel
private theorem leaf58 : ∀ r ∈ Set.Icc ((11621:ℝ)/16000) ((23251:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet58 valid58 r
    (by simpa only [packet58,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet59 : Packet := ⟨((23251:ℚ)/32000),((1163:ℚ)/1600),((777856719:ℚ)/2500000000),((787622071:ℚ)/2500000000)⟩
theorem valid59 : Valid packet59 := by
  constructor <;> decide +kernel
private theorem leaf59 : ∀ r ∈ Set.Icc ((23251:ℝ)/32000) ((1163:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet59 valid59 r
    (by simpa only [packet59,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet60 : Packet := ⟨((1163:ℚ)/1600),((23269:ℚ)/32000),((9732087:ℚ)/31250000),((313852343:ℚ)/1000000000)⟩
theorem valid60 : Valid packet60 := by
  constructor <;> decide +kernel
private theorem leaf60 : ∀ r ∈ Set.Icc ((1163:ℝ)/1600) ((23269:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet60 valid60 r
    (by simpa only [packet60,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet61 : Packet := ⟨((23269:ℚ)/32000),((11639:ℚ)/16000),((3117100559:ℚ)/10000000000),((3126514307:ℚ)/10000000000)⟩
theorem valid61 : Valid packet61 := by
  constructor <;> decide +kernel
private theorem leaf61 : ∀ r ∈ Set.Icc ((23269:ℝ)/32000) ((11639:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet61 valid61 r
    (by simpa only [packet61,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet62 : Packet := ⟨((11639:ℚ)/16000),((23287:ℚ)/32000),((3119925061:ℚ)/10000000000),((3114460403:ℚ)/10000000000)⟩
theorem valid62 : Valid packet62 := by
  constructor <;> decide +kernel
private theorem leaf62 : ∀ r ∈ Set.Icc ((11639:ℝ)/16000) ((23287:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet62 valid62 r
    (by simpa only [packet62,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet63 : Packet := ⟨((23287:ℚ)/32000),((91:ℚ)/125),((3122741377:ℚ)/10000000000),((1551180597:ℚ)/5000000000)⟩
theorem valid63 : Valid packet63 := by
  constructor <;> decide +kernel
private theorem leaf63 : ∀ r ∈ Set.Icc ((23287:ℝ)/32000) ((91:ℝ)/125), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet63 valid63 r
    (by simpa only [packet63,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((71:ℝ)/100) ((11369:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((11369:ℝ)/16000) ((5689:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((71:ℝ)/100) ((5689:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((5689:ℝ)/8000) ((11387:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((11387:ℝ)/16000) ((2849:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((5689:ℝ)/8000) ((2849:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((71:ℝ)/100) ((2849:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((2849:ℝ)/4000) ((2281:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((2281:ℝ)/3200) ((5707:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((2849:ℝ)/4000) ((5707:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((5707:ℝ)/8000) ((11423:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((11423:ℝ)/16000) ((1429:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((5707:ℝ)/8000) ((1429:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((2849:ℝ)/4000) ((1429:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((71:ℝ)/100) ((1429:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((1429:ℝ)/2000) ((11441:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((11441:ℝ)/16000) ((229:ℝ)/320), model r < (cap:ℝ) :=
  interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((1429:ℝ)/2000) ((229:ℝ)/320), model r < (cap:ℝ) :=
  interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((229:ℝ)/320) ((11459:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((11459:ℝ)/16000) ((2867:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((229:ℝ)/320) ((2867:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((1429:ℝ)/2000) ((2867:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((2867:ℝ)/4000) ((11477:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((11477:ℝ)/16000) ((5743:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((2867:ℝ)/4000) ((5743:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((5743:ℝ)/8000) ((2299:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((2299:ℝ)/3200) ((719:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((5743:ℝ)/8000) ((719:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((2867:ℝ)/4000) ((719:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((1429:ℝ)/2000) ((719:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((71:ℝ)/100) ((719:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node0_16 node16_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((719:ℝ)/1000) ((11513:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf32 leaf33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((11513:ℝ)/16000) ((5761:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf34 leaf35
private theorem node32_36 :
    ∀ r ∈ Set.Icc ((719:ℝ)/1000) ((5761:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node32_34 node34_36
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((5761:ℝ)/8000) ((11531:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf36 leaf37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((11531:ℝ)/16000) ((577:ℝ)/800), model r < (cap:ℝ) :=
  interval_join leaf38 leaf39
private theorem node36_40 :
    ∀ r ∈ Set.Icc ((5761:ℝ)/8000) ((577:ℝ)/800), model r < (cap:ℝ) :=
  interval_join node36_38 node38_40
private theorem node32_40 :
    ∀ r ∈ Set.Icc ((719:ℝ)/1000) ((577:ℝ)/800), model r < (cap:ℝ) :=
  interval_join node32_36 node36_40
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((577:ℝ)/800) ((11549:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf40 leaf41
private theorem node42_44 :
    ∀ r ∈ Set.Icc ((11549:ℝ)/16000) ((5779:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf42 leaf43
private theorem node40_44 :
    ∀ r ∈ Set.Icc ((577:ℝ)/800) ((5779:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node40_42 node42_44
private theorem node44_46 :
    ∀ r ∈ Set.Icc ((5779:ℝ)/8000) ((11567:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf44 leaf45
private theorem node46_48 :
    ∀ r ∈ Set.Icc ((11567:ℝ)/16000) ((1447:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf46 leaf47
private theorem node44_48 :
    ∀ r ∈ Set.Icc ((5779:ℝ)/8000) ((1447:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node44_46 node46_48
private theorem node40_48 :
    ∀ r ∈ Set.Icc ((577:ℝ)/800) ((1447:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node40_44 node44_48
private theorem node32_48 :
    ∀ r ∈ Set.Icc ((719:ℝ)/1000) ((1447:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node32_40 node40_48
private theorem node48_50 :
    ∀ r ∈ Set.Icc ((1447:ℝ)/2000) ((2317:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf48 leaf49
private theorem node50_52 :
    ∀ r ∈ Set.Icc ((2317:ℝ)/3200) ((5797:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf50 leaf51
private theorem node48_52 :
    ∀ r ∈ Set.Icc ((1447:ℝ)/2000) ((5797:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node48_50 node50_52
private theorem node52_54 :
    ∀ r ∈ Set.Icc ((5797:ℝ)/8000) ((11603:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf52 leaf53
private theorem node54_56 :
    ∀ r ∈ Set.Icc ((11603:ℝ)/16000) ((2903:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf54 leaf55
private theorem node52_56 :
    ∀ r ∈ Set.Icc ((5797:ℝ)/8000) ((2903:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node52_54 node54_56
private theorem node48_56 :
    ∀ r ∈ Set.Icc ((1447:ℝ)/2000) ((2903:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node48_52 node52_56
private theorem node56_58 :
    ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((11621:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf56 leaf57
private theorem node58_60 :
    ∀ r ∈ Set.Icc ((11621:ℝ)/16000) ((1163:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf58 leaf59
private theorem node56_60 :
    ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((1163:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node56_58 node58_60
private theorem node60_62 :
    ∀ r ∈ Set.Icc ((1163:ℝ)/1600) ((11639:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf60 leaf61
private theorem node62_64 :
    ∀ r ∈ Set.Icc ((11639:ℝ)/16000) ((91:ℝ)/125), model r < (cap:ℝ) :=
  interval_join leaf62 leaf63
private theorem node60_64 :
    ∀ r ∈ Set.Icc ((1163:ℝ)/1600) ((91:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node60_62 node62_64
private theorem node56_64 :
    ∀ r ∈ Set.Icc ((2903:ℝ)/4000) ((91:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node56_60 node60_64
private theorem node48_64 :
    ∀ r ∈ Set.Icc ((1447:ℝ)/2000) ((91:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node48_56 node56_64
private theorem node32_64 :
    ∀ r ∈ Set.Icc ((719:ℝ)/1000) ((91:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node32_48 node48_64
private theorem node0_64 :
    ∀ r ∈ Set.Icc ((71:ℝ)/100) ((91:ℝ)/125), model r < (cap:ℝ) :=
  interval_join node0_32 node32_64
theorem bound : ∀ r ∈ Set.Icc ((71:ℝ)/100) ((91:ℝ)/125), model r < (cap:ℝ) := node0_64
end N11Formalization.C450FirstRadialG06
#check @N11Formalization.C450FirstRadialG06.bound
#print axioms N11Formalization.C450FirstRadialG06.bound
