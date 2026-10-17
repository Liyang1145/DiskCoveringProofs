import N11Formalization.C450FirstRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450FirstRadialG07
open C450FirstRadialKernel
def packet0 : Packet := ⟨((91:ℚ)/125),((4661:ℚ)/6400),((781387383:ℚ)/2500000000),((3090216149:ℚ)/10000000000)⟩
theorem valid0 : Valid packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((91:ℝ)/125) ((4661:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((4661:ℚ)/6400),((11657:ℚ)/16000),((3128349557:ℚ)/10000000000),((769506181:ℚ)/2500000000)⟩
theorem valid1 : Valid packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((4661:ℝ)/6400) ((11657:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((11657:ℚ)/16000),((23323:ℚ)/32000),((1565570739:ℚ)/5000000000),((613157273:ℚ)/2000000000)⟩
theorem valid2 : Valid packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((11657:ℝ)/16000) ((23323:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((23323:ℚ)/32000),((5833:ℚ)/8000),((783481331:ℚ)/2500000000),((3053500509:ℚ)/10000000000)⟩
theorem valid3 : Valid packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((23323:ℝ)/32000) ((5833:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((5833:ℚ)/8000),((23341:ℚ)/32000),((3136701121:ℚ)/10000000000),((1520583289:ℚ)/5000000000)⟩
theorem valid4 : Valid packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((5833:ℝ)/8000) ((23341:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((23341:ℚ)/32000),((467:ℚ)/640),((1569734449:ℚ)/5000000000),((605756797:ℚ)/2000000000)⟩
theorem valid5 : Valid packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((23341:ℝ)/32000) ((467:ℝ)/640), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((467:ℚ)/640),((23359:ℚ)/32000),((3142228681:ℚ)/10000000000),((301635213:ℚ)/1000000000)⟩
theorem valid6 : Valid packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((467:ℝ)/640) ((23359:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((23359:ℚ)/32000),((2921:ℚ)/4000),((1572490249:ℚ)/5000000000),((3003870401:ℚ)/10000000000)⟩
theorem valid7 : Valid packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((23359:ℝ)/32000) ((2921:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2921:ℚ)/4000),((23377:ℚ)/32000),((5036359:ℚ)/16000000),((2991338173:ℚ)/10000000000)⟩
theorem valid8 : Valid packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2921:ℝ)/4000) ((23377:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((23377:ℚ)/32000),((11693:ℚ)/16000),((157523017:ℚ)/500000000),((2978754809:ℚ)/10000000000)⟩
theorem valid9 : Valid packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((23377:ℝ)/32000) ((11693:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((11693:ℚ)/16000),((4679:ℚ)/6400),((1576594209:ℚ)/5000000000),((2966119657:ℚ)/10000000000)⟩
theorem valid10 : Valid packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((11693:ℝ)/16000) ((4679:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((4679:ℚ)/6400),((5851:ℚ)/8000),((3155908637:ℚ)/10000000000),((2953432051:ℚ)/10000000000)⟩
theorem valid11 : Valid packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((4679:ℝ)/6400) ((5851:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((5851:ℚ)/8000),((23413:ℚ)/32000),((1579310511:ℚ)/5000000000),((1470345657:ℚ)/5000000000)⟩
theorem valid12 : Valid packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((5851:ℝ)/8000) ((23413:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((23413:ℚ)/32000),((11711:ℚ)/16000),((3951657:ℚ)/12500000),((2927896749:ℚ)/10000000000)⟩
theorem valid13 : Valid packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((23413:ℝ)/32000) ((11711:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((11711:ℚ)/16000),((23431:ℚ)/32000),((791005599:ℚ)/2500000000),((2915047649:ℚ)/10000000000)⟩
theorem valid14 : Valid packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((11711:ℝ)/16000) ((23431:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((23431:ℚ)/32000),((293:ℚ)/400),((791677859:ℚ)/2500000000),((362767911:ℚ)/1250000000)⟩
theorem valid15 : Valid packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((23431:ℝ)/32000) ((293:ℝ)/400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((293:ℚ)/400),((23449:ℚ)/32000),((3169392747:ℚ)/10000000000),((115567317:ℚ)/400000000)⟩
theorem valid16 : Valid packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((293:ℝ)/400) ((23449:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((23449:ℚ)/32000),((11729:ℚ)/16000),((3172066353:ℚ)/10000000000),((2876165803:ℚ)/10000000000)⟩
theorem valid17 : Valid packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((23449:ℝ)/32000) ((11729:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((11729:ℚ)/16000),((23467:ℚ)/32000),((79368307:ℚ)/250000000),((2863091147:ℚ)/10000000000)⟩
theorem valid18 : Valid packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((11729:ℝ)/16000) ((23467:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((23467:ℚ)/32000),((5869:ℚ)/8000),((3177390553:ℚ)/10000000000),((569991633:ℚ)/2000000000)⟩
theorem valid19 : Valid packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((23467:ℝ)/32000) ((5869:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((5869:ℚ)/8000),((4697:ℚ)/6400),((3180041197:ℚ)/10000000000),((1418383023:ℚ)/5000000000)⟩
theorem valid20 : Valid packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((5869:ℝ)/8000) ((4697:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((4697:ℚ)/6400),((11747:ℚ)/16000),((795671059:ℚ)/2500000000),((2823513961:ℚ)/10000000000)⟩
theorem valid21 : Valid packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((4697:ℝ)/6400) ((11747:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((11747:ℚ)/16000),((23503:ℚ)/32000),((3185319697:ℚ)/10000000000),((140510053:ℚ)/500000000)⟩
theorem valid22 : Valid packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((11747:ℝ)/16000) ((23503:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((23503:ℚ)/32000),((2939:ℚ)/4000),((3187947603:ℚ)/10000000000),((699206619:ℚ)/2500000000)⟩
theorem valid23 : Valid packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((23503:ℝ)/32000) ((2939:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((2939:ℚ)/4000),((23521:ℚ)/32000),((1595283989:ℚ)/5000000000),((1391694659:ℚ)/5000000000)⟩
theorem valid24 : Valid packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((2939:ℝ)/4000) ((23521:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((23521:ℚ)/32000),((2353:ℚ)/3200),((199573803:ℚ)/625000000),((110795547:ℚ)/400000000)⟩
theorem valid25 : Valid packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((23521:ℝ)/32000) ((2353:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((2353:ℚ)/3200),((23539:ℚ)/32000),((798946559:ℚ)/2500000000),((1378161807:ℚ)/5000000000)⟩
theorem valid26 : Valid packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((2353:ℝ)/3200) ((23539:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((23539:ℚ)/32000),((5887:ℚ)/8000),((1599192083:ℚ)/5000000000),((1371346589:ℚ)/5000000000)⟩
theorem valid27 : Valid packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((23539:ℝ)/32000) ((5887:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((5887:ℚ)/8000),((23557:ℚ)/32000),((3200974663:ℚ)/10000000000),((682249097:ℚ)/2500000000)⟩
theorem valid28 : Valid packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((5887:ℝ)/8000) ((23557:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((23557:ℚ)/32000),((11783:ℚ)/16000),((3203557749:ℚ)/10000000000),((1357616119:ℚ)/5000000000)⟩
theorem valid29 : Valid packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((23557:ℝ)/32000) ((11783:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((11783:ℚ)/16000),((943:ℚ)/1280),((3206133449:ℚ)/10000000000),((2701399699:ℚ)/10000000000)⟩
theorem valid30 : Valid packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((11783:ℝ)/16000) ((943:ℝ)/1280), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((943:ℚ)/1280),((737:ℚ)/1000),((1604350893:ℚ)/5000000000),((2687497713:ℚ)/10000000000)⟩
theorem valid31 : Valid packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((943:ℝ)/1280) ((737:ℝ)/1000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((737:ℚ)/1000),((23593:ℚ)/32000),((50175981:ℚ)/156250000),((1336762599:ℚ)/5000000000)⟩
theorem valid32 : Valid packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((737:ℝ)/1000) ((23593:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((23593:ℚ)/32000),((11801:ℚ)/16000),((642763293:ℚ)/2000000000),((33243513:ℚ)/125000000)⟩
theorem valid33 : Valid packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((23593:ℝ)/32000) ((11801:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((11801:ℚ)/16000),((23611:ℚ)/32000),((3216362853:ℚ)/10000000000),((2645364099:ℚ)/10000000000)⟩
theorem valid34 : Valid packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((11801:ℝ)/16000) ((23611:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((23611:ℚ)/32000),((1181:ℚ)/1600),((3218901971:ℚ)/10000000000),((1315586601:ℚ)/5000000000)⟩
theorem valid35 : Valid packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((23611:ℝ)/32000) ((1181:ℝ)/1600), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((1181:ℚ)/1600),((23629:ℚ)/32000),((1610716921:ℚ)/5000000000),((523381429:ℚ)/2000000000)⟩
theorem valid36 : Valid packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((1181:ℝ)/1600) ((23629:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((23629:ℚ)/32000),((11819:ℚ)/16000),((402994811:ℚ)/1250000000),((2602564693:ℚ)/10000000000)⟩
theorem valid37 : Valid packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((23629:ℝ)/32000) ((11819:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((11819:ℚ)/16000),((23647:ℚ)/32000),((3226475931:ℚ)/10000000000),((1294072287:ℚ)/5000000000)⟩
theorem valid38 : Valid packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((11819:ℝ)/16000) ((23647:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((23647:ℚ)/32000),((2957:ℚ)/4000),((645797239:ℚ)/2000000000),((1286822741:ℚ)/5000000000)⟩
theorem valid39 : Valid packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((23647:ℝ)/32000) ((2957:ℝ)/4000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((2957:ℚ)/4000),((4733:ℚ)/6400),((1615744651:ℚ)/5000000000),((102362643:ℚ)/400000000)⟩
theorem valid40 : Valid packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((2957:ℝ)/4000) ((4733:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((4733:ℚ)/6400),((11837:ℚ)/16000),((1616992637:ℚ)/5000000000),((2544404971:ℚ)/10000000000)⟩
theorem valid41 : Valid packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((4733:ℝ)/6400) ((11837:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((11837:ℚ)/16000),((23683:ℚ)/32000),((809118533:ℚ)/2500000000),((10118643:ℚ)/40000000)⟩
theorem valid42 : Valid packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((11837:ℝ)/16000) ((23683:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((23683:ℚ)/32000),((5923:ℚ)/8000),((32389559:ℚ)/100000000),((628707987:ℚ)/2500000000)⟩
theorem valid43 : Valid packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((23683:ℝ)/32000) ((5923:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((5923:ℚ)/8000),((23701:ℚ)/32000),((1620715299:ℚ)/5000000000),((2499917061:ℚ)/10000000000)⟩
theorem valid44 : Valid packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((5923:ℝ)/8000) ((23701:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((23701:ℚ)/32000),((2371:ℚ)/3200),((3243898249:ℚ)/10000000000),((2484914537:ℚ)/10000000000)⟩
theorem valid45 : Valid packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((23701:ℝ)/32000) ((2371:ℝ)/3200), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet46 : Packet := ⟨((2371:ℚ)/3200),((23719:ℚ)/32000),((1623179437:ℚ)/5000000000),((2469822779:ℚ)/10000000000)⟩
theorem valid46 : Valid packet46 := by
  constructor <;> decide +kernel
private theorem leaf46 : ∀ r ∈ Set.Icc ((2371:ℝ)/3200) ((23719:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet46 valid46 r
    (by simpa only [packet46,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet47 : Packet := ⟨((23719:ℚ)/32000),((1483:ℚ)/2000),((649762499:ℚ)/2000000000),((2454640141:ℚ)/10000000000)⟩
theorem valid47 : Valid packet47 := by
  constructor <;> decide +kernel
private theorem leaf47 : ∀ r ∈ Set.Icc ((23719:ℝ)/32000) ((1483:ℝ)/2000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet47 valid47 r
    (by simpa only [packet47,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet48 : Packet := ⟨((1483:ℚ)/2000),((23737:ℚ)/32000),((812814783:ℚ)/2500000000),((609841231:ℚ)/2500000000)⟩
theorem valid48 : Valid packet48 := by
  constructor <;> decide +kernel
private theorem leaf48 : ∀ r ∈ Set.Icc ((1483:ℝ)/2000) ((23737:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet48 valid48 r
    (by simpa only [packet48,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet49 : Packet := ⟨((23737:ℚ)/32000),((11873:ℚ)/16000),((406712351:ℚ)/1250000000),((2423995379:ℚ)/10000000000)⟩
theorem valid49 : Valid packet49 := by
  constructor <;> decide +kernel
private theorem leaf49 : ∀ r ∈ Set.Icc ((23737:ℝ)/32000) ((11873:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet49 valid49 r
    (by simpa only [packet49,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet50 : Packet := ⟨((11873:ℚ)/16000),((4751:ℚ)/6400),((3256131543:ℚ)/10000000000),((1204264849:ℚ)/5000000000)⟩
theorem valid50 : Valid packet50 := by
  constructor <;> decide +kernel
private theorem leaf50 : ∀ r ∈ Set.Icc ((11873:ℝ)/16000) ((4751:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet50 valid50 r
    (by simpa only [packet50,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet51 : Packet := ⟨((4751:ℚ)/6400),((5941:ℚ)/8000),((1629278679:ℚ)/5000000000),((1196483009:ℚ)/5000000000)⟩
theorem valid51 : Valid packet51 := by
  constructor <;> decide +kernel
private theorem leaf51 : ∀ r ∈ Set.Icc ((4751:ℝ)/6400) ((5941:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet51 valid51 r
    (by simpa only [packet51,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet52 : Packet := ⟨((5941:ℚ)/8000),((23773:ℚ)/32000),((130439051:ℚ)/400000000),((594325603:ℚ)/2500000000)⟩
theorem valid52 : Valid packet52 := by
  constructor <;> decide +kernel
private theorem leaf52 : ∀ r ∈ Set.Icc ((5941:ℝ)/8000) ((23773:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet52 valid52 r
    (by simpa only [packet52,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet53 : Packet := ⟨((23773:ℚ)/32000),((11891:ℚ)/16000),((1631694157:ℚ)/5000000000),((2361536893:ℚ)/10000000000)⟩
theorem valid53 : Valid packet53 := by
  constructor <;> decide +kernel
private theorem leaf53 : ∀ r ∈ Set.Icc ((23773:ℝ)/32000) ((11891:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet53 valid53 r
    (by simpa only [packet53,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet54 : Packet := ⟨((11891:ℚ)/16000),((23791:ℚ)/32000),((653158699:ℚ)/2000000000),((586416851:ℚ)/2500000000)⟩
theorem valid54 : Valid packet54 := by
  constructor <;> decide +kernel
private theorem leaf54 : ∀ r ∈ Set.Icc ((11891:ℝ)/16000) ((23791:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet54 valid54 r
    (by simpa only [packet54,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet55 : Packet := ⟨((23791:ℚ)/32000),((119:ℚ)/160),((3268191839:ℚ)/10000000000),((116484591:ℚ)/500000000)⟩
theorem valid55 : Valid packet55 := by
  constructor <;> decide +kernel
private theorem leaf55 : ∀ r ∈ Set.Icc ((23791:ℝ)/32000) ((119:ℝ)/160), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet55 valid55 r
    (by simpa only [packet55,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet56 : Packet := ⟨((119:ℚ)/160),((23809:ℚ)/32000),((408822921:ℚ)/1250000000),((1156803971:ℚ)/5000000000)⟩
theorem valid56 : Valid packet56 := by
  constructor <;> decide +kernel
private theorem leaf56 : ∀ r ∈ Set.Icc ((119:ℝ)/160) ((23809:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet56 valid56 r
    (by simpa only [packet56,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet57 : Packet := ⟨((23809:ℚ)/32000),((11909:ℚ)/16000),((32729681:ℚ)/100000000),((2297413497:ℚ)/10000000000)⟩
theorem valid57 : Valid packet57 := by
  constructor <;> decide +kernel
private theorem leaf57 : ∀ r ∈ Set.Icc ((23809:ℝ)/32000) ((11909:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet57 valid57 r
    (by simpa only [packet57,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet58 : Packet := ⟨((11909:ℚ)/16000),((23827:ℚ)/32000),((3275346057:ℚ)/10000000000),((142569133:ℚ)/625000000)⟩
theorem valid58 : Valid packet58 := by
  constructor <;> decide +kernel
private theorem leaf58 : ∀ r ∈ Set.Icc ((11909:ℝ)/16000) ((23827:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet58 valid58 r
    (by simpa only [packet58,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet59 : Packet := ⟨((23827:ℚ)/32000),((5959:ℚ)/8000),((1638858629:ℚ)/5000000000),((452936679:ℚ)/2000000000)⟩
theorem valid59 : Valid packet59 := by
  constructor <;> decide +kernel
private theorem leaf59 : ∀ r ∈ Set.Icc ((23827:ℝ)/32000) ((5959:ℝ)/8000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet59 valid59 r
    (by simpa only [packet59,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet60 : Packet := ⟨((5959:ℚ)/8000),((4769:ℚ)/6400),((3280081723:ℚ)/10000000000),((2248142769:ℚ)/10000000000)⟩
theorem valid60 : Valid packet60 := by
  constructor <;> decide +kernel
private theorem leaf60 : ∀ r ∈ Set.Icc ((5959:ℝ)/8000) ((4769:ℝ)/6400), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet60 valid60 r
    (by simpa only [packet60,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet61 : Packet := ⟨((4769:ℚ)/6400),((11927:ℚ)/16000),((3282439473:ℚ)/10000000000),((2231481629:ℚ)/10000000000)⟩
theorem valid61 : Valid packet61 := by
  constructor <;> decide +kernel
private theorem leaf61 : ∀ r ∈ Set.Icc ((4769:ℝ)/6400) ((11927:ℝ)/16000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet61 valid61 r
    (by simpa only [packet61,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet62 : Packet := ⟨((11927:ℚ)/16000),((23863:ℚ)/32000),((3284790527:ℚ)/10000000000),((2214697253:ℚ)/10000000000)⟩
theorem valid62 : Valid packet62 := by
  constructor <;> decide +kernel
private theorem leaf62 : ∀ r ∈ Set.Icc ((11927:ℝ)/16000) ((23863:ℝ)/32000), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet62 valid62 r
    (by simpa only [packet62,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet63 : Packet := ⟨((23863:ℚ)/32000),((373:ℚ)/500),((657426981:ℚ)/2000000000),((2197786817:ℚ)/10000000000)⟩
theorem valid63 : Valid packet63 := by
  constructor <;> decide +kernel
private theorem leaf63 : ∀ r ∈ Set.Icc ((23863:ℝ)/32000) ((373:ℝ)/500), model r < (cap:ℝ) := by
  intro r hr
  exact packet_bound packet63 valid63 r
    (by simpa only [packet63,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node0_2 :
    ∀ r ∈ Set.Icc ((91:ℝ)/125) ((11657:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf0 leaf1
private theorem node2_4 :
    ∀ r ∈ Set.Icc ((11657:ℝ)/16000) ((5833:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf2 leaf3
private theorem node0_4 :
    ∀ r ∈ Set.Icc ((91:ℝ)/125) ((5833:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node0_2 node2_4
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((5833:ℝ)/8000) ((467:ℝ)/640), model r < (cap:ℝ) :=
  interval_join leaf4 leaf5
private theorem node6_8 :
    ∀ r ∈ Set.Icc ((467:ℝ)/640) ((2921:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf6 leaf7
private theorem node4_8 :
    ∀ r ∈ Set.Icc ((5833:ℝ)/8000) ((2921:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node4_6 node6_8
private theorem node0_8 :
    ∀ r ∈ Set.Icc ((91:ℝ)/125) ((2921:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node0_4 node4_8
private theorem node8_10 :
    ∀ r ∈ Set.Icc ((2921:ℝ)/4000) ((11693:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf8 leaf9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((11693:ℝ)/16000) ((5851:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf10 leaf11
private theorem node8_12 :
    ∀ r ∈ Set.Icc ((2921:ℝ)/4000) ((5851:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node8_10 node10_12
private theorem node12_14 :
    ∀ r ∈ Set.Icc ((5851:ℝ)/8000) ((11711:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf12 leaf13
private theorem node14_16 :
    ∀ r ∈ Set.Icc ((11711:ℝ)/16000) ((293:ℝ)/400), model r < (cap:ℝ) :=
  interval_join leaf14 leaf15
private theorem node12_16 :
    ∀ r ∈ Set.Icc ((5851:ℝ)/8000) ((293:ℝ)/400), model r < (cap:ℝ) :=
  interval_join node12_14 node14_16
private theorem node8_16 :
    ∀ r ∈ Set.Icc ((2921:ℝ)/4000) ((293:ℝ)/400), model r < (cap:ℝ) :=
  interval_join node8_12 node12_16
private theorem node0_16 :
    ∀ r ∈ Set.Icc ((91:ℝ)/125) ((293:ℝ)/400), model r < (cap:ℝ) :=
  interval_join node0_8 node8_16
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((293:ℝ)/400) ((11729:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf16 leaf17
private theorem node18_20 :
    ∀ r ∈ Set.Icc ((11729:ℝ)/16000) ((5869:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf18 leaf19
private theorem node16_20 :
    ∀ r ∈ Set.Icc ((293:ℝ)/400) ((5869:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node16_18 node18_20
private theorem node20_22 :
    ∀ r ∈ Set.Icc ((5869:ℝ)/8000) ((11747:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf20 leaf21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((11747:ℝ)/16000) ((2939:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf22 leaf23
private theorem node20_24 :
    ∀ r ∈ Set.Icc ((5869:ℝ)/8000) ((2939:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node20_22 node22_24
private theorem node16_24 :
    ∀ r ∈ Set.Icc ((293:ℝ)/400) ((2939:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node16_20 node20_24
private theorem node24_26 :
    ∀ r ∈ Set.Icc ((2939:ℝ)/4000) ((2353:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf24 leaf25
private theorem node26_28 :
    ∀ r ∈ Set.Icc ((2353:ℝ)/3200) ((5887:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf26 leaf27
private theorem node24_28 :
    ∀ r ∈ Set.Icc ((2939:ℝ)/4000) ((5887:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node24_26 node26_28
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((5887:ℝ)/8000) ((11783:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf28 leaf29
private theorem node30_32 :
    ∀ r ∈ Set.Icc ((11783:ℝ)/16000) ((737:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join leaf30 leaf31
private theorem node28_32 :
    ∀ r ∈ Set.Icc ((5887:ℝ)/8000) ((737:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node28_30 node30_32
private theorem node24_32 :
    ∀ r ∈ Set.Icc ((2939:ℝ)/4000) ((737:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node24_28 node28_32
private theorem node16_32 :
    ∀ r ∈ Set.Icc ((293:ℝ)/400) ((737:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node16_24 node24_32
private theorem node0_32 :
    ∀ r ∈ Set.Icc ((91:ℝ)/125) ((737:ℝ)/1000), model r < (cap:ℝ) :=
  interval_join node0_16 node16_32
private theorem node32_34 :
    ∀ r ∈ Set.Icc ((737:ℝ)/1000) ((11801:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf32 leaf33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((11801:ℝ)/16000) ((1181:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join leaf34 leaf35
private theorem node32_36 :
    ∀ r ∈ Set.Icc ((737:ℝ)/1000) ((1181:ℝ)/1600), model r < (cap:ℝ) :=
  interval_join node32_34 node34_36
private theorem node36_38 :
    ∀ r ∈ Set.Icc ((1181:ℝ)/1600) ((11819:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf36 leaf37
private theorem node38_40 :
    ∀ r ∈ Set.Icc ((11819:ℝ)/16000) ((2957:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join leaf38 leaf39
private theorem node36_40 :
    ∀ r ∈ Set.Icc ((1181:ℝ)/1600) ((2957:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node36_38 node38_40
private theorem node32_40 :
    ∀ r ∈ Set.Icc ((737:ℝ)/1000) ((2957:ℝ)/4000), model r < (cap:ℝ) :=
  interval_join node32_36 node36_40
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((2957:ℝ)/4000) ((11837:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf40 leaf41
private theorem node42_44 :
    ∀ r ∈ Set.Icc ((11837:ℝ)/16000) ((5923:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf42 leaf43
private theorem node40_44 :
    ∀ r ∈ Set.Icc ((2957:ℝ)/4000) ((5923:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node40_42 node42_44
private theorem node44_46 :
    ∀ r ∈ Set.Icc ((5923:ℝ)/8000) ((2371:ℝ)/3200), model r < (cap:ℝ) :=
  interval_join leaf44 leaf45
private theorem node46_48 :
    ∀ r ∈ Set.Icc ((2371:ℝ)/3200) ((1483:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join leaf46 leaf47
private theorem node44_48 :
    ∀ r ∈ Set.Icc ((5923:ℝ)/8000) ((1483:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node44_46 node46_48
private theorem node40_48 :
    ∀ r ∈ Set.Icc ((2957:ℝ)/4000) ((1483:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node40_44 node44_48
private theorem node32_48 :
    ∀ r ∈ Set.Icc ((737:ℝ)/1000) ((1483:ℝ)/2000), model r < (cap:ℝ) :=
  interval_join node32_40 node40_48
private theorem node48_50 :
    ∀ r ∈ Set.Icc ((1483:ℝ)/2000) ((11873:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf48 leaf49
private theorem node50_52 :
    ∀ r ∈ Set.Icc ((11873:ℝ)/16000) ((5941:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf50 leaf51
private theorem node48_52 :
    ∀ r ∈ Set.Icc ((1483:ℝ)/2000) ((5941:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node48_50 node50_52
private theorem node52_54 :
    ∀ r ∈ Set.Icc ((5941:ℝ)/8000) ((11891:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf52 leaf53
private theorem node54_56 :
    ∀ r ∈ Set.Icc ((11891:ℝ)/16000) ((119:ℝ)/160), model r < (cap:ℝ) :=
  interval_join leaf54 leaf55
private theorem node52_56 :
    ∀ r ∈ Set.Icc ((5941:ℝ)/8000) ((119:ℝ)/160), model r < (cap:ℝ) :=
  interval_join node52_54 node54_56
private theorem node48_56 :
    ∀ r ∈ Set.Icc ((1483:ℝ)/2000) ((119:ℝ)/160), model r < (cap:ℝ) :=
  interval_join node48_52 node52_56
private theorem node56_58 :
    ∀ r ∈ Set.Icc ((119:ℝ)/160) ((11909:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf56 leaf57
private theorem node58_60 :
    ∀ r ∈ Set.Icc ((11909:ℝ)/16000) ((5959:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join leaf58 leaf59
private theorem node56_60 :
    ∀ r ∈ Set.Icc ((119:ℝ)/160) ((5959:ℝ)/8000), model r < (cap:ℝ) :=
  interval_join node56_58 node58_60
private theorem node60_62 :
    ∀ r ∈ Set.Icc ((5959:ℝ)/8000) ((11927:ℝ)/16000), model r < (cap:ℝ) :=
  interval_join leaf60 leaf61
private theorem node62_64 :
    ∀ r ∈ Set.Icc ((11927:ℝ)/16000) ((373:ℝ)/500), model r < (cap:ℝ) :=
  interval_join leaf62 leaf63
private theorem node60_64 :
    ∀ r ∈ Set.Icc ((5959:ℝ)/8000) ((373:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node60_62 node62_64
private theorem node56_64 :
    ∀ r ∈ Set.Icc ((119:ℝ)/160) ((373:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node56_60 node60_64
private theorem node48_64 :
    ∀ r ∈ Set.Icc ((1483:ℝ)/2000) ((373:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node48_56 node56_64
private theorem node32_64 :
    ∀ r ∈ Set.Icc ((737:ℝ)/1000) ((373:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node32_48 node48_64
private theorem node0_64 :
    ∀ r ∈ Set.Icc ((91:ℝ)/125) ((373:ℝ)/500), model r < (cap:ℝ) :=
  interval_join node0_32 node32_64
theorem bound : ∀ r ∈ Set.Icc ((91:ℝ)/125) ((373:ℝ)/500), model r < (cap:ℝ) := node0_64
end N11Formalization.C450FirstRadialG07
#check @N11Formalization.C450FirstRadialG07.bound
#print axioms N11Formalization.C450FirstRadialG07.bound
