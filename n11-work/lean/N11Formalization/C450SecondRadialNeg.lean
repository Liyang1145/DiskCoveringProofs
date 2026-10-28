import N11Formalization.C450SecondRadialKernel
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SecondRadialNeg
open C450SecondRadialKernel
def packet0 : Packet := ⟨((31:ℚ)/50),((262005041:ℚ)/400000000),((1971770483:ℚ)/10000000000),((1233636147:ℚ)/2000000000)⟩
theorem valid0 : Valid .neg packet0 := by
  constructor <;> decide +kernel
private theorem leaf0 : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((262005041:ℝ)/400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet0 valid0 r
    (by simpa only [packet0,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet1 : Packet := ⟨((262005041:ℚ)/400000000),((538015123:ℚ)/800000000),((29449497:ℚ)/125000000),((266001893:ℚ)/500000000)⟩
theorem valid1 : Valid .neg packet1 := by
  constructor <;> decide +kernel
private theorem leaf1 : ∀ r ∈ Set.Icc ((262005041:ℝ)/400000000) ((538015123:ℝ)/800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet1 valid1 r
    (by simpa only [packet1,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet2 : Packet := ⟨((538015123:ℚ)/800000000),((1090035287:ℚ)/1600000000),((251344139:ℚ)/1000000000),((4846738297:ℚ)/10000000000)⟩
theorem valid2 : Valid .neg packet2 := by
  constructor <;> decide +kernel
private theorem leaf2 : ∀ r ∈ Set.Icc ((538015123:ℝ)/800000000) ((1090035287:ℝ)/1600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet2 valid2 r
    (by simpa only [packet2,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet3 : Packet := ⟨((1090035287:ℚ)/1600000000),((138005041:ℚ)/200000000),((265391249:ℚ)/1000000000),((4593423441:ℚ)/10000000000)⟩
theorem valid3 : Valid .neg packet3 := by
  constructor <;> decide +kernel
private theorem leaf3 : ∀ r ∈ Set.Icc ((1090035287:ℝ)/1600000000) ((138005041:ℝ)/200000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet3 valid3 r
    (by simpa only [packet3,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet4 : Packet := ⟨((138005041:ℚ)/200000000),((2222085697:ℚ)/3200000000),((1359344127:ℚ)/5000000000),((4326411263:ℚ)/10000000000)⟩
theorem valid4 : Valid .neg packet4 := by
  constructor <;> decide +kernel
private theorem leaf4 : ∀ r ∈ Set.Icc ((138005041:ℝ)/200000000) ((2222085697:ℝ)/3200000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet4 valid4 r
    (by simpa only [packet4,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet5 : Packet := ⟨((2222085697:ℚ)/3200000000),((1118045369:ℚ)/1600000000),((139010489:ℚ)/500000000),((33495613:ℚ)/80000000)⟩
theorem valid5 : Valid .neg packet5 := by
  constructor <;> decide +kernel
private theorem leaf5 : ∀ r ∈ Set.Icc ((2222085697:ℝ)/3200000000) ((1118045369:ℝ)/1600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet5 valid5 r
    (by simpa only [packet5,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet6 : Packet := ⟨((1118045369:ℚ)/1600000000),((4486186517:ℚ)/6400000000),((2809826851:ℚ)/10000000000),((4042977359:ℚ)/10000000000)⟩
theorem valid6 : Valid .neg packet6 := by
  constructor <;> decide +kernel
private theorem leaf6 : ∀ r ∈ Set.Icc ((1118045369:ℝ)/1600000000) ((4486186517:ℝ)/6400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet6 valid6 r
    (by simpa only [packet6,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet7 : Packet := ⟨((4486186517:ℚ)/6400000000),((2250095779:ℚ)/3200000000),((2838718367:ℚ)/10000000000),((62017873:ℚ)/156250000)⟩
theorem valid7 : Valid .neg packet7 := by
  constructor <;> decide +kernel
private theorem leaf7 : ∀ r ∈ Set.Icc ((4486186517:ℝ)/6400000000) ((2250095779:ℝ)/3200000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet7 valid7 r
    (by simpa only [packet7,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet8 : Packet := ⟨((2250095779:ℚ)/3200000000),((4514196599:ℚ)/6400000000),((2866909841:ℚ)/10000000000),((155759451:ℚ)/400000000)⟩
theorem valid8 : Valid .neg packet8 := by
  constructor <;> decide +kernel
private theorem leaf8 : ∀ r ∈ Set.Icc ((2250095779:ℝ)/3200000000) ((4514196599:ℝ)/6400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet8 valid8 r
    (by simpa only [packet8,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet9 : Packet := ⟨((4514196599:ℚ)/6400000000),((9042398239:ℚ)/12800000000),((576150121:ℚ)/2000000000),((14911821:ℚ)/39062500)⟩
theorem valid9 : Valid .neg packet9 := by
  constructor <;> decide +kernel
private theorem leaf9 : ∀ r ∈ Set.Icc ((4514196599:ℝ)/6400000000) ((9042398239:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet9 valid9 r
    (by simpa only [packet9,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet10 : Packet := ⟨((9042398239:ℚ)/12800000000),((113205041:ℚ)/160000000),((2894425229:ℚ)/10000000000),((3778593551:ℚ)/10000000000)⟩
theorem valid10 : Valid .neg packet10 := by
  constructor <;> decide +kernel
private theorem leaf10 : ∀ r ∈ Set.Icc ((9042398239:ℝ)/12800000000) ((113205041:ℝ)/160000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet10 valid10 r
    (by simpa only [packet10,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet11 : Packet := ⟨((113205041:ℚ)/160000000),((9070408321:ℚ)/12800000000),((1453968243:ℚ)/5000000000),((747875449:ℚ)/2000000000)⟩
theorem valid11 : Valid .neg packet11 := by
  constructor <;> decide +kernel
private theorem leaf11 : ∀ r ∈ Set.Icc ((113205041:ℝ)/160000000) ((9070408321:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet11 valid11 r
    (by simpa only [packet11,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet12 : Packet := ⟨((9070408321:ℚ)/12800000000),((4542206681:ℚ)/6400000000),((2921287067:ℚ)/10000000000),((3699765033:ℚ)/10000000000)⟩
theorem valid12 : Valid .neg packet12 := by
  constructor <;> decide +kernel
private theorem leaf12 : ∀ r ∈ Set.Icc ((9070408321:ℝ)/12800000000) ((4542206681:ℝ)/6400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet12 valid12 r
    (by simpa only [packet12,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet13 : Packet := ⟨((4542206681:ℚ)/6400000000),((9098418403:ℚ)/12800000000),((733619897:ℚ)/2500000000),((3659744037:ℚ)/10000000000)⟩
theorem valid13 : Valid .neg packet13 := by
  constructor <;> decide +kernel
private theorem leaf13 : ∀ r ∈ Set.Icc ((4542206681:ℝ)/6400000000) ((9098418403:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet13 valid13 r
    (by simpa only [packet13,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet14 : Packet := ⟨((9098418403:ℚ)/12800000000),((18210841847:ℚ)/25600000000),((735254343:ℚ)/2500000000),((56551573:ℚ)/156250000)⟩
theorem valid14 : Valid .neg packet14 := by
  constructor <;> decide +kernel
private theorem leaf14 : ∀ r ∈ Set.Icc ((9098418403:ℝ)/12800000000) ((18210841847:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet14 valid14 r
    (by simpa only [packet14,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet15 : Packet := ⟨((18210841847:ℚ)/25600000000),((2278105861:ℚ)/3200000000),((736879147:ℚ)/2500000000),((3598916149:ℚ)/10000000000)⟩
theorem valid15 : Valid .neg packet15 := by
  constructor <;> decide +kernel
private theorem leaf15 : ∀ r ∈ Set.Icc ((18210841847:ℝ)/25600000000) ((2278105861:ℝ)/3200000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet15 valid15 r
    (by simpa only [packet15,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet16 : Packet := ⟨((2278105861:ℚ)/3200000000),((18238851929:ℚ)/25600000000),((2953977541:ℚ)/10000000000),((223651287:ℚ)/625000000)⟩
theorem valid16 : Valid .neg packet16 := by
  constructor <;> decide +kernel
private theorem leaf16 : ∀ r ∈ Set.Icc ((2278105861:ℝ)/3200000000) ((18238851929:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet16 valid16 r
    (by simpa only [packet16,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet17 : Packet := ⟨((18238851929:ℚ)/25600000000),((1825285697:ℚ)/2560000000),((2960400533:ℚ)/10000000000),((3557812079:ℚ)/10000000000)⟩
theorem valid17 : Valid .neg packet17 := by
  constructor <;> decide +kernel
private theorem leaf17 : ∀ r ∈ Set.Icc ((18238851929:ℝ)/25600000000) ((1825285697:ℝ)/2560000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet17 valid17 r
    (by simpa only [packet17,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet18 : Packet := ⟨((1825285697:ℚ)/2560000000),((18266862011:ℚ)/25600000000),((2966785863:ℚ)/10000000000),((442136079:ℚ)/1250000000)⟩
theorem valid18 : Valid .neg packet18 := by
  constructor <;> decide +kernel
private theorem leaf18 : ∀ r ∈ Set.Icc ((1825285697:ℝ)/2560000000) ((18266862011:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet18 valid18 r
    (by simpa only [packet18,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet19 : Packet := ⟨((18266862011:ℚ)/25600000000),((4570216763:ℚ)/6400000000),((2903451:ℚ)/9765625),((3516248217:ℚ)/10000000000)⟩
theorem valid19 : Valid .neg packet19 := by
  constructor <;> decide +kernel
private theorem leaf19 : ∀ r ∈ Set.Icc ((18266862011:ℝ)/25600000000) ((4570216763:ℝ)/6400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet19 valid19 r
    (by simpa only [packet19,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet20 : Packet := ⟨((4570216763:ℚ)/6400000000),((18294872093:ℚ)/25600000000),((595888941:ℚ)/2000000000),((3495288737:ℚ)/10000000000)⟩
theorem valid20 : Valid .neg packet20 := by
  constructor <;> decide +kernel
private theorem leaf20 : ∀ r ∈ Set.Icc ((4570216763:ℝ)/6400000000) ((18294872093:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet20 valid20 r
    (by simpa only [packet20,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet21 : Packet := ⟨((18294872093:ℚ)/25600000000),((9154438567:ℚ)/12800000000),((2985718791:ℚ)/10000000000),((1737104017:ℚ)/5000000000)⟩
theorem valid21 : Valid .neg packet21 := by
  constructor <;> decide +kernel
private theorem leaf21 : ∀ r ∈ Set.Icc ((18294872093:ℝ)/25600000000) ((9154438567:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet21 valid21 r
    (by simpa only [packet21,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet22 : Packet := ⟨((9154438567:ℚ)/12800000000),((732915287:ℚ)/1024000000),((598391273:ℚ)/2000000000),((1726501943:ℚ)/5000000000)⟩
theorem valid22 : Valid .neg packet22 := by
  constructor <;> decide +kernel
private theorem leaf22 : ∀ r ∈ Set.Icc ((9154438567:ℝ)/12800000000) ((732915287:ℝ)/1024000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet22 valid22 r
    (by simpa only [packet22,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet23 : Packet := ⟨((732915287:ℚ)/1024000000),((1146055451:ℚ)/1600000000),((374769713:ℚ)/1250000000),((3431674001:ℚ)/10000000000)⟩
theorem valid23 : Valid .neg packet23 := by
  constructor <;> decide +kernel
private theorem leaf23 : ∀ r ∈ Set.Icc ((732915287:ℝ)/1024000000) ((1146055451:ℝ)/1600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet23 valid23 r
    (by simpa only [packet23,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet24 : Packet := ⟨((1146055451:ℚ)/1600000000),((18350892257:ℚ)/25600000000),((3004323083:ℚ)/10000000000),((3410216017:ℚ)/10000000000)⟩
theorem valid24 : Valid .neg packet24 := by
  constructor <;> decide +kernel
private theorem leaf24 : ∀ r ∈ Set.Icc ((1146055451:ℝ)/1600000000) ((18350892257:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet24 valid24 r
    (by simpa only [packet24,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet25 : Packet := ⟨((18350892257:ℚ)/25600000000),((9182448649:ℚ)/12800000000),((3010452771:ℚ)/10000000000),((423578437:ℚ)/1250000000)⟩
theorem valid25 : Valid .neg packet25 := by
  constructor <;> decide +kernel
private theorem leaf25 : ∀ r ∈ Set.Icc ((18350892257:ℝ)/25600000000) ((9182448649:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet25 valid25 r
    (by simpa only [packet25,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet26 : Packet := ⟨((9182448649:ℚ)/12800000000),((18378902339:ℚ)/25600000000),((754136759:ℚ)/2500000000),((134676237:ℚ)/400000000)⟩
theorem valid26 : Valid .neg packet26 := by
  constructor <;> decide +kernel
private theorem leaf26 : ∀ r ∈ Set.Icc ((9182448649:ℝ)/12800000000) ((18378902339:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet26 valid26 r
    (by simpa only [packet26,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet27 : Packet := ⟨((18378902339:ℚ)/25600000000),((919645369:ℚ)/1280000000),((151130307:ℚ)/500000000),((3345048709:ℚ)/10000000000)⟩
theorem valid27 : Valid .neg packet27 := by
  constructor <;> decide +kernel
private theorem leaf27 : ∀ r ∈ Set.Icc ((18378902339:ℝ)/25600000000) ((919645369:ℝ)/1280000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet27 valid27 r
    (by simpa only [packet27,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet28 : Packet := ⟨((919645369:ℚ)/1280000000),((18406912421:ℚ)/25600000000),((378578793:ℚ)/1250000000),((3323053167:ℚ)/10000000000)⟩
theorem valid28 : Valid .neg packet28 := by
  constructor <;> decide +kernel
private theorem leaf28 : ∀ r ∈ Set.Icc ((919645369:ℝ)/1280000000) ((18406912421:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet28 valid28 r
    (by simpa only [packet28,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet29 : Packet := ⟨((18406912421:ℚ)/25600000000),((9210458731:ℚ)/12800000000),((2963496:ℚ)/9765625),((825229133:ℚ)/2500000000)⟩
theorem valid29 : Valid .neg packet29 := by
  constructor <;> decide +kernel
private theorem leaf29 : ∀ r ∈ Set.Icc ((18406912421:ℝ)/25600000000) ((9210458731:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet29 valid29 r
    (by simpa only [packet29,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet30 : Packet := ⟨((9210458731:ℚ)/12800000000),((18434922503:ℚ)/25600000000),((3040575073:ℚ)/10000000000),((1639317971:ℚ)/5000000000)⟩
theorem valid30 : Valid .neg packet30 := by
  constructor <;> decide +kernel
private theorem leaf30 : ∀ r ∈ Set.Icc ((9210458731:ℝ)/12800000000) ((18434922503:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet30 valid30 r
    (by simpa only [packet30,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet31 : Packet := ⟨((18434922503:ℚ)/25600000000),((2306115943:ℚ)/3200000000),((30464961:ℚ)/100000000),((1628104219:ℚ)/5000000000)⟩
theorem valid31 : Valid .neg packet31 := by
  constructor <;> decide +kernel
private theorem leaf31 : ∀ r ∈ Set.Icc ((18434922503:ℝ)/25600000000) ((2306115943:ℝ)/3200000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet31 valid31 r
    (by simpa only [packet31,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet32 : Packet := ⟨((2306115943:ℚ)/3200000000),((3692586517:ℚ)/5120000000),((2980843:ℚ)/9765625),((3233630961:ℚ)/10000000000)⟩
theorem valid32 : Valid .neg packet32 := by
  constructor <;> decide +kernel
private theorem leaf32 : ∀ r ∈ Set.Icc ((2306115943:ℝ)/3200000000) ((3692586517:ℝ)/5120000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet32 valid32 r
    (by simpa only [packet32,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet33 : Packet := ⟨((3692586517:ℚ)/5120000000),((9238468813:ℚ)/12800000000),((3058236713:ℚ)/10000000000),((401362543:ℚ)/1250000000)⟩
theorem valid33 : Valid .neg packet33 := by
  constructor <;> decide +kernel
private theorem leaf33 : ∀ r ∈ Set.Icc ((3692586517:ℝ)/5120000000) ((9238468813:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet33 valid33 r
    (by simpa only [packet33,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet34 : Packet := ⟨((9238468813:ℚ)/12800000000),((18490942667:ℚ)/25600000000),((3064056783:ℚ)/10000000000),((797003327:ℚ)/2500000000)⟩
theorem valid34 : Valid .neg packet34 := by
  constructor <;> decide +kernel
private theorem leaf34 : ∀ r ∈ Set.Icc ((9238468813:ℝ)/12800000000) ((18490942667:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet34 valid34 r
    (by simpa only [packet34,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet35 : Packet := ⟨((18490942667:ℚ)/25600000000),((4626236927:ℚ)/6400000000),((1534921839:ℚ)/5000000000),((395620807:ℚ)/1250000000)⟩
theorem valid35 : Valid .neg packet35 := by
  constructor <;> decide +kernel
private theorem leaf35 : ∀ r ∈ Set.Icc ((18490942667:ℝ)/25600000000) ((4626236927:ℝ)/6400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet35 valid35 r
    (by simpa only [packet35,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet36 : Packet := ⟨((4626236927:ℚ)/6400000000),((18518952749:ℚ)/25600000000),((1537798817:ℚ)/5000000000),((3141756267:ℚ)/10000000000)⟩
theorem valid36 : Valid .neg packet36 := by
  constructor <;> decide +kernel
private theorem leaf36 : ∀ r ∈ Set.Icc ((4626236927:ℝ)/6400000000) ((18518952749:ℝ)/25600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet36 valid36 r
    (by simpa only [packet36,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet37 : Packet := ⟨((18518952749:ℚ)/25600000000),((1853295779:ℚ)/2560000000),((3081318881:ℚ)/10000000000),((3118379091:ℚ)/10000000000)⟩
theorem valid37 : Valid .neg packet37 := by
  constructor <;> decide +kernel
private theorem leaf37 : ∀ r ∈ Set.Icc ((18518952749:ℝ)/25600000000) ((1853295779:ℝ)/2560000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet37 valid37 r
    (by simpa only [packet37,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet38 : Packet := ⟨((1853295779:ℚ)/2560000000),((290015123:ℚ)/400000000),((3092664161:ℚ)/10000000000),((3094831141:ℚ)/10000000000)⟩
theorem valid38 : Valid .neg packet38 := by
  constructor <;> decide +kernel
private theorem leaf38 : ∀ r ∈ Set.Icc ((1853295779:ℝ)/2560000000) ((290015123:ℝ)/400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet38 valid38 r
    (by simpa only [packet38,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet39 : Packet := ⟨((290015123:ℚ)/400000000),((9294488977:ℚ)/12800000000),((3103881311:ℚ)/10000000000),((1523603519:ℚ)/5000000000)⟩
theorem valid39 : Valid .neg packet39 := by
  constructor <;> decide +kernel
private theorem leaf39 : ∀ r ∈ Set.Icc ((290015123:ℝ)/400000000) ((9294488977:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet39 valid39 r
    (by simpa only [packet39,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet40 : Packet := ⟨((9294488977:ℚ)/12800000000),((4654247009:ℚ)/6400000000),((3114972081:ℚ)/10000000000),((2998850629:ℚ)/10000000000)⟩
theorem valid40 : Valid .neg packet40 := by
  constructor <;> decide +kernel
private theorem leaf40 : ∀ r ∈ Set.Icc ((9294488977:ℝ)/12800000000) ((4654247009:ℝ)/6400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet40 valid40 r
    (by simpa only [packet40,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet41 : Packet := ⟨((4654247009:ℚ)/6400000000),((9322499059:ℚ)/12800000000),((1562969089:ℚ)/5000000000),((2949725871:ℚ)/10000000000)⟩
theorem valid41 : Valid .neg packet41 := by
  constructor <;> decide +kernel
private theorem leaf41 : ∀ r ∈ Set.Icc ((4654247009:ℝ)/6400000000) ((9322499059:ℝ)/12800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet41 valid41 r
    (by simpa only [packet41,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet42 : Packet := ⟨((9322499059:ℚ)/12800000000),((93365041:ℚ)/128000000),((784195317:ℚ)/2500000000),((1449896843:ℚ)/5000000000)⟩
theorem valid42 : Valid .neg packet42 := by
  constructor <;> decide +kernel
private theorem leaf42 : ∀ r ∈ Set.Icc ((9322499059:ℝ)/12800000000) ((93365041:ℝ)/128000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet42 valid42 r
    (by simpa only [packet42,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet43 : Packet := ⟨((93365041:ℚ)/128000000),((4682257091:ℚ)/6400000000),((1579052451:ℚ)/5000000000),((284901159:ℚ)/1000000000)⟩
theorem valid43 : Valid .neg packet43 := by
  constructor <;> decide +kernel
private theorem leaf43 : ∀ r ∈ Set.Icc ((93365041:ℝ)/128000000) ((4682257091:ℝ)/6400000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet43 valid43 r
    (by simpa only [packet43,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet44 : Packet := ⟨((4682257091:ℚ)/6400000000),((1174065533:ℚ)/1600000000),((794738887:ℚ)/2500000000),((1372354033:ℚ)/5000000000)⟩
theorem valid44 : Valid .neg packet44 := by
  constructor <;> decide +kernel
private theorem leaf44 : ∀ r ∈ Set.Icc ((4682257091:ℝ)/6400000000) ((1174065533:ℝ)/1600000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet44 valid44 r
    (by simpa only [packet44,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet45 : Packet := ⟨((1174065533:ℚ)/1600000000),((2362136107:ℚ)/3200000000),((3219285331:ℚ)/10000000000),((1318194537:ℚ)/5000000000)⟩
theorem valid45 : Valid .neg packet45 := by
  constructor <;> decide +kernel
private theorem leaf45 : ∀ r ∈ Set.Icc ((1174065533:ℝ)/1600000000) ((2362136107:ℝ)/3200000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet45 valid45 r
    (by simpa only [packet45,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet46 : Packet := ⟨((2362136107:ℚ)/3200000000),((594035287:ℚ)/800000000),((3257860369:ℚ)/10000000000),((2405514699:ℚ)/10000000000)⟩
theorem valid46 : Valid .neg packet46 := by
  constructor <;> decide +kernel
private theorem leaf46 : ∀ r ∈ Set.Icc ((2362136107:ℝ)/3200000000) ((594035287:ℝ)/800000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet46 valid46 r
    (by simpa only [packet46,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet47 : Packet := ⟨((594035287:ℚ)/800000000),((240415123:ℚ)/320000000),((3330068359:ℚ)/10000000000),((430103117:ℚ)/2000000000)⟩
theorem valid47 : Valid .neg packet47 := by
  constructor <;> decide +kernel
private theorem leaf47 : ∀ r ∈ Set.Icc ((594035287:ℝ)/800000000) ((240415123:ℝ)/320000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet47 valid47 r
    (by simpa only [packet47,Rat.cast_div,Rat.cast_ofNat] using hr)
def packet48 : Packet := ⟨((240415123:ℚ)/320000000),((76005041:ℚ)/100000000),((849040353:ℚ)/2500000000),((189897009:ℚ)/1250000000)⟩
theorem valid48 : Valid .neg packet48 := by
  constructor <;> decide +kernel
private theorem leaf48 : ∀ r ∈ Set.Icc ((240415123:ℝ)/320000000) ((76005041:ℝ)/100000000),
    model .neg r < (cap:ℝ) := by
  intro r hr
  exact packet_bound .neg packet48 valid48 r
    (by simpa only [packet48,Rat.cast_div,Rat.cast_ofNat] using hr)
private theorem node1_3 :
    ∀ r ∈ Set.Icc ((262005041:ℝ)/400000000) ((1090035287:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf1 leaf2
private theorem node0_3 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1090035287:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf0 node1_3
private theorem node4_6 :
    ∀ r ∈ Set.Icc ((138005041:ℝ)/200000000) ((1118045369:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf4 leaf5
private theorem node3_6 :
    ∀ r ∈ Set.Icc ((1090035287:ℝ)/1600000000) ((1118045369:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf3 node4_6
private theorem node0_6 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1118045369:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_3 node3_6
private theorem node7_9 :
    ∀ r ∈ Set.Icc ((4486186517:ℝ)/6400000000) ((4514196599:ℝ)/6400000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf7 leaf8
private theorem node6_9 :
    ∀ r ∈ Set.Icc ((1118045369:ℝ)/1600000000) ((4514196599:ℝ)/6400000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf6 node7_9
private theorem node10_12 :
    ∀ r ∈ Set.Icc ((9042398239:ℝ)/12800000000) ((9070408321:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf10 leaf11
private theorem node9_12 :
    ∀ r ∈ Set.Icc ((4514196599:ℝ)/6400000000) ((9070408321:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf9 node10_12
private theorem node6_12 :
    ∀ r ∈ Set.Icc ((1118045369:ℝ)/1600000000) ((9070408321:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node6_9 node9_12
private theorem node0_12 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((9070408321:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_6 node6_12
private theorem node13_15 :
    ∀ r ∈ Set.Icc ((4542206681:ℝ)/6400000000) ((18210841847:ℝ)/25600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf13 leaf14
private theorem node12_15 :
    ∀ r ∈ Set.Icc ((9070408321:ℝ)/12800000000) ((18210841847:ℝ)/25600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf12 node13_15
private theorem node16_18 :
    ∀ r ∈ Set.Icc ((2278105861:ℝ)/3200000000) ((1825285697:ℝ)/2560000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf16 leaf17
private theorem node15_18 :
    ∀ r ∈ Set.Icc ((18210841847:ℝ)/25600000000) ((1825285697:ℝ)/2560000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf15 node16_18
private theorem node12_18 :
    ∀ r ∈ Set.Icc ((9070408321:ℝ)/12800000000) ((1825285697:ℝ)/2560000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node12_15 node15_18
private theorem node19_21 :
    ∀ r ∈ Set.Icc ((18266862011:ℝ)/25600000000) ((18294872093:ℝ)/25600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf19 leaf20
private theorem node18_21 :
    ∀ r ∈ Set.Icc ((1825285697:ℝ)/2560000000) ((18294872093:ℝ)/25600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf18 node19_21
private theorem node22_24 :
    ∀ r ∈ Set.Icc ((9154438567:ℝ)/12800000000) ((1146055451:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf22 leaf23
private theorem node21_24 :
    ∀ r ∈ Set.Icc ((18294872093:ℝ)/25600000000) ((1146055451:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf21 node22_24
private theorem node18_24 :
    ∀ r ∈ Set.Icc ((1825285697:ℝ)/2560000000) ((1146055451:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node18_21 node21_24
private theorem node12_24 :
    ∀ r ∈ Set.Icc ((9070408321:ℝ)/12800000000) ((1146055451:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node12_18 node18_24
private theorem node0_24 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((1146055451:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_12 node12_24
private theorem node25_27 :
    ∀ r ∈ Set.Icc ((18350892257:ℝ)/25600000000) ((18378902339:ℝ)/25600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf25 leaf26
private theorem node24_27 :
    ∀ r ∈ Set.Icc ((1146055451:ℝ)/1600000000) ((18378902339:ℝ)/25600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf24 node25_27
private theorem node28_30 :
    ∀ r ∈ Set.Icc ((919645369:ℝ)/1280000000) ((9210458731:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf28 leaf29
private theorem node27_30 :
    ∀ r ∈ Set.Icc ((18378902339:ℝ)/25600000000) ((9210458731:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf27 node28_30
private theorem node24_30 :
    ∀ r ∈ Set.Icc ((1146055451:ℝ)/1600000000) ((9210458731:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node24_27 node27_30
private theorem node31_33 :
    ∀ r ∈ Set.Icc ((18434922503:ℝ)/25600000000) ((3692586517:ℝ)/5120000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf31 leaf32
private theorem node30_33 :
    ∀ r ∈ Set.Icc ((9210458731:ℝ)/12800000000) ((3692586517:ℝ)/5120000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf30 node31_33
private theorem node34_36 :
    ∀ r ∈ Set.Icc ((9238468813:ℝ)/12800000000) ((4626236927:ℝ)/6400000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf34 leaf35
private theorem node33_36 :
    ∀ r ∈ Set.Icc ((3692586517:ℝ)/5120000000) ((4626236927:ℝ)/6400000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf33 node34_36
private theorem node30_36 :
    ∀ r ∈ Set.Icc ((9210458731:ℝ)/12800000000) ((4626236927:ℝ)/6400000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node30_33 node33_36
private theorem node24_36 :
    ∀ r ∈ Set.Icc ((1146055451:ℝ)/1600000000) ((4626236927:ℝ)/6400000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node24_30 node30_36
private theorem node37_39 :
    ∀ r ∈ Set.Icc ((18518952749:ℝ)/25600000000) ((290015123:ℝ)/400000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf37 leaf38
private theorem node36_39 :
    ∀ r ∈ Set.Icc ((4626236927:ℝ)/6400000000) ((290015123:ℝ)/400000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf36 node37_39
private theorem node40_42 :
    ∀ r ∈ Set.Icc ((9294488977:ℝ)/12800000000) ((9322499059:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf40 leaf41
private theorem node39_42 :
    ∀ r ∈ Set.Icc ((290015123:ℝ)/400000000) ((9322499059:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf39 node40_42
private theorem node36_42 :
    ∀ r ∈ Set.Icc ((4626236927:ℝ)/6400000000) ((9322499059:ℝ)/12800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node36_39 node39_42
private theorem node43_45 :
    ∀ r ∈ Set.Icc ((93365041:ℝ)/128000000) ((1174065533:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf43 leaf44
private theorem node42_45 :
    ∀ r ∈ Set.Icc ((9322499059:ℝ)/12800000000) ((1174065533:ℝ)/1600000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf42 node43_45
private theorem node45_47 :
    ∀ r ∈ Set.Icc ((1174065533:ℝ)/1600000000) ((594035287:ℝ)/800000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf45 leaf46
private theorem node47_49 :
    ∀ r ∈ Set.Icc ((594035287:ℝ)/800000000) ((76005041:ℝ)/100000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join leaf47 leaf48
private theorem node45_49 :
    ∀ r ∈ Set.Icc ((1174065533:ℝ)/1600000000) ((76005041:ℝ)/100000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node45_47 node47_49
private theorem node42_49 :
    ∀ r ∈ Set.Icc ((9322499059:ℝ)/12800000000) ((76005041:ℝ)/100000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node42_45 node45_49
private theorem node36_49 :
    ∀ r ∈ Set.Icc ((4626236927:ℝ)/6400000000) ((76005041:ℝ)/100000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node36_42 node42_49
private theorem node24_49 :
    ∀ r ∈ Set.Icc ((1146055451:ℝ)/1600000000) ((76005041:ℝ)/100000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node24_36 node36_49
private theorem node0_49 :
    ∀ r ∈ Set.Icc ((31:ℝ)/50) ((76005041:ℝ)/100000000),
      model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join node0_24 node24_49
theorem near_bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) (finish .neg:ℝ),
    model .neg r < (cap:ℝ) := by
  have hh := node0_49
  norm_num [finish,F,E,R] at hh ⊢
  exact hh
theorem bound : ∀ r ∈ Set.Icc ((31:ℝ)/50) ((69:ℝ)/50),
    model .neg r < (cap:ℝ) :=
  C450FirstRadialKernel.interval_join near_bound (fun r hr => far_bound .neg r hr)
end N11Formalization.C450SecondRadialNeg
#check @N11Formalization.C450SecondRadialNeg.bound
#print axioms N11Formalization.C450SecondRadialNeg.bound
