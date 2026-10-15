import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6647749589:ℚ)/10000000000),((6838750003:ℚ)/10000000000),(-1:ℚ),((-18279248767:ℚ)/20220000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5059718083:ℚ)/10000000000),((774353207440902397090472377182741:ℚ)/14196125000000000000000000000000000),((6987690287966325757501899:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((6766541897:ℚ)/10000000000),((6957500003:ℚ)/10000000000),(-1:ℚ),((-18635625691:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4727171029:ℚ)/10000000000),((7211707698488520796739948589684313:ℚ)/132612500000000000000000000000000000),((7012893527755538595001899:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3442666321:ℚ)/5000000000),((3508437501:ℚ)/5000000000),(-1:ℚ),((-863272633:ℚ)/945000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((273214459:ℚ)/625000000),((39143259244199157151137801623:ℚ)/738281250000000000000000000000),((1756374344752530679375211:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((217022733:ℚ)/312500000),((7076250003:ℚ)/10000000000),(-1:ℚ),((-599068199:ℚ)/655625000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4183021787:ℚ)/10000000000),((910611108325020515595377081441871:ℚ)/17193765625000000000000000000000000),((7038102718404126432501899:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7004121911:ℚ)/10000000000),((3552968751:ℚ)/5000000000),(-1:ℚ),((-19348365733:ℚ)/21075000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((996566269:ℚ)/2500000000),((967934604336651959696637831314741:ℚ)/18506484375000000000000000000000000),((1761101486418931307500211:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7033819007:ℚ)/10000000000),((7135625003:ℚ)/10000000000),(-1:ℚ),((-19437457021:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((971090279:ℚ)/2500000000),((21965535650774850901830887345816471:ℚ)/420158343750000000000000000000000000),((7050709545300685976251899:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7063516017:ℚ)/10000000000),((7150468753:ℚ)/10000000000),(-1:ℚ),((-19526548051:ℚ)/21217500000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3779854129:ℚ)/10000000000),((180471583335420397066670214857693:ℚ)/3473628906250000000000000000000000),((7053861484480270198126899:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((707836449:ℚ)/1000000000),((7165312503:ℚ)/10000000000),(-1:ℚ),((-1957109347:ℚ)/2126500000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((372655613:ℚ)/1000000000),((146808111367004244578329763129529:ℚ)/2826251406250000000000000000000000),((7057013516642032154376899:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),(-1:ℚ),((-15:ℚ)/16),((3546606471:ℚ)/5000000000),((1795039063:ℚ)/2500000000),(-1:ℚ),((-9807819413:ℚ)/10656250000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((1836260711:ℚ)/5000000000),((147435709699160399825270090321651:ℚ)/2838891601562500000000000000000000),((441260352598350938691459:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7108061373:ℚ)/10000000000),((3597500001:ℚ)/5000000000),(-1:ℚ),((-19660184119:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((723543387:ℚ)/2000000000),((1233873142390603443624197534358541:ℚ)/23763000000000000000000000000000000),((1765829464924931545000211:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7122909783:ℚ)/10000000000),((901230469:ℚ)/1250000000),(-1:ℚ),((-19704729349:ℚ)/21407500000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((1781053539:ℚ)/5000000000),((178434375776007937358179948239423517:ℚ)/3437107921875000000000000000000000000),((110413596418875235551771:ℚ)/225625000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1784439543:ℚ)/2500000000),((3612343751:ℚ)/5000000000),(-1:ℚ),((-4937318629:ℚ)/5363750000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((1752826731:ℚ)/5000000000),((3733182936412902674014609168972727:ℚ)/71924535156250000000000000000000000),((1767405643724620426250211:ℚ)/3610000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4291:ℚ)/6400),((17183:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7152606541:ℚ)/10000000000),((3616054689:ℚ)/5000000000),(-1:ℚ),((-19793819623:ℚ)/21478750000),((9729609943:ℚ)/10000000000),((9732954333:ℚ)/10000000000),((2330739941:ℚ)/10000000000),((1724157291:ℚ)/5000000000),((716163127659429164969720602726764661:ℚ)/13840101046875000000000000000000000000),((1767799703006102605098131:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((17183:ℚ)/25600) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((17183:ℚ)/25600),((8601:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7160030717:ℚ)/10000000000),((1809882813:ℚ)/2500000000),(-1:ℚ),((-19816092151:ℚ)/21502500000),((1215785143:ℚ)/1250000000),((2432402487:ℚ)/2500000000),((2345108749:ℚ)/10000000000),((3419299261:ℚ)/10000000000),((188015365700949653097325346411:ℚ)/3633789062500000000000000000000),((442048441998195379316459:ℚ)/902500000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((17183:ℚ)/25600) ((8601:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8601:ℚ)/12800),((17221:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7167454889:ℚ)/10000000000),((905869141:ℚ)/1250000000),(-1:ℚ),((-19838364667:ℚ)/21526250000),((9722967879:ℚ)/10000000000),((9726281149:ℚ)/10000000000),((2359325197:ℚ)/10000000000),((3390045457:ℚ)/10000000000),((829532975451995888684778515682159:ℚ)/16033890625000000000000000000000000),((110536739931064842432891:ℚ)/225625000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((8601:ℚ)/12800) ((17221:ℚ)/25600) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((17221:ℚ)/25600),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((448429941:ℚ)/625000000),((7254375003:ℚ)/10000000000),(-1:ℚ),((-1241289823:ℚ)/1346875000),((607479381:ℚ)/625000000),((2430741971:ℚ)/2500000000),((2373392223:ℚ)/10000000000),((3360546939:ℚ)/10000000000),((234612210026936507382633014108591:ℚ)/4535180664062500000000000000000000),((7075927662238336313751899:ℚ)/14440000000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((17221:ℚ)/25600) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((431:ℚ)/640),((17259:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7182303217:ℚ)/10000000000),((3630898439:ℚ)/5000000000),(-1:ℚ),((-1807537241:ℚ)/1961250000),((1943277549:ℚ)/2000000000),((9719670101:ℚ)/10000000000),((1193656329:ℚ)/5000000000),((3330797199:ℚ)/10000000000),((44215126271178080450034101519411:ℚ)/854778125000000000000000000000000),((1769375998033516786348131:ℚ)/3610000000000000000000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((17259:ℚ)/25600) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((17259:ℚ)/25600),((8639:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3594863687:ℚ)/5000000000),((7269218753:ℚ)/10000000000),(-1:ℚ),((-187784737:ℚ)/203750000),((4856560387:ℚ)/5000000000),((38865551:ℚ)/40000000),((9604357:ℚ)/40000000),((330078943:ℚ)/1000000000),((32932654040356751716022615813:ℚ)/636718750000000000000000000000),((7079080345275342410626899:ℚ)/14440000000000000000000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((17259:ℚ)/25600) ((8639:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((287886061:ℚ)/400000000),((3642031251:ℚ)/5000000000),(-1:ℚ),((-797098183:ℚ)/865800000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3270516529:ℚ)/10000000000),((8099733825640754400753459901189:ℚ)/156168675000000000000000000000000),((1770558280270531391875211:ℚ)/3610000000000000000000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7211999813:ℚ)/10000000000),((1824726563:ℚ)/2500000000),(-1:ℚ),((-19971999439:ℚ)/21692500000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3209145201:ℚ)/10000000000),((183011218618840672132303551941607469:ℚ)/3529234171875000000000000000000000000),((442836624380217554316459:ℚ)/902500000000000000000000)⟩
theorem valid19 : Valid source14 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7226848081:ℚ)/10000000000),((3656875001:ℚ)/5000000000),(-1:ℚ),((-20016544243:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3146619333:ℚ)/10000000000),((7657507719072871628730825334227093:ℚ)/147696125000000000000000000000000000),((1772134738016753476250211:ℚ)/3610000000000000000000000)⟩
theorem valid20 : Valid source14 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source14 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((7241696329:ℚ)/10000000000),((7328593753:ℚ)/10000000000),(-1:ℚ),((-20061088987:ℚ)/21787500000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((24084911:ℚ)/78125000),((122057480509587443912262820967447:ℚ)/2354638671875000000000000000000000),((7091692007245144141876899:ℚ)/14440000000000000000000000)⟩
theorem valid21 : Valid source14 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source14 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3628272279:ℚ)/5000000000),((7343437503:ℚ)/10000000000),(-1:ℚ),((-10052816837:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((94306729:ℚ)/312500000),((3860904040460091881841664296344959:ℚ)/74494878906250000000000000000000000),((7094845155193038910626899:ℚ)/14440000000000000000000000)⟩
theorem valid22 : Valid source14 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7271392767:ℚ)/10000000000),((3686562501:ℚ)/5000000000),(-1:ℚ),((-20150178301:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((184460831:ℚ)/625000000),((19193931799579805350005648022153:ℚ)/368355468750000000000000000000000),((1775287932455730848125211:ℚ)/3610000000000000000000000)⟩
theorem valid23 : Valid source14 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7301089127:ℚ)/10000000000),((3701406251:ℚ)/5000000000),(-1:ℚ),((-20239267381:ℚ)/22025000000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((2813927143:ℚ)/10000000000),((15792211680154614853637098684163939:ℚ)/303187890625000000000000000000000000),((1776864669148486135625211:ℚ)/3610000000000000000000000)⟩
theorem valid24 : Valid source14 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7330785411:ℚ)/10000000000),((7432500003:ℚ)/10000000000),(-1:ℚ),((-20328356233:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2669610523:ℚ)/10000000000),((142167513048719981279713004200843:ℚ)/2730437500000000000000000000000000),((7113765995506139945001899:ℚ)/14440000000000000000000000)⟩
theorem valid25 : Valid source14 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((368024081:ℚ)/500000000),((3745937501:ℚ)/5000000000),(-1:ℚ),((-1020872243:ℚ)/1115500000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((629310341:ℚ)/2500000000),((163656875238527155781576549502447:ℚ)/3110850625000000000000000000000000),((1781595437119818404375211:ℚ)/3610000000000000000000000)⟩
theorem valid26 : Valid source14 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((3709936907:ℚ)/5000000000),((3775625001:ℚ)/5000000000),(-1:ℚ),((-10297810721:ℚ)/11250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2181514689:ℚ)/10000000000),((115497714432143534782479376767079:ℚ)/2197265625000000000000000000000000),((1784749747344928588750211:ℚ)/3610000000000000000000000)⟩
theorem valid27 : Valid source14 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((3739632859:ℚ)/5000000000),((7670000003:ℚ)/10000000000),(-1:ℚ),((-944263507:ℚ)/1040000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1784843421:ℚ)/10000000000),((18113749085698043734700955178207:ℚ)/338000000000000000000000000000000),((123777:ℚ)/250000)⟩
theorem valid28 : Valid source14 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((3799024341:ℚ)/5000000000),((8620000003:ℚ)/10000000000),(-1:ℚ),((-10565073023:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2832641:ℚ)/125000000),((1145236278891431405617802245031591:ℚ)/17496000000000000000000000000000000),((123777:ℚ)/250000)⟩
theorem valid29 : Valid source14 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((1068534699:ℚ)/1250000000),((5260000001:ℚ)/5000000000),(-1:ℚ),((-2997604097:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1082013745664814529987237950445541:ℚ)/15000000000000000000000000000000000),((123777:ℚ)/250000)⟩
theorem valid30 : Valid source14 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((104486049:ℚ)/100000000),((14320000003:ℚ)/10000000000),(-1:ℚ),((-296818147:ℚ)/441600000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((167402355421577626409:ℚ)/2031360000000000000000),((123777:ℚ)/250000)⟩
theorem valid31 : Valid source14 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet31 valid31
private theorem node0_2 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source14 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_8 node8_16
private theorem node16_18 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source14 nn0 nn1 Qcell ((8639:ℚ)/12800) ((8677:ℚ)/12800) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((8677:ℚ)/12800) :=
  cell_join node16_18 node18_20
private theorem node20_22 :
    CellBound source14 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf20 leaf21
private theorem node22_24 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((2193:ℚ)/3200) :=
  cell_join leaf22 leaf23
private theorem node20_24 :
    CellBound source14 nn0 nn1 Qcell ((8677:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_join node20_22 node22_24
private theorem node16_24 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join node16_20 node20_24
private theorem node24_26 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join node24_26 node26_28
private theorem node28_30 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf28 leaf29
private theorem node30_32 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf30 leaf31
private theorem node28_32 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node28_30 node30_32
private theorem node24_32 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node24_28 node28_32
private theorem node16_32 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node16_24 node24_32
private theorem node0_32 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_16 node16_32
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_32
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31]
theorem packet_count : packets.length = 32 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC01
#check @N11Formalization.C450Source14GroupedC01.bound
#print axioms N11Formalization.C450Source14GroupedC01.valid0
#print axioms N11Formalization.C450Source14GroupedC01.valid1
#print axioms N11Formalization.C450Source14GroupedC01.valid2
#print axioms N11Formalization.C450Source14GroupedC01.valid3
#print axioms N11Formalization.C450Source14GroupedC01.valid4
#print axioms N11Formalization.C450Source14GroupedC01.valid5
#print axioms N11Formalization.C450Source14GroupedC01.valid6
#print axioms N11Formalization.C450Source14GroupedC01.valid7
#print axioms N11Formalization.C450Source14GroupedC01.valid8
#print axioms N11Formalization.C450Source14GroupedC01.valid9
#print axioms N11Formalization.C450Source14GroupedC01.valid10
#print axioms N11Formalization.C450Source14GroupedC01.valid11
#print axioms N11Formalization.C450Source14GroupedC01.valid12
#print axioms N11Formalization.C450Source14GroupedC01.valid13
#print axioms N11Formalization.C450Source14GroupedC01.valid14
#print axioms N11Formalization.C450Source14GroupedC01.valid15
#print axioms N11Formalization.C450Source14GroupedC01.valid16
#print axioms N11Formalization.C450Source14GroupedC01.valid17
#print axioms N11Formalization.C450Source14GroupedC01.valid18
#print axioms N11Formalization.C450Source14GroupedC01.valid19
#print axioms N11Formalization.C450Source14GroupedC01.valid20
#print axioms N11Formalization.C450Source14GroupedC01.valid21
#print axioms N11Formalization.C450Source14GroupedC01.valid22
#print axioms N11Formalization.C450Source14GroupedC01.valid23
#print axioms N11Formalization.C450Source14GroupedC01.valid24
#print axioms N11Formalization.C450Source14GroupedC01.valid25
#print axioms N11Formalization.C450Source14GroupedC01.valid26
#print axioms N11Formalization.C450Source14GroupedC01.valid27
#print axioms N11Formalization.C450Source14GroupedC01.valid28
#print axioms N11Formalization.C450Source14GroupedC01.valid29
#print axioms N11Formalization.C450Source14GroupedC01.valid30
#print axioms N11Formalization.C450Source14GroupedC01.valid31
#print axioms N11Formalization.C450Source14GroupedC01.bound
#print axioms N11Formalization.C450Source14GroupedC01.endpoint_checks
