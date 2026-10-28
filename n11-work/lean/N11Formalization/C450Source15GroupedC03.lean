import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6615084777:ℚ)/10000000000),((68029313:ℚ)/100000000),((-434605191:ℚ)/496000000),((-77036102101:ℚ)/101100000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2573850921:ℚ)/5000000000),((236464613342667084406887391050006581062513:ℚ)/4060000894800000000000000000000000000000000),((78606195451232372766429:ℚ)/184832000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((1346794859:ℚ)/2000000000),((6921788731:ℚ)/10000000000),((-44292521117:ℚ)/50550000000),((-15716333167:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4820438807:ℚ)/10000000000),((1152779690925932120693833093566168198178234802797355523081:ℚ)/19825958817236328125000000000000000000000000000000000000000),((788046188721377427071118101:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3426429329:ℚ)/5000000000),((1745303993:ℚ)/2500000000),((-11177127951:ℚ)/12875000000),((-40063581277:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2235647857:ℚ)/5000000000),((199443593583827975671217215125030084492790755538184563783:ℚ)/3574787201356887817382812500000000000000000000000000000000),((49314896112372815994965709:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3456149497:ℚ)/5000000000),((3520321133:ℚ)/5000000000),((-22562247931:ℚ)/25987500000),((-40449943461:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2143426483:ℚ)/5000000000),((3238255509704196005281238671472721707916673657990691940379:ℚ)/58059061506848144531250000000000000000000000000000000000000),((197507627196956234242102949:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((1394347629:ℚ)/2000000000),((1414071013:ℚ)/2000000000),((-9066497091:ℚ)/10490000000),((-16334519177:ℚ)/21075000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((511831191:ℚ)/1250000000),((2802072870629851394728526173000614320721880934779660759061:ℚ)/51269800930700062500000000000000000000000000000000000000000),((31621064104745226765388629:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3500728643:ℚ)/5000000000),((3550033819:ℚ)/5000000000),((-7590078911:ℚ)/8781250000),((-41029472359:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((799057631:ℚ)/2000000000),((1036567773246506365596550186176874764853309939053207286148841:ℚ)/18966655594110298156738281250000000000000000000000000000000000),((197755675526643262533948501:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7031176143:ℚ)/10000000000),((3564889993:ℚ)/5000000000),((-22874229951:ℚ)/26462500000),((-82445289859:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3893532439:ℚ)/10000000000),((114487697123755902715565106397659898269502096324435765710964561:ℚ)/2094900477997613732910156250000000000000000000000000000000000000),((197879701817033496015401709:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7060894719:ℚ)/10000000000),((447468257:ℚ)/625000000),((-2872277799:ℚ)/3322656250),((-82831631347:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3789189011:ℚ)/10000000000),((457311346359469111854365062107552584960078878720928911230857:ℚ)/8368136201515278625488281250000000000000000000000000000000000),((3093808274035904177999709:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3545306509:ℚ)/5000000000),((7174348093:ℚ)/10000000000),((-46060436651:ℚ)/53400000000),((-41608984617:ℚ)/53518750000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((736407477:ℚ)/2000000000),((419533690373600437893045698860969768206455510108801238648933469:ℚ)/7753774510644150000000000000000000000000000000000000000000000000),((792262975762837326346442309:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1421094413:ℚ)/2000000000),((359460201:ℚ)/500000000),((-2308221407:ℚ)/2675937500),((-16682227369:ℚ)/21455000000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((906832707:ℚ)/2500000000),((7457015898464696636070532393401105704736723042151425013193:ℚ)/137817688269896096074581146240234375000000000000000000000000),((1981277587070812611501741:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1780082761:ℚ)/2500000000),((7204059893:ℚ)/10000000000),((-46268419251:ℚ)/53637500000),((-20901075893:ℚ)/26878125000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((1785912167:ℚ)/5000000000),((1283429290337366258656637765600715621802465038667871017304243:ℚ)/23719507285177820777893066406250000000000000000000000000000000),((2196008574375703369492269:ℚ)/5120000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((1427037991:ℚ)/2000000000),((7218915713:ℚ)/10000000000),((-15457469997:ℚ)/17918750000),((-16759493883:ℚ)/21550000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((70309599:ℚ)/200000000),((1411854443132073799737535787200212848169198064404165392457:ℚ)/26092622028346318006515502929687500000000000000000000000000),((793007157343421280311588829:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((8937561:ℚ)/12500000),((180844287:ℚ)/250000000),((-1161910009:ℚ)/1346875000),((-104988293:ℚ)/134984375),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((3458256651:ℚ)/10000000000),((94584312183051551121847501230976310127790943621724775293:ℚ)/1747999262819147109985351562500000000000000000000000000000),((495784513006048065428829:ℚ)/1155200000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3582453789:ℚ)/5000000000),((7248627193:ℚ)/10000000000),((-46580390351:ℚ)/53993750000),((-42091899257:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3400110003:ℚ)/10000000000),((62351794100293670816222876493690408357827213722216608488334761:ℚ)/1152300314348959892177581787109375000000000000000000000000000000),((793503285731672194075448909:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((717976629:ℚ)/1000000000),((3631741427:ℚ)/5000000000),((-23342189989:ℚ)/27056250000),((-8437696177:ℚ)/10846250000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((133639669:ℚ)/400000000),((56036105301945999020171607489158751654314760014890864413879739:ℚ)/1035570123163586439514160156250000000000000000000000000000000000),((198437838035694621488393189:ℚ)/462080000000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7194624937:ℚ)/10000000000),((227448077:ℚ)/312500000),((-2924273078:ℚ)/3389453125),((-84570124181:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((131233969:ℚ)/400000000),((7966935453346703093932309832058836324068418580058233178616139:ℚ)/147230559646756377601623535156250000000000000000000000000000000),((775390058652021197438789:ℚ)/1805000000000000000000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((3604741759:ℚ)/5000000000),((7293194021:ℚ)/10000000000),((-46892358147:ℚ)/54350000000),((-14127214289:ℚ)/18156250000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((3219625043:ℚ)/10000000000),((2618369166337812722931833337413371429176149273736948696677939:ℚ)/48387466914975781250000000000000000000000000000000000000000000),((794247489448923895742823381:ℚ)/1848320000000000000000000000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1444868407:ℚ)/2000000000),((7308049527:ℚ)/10000000000),((-46996346689:ℚ)/54468750000),((-16991289291:ℚ)/21835000000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((3157256177:ℚ)/10000000000),((7238165890300074257126390906533156649735912734854103909689791:ℚ)/133759961613762938976287841796875000000000000000000000000000000),((794495560343913820577636589:ℚ)/1848320000000000000000000000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7239200487:ℚ)/10000000000),((3668880193:ℚ)/5000000000),((-23602161351:ℚ)/27293750000),((-85149606331:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3093673331:ℚ)/10000000000),((8348015234454705170612685765762371911078682995340939772119761:ℚ)/152787180700372271347045898437500000000000000000000000000000000),((198747926662750939997826909:ℚ)/462080000000000000000000000)⟩
theorem valid18 : Valid source15 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((18172293:ℚ)/25000000),((7367471043:ℚ)/10000000000),((-47412297301:ℚ)/54825000000),((-213839809:ℚ)/275312500),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((2962551261:ℚ)/10000000000),((1213234685183422290706451724441671440080989789302711839533539:ℚ)/22205740202376782226562500000000000000000000000000000000000000),((795487859014144559775421509:ℚ)/1848320000000000000000000000)⟩
theorem valid19 : Valid source15 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7298633661:ℚ)/10000000000),((7397181501:ℚ)/10000000000),((-47620270507:ℚ)/55062500000),((-85922237593:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((565107699:ℚ)/2000000000),((38911880236078049856559018236772804994278484497538650038701:ℚ)/712229640001463890075683593750000000000000000000000000000000),((795984017483243746250038341:ℚ)/1848320000000000000000000000)⟩
theorem valid20 : Valid source15 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7328349873:ℚ)/10000000000),((7456601829:ℚ)/10000000000),((-48036212803:ℚ)/55300000000),((-86308548349:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((670432913:ℚ)/2500000000),((41831566372966284973818461487683665914265465055993800487170419:ℚ)/751547633836693750000000000000000000000000000000000000000000000),((796976352888864676661732181:ℚ)/1848320000000000000000000000)⟩
theorem valid21 : Valid source15 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((7387781561:ℚ)/10000000000),((469751337:ℚ)/625000000),((-3028259359:ℚ)/3485937500),((-9675684477:ℚ)/12500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2368729987:ℚ)/10000000000),((640517824840349907799392162726787503788174833480693:ℚ)/11510944771766662597656250000000000000000000000000000),((3117065286069510943906029:ℚ)/7220000000000000000000000)⟩
theorem valid22 : Valid source15 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7447212291:ℚ)/10000000000),((3817429147:ℚ)/5000000000),((-8214001343:ℚ)/9375000000),((-87853759783:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2008550167:ℚ)/10000000000),((224789657321971849048904816228673868582333587578481146971:ℚ)/3900337219238281250000000000000000000000000000000000000000),((55358123:ℚ)/128000000)⟩
theorem valid23 : Valid source15 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((7566070971:ℚ)/10000000000),((4055089403:ℚ)/5000000000),((-26305625821:ℚ)/28600000000),((-89398922623:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((945269447:ℚ)/10000000000),((9410954144581218087105901720995834938651359669649704742651:ℚ)/136012178087500000000000000000000000000000000000000000000000),((55358123:ℚ)/128000000)⟩
theorem valid24 : Valid source15 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((1608294359:ℚ)/2000000000),((4292730847:ℚ)/5000000000),((-27969115929:ℚ)/30500000000),((-19115826667:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((19783576887710021893921101639838498547645173623156707179919:ℚ)/290863738476562500000000000000000000000000000000000000000000),((55358123:ℚ)/128000000)⟩
theorem valid25 : Valid source15 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((2129206389:ℚ)/2500000000),((10486324327:ℚ)/10000000000),(-1:ℚ),((-25439683057:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((187467794040742073996786894279012011:ℚ)/2000000000000000000000000000000000000),((55358123:ℚ)/128000000)⟩
theorem valid26 : Valid source15 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5208952127:ℚ)/5000000000),((7143668351:ℚ)/5000000000),(-1:ℚ),((-63236377651:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((631202083568018475718376609:ℚ)/6094080000000000000000000000),((55358123:ℚ)/128000000)⟩
theorem valid27 : Valid source15 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet27 valid27
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source15 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((2193:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((553:ℚ)/800) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node14_17 node17_21
private theorem node22_24 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf21 node22_24
private theorem node24_26 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node24_26 node26_28
private theorem node21_28 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node21_24 node24_28
private theorem node14_28 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node14_21 node21_28
private theorem node0_28 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_28
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_28
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27]
theorem packet_count : packets.length = 28 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC03
#check @N11Formalization.C450Source15GroupedC03.bound
#print axioms N11Formalization.C450Source15GroupedC03.valid0
#print axioms N11Formalization.C450Source15GroupedC03.valid1
#print axioms N11Formalization.C450Source15GroupedC03.valid2
#print axioms N11Formalization.C450Source15GroupedC03.valid3
#print axioms N11Formalization.C450Source15GroupedC03.valid4
#print axioms N11Formalization.C450Source15GroupedC03.valid5
#print axioms N11Formalization.C450Source15GroupedC03.valid6
#print axioms N11Formalization.C450Source15GroupedC03.valid7
#print axioms N11Formalization.C450Source15GroupedC03.valid8
#print axioms N11Formalization.C450Source15GroupedC03.valid9
#print axioms N11Formalization.C450Source15GroupedC03.valid10
#print axioms N11Formalization.C450Source15GroupedC03.valid11
#print axioms N11Formalization.C450Source15GroupedC03.valid12
#print axioms N11Formalization.C450Source15GroupedC03.valid13
#print axioms N11Formalization.C450Source15GroupedC03.valid14
#print axioms N11Formalization.C450Source15GroupedC03.valid15
#print axioms N11Formalization.C450Source15GroupedC03.valid16
#print axioms N11Formalization.C450Source15GroupedC03.valid17
#print axioms N11Formalization.C450Source15GroupedC03.valid18
#print axioms N11Formalization.C450Source15GroupedC03.valid19
#print axioms N11Formalization.C450Source15GroupedC03.valid20
#print axioms N11Formalization.C450Source15GroupedC03.valid21
#print axioms N11Formalization.C450Source15GroupedC03.valid22
#print axioms N11Formalization.C450Source15GroupedC03.valid23
#print axioms N11Formalization.C450Source15GroupedC03.valid24
#print axioms N11Formalization.C450Source15GroupedC03.valid25
#print axioms N11Formalization.C450Source15GroupedC03.valid26
#print axioms N11Formalization.C450Source15GroupedC03.valid27
#print axioms N11Formalization.C450Source15GroupedC03.bound
#print axioms N11Formalization.C450Source15GroupedC03.endpoint_checks
