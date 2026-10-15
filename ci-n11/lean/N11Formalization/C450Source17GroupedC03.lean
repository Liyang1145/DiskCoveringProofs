import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6677625703:ℚ)/10000000000),((107361703:ℚ)/156250000),((-676531921:ℚ)/775000000),((-25523044713:ℚ)/33700000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2489002227:ℚ)/5000000000),((2989149039195471047073679505927047513499:ℚ)/42291675987500000000000000000000000000000),((226765504780207209738187:ℚ)/451250000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((6796561561:ℚ)/10000000000),((6990039369:ℚ)/10000000000),((-14710091861:ℚ)/16850000000),((-78115300293:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2319833811:ℚ)/5000000000),((699437022281958364557266058798421442960621291842739963173:ℚ)/9912979408618164062500000000000000000000000000000000000000),((2794356509064994184122113169:ℚ)/5544960000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((6915490547:ℚ)/10000000000),((7049482629:ℚ)/10000000000),((-44546378403:ℚ)/51500000000),((-79661377111:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4276739151:ℚ)/10000000000),((44974359003308987256128768470303112141470295485158412280167:ℚ)/665560380761718750000000000000000000000000000000000000000000),((2798287867941487971561104089:ℚ)/5544960000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((348747629:ℚ)/500000000),((7079203793:ℚ)/10000000000),((-44754426551:ℚ)/51975000000),((-4021719177:ℚ)/5221250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((2042006361:ℚ)/5000000000),((11506359246198135041534258061440930784807701868381515421463397:ℚ)/173984191658576916503906250000000000000000000000000000000000000),((933417879955111785910165707:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3502341501:ℚ)/5000000000),((1777231163:ℚ)/2500000000),((-11240618141:ℚ)/13053125000),((-40410439513:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1992181309:ℚ)/5000000000),((126446084188166313485079550624807371081936199837568579272577:ℚ)/1911985073830757927894592285156250000000000000000000000000000),((58379572371200673125367667:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((3517206517:ℚ)/5000000000),((7138645209:ℚ)/10000000000),((-45170516463:ℚ)/52450000000),((-40603684721:ℚ)/52687500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((48528711:ℚ)/125000000),((211911466869103051539834097072099618941299508069694511080559:ℚ)/3204362558168753906250000000000000000000000000000000000000000),((2804185369994290324777123249:ℚ)/5544960000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3532071341:ℚ)/5000000000),((7168365469:ℚ)/10000000000),((-45378558283:ℚ)/52687500000),((-40796927433:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((1888809609:ℚ)/5000000000),((1557037868308938126873236143835079873558987954785329993835837:ℚ)/23544813840964508056640625000000000000000000000000000000000000),((935383776241184808109765123:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7093871951:ℚ)/10000000000),((7183225489:ℚ)/10000000000),((-45482578423:ℚ)/52925000000),((-81980335363:ℚ)/106087500000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((1835052823:ℚ)/5000000000),((242609660876082479904158617967550063851011589991048561753127679:ℚ)/3707648176519615869140625000000000000000000000000000000000000000),((935711443878534014567837003:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1421747289:ℚ)/2000000000),((1799521359:ℚ)/2500000000),((-3798883171:ℚ)/4420312500),((-16434714757:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((361520643:ℚ)/1000000000),((2597246969659310948025333482410865483266723030893875668609:ℚ)/39691233521162116527557373046875000000000000000000000000000),((175507334391723253038966049:ℚ)/346560000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-7:ℚ)/8),((-13:ℚ)/16),((3561800423:ℚ)/5000000000),((7212945311:ℚ)/10000000000),((-45690617177:ℚ)/53162500000),((-41183405499:ℚ)/53281250000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((1779749343:ℚ)/5000000000),((389754335381208307420675747493256802204469089164732722833:ℚ)/5956121216090090332031250000000000000000000000000000000000),((936366794895105300687413803:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((1427693031:ℚ)/2000000000),((3613902557:ℚ)/5000000000),((-22897317899:ℚ)/26640625000),((-16512009403:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((875735943:ℚ)/2500000000),((1102558556982598594600402078778995651966766455216605802506323:ℚ)/16848675413542985916137695312500000000000000000000000000000000),((234173619574044576057195907:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1788332343:ℚ)/2500000000),((1448532969:ℚ)/2000000000),((-3059910261:ℚ)/3560000000),((-20688320459:ℚ)/26759375000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((344549991:ℚ)/1000000000),((676543892688398941290834608285360264335700348856242789869717:ℚ)/10338366014192200000000000000000000000000000000000000000000000),((112442660035077215624380369:ℚ)/221798400000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3584096749:ℚ)/5000000000),((3628762253:ℚ)/5000000000),((-23001335771:ℚ)/26759375000),((-41473257737:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((1693560901:ℚ)/5000000000),((1127371170133069776117817538905087065279137515521716846732203:ℚ)/17227211033737012009322643280029296875000000000000000000000000),((649134252719880090679467:ℚ)/1280000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3591528767:ℚ)/5000000000),((227262003:ℚ)/312500000),((-1440834021:ℚ)/1676171875),((-13856624657:ℚ)/17918750000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((831940053:ℚ)/2500000000),((21053909001509856219536119216734031978718000718727697567:ℚ)/321716407405298133380711078643798828125000000000000000000),((2747102227088725755506761:ℚ)/5415000000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((179948037:ℚ)/250000000),((227726363:ℚ)/312500000),((-61450406:ℚ)/71484375),((-2083324481:ℚ)/2693750000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((326736147:ℚ)/1000000000),((2601992408314876900719148520304910919402319029650979:ℚ)/39759343732392881065607070922851562500000000000000000),((916020766344987283261267:ℚ)/1805000000000000000000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((901598167:ℚ)/1250000000),((7302103067:ℚ)/10000000000),((-46314721469:ℚ)/53875000000),((-10440776171:ℚ)/13498437500),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((3205866889:ℚ)/10000000000),((3660707558097046651128916062889022148521364137542126257599351:ℚ)/55935976410212707519531250000000000000000000000000000000000000),((938332974622410016045042227:ℚ)/1848320000000000000000000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1445529821:ℚ)/2000000000),((7316962449:ℚ)/10000000000),((-46418737143:ℚ)/53993750000),((-5581295891:ℚ)/7215000000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((314321207:ℚ)/1000000000),((4189610909866740972840365316590536613934584722629569961930151:ℚ)/64016684130497771787643432617187500000000000000000000000000000),((2815982069504856277814696929:ℚ)/5544960000000000000000000000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1448502557:ℚ)/2000000000),((7346681007:ℚ)/10000000000),((-15542255683:ℚ)/18037500000),((-16782533241:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3079326131:ℚ)/10000000000),((12907702947358960251273789706849819316557746218140231275629:ℚ)/195215889238604736328125000000000000000000000000000000000000),((2817948408791721889654765921:ℚ)/5544960000000000000000000000)⟩
theorem valid17 : Valid source17 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7272239883:ℚ)/10000000000),((1475279859:ℚ)/2000000000),((-9366959013:ℚ)/10870000000),((-84299118479:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((2947538851:ℚ)/10000000000),((28754893234052555236716188730612339207761749935582349724959:ℚ)/434902966442499414062500000000000000000000000000000000000000),((112796592496038550645203049:ℚ)/221798400000000000000000000)⟩
theorem valid18 : Valid source17 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1825491659:ℚ)/2500000000),((1851529329:ℚ)/2500000000),((-11760705303:ℚ)/13646875000),((-21171391567:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((2809766271:ℚ)/10000000000),((14682590934824920169533156187905919891621044415025432650893:ℚ)/222074390552866673469543457031250000000000000000000000000000),((176367580033053667114723489:ℚ)/346560000000000000000000000)⟩
theorem valid19 : Valid source17 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((916461631:ℚ)/1250000000),((7465552569:ℚ)/10000000000),((-15819622661:ℚ)/18275000000),((-1519143029:ℚ)/1975000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1332539827:ℚ)/5000000000),((376257734319993478819590650735277005761765897879579417031:ℚ)/5579787272028350830078125000000000000000000000000000000000),((2825814411125880678811379569:ℚ)/5544960000000000000000000000)⟩
theorem valid20 : Valid source17 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((1847786217:ℚ)/2500000000),((7584420019:ℚ)/10000000000),((-48290940133:ℚ)/55300000000),((-21461220821:ℚ)/28125000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((293724659:ℚ)/1250000000),((142717599857638697387423025059326998117591445018543580441:ℚ)/2038408115625000000000000000000000000000000000000000000000),((2616511039928574830828843:ℚ)/5120000000000000000000000)⟩
theorem valid21 : Valid source17 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((117344447:ℚ)/156250000),((7703283561:ℚ)/10000000000),((-16374328309:ℚ)/18750000000),((-1365477811:ℚ)/1787500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((770053869:ℚ)/5000000000),((2677377163986568014069367241027924407253047733220236012503:ℚ)/38294219970703125000000000000000000000000000000000000000000),((65436581:ℚ)/128000000)⟩
theorem valid22 : Valid source17 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((3814469683:ℚ)/5000000000),((8654071907:ℚ)/10000000000),((-55778503349:ℚ)/57200000000),((-44468105879:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((33377454093893731243494465833682801710248344027464101178791:ℚ)/319762035450000000000000000000000000000000000000000000000000),((65436581:ℚ)/128000000)⟩
theorem valid23 : Valid source17 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((857994439:ℚ)/1000000000),((211103977:ℚ)/200000000),(-1:ℚ),((-10129927707:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((27957348762225857373177792786352171:ℚ)/240000000000000000000000000000000000),((65436581:ℚ)/128000000)⟩
theorem valid24 : Valid source17 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5240690469:ℚ)/5000000000),((14356521303:ℚ)/10000000000),(-1:ℚ),((-63008976097:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((196587337729375782863288747:ℚ)/1523520000000000000000000000),((65436581:ℚ)/128000000)⟩
theorem valid25 : Valid source17 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((4291:ℚ)/6400) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((8639:ℚ)/12800) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8639:ℚ)/12800) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source17 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4367:ℚ)/6400) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC03
#check @N11Formalization.C450Source17GroupedC03.bound
#print axioms N11Formalization.C450Source17GroupedC03.valid0
#print axioms N11Formalization.C450Source17GroupedC03.valid1
#print axioms N11Formalization.C450Source17GroupedC03.valid2
#print axioms N11Formalization.C450Source17GroupedC03.valid3
#print axioms N11Formalization.C450Source17GroupedC03.valid4
#print axioms N11Formalization.C450Source17GroupedC03.valid5
#print axioms N11Formalization.C450Source17GroupedC03.valid6
#print axioms N11Formalization.C450Source17GroupedC03.valid7
#print axioms N11Formalization.C450Source17GroupedC03.valid8
#print axioms N11Formalization.C450Source17GroupedC03.valid9
#print axioms N11Formalization.C450Source17GroupedC03.valid10
#print axioms N11Formalization.C450Source17GroupedC03.valid11
#print axioms N11Formalization.C450Source17GroupedC03.valid12
#print axioms N11Formalization.C450Source17GroupedC03.valid13
#print axioms N11Formalization.C450Source17GroupedC03.valid14
#print axioms N11Formalization.C450Source17GroupedC03.valid15
#print axioms N11Formalization.C450Source17GroupedC03.valid16
#print axioms N11Formalization.C450Source17GroupedC03.valid17
#print axioms N11Formalization.C450Source17GroupedC03.valid18
#print axioms N11Formalization.C450Source17GroupedC03.valid19
#print axioms N11Formalization.C450Source17GroupedC03.valid20
#print axioms N11Formalization.C450Source17GroupedC03.valid21
#print axioms N11Formalization.C450Source17GroupedC03.valid22
#print axioms N11Formalization.C450Source17GroupedC03.valid23
#print axioms N11Formalization.C450Source17GroupedC03.valid24
#print axioms N11Formalization.C450Source17GroupedC03.valid25
#print axioms N11Formalization.C450Source17GroupedC03.bound
#print axioms N11Formalization.C450Source17GroupedC03.endpoint_checks
