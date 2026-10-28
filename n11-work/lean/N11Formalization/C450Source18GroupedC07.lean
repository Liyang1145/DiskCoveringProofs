import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((3268689041:ℚ)/5000000000),((6840577237:ℚ)/10000000000),((-5816577237:ℚ)/9920000000),((-23978201369:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2675856053:ℚ)/5000000000),((2226032428090223636127330682621175089474759884801322443791:ℚ)/32363798425600000000000000000000000000000000000000000000000),((1298860494598137771607887:ℚ)/4620800000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3387857783:ℚ)/5000000000),((6959725633:ℚ)/10000000000),((-5935725633:ℚ)/10300000000),((-25050720047:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((940118197:ℚ)/2000000000),((62113903119044655772614225114133022504385638132499351030419:ℚ)/939404596505468750000000000000000000000000000000000000000000),((1290068349807117434415903:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6894861439:ℚ)/10000000000),((7019294441:ℚ)/10000000000),((-5995294441:ℚ)/10490000000),((-51173752951:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4341721163:ℚ)/10000000000),((14365720940312945658595219736800796518604049512363615255299:ℚ)/221460023762678125000000000000000000000000000000000000000000),((5142544559816810427545967:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((6954429021:ℚ)/10000000000),((1415771957:ℚ)/2000000000),((-1210971957:ℚ)/2117000000),((-51709861189:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((4151484669:ℚ)/10000000000),((52213091144738105418634105590757480605922153471463503:ℚ)/804284608203906250000000000000000000000000000000000000),((5133643964937510776954407:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((175349829:ℚ)/250000000),((1784605439:ℚ)/2500000000),((-1528605439:ℚ)/2670000000),((-1306148461:ℚ)/2693750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1976334363:ℚ)/5000000000),((8412202929852251916878515856534233317125279048123790671:ℚ)/129485051991320800781250000000000000000000000000000000000),((3202949525111698746007:ℚ)/11552000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((1768388487:ℚ)/2500000000),((1433640301:ℚ)/2000000000),((-1228840301:ℚ)/2155000000),((-13195496383:ℚ)/27056250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3743902529:ℚ)/10000000000),((2357927617605591162781839479279285755759570509092650309087:ℚ)/36630853186543725585937500000000000000000000000000000000000),((319735648498254205936063:ℚ)/1155200000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((7103333113:ℚ)/10000000000),((1799495111:ℚ)/2500000000),((-1543495111:ℚ)/2705625000),((-53049998017:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((727050851:ℚ)/2000000000),((84854902671492595020239661271953955802194382249942669729:ℚ)/1317707252360581970214843750000000000000000000000000000000),((5111286888713479929619263:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7133111473:ℚ)/10000000000),((903469823:ℚ)/1250000000),((-775469823:ℚ)/1358750000),((-53318003257:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((704682677:ℚ)/2000000000),((601926366551258734314380492561531730103325324117180577789:ℚ)/9343618419663073348999023437500000000000000000000000000000),((5106797363200183046151183:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7162889039:ℚ)/10000000000),((1451507187:ℚ)/2000000000),((-113337017:ℚ)/198500000),((-53586001351:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((681613011:ℚ)/2000000000),((1893839401852911463485661433961261591592038421801381531:ℚ)/29386565183542675781250000000000000000000000000000000000),((5102301798269871916951567:ℚ)/18483200000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((3596332911:ℚ)/5000000000),((7287312507:ℚ)/10000000000),((-6263312507:ℚ)/10965000000),((-26926996199:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((3288839653:ℚ)/10000000000),((51537574566226452077404877644676192154290107086225804539881:ℚ)/799406647285564160156250000000000000000000000000000000000000),((1274450048187781954092367:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((722244183:ℚ)/1000000000),((7317088311:ℚ)/10000000000),((-6293088311:ℚ)/11012500000),((-5412197647:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((197831157:ℚ)/625000000),((7716908862384212835290254137939794807956886334299737356863:ℚ)/119654579520245933532714843750000000000000000000000000000000),((50932925459178844500703:ℚ)/184832000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((290088683:ℚ)/400000000),((1844159413:ℚ)/2500000000),((-1588159413:ℚ)/2765000000),((-2175598147:ℚ)/4462000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3036914357:ℚ)/10000000000),((2420484271916277660673455041183415470584924926354061423:ℚ)/37161176514868164062500000000000000000000000000000000000),((8142046170289060539703:ℚ)/29573120000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((3655882657:ℚ)/5000000000),((7436184037:ℚ)/10000000000),((-6412184037:ℚ)/11155000000),((-27462943913:ℚ)/56250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((43170151:ℚ)/156250000),((89445856791421960695120357437329776020113662662263259:ℚ)/1372472967027282714843750000000000000000000000000000000),((1269933336401940564479023:ℚ)/4620800000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((3685655307:ℚ)/5000000000),((755526823:ℚ)/1000000000),((-72569647:ℚ)/125000000),((-27730897763:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2459383661:ℚ)/10000000000),((8288234989640963840904877312239298591974719120952821:ℚ)/124810791015625000000000000000000000000000000000000000),((1267665913145799493263223:ℚ)/4620800000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((3745196347:ℚ)/5000000000),((243543883:ℚ)/312500000),((-211543883:ℚ)/357500000),((-28266767123:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1700400757:ℚ)/10000000000),((285768721209815607256398649326225053272551179789677987:ℚ)/4155964946154785156250000000000000000000000000000000000),((1263112922242728104467543:ℚ)/4620800000000000000000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((7728524697:ℚ)/10000000000),((250984391:ℚ)/312500000),((-72994797:ℚ)/123125000),((-58676722273:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((47723888086499109662049803123870386813366182591188283:ℚ)/694541819653320312500000000000000000000000000000000000),((8718147:ℚ)/32000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7966617183:ℚ)/10000000000),((8507587769:ℚ)/10000000000),((-7483587769:ℚ)/12200000000),((-60819554647:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2711339215500451174314625433156594092630220739702714647387:ℚ)/37230558525000000000000000000000000000000000000000000000000),((8718147:ℚ)/32000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8442697567:ℚ)/10000000000),((5205450657:ℚ)/5000000000),((-4693450657:ℚ)/6480000000),((-65104278103:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((242050247609465840895926902254693705294261025909419137:ℚ)/2550916800000000000000000000000000000000000000000000000),((8718147:ℚ)/32000000)⟩
theorem valid17 : Valid source18 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((1293248773:ℚ)/1250000000),((1776848373:ℚ)/1250000000),((-1648848373:ℚ)/2000000000),((-10279238957:ℚ)/27600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3527647258043052313121540736547086875209773844244897791:ℚ)/29756250000000000000000000000000000000000000000000000000),((8718147:ℚ)/32000000)⟩
theorem valid18 : Valid source18 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC07
#check @N11Formalization.C450Source18GroupedC07.bound
#print axioms N11Formalization.C450Source18GroupedC07.valid0
#print axioms N11Formalization.C450Source18GroupedC07.valid1
#print axioms N11Formalization.C450Source18GroupedC07.valid2
#print axioms N11Formalization.C450Source18GroupedC07.valid3
#print axioms N11Formalization.C450Source18GroupedC07.valid4
#print axioms N11Formalization.C450Source18GroupedC07.valid5
#print axioms N11Formalization.C450Source18GroupedC07.valid6
#print axioms N11Formalization.C450Source18GroupedC07.valid7
#print axioms N11Formalization.C450Source18GroupedC07.valid8
#print axioms N11Formalization.C450Source18GroupedC07.valid9
#print axioms N11Formalization.C450Source18GroupedC07.valid10
#print axioms N11Formalization.C450Source18GroupedC07.valid11
#print axioms N11Formalization.C450Source18GroupedC07.valid12
#print axioms N11Formalization.C450Source18GroupedC07.valid13
#print axioms N11Formalization.C450Source18GroupedC07.valid14
#print axioms N11Formalization.C450Source18GroupedC07.valid15
#print axioms N11Formalization.C450Source18GroupedC07.valid16
#print axioms N11Formalization.C450Source18GroupedC07.valid17
#print axioms N11Formalization.C450Source18GroupedC07.valid18
#print axioms N11Formalization.C450Source18GroupedC07.bound
#print axioms N11Formalization.C450Source18GroupedC07.endpoint_checks
