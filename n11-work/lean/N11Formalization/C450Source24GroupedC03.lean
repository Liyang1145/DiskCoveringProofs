import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1723434939:ℚ)/2500000000),((7048508663:ℚ)/10000000000),((-42299560641:ℚ)/49600000000),((-18724654207:ℚ)/25037500000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((1086307093:ℚ)/2500000000),((607039863088579113678914283350558423272172832543188735930029:ℚ)/2447805647237120000000000000000000000000000000000000000000000),((53634466817197868427640269:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((695331711:ℚ)/1000000000),((7108033127:ℚ)/10000000000),((-42716231889:ℚ)/50075000000),((-7567312243:ℚ)/10110000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((207755531:ℚ)/500000000),((33145729637682310677868430399198078422880119450975081590887303:ℚ)/133688469696146923828125000000000000000000000000000000000000000),((53754867398438298961438829:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7012890641:ℚ)/10000000000),((3568897153:ℚ)/5000000000),((-7154093357:ℚ)/8425000000),((-76447578333:ℚ)/101575000000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3956434501:ℚ)/10000000000),((1878763998838561191895591188214719489651438712386274933946873:ℚ)/7712468506697473144531250000000000000000000000000000000000000),((13453769689864971784370109:ℚ)/18483200000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((880334501:ℚ)/1250000000),((7167554797:ℚ)/10000000000),((-43132883579:ℚ)/50787500000),((-9604348513:ℚ)/12756250000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((1926737157:ℚ)/5000000000),((1536286503143186623674997387344831878567865438319896701359:ℚ)/6306666267320644378662109375000000000000000000000000000000),((53875297528249086864715909:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7072460459:ℚ)/10000000000),((719731461:ℚ)/1000000000),((-4334120227:ℚ)/5102500000),((-25740661989:ℚ)/34175000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((1873917441:ℚ)/5000000000),((141730248156895593098634104994982032843063025889414933350309:ℚ)/581831666644356774902343750000000000000000000000000000000000),((1618065711733035493146463:ℚ)/2217984000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((7102244007:ℚ)/10000000000),((903384219:ℚ)/1250000000),((-5443689533:ℚ)/6407812500),((-77609172091:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3639282351:ℚ)/10000000000),((203977567385358116426970517652034504087364231771036096368397:ℚ)/837384832044192123413085937500000000000000000000000000000000),((2531051126324253616138783:ℚ)/3465600000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1426405333:ℚ)/2000000000),((1810488269:ℚ)/2500000000),((-10913417883:ℚ)/12875000000),((-5199756443:ℚ)/6882500000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((3527547237:ℚ)/10000000000),((12206986939565358189110409232821167006649432901141073835641847:ℚ)/50548021042132568359375000000000000000000000000000000000000000),((3376617311231059798542661:ℚ)/4620800000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((223341177:ℚ)/312500000),((1451366447:ℚ)/2000000000),((-8751565129:ℚ)/10323750000),((-2443435301:ℚ)/3233593750),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((694078063:ℚ)/2000000000),((426762147638442468678241651712612971275587533750184244192823:ℚ)/1767154685550900926330566406250000000000000000000000000000000),((2162239938535854816588509:ℚ)/2957312000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1432361689:ℚ)/2000000000),((14202561:ℚ)/19531250),((-1370686832:ℚ)/1616796875),((-15676701957:ℚ)/20742500000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((1706158173:ℚ)/5000000000),((1756574800524844548709335886075521407828327713742307142501231:ℚ)/7273585899410132126510143280029296875000000000000000000000000),((309483271514986214219:ℚ)/423046875000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((717669901:ℚ)/1000000000),((7286590067:ℚ)/10000000000),((-43966130469:ℚ)/51856250000),((-7857708713:ℚ)/10395000000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((3353277609:ℚ)/10000000000),((1805038034773907850183268717741485318926162843645543853064327:ℚ)/7474149523907911491394042968750000000000000000000000000000000),((54116247045485093504693189:ℚ)/73932800000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((89894867:ℚ)/125000000),((3650734371:ℚ)/5000000000),((-22035140597:ℚ)/25987500000),((-984633271:ℚ)/1302343750),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((3293222147:ℚ)/10000000000),((3943744564920469843445535174860425829613569585476848886444013:ℚ)/16329690431963896179199218750000000000000000000000000000000000),((40609780610835423946347823:ℚ)/55449600000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((900809937:ℚ)/1250000000),((7316347257:ℚ)/10000000000),((-44174430799:ℚ)/52093750000),((-9870529181:ℚ)/13053125000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((808023303:ℚ)/2500000000),((465385314803473229734911437429423462815846084315699190151307579:ℚ)/1926973957840939211845397949218750000000000000000000000000000000),((162529509376495470676602247:ℚ)/221798400000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((361068471:ℚ)/500000000),((3665612807:ℚ)/5000000000),((-22139289649:ℚ)/26106250000),((-3957890123:ℚ)/5233125000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((3169828623:ℚ)/10000000000),((235357627737267310550411292488954055304783148378641901564046589:ℚ)/974508632523070918464660644531250000000000000000000000000000000),((13551658495654588695355949:ℚ)/18483200000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3618129567:ℚ)/5000000000),((7346103813:ℚ)/10000000000),((-44382726691:ℚ)/52331250000),((-39675684371:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3106360011:ℚ)/10000000000),((29755854982211866174208993012638664688742212592525206414596351:ℚ)/123203865057399352455139160156250000000000000000000000000000000),((162710300157210274706055007:ℚ)/221798400000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7251148639:ℚ)/10000000000),((7360981857:ℚ)/10000000000),((-44486872999:ℚ)/52450000000),((-79544932307:ℚ)/105137500000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((380201491:ℚ)/1250000000),((7704334634750397822484628300102973845082174494463060563175777771:ℚ)/31899344969599112890625000000000000000000000000000000000000000000),((162800704022580549083395447:ℚ)/221798400000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((454127371:ℚ)/625000000),((1475171949:ℚ)/2000000000),((-8918203643:ℚ)/10513750000),((-4983655823:ℚ)/6585937500),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((743875193:ℚ)/2500000000),((6233565290018599297400401829131196703145196387016555162127:ℚ)/25809411910176063171386718750000000000000000000000000000000),((6515644541507307536130703:ℚ)/8871936000000000000000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7280927027:ℚ)/10000000000),((370280753:ℚ)/500000000),((-2239965271:ℚ)/2634375000),((-79932051351:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((726983373:ℚ)/2500000000),((20787346292682582009050788593805528883886680880639828431197:ℚ)/85349950173496341705322265625000000000000000000000000000000),((135893291298997983991709:ℚ)/184832000000000000000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1462140919:ℚ)/2000000000),((929421221:ℚ)/1250000000),((-5625948547:ℚ)/6615625000),((-16063831947:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((553600287:ℚ)/2000000000),((3985994000985294611871634264815101343519946573898228267137863:ℚ)/16366409984356357288360595703125000000000000000000000000000000),((850275043123442639641141:ℚ)/1155200000000000000000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((1468096271:ℚ)/2000000000),((59720991:ℚ)/80000000),((-361726937:ℚ)/425300000),((-16141251523:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((524162707:ℚ)/2000000000),((1043442955442111184050251244243109425009715288070577183:ℚ)/4284485735175822656250000000000000000000000000000000000),((10459756143056373569143:ℚ)/14195097600000000000000)⟩
theorem valid18 : Valid source24 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((3685128659:ℚ)/5000000000),((7524630323:ℚ)/10000000000),((-15210804087:ℚ)/17800000000),((-40546672567:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2465069649:ℚ)/10000000000),((3165239318651145708783580726634437516874335525475650674867:ℚ)/12788647110253906250000000000000000000000000000000000000000),((54598507022978907908585029:ℚ)/73932800000000000000000000)⟩
theorem valid19 : Valid source24 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7429806893:ℚ)/10000000000),((1516826893:ℚ)/2000000000),((-9209788251:ℚ)/10775000000),((-81867489609:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2120278909:ℚ)/10000000000),((1142968954226215033898938449836088316353409992211183081780631:ℚ)/4619138096331982421875000000000000000000000000000000000000000),((2188765918910943719230149:ℚ)/2957312000000000000000000)⟩
theorem valid20 : Valid source24 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7489353403:ℚ)/10000000000),((7703136073:ℚ)/10000000000),((-46881952511:ℚ)/54350000000),((-82641594239:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((427115717:ℚ)/2500000000),((3317514219370675731327722692534475230820183132707918475849:ℚ)/13005141415264892578125000000000000000000000000000000000000),((94791067:ℚ)/128000000)⟩
theorem valid21 : Valid source24 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7608437547:ℚ)/10000000000),((7941114141:ℚ)/10000000000),((-48547798987:ℚ)/55300000000),((-84189688111:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((59503774889796125284238966762686845551813313108563186217807:ℚ)/220547129928125000000000000000000000000000000000000000000000),((94791067:ℚ)/128000000)⟩
theorem valid22 : Valid source24 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((1569314481:ℚ)/2000000000),((4446372681:ℚ)/5000000000),((-27604608767:ℚ)/28600000000),((-17457088253:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((14158159385188756269514663825135583819767014901803127287121:ℚ)/39970254431250000000000000000000000000000000000000000000000),((94791067:ℚ)/128000000)⟩
theorem valid23 : Valid source24 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((68740143:ℚ)/78125000),((9844033413:ℚ)/10000000000),((-61868233891:ℚ)/64800000000),((-778621859:ℚ)/1131250000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),(0:ℚ),((1768796667885097941285128358189972787265310755779951363591117:ℚ)/5223161580300000000000000000000000000000000000000000000000000),((94791067:ℚ)/128000000)⟩
theorem valid24 : Valid source24 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((9750448243:ℚ)/10000000000),((10795076329:ℚ)/10000000000),((-68525534303:ℚ)/72400000000),((-112035827159:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((97168646561275585549910523525028608953968823753347571843:ℚ)/296487050000000000000000000000000000000000000000000000000),((94791067:ℚ)/128000000)⟩
theorem valid25 : Valid source24 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((5350916289:ℚ)/5000000000),((1459781063:ℚ)/1000000000),(-1:ℚ),((-62201911757:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1311427325515206250809012257:ℚ)/3047040000000000000000000000),((94791067:ℚ)/128000000)⟩
theorem valid26 : Valid source24 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((2003:ℚ)/3200) ((4063:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((4063:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((4063:ℚ)/6400) ((103:ℚ)/160) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((8259:ℚ)/12800) ((8297:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((8297:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((8297:ℚ)/12800) ((1667:ℚ)/2560) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source24 nn0 nn1 Qcell ((1667:ℚ)/2560) ((8373:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source24 nn0 nn1 Qcell ((8297:ℚ)/12800) ((8373:ℚ)/12800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((8373:ℚ)/12800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((8373:ℚ)/12800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source24 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source24 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source24 nn0 nn1 Qcell ((843:ℚ)/1280) ((431:ℚ)/640) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((143:ℚ)/200) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((181:ℚ)/200) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound source24 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound source24 nn0 nn1 Qcell ((8373:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC03
#check @N11Formalization.C450Source24GroupedC03.bound
#print axioms N11Formalization.C450Source24GroupedC03.valid0
#print axioms N11Formalization.C450Source24GroupedC03.valid1
#print axioms N11Formalization.C450Source24GroupedC03.valid2
#print axioms N11Formalization.C450Source24GroupedC03.valid3
#print axioms N11Formalization.C450Source24GroupedC03.valid4
#print axioms N11Formalization.C450Source24GroupedC03.valid5
#print axioms N11Formalization.C450Source24GroupedC03.valid6
#print axioms N11Formalization.C450Source24GroupedC03.valid7
#print axioms N11Formalization.C450Source24GroupedC03.valid8
#print axioms N11Formalization.C450Source24GroupedC03.valid9
#print axioms N11Formalization.C450Source24GroupedC03.valid10
#print axioms N11Formalization.C450Source24GroupedC03.valid11
#print axioms N11Formalization.C450Source24GroupedC03.valid12
#print axioms N11Formalization.C450Source24GroupedC03.valid13
#print axioms N11Formalization.C450Source24GroupedC03.valid14
#print axioms N11Formalization.C450Source24GroupedC03.valid15
#print axioms N11Formalization.C450Source24GroupedC03.valid16
#print axioms N11Formalization.C450Source24GroupedC03.valid17
#print axioms N11Formalization.C450Source24GroupedC03.valid18
#print axioms N11Formalization.C450Source24GroupedC03.valid19
#print axioms N11Formalization.C450Source24GroupedC03.valid20
#print axioms N11Formalization.C450Source24GroupedC03.valid21
#print axioms N11Formalization.C450Source24GroupedC03.valid22
#print axioms N11Formalization.C450Source24GroupedC03.valid23
#print axioms N11Formalization.C450Source24GroupedC03.valid24
#print axioms N11Formalization.C450Source24GroupedC03.valid25
#print axioms N11Formalization.C450Source24GroupedC03.valid26
#print axioms N11Formalization.C450Source24GroupedC03.bound
#print axioms N11Formalization.C450Source24GroupedC03.endpoint_checks
