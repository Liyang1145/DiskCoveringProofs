import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((54071867:ℚ)/80000000),((3479375001:ℚ)/5000000000),(-1:ℚ),((-145831601:ℚ)/161760000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((189958717:ℚ)/400000000),((826773321228751629786978733127:ℚ)/10902624000000000000000000000000),((6943879604192982436256647:ℚ)/10830000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((13755599:ℚ)/20000000),((3509062501:ℚ)/5000000000),(-1:ℚ),((-37170797:ℚ)/40820000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4394786159:ℚ)/10000000000),((2841330755619203636502412851:ℚ)/38514062500000000000000000000),((2319850994359869190210549:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((6937206639:ℚ)/10000000000),((7077500003:ℚ)/10000000000),(-1:ℚ),((-18763619917:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((2103658383:ℚ)/5000000000),((117214562538385970267566718194354051:ℚ)/1591350000000000000000000000000000000),((9300317438488324785019941:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((109322081:ℚ)/156250000),((7107187503:ℚ)/10000000000),(-1:ℚ),((-295966243:ℚ)/323359375),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((4011642289:ℚ)/10000000000),((7597800050491518197110395114329:ℚ)/104561285400390625000000000000000),((27932340081463716945684823:ℚ)/43320000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7026316239:ℚ)/10000000000),((3568437501:ℚ)/5000000000),(-1:ℚ),((-1730086247:ℚ)/1890000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3910344097:ℚ)/10000000000),((2573282535588589739457342773429:ℚ)/35437500000000000000000000000000),((6990934890760084401881647:ℚ)/10830000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((441001197:ℚ)/625000000),((3583281251:ℚ)/5000000000),(-1:ℚ),((-1195003591:ℚ)/1305312500),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3806493771:ℚ)/10000000000),((9891358119529915629914373363525689:ℚ)/136307257812500000000000000000000000),((2332929230192514158960549:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((283428877:ℚ)/400000000),((1795351563:ℚ)/2500000000),(-1:ℚ),((-768366631:ℚ)/837300000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((3699875929:ℚ)/10000000000),((63168253193068955585474845634459:ℚ)/876339112500000000000000000000000),((1750678797230218086114943:ℚ)/2707500000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7100573259:ℚ)/10000000000),((3598125001:ℚ)/5000000000),(-1:ℚ),((-19253719777:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((911363351:ℚ)/2500000000),((59471284198442208285972459103492487:ℚ)/825300750000000000000000000000000000),((2335547806517978699585549:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7115424559:ℚ)/10000000000),((901386719:ℚ)/1250000000),(-1:ℚ),((-19298273677:ℚ)/21027500000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((3590243531:ℚ)/10000000000),((4976911951187607618201630236918849:ℚ)/69086836914062500000000000000000000),((146053591301598619578589:ℚ)/225625000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((285211033:ℚ)/400000000),((3612968751:ℚ)/5000000000),(-1:ℚ),((-773713099:ℚ)/843000000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3534209349:ℚ)/10000000000),((6397356257746334538860963654333:ℚ)/88831125000000000000000000000000),((7014502077689265267506647:ℚ)/10830000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((843:ℚ)/1280),((16879:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7145127057:ℚ)/10000000000),((7233359377:ℚ)/10000000000),(-1:ℚ),((-19387381171:ℚ)/21098750000),((9785026151:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((2077250707:ℚ)/10000000000),((869327737:ℚ)/2500000000),((479291284249065830796824065189879711:ℚ)/6677358773437500000000000000000000000),((9355289599872241651857821:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((16879:ℚ)/25600) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((16879:ℚ)/25600),((8449:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((357627633:ℚ)/500000000),((1810195313:ℚ)/2500000000),(-1:ℚ),((-970482899:ℚ)/1056125000),((4890720817:ℚ)/5000000000),((2446256539:ℚ)/2500000000),((83782417:ℚ)/400000000),((215532769:ℚ)/625000000),((100063061625662728807651681257647:ℚ)/1394250019531250000000000000000000),((584869375432627556829981:ℚ)/902500000000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((16879:ℚ)/25600) ((8449:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8449:ℚ)/12800),((16917:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((1431995651:ℚ)/2000000000),((7248203127:ℚ)/10000000000),(-1:ℚ),((-3886386953:ℚ)/4229250000),((1955574701:ℚ)/2000000000),((9781441639:ℚ)/10000000000),((105582607:ℚ)/500000000),((854876281:ℚ)/2500000000),((1283507547028310258914285514302273:ℚ)/17886555562500000000000000000000000),((28081591974205254386823463:ℚ)/43320000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((8449:ℚ)/12800) ((16917:ℚ)/25600) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((16917:ℚ)/25600),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3583701921:ℚ)/5000000000),((7255625003:ℚ)/10000000000),(-1:ℚ),((-9727105763:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((977787351:ℚ)/1000000000),((425706267:ℚ)/2000000000),((847561857:ℚ)/2500000000),((1039502558620515791369043301741001:ℚ)/14488218750000000000000000000000000),((9363151553664520903769941:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((16917:ℚ)/25600) ((2117:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2117:ℚ)/3200),((3391:ℚ)/5120),(-1:ℚ),((-15:ℚ)/16),((358741471:ℚ)/500000000),((3631523439:ℚ)/5000000000),(-1:ℚ),((-973824413:ℚ)/1059687500),((9770786189:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((536300817:ℚ)/2500000000),((672148997:ℚ)/2000000000),((4833442671504347144691160018141819:ℚ)/67376255859375000000000000000000000),((7024329519753065202534487:ℚ)/10830000000000000000000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((3391:ℚ)/5120) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((3391:ℚ)/5120),((8487:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((718225499:ℚ)/1000000000),((7270468753:ℚ)/10000000000),(-1:ℚ),((-84777239:ℚ)/92250000),((9767266893:ℚ)/10000000000),((4885393097:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3330991277:ℚ)/10000000000),((662337560336944203598931687:ℚ)/9234008789062500000000000000),((9368394076440230931894941:ℚ)/14440000000000000000000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((3391:ℚ)/5120) ((8487:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8487:ℚ)/12800),((16993:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7189680551:ℚ)/10000000000),((1819472657:ℚ)/2500000000),(-1:ℚ),((-19521041653:ℚ)/21241250000),((1952752753:ℚ)/2000000000),((4883633449:ℚ)/5000000000),((435589041:ℚ)/2000000000),((3300979507:ℚ)/10000000000),((1011204363905452251097360168026077:ℚ)/14099709423828125000000000000000000),((585688481498309555582301:ℚ)/902500000000000000000000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((16993:ℚ)/25600) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((16993:ℚ)/25600),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1439421221:ℚ)/2000000000),((7285312503:ℚ)/10000000000),(-1:ℚ),((-3908663663:ℚ)/4253000000),((9760276751:ℚ)/10000000000),((976376377:ℚ)/1000000000),((438804929:ℚ)/2000000000),((654140511:ℚ)/2000000000),((1621322806514195898190465450188277:ℚ)/22610011250000000000000000000000000),((28120912726806758426934823:ℚ)/43320000000000000000000000)⟩
theorem valid17 : Valid source17 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source17 nn0 nn1 Qcell ((16993:ℚ)/25600) ((4253:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4253:ℚ)/6400),((17031:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((144090633:ℚ)/200000000),((3646367189:ℚ)/5000000000),(-1:ℚ),((-391311899:ℚ)/425775000),((9756805797:ℚ)/10000000000),((2440069189:ℚ)/2500000000),((2209915701:ℚ)/10000000000),((3240152987:ℚ)/10000000000),((56413982835419783300117555043:ℚ)/786824438476562500000000000000),((2344064922832032672719829:ℚ)/3610000000000000000000000)⟩
theorem valid18 : Valid source17 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((17031:ℚ)/25600) :=
  cell_of_packet source17 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((17031:ℚ)/25600),((341:ℚ)/512),(-1:ℚ),((-15:ℚ)/16),((7211957187:ℚ)/10000000000),((7300156253:ℚ)/10000000000),(-1:ℚ),((-19587871561:ℚ)/21312500000),((195067017:ℚ)/200000000),((4878402901:ℚ)/5000000000),((1112811311:ℚ)/5000000000),((802330751:ℚ)/2500000000),((74005758122537798455442872106271:ℚ)/1032324218750000000000000000000000),((9378882051150586535019941:ℚ)/14440000000000000000000000)⟩
theorem valid19 : Valid source17 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source17 nn0 nn1 Qcell ((17031:ℚ)/25600) ((341:ℚ)/512) :=
  cell_of_packet source17 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((1804845679:ℚ)/2500000000),((3657500001:ℚ)/5000000000),(-1:ℚ),((-4902537037:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((3178204439:ℚ)/10000000000),((1281285339872778391521383318425687:ℚ)/17822250000000000000000000000000000),((7038095627048866055006647:ℚ)/10830000000000000000000000)⟩
theorem valid20 : Valid source17 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source17 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7234233749:ℚ)/10000000000),((916230469:ℚ)/1250000000),(-1:ℚ),((-19654701247:ℚ)/21407500000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((3115066857:ℚ)/10000000000),((3859890690230406686085354343961093:ℚ)/53704811279296875000000000000000000),((146708967672698641453589:ℚ)/225625000000000000000000)⟩
theorem valid21 : Valid source17 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((28996339:ℚ)/40000000),((3672343751:ℚ)/5000000000),(-1:ℚ),((-78797017:ℚ)/85820000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((152533317:ℚ)/500000000),((4134361151046052563224938904787:ℚ)/57539628125000000000000000000000),((2348655333939979137085549:ℚ)/3610000000000000000000000)⟩
theorem valid22 : Valid source17 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source17 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3631967859:ℚ)/5000000000),((1839882813:ℚ)/2500000000),(-1:ℚ),((-9871903577:ℚ)/10751250000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((2984921079:ℚ)/10000000000),((883307729550235156829606844110831:ℚ)/12296742187500000000000000000000000),((1762475571910018479864943:ℚ)/2707500000000000000000000)⟩
theorem valid23 : Valid source17 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((1455757331:ℚ)/2000000000),((3687187501:ℚ)/5000000000),(-1:ℚ),((-3957671993:ℚ)/4310000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((291774009:ℚ)/1000000000),((13027413313657773809429499168369:ℚ)/181407226562500000000000000000000),((2351279768583314771460549:ℚ)/3610000000000000000000000)⟩
theorem valid24 : Valid source17 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((182340939:ℚ)/250000000),((3702031251:ℚ)/5000000000),(-1:ℚ),((-495822817:ℚ)/541125000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((142451087:ℚ)/500000000),((422896546818666101279854349941049:ℚ)/5856325312500000000000000000000000),((7061715538838886764381647:ℚ)/10830000000000000000000000)⟩
theorem valid25 : Valid source17 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1830834819:ℚ)/2500000000),((3716875001:ℚ)/5000000000),(-1:ℚ),((-4980504457:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((541300331:ℚ)/2000000000),((7994537877639109427778173353243819:ℚ)/110772093750000000000000000000000000),((2356531567028921587085549:ℚ)/3610000000000000000000000)⟩
theorem valid26 : Valid source17 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1838260217:ℚ)/2500000000),((7493125003:ℚ)/10000000000),(-1:ℚ),((-5002780651:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1278126503:ℚ)/5000000000),((31869688297266713024892728210999:ℚ)/436886718750000000000000000000000),((9447149084433303228769941:ℚ)/14440000000000000000000000)⟩
theorem valid27 : Valid source17 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((1482488737:ℚ)/2000000000),((3776250001:ℚ)/5000000000),(-1:ℚ),((-4037866211:ℚ)/4424000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((22262363:ℚ)/100000000),((31829968737723859338652229215447:ℚ)/436870000000000000000000000000000),((2367046880555877405835549:ℚ)/3610000000000000000000000)⟩
theorem valid28 : Valid source17 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7471846023:ℚ)/10000000000),((7790000003:ℚ)/10000000000),(-1:ℚ),((-20367538069:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((73560793:ℚ)/400000000),((4598945522046729433119463190568773:ℚ)/59488000000000000000000000000000000),((328429:ℚ)/500000)⟩
theorem valid29 : Valid source17 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((7709450833:ℚ)/10000000000),((8740000003:ℚ)/10000000000),(-1:ℚ),((-21080352499:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((76413987122170213617109848785037557:ℚ)/839808000000000000000000000000000000),((328429:ℚ)/500000)⟩
theorem valid30 : Valid source17 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((4329904289:ℚ)/5000000000),((5320000001:ℚ)/5000000000),(-1:ℚ),((-11965712867:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((96304247212946157564668796563388421:ℚ)/960000000000000000000000000000000000),((328429:ℚ)/500000)⟩
theorem valid31 : Valid source17 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((1320040009:ℚ)/1250000000),((14440000003:ℚ)/10000000000),(-1:ℚ),((-3704120027:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((439409894522446831840307:ℚ)/3808800000000000000000000),((328429:ℚ)/500000)⟩
theorem valid32 : Valid source17 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet32 valid32
private theorem node0_2 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source17 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4139:ℚ)/6400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source17 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source17 nn0 nn1 Qcell ((4139:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8449:ℚ)/12800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source17 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8487:ℚ)/12800) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((8487:ℚ)/12800) :=
  cell_join node0_8 node8_16
private theorem node16_18 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((341:ℚ)/512) :=
  cell_join node16_18 node18_20
private theorem node20_22 :
    CellBound source17 nn0 nn1 Qcell ((341:ℚ)/512) ((8563:ℚ)/12800) :=
  cell_join leaf20 leaf21
private theorem node22_24 :
    CellBound source17 nn0 nn1 Qcell ((8563:ℚ)/12800) ((8601:ℚ)/12800) :=
  cell_join leaf22 leaf23
private theorem node20_24 :
    CellBound source17 nn0 nn1 Qcell ((341:ℚ)/512) ((8601:ℚ)/12800) :=
  cell_join node20_22 node22_24
private theorem node16_24 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((8601:ℚ)/12800) :=
  cell_join node16_20 node20_24
private theorem node24_26 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_join node24_26 node26_28
private theorem node28_30 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf28 leaf29
private theorem node31_33 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf31 leaf32
private theorem node30_33 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf30 node31_33
private theorem node28_33 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node28_30 node30_33
private theorem node24_33 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node24_28 node28_33
private theorem node16_33 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node16_24 node24_33
private theorem node0_33 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_16 node16_33
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_33
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32]
theorem packet_count : packets.length = 33 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC01
#check @N11Formalization.C450Source17GroupedC01.bound
#print axioms N11Formalization.C450Source17GroupedC01.valid0
#print axioms N11Formalization.C450Source17GroupedC01.valid1
#print axioms N11Formalization.C450Source17GroupedC01.valid2
#print axioms N11Formalization.C450Source17GroupedC01.valid3
#print axioms N11Formalization.C450Source17GroupedC01.valid4
#print axioms N11Formalization.C450Source17GroupedC01.valid5
#print axioms N11Formalization.C450Source17GroupedC01.valid6
#print axioms N11Formalization.C450Source17GroupedC01.valid7
#print axioms N11Formalization.C450Source17GroupedC01.valid8
#print axioms N11Formalization.C450Source17GroupedC01.valid9
#print axioms N11Formalization.C450Source17GroupedC01.valid10
#print axioms N11Formalization.C450Source17GroupedC01.valid11
#print axioms N11Formalization.C450Source17GroupedC01.valid12
#print axioms N11Formalization.C450Source17GroupedC01.valid13
#print axioms N11Formalization.C450Source17GroupedC01.valid14
#print axioms N11Formalization.C450Source17GroupedC01.valid15
#print axioms N11Formalization.C450Source17GroupedC01.valid16
#print axioms N11Formalization.C450Source17GroupedC01.valid17
#print axioms N11Formalization.C450Source17GroupedC01.valid18
#print axioms N11Formalization.C450Source17GroupedC01.valid19
#print axioms N11Formalization.C450Source17GroupedC01.valid20
#print axioms N11Formalization.C450Source17GroupedC01.valid21
#print axioms N11Formalization.C450Source17GroupedC01.valid22
#print axioms N11Formalization.C450Source17GroupedC01.valid23
#print axioms N11Formalization.C450Source17GroupedC01.valid24
#print axioms N11Formalization.C450Source17GroupedC01.valid25
#print axioms N11Formalization.C450Source17GroupedC01.valid26
#print axioms N11Formalization.C450Source17GroupedC01.valid27
#print axioms N11Formalization.C450Source17GroupedC01.valid28
#print axioms N11Formalization.C450Source17GroupedC01.valid29
#print axioms N11Formalization.C450Source17GroupedC01.valid30
#print axioms N11Formalization.C450Source17GroupedC01.valid31
#print axioms N11Formalization.C450Source17GroupedC01.valid32
#print axioms N11Formalization.C450Source17GroupedC01.bound
#print axioms N11Formalization.C450Source17GroupedC01.endpoint_checks
