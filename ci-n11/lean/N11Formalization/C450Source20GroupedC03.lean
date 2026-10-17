import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((338538801:ℚ)/500000000),((6973028741:ℚ)/10000000000),((-43051201187:ℚ)/49600000000),((-3793004413:ℚ)/5055000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4714920183:ℚ)/10000000000),((456326691823354942799744682035878089800141:ℚ)/5196801145344000000000000000000000000000000),((1168360358763962806937285539:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1722448483:ℚ)/2500000000),((3516251857:ℚ)/5000000000),((-21733762999:ℚ)/25275000000),((-19351830279:ℚ)/25512500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4357544929:ℚ)/10000000000),((65157270255039003149427308389768341882607882741587648449:ℚ)/777325359949310302734375000000000000000000000000000000000),((292557871156952972347361531:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((1389859827:ℚ)/2000000000),((3545988419:ℚ)/5000000000),((-21941918933:ℚ)/25512500000),((-15636177751:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((521023563:ℚ)/1250000000),((138403041079218720780618195949700529994701710658328371989441:ℚ)/1651599637882489013671875000000000000000000000000000000000000),((293025712982571498555020659:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7008801929:ℚ)/10000000000),((7121712723:ℚ)/10000000000),((-44091989061:ℚ)/51500000000),((-78954425077:ℚ)/103475000000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((794074081:ℚ)/2000000000),((5988720627621712153002648341214853212689482655716225608701019:ℚ)/73124441415496093750000000000000000000000000000000000000000000),((3519115879882827971474842553:ℚ)/5544960000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3519276221:ℚ)/5000000000),((1430289633:ℚ)/2000000000),((-8860027431:ℚ)/10347500000),((-13223530291:ℚ)/17325000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3867883463:ℚ)/10000000000),((540376506772405148423488697387421550505358124731484273487:ℚ)/6598151077510217285156250000000000000000000000000000000000),((140876935473606473200160273:ℚ)/221798400000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7068302379:ℚ)/10000000000),((718118317:ℚ)/1000000000),((-4450828219:ℚ)/5197500000),((-79727930927:ℚ)/104425000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3762752221:ℚ)/10000000000),((14249038148407652872464511517986415643718212429848451541279:ℚ)/173984191658576916503906250000000000000000000000000000000000),((11749103590731274956038291:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1419610349:ℚ)/2000000000),((7210917743:ℚ)/10000000000),((-44716424201:ℚ)/52212500000),((-16022934537:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((730949597:ℚ)/2000000000),((10021682661019593367020056919894439217996036972567262304374151:ℚ)/122367044725168507385253906250000000000000000000000000000000000),((1175846317160919763126807931:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7127800549:ℚ)/10000000000),((722578487:ℚ)/1000000000),((-4482049409:ℚ)/5245000000),((-80501407137:ℚ)/105137500000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((3543607533:ℚ)/10000000000),((2583199341810911935044226386758642537401902248037943492704111:ℚ)/31899344969599112890625000000000000000000000000000000000000000),((11763143192680144003795211:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((7142674743:ℚ)/10000000000),((7240651891:ℚ)/10000000000),((-44924563237:ℚ)/52568750000),((-80694771659:ℚ)/105375000000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3486767671:ℚ)/10000000000),((261263704424522132431316418167070294549461010073866125226043:ℚ)/3226176488772007896423339843750000000000000000000000000000000),((1176782336760532702541270739:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7157548799:ℚ)/10000000000),((7255518807:ℚ)/10000000000),((-15009543883:ℚ)/17562500000),((-80888134387:ℚ)/105612500000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((1714512691:ℚ)/5000000000),((24466116086943280442963206407892683562485158833664396282391277:ℚ)/302106216773536872863769531250000000000000000000000000000000000),((3531751109008669038562708193:ℚ)/5544960000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7172422719:ℚ)/10000000000),((7270385619:ℚ)/10000000000),((-45132699333:ℚ)/52806250000),((-81081495347:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1685167107:ℚ)/5000000000),((23859924929347377435074303169611237059450370979313206351208741:ℚ)/294611489678518236541748046875000000000000000000000000000000000),((3533155254078516143706197177:ℚ)/5544960000000000000000000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7187296503:ℚ)/10000000000),((7285252327:ℚ)/10000000000),((-45236766289:ℚ)/52925000000),((-81274854539:ℚ)/106087500000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3310643633:ℚ)/10000000000),((300283554152243622370328577170870125112470475429392859063733119:ℚ)/3707648176519615869140625000000000000000000000000000000000000000),((3263674464903010830243891:ℚ)/5120000000000000000000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7202170151:ℚ)/10000000000),((7300118933:ℚ)/10000000000),((-45340832531:ℚ)/53043750000),((-81468211963:ℚ)/106325000000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1624949253:ℚ)/5000000000),((5555007138351460301760049535800081086079551808185438254188967:ℚ)/68586451524568137359619140625000000000000000000000000000000000),((1178654561143579863898812291:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid source20 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source20 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-7:ℚ)/8),((-13:ℚ)/16),((3608521833:ℚ)/5000000000),((7314985437:ℚ)/10000000000),((-45444898059:ℚ)/53162500000),((-119738369:ℚ)/156250000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((398504809:ℚ)/1250000000),((15211966640543479185441406452297426053973231915522909:ℚ)/187813237980957031250000000000000000000000000000000000),((3537367967899696720641678233:ℚ)/5544960000000000000000000000)⟩
theorem valid13 : Valid source20 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source20 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((903989631:ℚ)/1250000000),((7329851839:ℚ)/10000000000),((-1469321383:ℚ)/1718750000),((-10231865203:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((3124997251:ℚ)/10000000000),((22904580998730728072748836670541547958202416553822528297:ℚ)/282781299948692321777343750000000000000000000000000000000),((1179590766298558704409945499:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid source20 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source20 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7246790297:ℚ)/10000000000),((3679792171:ℚ)/5000000000),((-22878545197:ℚ)/26700000000),((-82048273861:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3060701789:ℚ)/10000000000),((1401466026659760002654790315254163333261960967264774459333867:ℚ)/17112791573291162109375000000000000000000000000000000000000000),((295131758411370164918840579:ℚ)/462080000000000000000000000)⟩
theorem valid15 : Valid source20 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((7276536403:ℚ)/10000000000),((7389316447:ℚ)/10000000000),((-45965215129:ℚ)/53637500000),((-82434973239:ℚ)/107750000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2928015719:ℚ)/10000000000),((85970025015888547059384349385040690455538144157492130123773:ℚ)/1049763416949686837196350097656250000000000000000000000000000),((1181463363338768231183953371:ℚ)/1848320000000000000000000000)⟩
theorem valid16 : Valid source20 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source20 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7306281991:ℚ)/10000000000),((7419048159:ℚ)/10000000000),((-46173337113:ℚ)/53875000000),((-27607221961:ℚ)/36075000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1394608143:ℚ)/5000000000),((5208024773032672964718172313650004800127806425918100850754383:ℚ)/63595231226638412475585937500000000000000000000000000000000000),((3547199266598682989932176017:ℚ)/5544960000000000000000000000)⟩
theorem valid17 : Valid source20 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source20 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source20 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1834006767:ℚ)/2500000000),((1489755897:ℚ)/2000000000),((-1030699031:ℚ)/1202500000),((-20802087971:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1321669981:ℚ)/5000000000),((14210291379899949997893310642851442799715035820716736293:ℚ)/173525234878759765625000000000000000000000000000000000000),((142000345253445514432995713:ℚ)/221798400000000000000000000)⟩
theorem valid18 : Valid source20 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((184144291:ℚ)/250000000),((3754120497:ℚ)/5000000000),((-23398843479:ℚ)/27175000000),((-696625261:ℚ)/913750000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((497828423:ℚ)/2000000000),((700672810695445350419674289125088393388485308939616215105121:ℚ)/8377866632673132324218750000000000000000000000000000000000000),((888906981664735355475182513:ℚ)/1386240000000000000000000000)⟩
theorem valid19 : Valid source20 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source20 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((232039353:ℚ)/312500000),((3783850507:ℚ)/5000000000),((-23606953549:ℚ)/27412500000),((-2636511589:ℚ)/3456250000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1074263679:ℚ)/5000000000),((11021606579789372463507156338454994264186486863283757960239:ℚ)/131822474301669788360595703125000000000000000000000000000000),((296770664974702941740724931:ℚ)/462080000000000000000000000)⟩
theorem valid20 : Valid source20 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source20 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7484745011:ℚ)/10000000000),((243922717:ℚ)/312500000),((-1527459019:ℚ)/1728125000),((-85141685143:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((348753393:ℚ)/2000000000),((141343560028902264694543883187114778811701522234435504409:ℚ)/1507646395993041992187500000000000000000000000000000000000),((82278421:ℚ)/128000000)⟩
theorem valid21 : Valid source20 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((1544533887:ℚ)/2000000000),((4378319603:ℚ)/5000000000),((-27768237221:ℚ)/28600000000),((-17646940531:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5284778567505791046599196489791113749612484183155841772177:ℚ)/39970254431250000000000000000000000000000000000000000000000),((82278421:ℚ)/128000000)⟩
theorem valid22 : Valid source20 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((8674117687:ℚ)/10000000000),((66613931:ℚ)/62500000),(-1:ℚ),((-100603529931:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3581631775647777330376625820871063243:ℚ)/24000000000000000000000000000000000000),((82278421:ℚ)/128000000)⟩
theorem valid23 : Valid source20 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((2644046841:ℚ)/2500000000),((14460094239:ℚ)/10000000000),(-1:ℚ),((-31332608933:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((63107356502150020988218739:ℚ)/380880000000000000000000000),((82278421:ℚ)/128000000)⟩
theorem valid24 : Valid source20 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((103:ℚ)/160) ((4177:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((843:ℚ)/1280) ((8487:ℚ)/12800) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8487:ℚ)/12800) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((8487:ℚ)/12800) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source20 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source20 nn0 nn1 Qcell ((8487:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source20 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source20 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source20 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source20 nn0 nn1 Qcell ((4329:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source20 nn0 nn1 Qcell ((8487:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC03
#check @N11Formalization.C450Source20GroupedC03.bound
#print axioms N11Formalization.C450Source20GroupedC03.valid0
#print axioms N11Formalization.C450Source20GroupedC03.valid1
#print axioms N11Formalization.C450Source20GroupedC03.valid2
#print axioms N11Formalization.C450Source20GroupedC03.valid3
#print axioms N11Formalization.C450Source20GroupedC03.valid4
#print axioms N11Formalization.C450Source20GroupedC03.valid5
#print axioms N11Formalization.C450Source20GroupedC03.valid6
#print axioms N11Formalization.C450Source20GroupedC03.valid7
#print axioms N11Formalization.C450Source20GroupedC03.valid8
#print axioms N11Formalization.C450Source20GroupedC03.valid9
#print axioms N11Formalization.C450Source20GroupedC03.valid10
#print axioms N11Formalization.C450Source20GroupedC03.valid11
#print axioms N11Formalization.C450Source20GroupedC03.valid12
#print axioms N11Formalization.C450Source20GroupedC03.valid13
#print axioms N11Formalization.C450Source20GroupedC03.valid14
#print axioms N11Formalization.C450Source20GroupedC03.valid15
#print axioms N11Formalization.C450Source20GroupedC03.valid16
#print axioms N11Formalization.C450Source20GroupedC03.valid17
#print axioms N11Formalization.C450Source20GroupedC03.valid18
#print axioms N11Formalization.C450Source20GroupedC03.valid19
#print axioms N11Formalization.C450Source20GroupedC03.valid20
#print axioms N11Formalization.C450Source20GroupedC03.valid21
#print axioms N11Formalization.C450Source20GroupedC03.valid22
#print axioms N11Formalization.C450Source20GroupedC03.valid23
#print axioms N11Formalization.C450Source20GroupedC03.valid24
#print axioms N11Formalization.C450Source20GroupedC03.bound
#print axioms N11Formalization.C450Source20GroupedC03.endpoint_checks
