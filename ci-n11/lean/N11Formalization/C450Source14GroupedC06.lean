import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((6488667059:ℚ)/10000000000),((423994701:ℚ)/625000000),((-4183941711:ℚ)/6200000000),((-5656667059:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5476087077:ℚ)/10000000000),((788341894895526778347021050471735719153060394305457521401:ℚ)/15802635950000000000000000000000000000000000000000000000000),((3826111377715171954042916529:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6726585891:ℚ)/10000000000),((3451433163:ℚ)/5000000000),((-34125764793:ℚ)/51500000000),((-5894585891:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((968273427:ℚ)/2000000000),((11183276973630603240226123924326614400287082541976710815535287:ℚ)/234851149126367187500000000000000000000000000000000000000000000),((3822804292734246484714786129:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((68455339:ℚ)/100000000),((6962339167:ℚ)/10000000000),((-68905730837:ℚ)/104900000000),((-60135339:ℚ)/105850000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4493534419:ℚ)/10000000000),((20618472062251553741550225015467817705030428938538454698560251:ℚ)/442920047525356250000000000000000000000000000000000000000000000),((382114391365443935463489:ℚ)/1478656000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((6905005231:ℚ)/10000000000),((7021810263:ℚ)/10000000000),((-69559912893:ℚ)/105850000000),((-2024335077:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((538735353:ℚ)/1250000000),((9364258009277311539480817856081051352656776720541111481771:ℚ)/201071152050976562500000000000000000000000000000000000000000),((3820312012863345038954377449:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((3482237423:ℚ)/5000000000),((7081279661:ℚ)/10000000000),((-70214076271:ℚ)/106800000000),((-3066237423:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4118588867:ℚ)/10000000000),((772208180107939501157339564197588083532026301443177177518107:ℚ)/16574086654889062500000000000000000000000000000000000000000000),((954869742612006463058029161:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7023942787:ℚ)/10000000000),((888876717:ℚ)/1250000000),((-8817643887:ℚ)/13468750000),((-687993643:ℚ)/1202500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((489816201:ℚ)/1250000000),((10176036380244822611428986962647184632796902562013489543633:ℚ)/220816775092494487762451171875000000000000000000000000000000),((3818644785919818016693535121:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1410735229:ℚ)/2000000000),((1785186851:ℚ)/2500000000),((-17717055361:ℚ)/27056250000),((-1244335229:ℚ)/2174000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((476847899:ℚ)/1250000000),((60740392238309352683380661014865098571344035085743651510161:ℚ)/1317707252360581970214843750000000000000000000000000000000000),((152729090607196891168865169:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7083409101:ℚ)/10000000000),((7170480669:ℚ)/10000000000),((-71195287359:ℚ)/108700000000),((-6251409101:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3708282629:ℚ)/10000000000),((441146434741173901735536924180894845632618356437793472721459649:ℚ)/9567865261734987109375000000000000000000000000000000000000000000),((3817809458716477885639129009:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((355657083:ℚ)/500000000),((7200213537:ℚ)/10000000000),((-71522348907:ℚ)/109175000000),((-314057083:ℚ)/548250000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3598782901:ℚ)/10000000000),((8842408155700725434785768513836403767097989709752829570241263:ℚ)/191732932643604418945312500000000000000000000000000000000000000),((9543478416177424119712801:ℚ)/36966400000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((1785718457:ℚ)/2500000000),((1807486503:ℚ)/2500000000),((-5987450511:ℚ)/9137500000),((-1577718457:ℚ)/2753125000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((871500217:ℚ)/2500000000),((42680655364150319777247539411444793011973789515068455510561:ℚ)/925239175099032592773437500000000000000000000000000000000000),((238560811773163110686232441:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((717260561:ℚ)/1000000000),((7259678101:ℚ)/10000000000),((-72176459111:ℚ)/110125000000),((-634060561:ℚ)/1106000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3369606427:ℚ)/10000000000),((5520860470535201674331815737831443452466058163995848821145267:ℚ)/119654579520245933532714843750000000000000000000000000000000000),((38165543243564613892291689:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7202337011:ℚ)/10000000000),((7289409807:ℚ)/10000000000),((-72503507877:ℚ)/110600000000),((-6370337011:ℚ)/11107500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((812302707:ℚ)/2500000000),((641936114842968903062431477274493437927968801442751930986529361:ℚ)/13909668462341137500000000000000000000000000000000000000000000000),((10571012117366735476832649:ℚ)/40960000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1808017009:ℚ)/2500000000),((457446321:ℚ)/625000000),((-1517303177:ℚ)/2314062500),((-1600017009:ℚ)/2788750000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3124350981:ℚ)/10000000000),((1112126776038310263296470700465326787169091274550968224163:ℚ)/24092642083727420866489410400390625000000000000000000000000),((238482258646879437857605929:ℚ)/924160000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7261798689:ℚ)/10000000000),((1837218023:ℚ)/2500000000),((-18289398253:ℚ)/27887500000),((-6429798689:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((748616977:ℚ)/2500000000),((5026673211483353450442165692337987603094328629830279026599547:ℚ)/108872613008126050292968750000000000000000000000000000000000000),((10568688687681690603030049:ℚ)/40960000000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((291661159:ℚ)/400000000),((184465067:ℚ)/250000000),((-1837115737:ℚ)/2800625000),((-86127053:ℚ)/150000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2858876431:ℚ)/10000000000),((49532063487872754590757654318505137135364687755229:ℚ)/1072592933666706085205078125000000000000000000000000),((6103802892830011938300729:ℚ)/23658496000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7321258899:ℚ)/10000000000),((7438062773:ℚ)/10000000000),((-74138690503:ℚ)/112500000000),((-6489258899:ℚ)/11345000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2716721311:ℚ)/10000000000),((5347159602651201471699200796123556369113743485495037425892297:ℚ)/114537206085205078125000000000000000000000000000000000000000000),((3814456713587184409605505009:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7380717679:ℚ)/10000000000),((7497521449:ℚ)/10000000000),((-74792735939:ℚ)/113450000000),((-6548717679:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2408018407:ℚ)/10000000000),((8714746067939734515120800778025204517371055150592275060783309:ℚ)/186623183240578906250000000000000000000000000000000000000000000),((3813615665920094672095966569:ℚ)/14786560000000000000000000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1488035013:ℚ)/2000000000),((7616434691:ℚ)/10000000000),((-5853906277:ℚ)/8800000000),((-1321635013:ℚ)/2326000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2054444949:ℚ)/10000000000),((24966663265787196857315040134666562552284270779154824622217:ℚ)/523714716800000000000000000000000000000000000000000000000000),((152510938913024404749340321:ℚ)/591462400000000000000000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7559085791:ℚ)/10000000000),((309413707:ℚ)/400000000),((-3096350777:ℚ)/4652000000),((-6727085791:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1038102671:ℚ)/10000000000),((291024038362045181482331944865300561279910723580062777423:ℚ)/6104802192332300000000000000000000000000000000000000000000),((3811085648749202982314632329:ℚ)/14786560000000000000000000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((383899567:ℚ)/500000000),((1993285963:ℚ)/2500000000),((-20006145593:ℚ)/29550000000),((-342299567:ℚ)/610000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((89104477862973385705219793295089184850304291841479227721309:ℚ)/1800252396541406250000000000000000000000000000000000000000000),((263885307:ℚ)/1024000000)⟩
theorem valid19 : Valid source14 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((63326303:ℚ)/80000000),((8448693131:ℚ)/10000000000),((-85255624441:ℚ)/122000000000),((-18890101:ℚ)/34560000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((145777011220008081809025553514850996575043496464280968563077:ℚ)/2757819150000000000000000000000000000000000000000000000000000),((263885307:ℚ)/1024000000)⟩
theorem valid20 : Valid source14 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8391328689:ℚ)/10000000000),((2587591943:ℚ)/2500000000),((-26543511373:ℚ)/32400000000),((-7559328689:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((45368271163033800840637610641866074887705984295286041929:ℚ)/637729200000000000000000000000000000000000000000000000000),((263885307:ℚ)/1024000000)⟩
theorem valid21 : Valid source14 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((2573244383:ℚ)/2500000000),((2830466519:ℚ)/2000000000),((-29599131709:ℚ)/32000000000),((-2365244383:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1173125638118067218259723709453673714531:ℚ)/13000704000000000000000000000000000000000),((263885307:ℚ)/1024000000)⟩
theorem valid22 : Valid source14 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source14 nn0 nn1 Qcell ((4481:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source14 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC06
#check @N11Formalization.C450Source14GroupedC06.bound
#print axioms N11Formalization.C450Source14GroupedC06.valid0
#print axioms N11Formalization.C450Source14GroupedC06.valid1
#print axioms N11Formalization.C450Source14GroupedC06.valid2
#print axioms N11Formalization.C450Source14GroupedC06.valid3
#print axioms N11Formalization.C450Source14GroupedC06.valid4
#print axioms N11Formalization.C450Source14GroupedC06.valid5
#print axioms N11Formalization.C450Source14GroupedC06.valid6
#print axioms N11Formalization.C450Source14GroupedC06.valid7
#print axioms N11Formalization.C450Source14GroupedC06.valid8
#print axioms N11Formalization.C450Source14GroupedC06.valid9
#print axioms N11Formalization.C450Source14GroupedC06.valid10
#print axioms N11Formalization.C450Source14GroupedC06.valid11
#print axioms N11Formalization.C450Source14GroupedC06.valid12
#print axioms N11Formalization.C450Source14GroupedC06.valid13
#print axioms N11Formalization.C450Source14GroupedC06.valid14
#print axioms N11Formalization.C450Source14GroupedC06.valid15
#print axioms N11Formalization.C450Source14GroupedC06.valid16
#print axioms N11Formalization.C450Source14GroupedC06.valid17
#print axioms N11Formalization.C450Source14GroupedC06.valid18
#print axioms N11Formalization.C450Source14GroupedC06.valid19
#print axioms N11Formalization.C450Source14GroupedC06.valid20
#print axioms N11Formalization.C450Source14GroupedC06.valid21
#print axioms N11Formalization.C450Source14GroupedC06.valid22
#print axioms N11Formalization.C450Source14GroupedC06.bound
#print axioms N11Formalization.C450Source14GroupedC06.endpoint_checks
