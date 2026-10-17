import N11Formalization.C450Source14Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source14GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source14Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((6583682263:ℚ)/10000000000),((6887575789:ℚ)/10000000000),((-44373030523:ℚ)/49600000000),((-77267869419:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1307753513:ℚ)/2500000000),((11433244633272460125025395880759375877043479:ℚ)/202273740160000000000000000000000000000000000),((719613580497749570022413517:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source14 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source14 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((6821415569:ℚ)/10000000000),((277879833:ℚ)/400000000),((-1791558831:ℚ)/2060000000),((-11479771771:ℚ)/14850000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4566046699:ℚ)/10000000000),((35026521357090801008627371416862222821063001167742483:ℚ)/697253732226562500000000000000000000000000000000000000),((1152736948278620003352053:ℚ)/2957312000000000000000000)⟩
theorem valid1 : Valid source14 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3440423113:ℚ)/5000000000),((1401283009:ℚ)/2000000000),((-9040981063:ℚ)/10395000000),((-40565500469:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4385354477:ℚ)/10000000000),((1679470806981871311747444462417681485551673063575006939247:ℚ)/33442019427944531250000000000000000000000000000000000000000),((28852304145932768282957637:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source14 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source14 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3470137937:ℚ)/5000000000),((706583347:ℚ)/1000000000),((-4562083429:ℚ)/5245000000),((-40951793181:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((839483599:ℚ)/2000000000),((202914256046194395977666067820873503754763661192344008639779:ℚ)/4041645433668875781250000000000000000000000000000000000000000),((7221546137192219935998093:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source14 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((349985227:ℚ)/500000000),((886942799:ℚ)/1250000000),((-197537917:ℚ)/228125000),((-4133807951:ℚ)/5316250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((4001212887:ℚ)/10000000000),((66078441413763368886705416650121423690633590569099545283:ℚ)/1342114066534614562988281250000000000000000000000000000000),((11290283101945449078650277:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source14 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source14 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7029418513:ℚ)/10000000000),((3562625561:ℚ)/5000000000),((-23018378927:ℚ)/26581250000),((-27687480223:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3899620471:ℚ)/10000000000),((11444174710871954172446257511842713882481151209668098709077:ℚ)/232448227819868850708007812500000000000000000000000000000000),((180750405800010797564092917:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source14 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source14 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((28236529:ℚ)/40000000),((1430991933:ℚ)/2000000000),((-3082981177:ℚ)/3560000000),((-333794877:ℚ)/429100000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3795453173:ℚ)/10000000000),((3994041471252362890384486437917029200826812345317830458487:ℚ)/81127308199306250000000000000000000000000000000000000000000),((28937005112682063299974253:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source14 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source14 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3544422877:ℚ)/5000000000),((3584906933:ℚ)/5000000000),((-23174348531:ℚ)/26818750000),((-41917497401:ℚ)/53756250000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((1844246179:ℚ)/5000000000),((1025315989857859356174713100499904616631904990936763407783:ℚ)/21027931990405869483947753906250000000000000000000000000000),((180909220024561836556004253:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source14 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((355185121:ℚ)/500000000),((7184668021:ℚ)/10000000000),((-46452676147:ℚ)/53756250000),((-4201406573:ℚ)/5387500000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((113558981:ℚ)/312500000),((103055108770216962729735157500321863314507887947558563630951:ℚ)/2113502384296051758527755737304687500000000000000000000000000),((723848632375484684943363357:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source14 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source14 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source14 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7118559029:ℚ)/10000000000),((7199522131:ℚ)/10000000000),((-46556654917:ℚ)/53875000000),((-84221267377:ℚ)/107987500000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((715697407:ℚ)/2000000000),((5454982732841982491422955026574255128165162770941135539303401:ℚ)/111871952820425415039062500000000000000000000000000000000000000),((724060384663013033119774797:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source14 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source14 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7133415581:ℚ)/10000000000),((3607188097:ℚ)/5000000000),((-23330316679:ℚ)/26996875000),((-6493415581:ℚ)/8325000000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3522253693:ℚ)/10000000000),((13853038235598171444729381403096296618359760224050931446507:ℚ)/284097710638303720951080322265625000000000000000000000000000),((181068034233078849937041093:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source14 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source14 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7148272077:ℚ)/10000000000),((7229230213:ℚ)/10000000000),((-3597277807:ℚ)/4162500000),((-84607537001:ℚ)/108462500000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3465146747:ℚ)/10000000000),((1654871019392532309720112519152708797993705948847560809834457:ℚ)/33937664482375158691406250000000000000000000000000000000000000),((724483889226152330541470013:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source14 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source14 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7163128517:ℚ)/10000000000),((7244084187:ℚ)/10000000000),((-46868589309:ℚ)/54231250000),((-84800670721:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((1703561103:ℚ)/5000000000),((57434760116493986213651658891298249544966639889625076503516539:ℚ)/1177844477174051020812988281250000000000000000000000000000000000),((724695641530262412077081213:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid source14 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source14 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source14 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((3588992451:ℚ)/5000000000),((1814734529:ℚ)/2500000000),((-11743141703:ℚ)/13587500000),((-42496901863:ℚ)/54468750000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((669626459:ℚ)/2000000000),((110602630633733972968650219486651801311435646759177212924773:ℚ)/2268162511639489746093750000000000000000000000000000000000000),((45306712115289982546169157:ℚ)/115520000000000000000000000)⟩
theorem valid13 : Valid source14 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source14 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source14 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7192841231:ℚ)/10000000000),((7273792001:ℚ)/10000000000),((-47076544007:ℚ)/54468750000),((-85186936003:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((1644062497:ℚ)/5000000000),((19567839200195683881130638656391963273599313993805505373714211:ℚ)/401279884841288816928863525390625000000000000000000000000000000),((725119146183534042109569477:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid source14 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3603848753:ℚ)/5000000000),((3644322921:ℚ)/5000000000),((-23590260447:ℚ)/27293750000),((-42690033789:ℚ)/54706250000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((129081739:ℚ)/400000000),((1186924104692679093319321156899801130368951301681080971465313:ℚ)/24340164596267832820892333984375000000000000000000000000000000),((181332724636734896060999957:ℚ)/462080000000000000000000000)⟩
theorem valid15 : Valid source14 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source14 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3611276863:ℚ)/5000000000),((7303499639:ℚ)/10000000000),((-47284497473:ℚ)/54706250000),((-42786599219:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((791206369:ℚ)/2500000000),((1176362348013862243004267523808636568906671020523353986996597:ℚ)/24123368482970170211791992187500000000000000000000000000000000),((725542650934850555213484117:ℚ)/1848320000000000000000000000)⟩
theorem valid16 : Valid source14 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source14 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((1809352473:ℚ)/2500000000),((3666603551:ℚ)/5000000000),((-23746224857:ℚ)/27412500000),((-21441582149:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((96918829:ℚ)/312500000),((114384223826581503906146773666494241322866966919015372334541:ℚ)/2323856532806872558593750000000000000000000000000000000000000),((181491538949605375180780677:ℚ)/462080000000000000000000000)⟩
theorem valid17 : Valid source14 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source14 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7267122063:ℚ)/10000000000),((1472582879:ℚ)/2000000000),((-9540080153:ℚ)/11012500000),((-86152586819:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((742657833:ℚ)/2500000000),((17948573153861097346592562171640126072928049141392898486281:ℚ)/364661575680749511718750000000000000000000000000000000000000),((29055586433819226762602757:ℚ)/73932800000000000000000000)⟩
theorem valid18 : Valid source14 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source14 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7296834023:ℚ)/10000000000),((7392621517:ℚ)/10000000000),((-47908350619:ℚ)/55300000000),((-86538842299:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((2834019177:ℚ)/10000000000),((16300087029147722341944489436313519361615207366733398789991363:ℚ)/331182582436693750000000000000000000000000000000000000000000000),((2013332869977083780637573:ℚ)/5120000000000000000000000)⟩
theorem valid19 : Valid source14 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source14 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1831636443:ℚ)/2500000000),((7422328473:ℚ)/10000000000),((-16038766437:ℚ)/18512500000),((-21731273759:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2690675899:ℚ)/10000000000),((9713566588812542904216897279781859370578500164087898113709083:ℚ)/197366923949895031738281250000000000000000000000000000000000000),((2014506015286418142708653:ℚ)/5120000000000000000000000)⟩
theorem valid20 : Valid source14 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source14 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source14 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((1471251463:ℚ)/2000000000),((7481741891:ℚ)/10000000000),((-48532193237:ℚ)/55775000000),((-17462269019:ℚ)/22500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((101578449:ℚ)/400000000),((21261668001001397986993384680734626076578000405167737629:ℚ)/424339468066406250000000000000000000000000000000000000000),((2016852308060543582454117:ℚ)/5120000000000000000000000)⟩
theorem valid21 : Valid source14 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source14 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7415679791:ℚ)/10000000000),((760056681:ℚ)/1000000000),((-1645465589:ℚ)/1875000000),((-6775679791:ℚ)/8800000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1103433959:ℚ)/5000000000),((258462985721694586239460171485900161316876086773614211:ℚ)/4985046386718750000000000000000000000000000000000000000),((50538063:ℚ)/128000000)⟩
theorem valid22 : Valid source14 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source14 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((60276179:ℚ)/80000000),((979776177:ℚ)/1250000000),((-6378433239:ℚ)/7150000000),((-239010109:ℚ)/315200000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((262722311:ℚ)/2000000000),((1223428187941472368146338388138922307823531883669982901921:ℚ)/22165146379492187500000000000000000000000000000000000000000),((50538063:ℚ)/128000000)⟩
theorem valid23 : Valid source14 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source14 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source14 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((7772198603:ℚ)/10000000000),((2018960783:ℚ)/2500000000),((-13172725481:ℚ)/14775000000),((-92718581839:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((12361235941100347782828442232751656390665647690973690856453:ℚ)/225031549567675781250000000000000000000000000000000000000000),((50538063:ℚ)/128000000)⟩
theorem valid24 : Valid source14 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source14 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((8009863841:ℚ)/10000000000),((427554351:ℚ)/500000000),((-2800880457:ℚ)/3050000000),((-95808229933:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((5907588329760819726699255529681377212836972815295468781:ℚ)/96954579492187500000000000000000000000000000000000000000),((50538063:ℚ)/128000000)⟩
theorem valid25 : Valid source14 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source14 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source14 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((8485165221:ℚ)/10000000000),((41807323:ℚ)/40000000),(-1:ℚ),((-101987147873:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((499267973014689081434877693560851931:ℚ)/6000000000000000000000000000000000000),((50538063:ℚ)/128000000)⟩
theorem valid26 : Valid source14 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source14 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10386084231:ℚ)/10000000000),((111349247:ℚ)/78125000),(-1:ℚ),((-126699095003:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((46622690201011203563562809:ℚ)/507840000000000000000000000),((50538063:ℚ)/128000000)⟩
theorem valid27 : Valid source14 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source14 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source14 nn0 nn1 packet27 valid27
private theorem node1_3 :
    CellBound source14 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source14 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source14 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source14 nn0 nn1 Qcell ((8601:ℚ)/12800) ((8639:ℚ)/12800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8639:ℚ)/12800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source14 nn0 nn1 Qcell ((8639:ℚ)/12800) ((8677:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source14 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source14 nn0 nn1 Qcell ((8639:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source14 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((1743:ℚ)/2560) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source14 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((2193:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source14 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source14 nn0 nn1 Qcell ((2193:ℚ)/3200) ((2231:ℚ)/3200) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_join node14_17 node17_21
private theorem node22_24 :
    CellBound source14 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf21 node22_24
private theorem node24_26 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source14 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source14 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node24_26 node26_28
private theorem node21_28 :
    CellBound source14 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node21_24 node24_28
private theorem node14_28 :
    CellBound source14 nn0 nn1 Qcell ((1743:ℚ)/2560) ((69:ℚ)/50) :=
  cell_join node14_21 node21_28
private theorem node0_28 :
    CellBound source14 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_28
theorem bound : CellBound source14 nn0 nn1 Qcell (31/50) (69/50) := node0_28
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27]
theorem packet_count : packets.length = 28 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source14GroupedC03
#check @N11Formalization.C450Source14GroupedC03.bound
#print axioms N11Formalization.C450Source14GroupedC03.valid0
#print axioms N11Formalization.C450Source14GroupedC03.valid1
#print axioms N11Formalization.C450Source14GroupedC03.valid2
#print axioms N11Formalization.C450Source14GroupedC03.valid3
#print axioms N11Formalization.C450Source14GroupedC03.valid4
#print axioms N11Formalization.C450Source14GroupedC03.valid5
#print axioms N11Formalization.C450Source14GroupedC03.valid6
#print axioms N11Formalization.C450Source14GroupedC03.valid7
#print axioms N11Formalization.C450Source14GroupedC03.valid8
#print axioms N11Formalization.C450Source14GroupedC03.valid9
#print axioms N11Formalization.C450Source14GroupedC03.valid10
#print axioms N11Formalization.C450Source14GroupedC03.valid11
#print axioms N11Formalization.C450Source14GroupedC03.valid12
#print axioms N11Formalization.C450Source14GroupedC03.valid13
#print axioms N11Formalization.C450Source14GroupedC03.valid14
#print axioms N11Formalization.C450Source14GroupedC03.valid15
#print axioms N11Formalization.C450Source14GroupedC03.valid16
#print axioms N11Formalization.C450Source14GroupedC03.valid17
#print axioms N11Formalization.C450Source14GroupedC03.valid18
#print axioms N11Formalization.C450Source14GroupedC03.valid19
#print axioms N11Formalization.C450Source14GroupedC03.valid20
#print axioms N11Formalization.C450Source14GroupedC03.valid21
#print axioms N11Formalization.C450Source14GroupedC03.valid22
#print axioms N11Formalization.C450Source14GroupedC03.valid23
#print axioms N11Formalization.C450Source14GroupedC03.valid24
#print axioms N11Formalization.C450Source14GroupedC03.valid25
#print axioms N11Formalization.C450Source14GroupedC03.valid26
#print axioms N11Formalization.C450Source14GroupedC03.valid27
#print axioms N11Formalization.C450Source14GroupedC03.bound
#print axioms N11Formalization.C450Source14GroupedC03.endpoint_checks
