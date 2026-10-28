import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((419886989:ℚ)/625000000),((1728705989:ℚ)/2500000000),((-151810257:ℚ)/160000000),((-873069641:ℚ)/1053125000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4865043489:ℚ)/10000000000),((13813588994231038811095323348277632567:ℚ)/181710400000000000000000000000000000000),((105381707602007237086809471:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((6837069909:ℚ)/10000000000),((3516823211:ℚ)/5000000000),((-3196823211:ℚ)/3370000000),((-42739489363:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((903820983:ℚ)/2000000000),((6005508740424052012487647441195893065189246636545567323:ℚ)/79303835268945312500000000000000000000000000000000000000),((423097607339966724915131871:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((347797163:ℚ)/500000000),((7093056661:ℚ)/10000000000),((-19359169983:ℚ)/20600000000),((-2178580141:ℚ)/2598750000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2073270961:ℚ)/5000000000),((47867009861912870373363320111415259053371518194368439787:ℚ)/665560380761718750000000000000000000000000000000000000000),((1695534253337208875214290271:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7015378243:ℚ)/10000000000),((7122761539:ℚ)/10000000000),((-2160920513:ℚ)/2310000000),((-43987647701:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((3947933:ℚ)/10000000),((203914799205904600803447385850957848672541684109115816591:ℚ)/2909396633653125000000000000000000000000000000000000000000),((1697106733202180639060729871:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1761273831:ℚ)/2500000000),((7152466261:ℚ)/10000000000),((-19537398783:ℚ)/20885000000),((-11048916817:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((153799861:ℚ)/400000000),((2194678433287740443998038091453680548839814270693671263211999:ℚ)/31325963449643137890625000000000000000000000000000000000000000),((1698679591907742079611861471:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7074812137:ℚ)/10000000000),((7167318563:ℚ)/10000000000),((-19581955689:ℚ)/20980000000),((-44403684959:ℚ)/52568750000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((1869686507:ℚ)/5000000000),((141208333691670899545388877083991695994647563994374019594493457:ℚ)/2041558078054343225000000000000000000000000000000000000000000000),((1699466163297356658167335119:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((1772417611:ℚ)/2500000000),((3591085413:ℚ)/5000000000),((-9813256239:ℚ)/10513750000),((-11126923277:ℚ)/13171875000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((1842740751:ℚ)/5000000000),((44621704586047522716081385391455951344220917091437011643767:ℚ)/645235297754401579284667968750000000000000000000000000000000),((425063207348706277689190719:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1420905737:ℚ)/2000000000),((1799255763:ℚ)/2500000000),((-1639255763:ℚ)/1756250000),((-8922340159:ℚ)/10561250000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((145233099:ℚ)/400000000),((10026719781118070786721726467739651903750484959116170764377:ℚ)/145010984051297698974609375000000000000000000000000000000000),((106314974394083549902982319:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7119386861:ℚ)/10000000000),((7211875239:ℚ)/10000000000),((-19715625717:ℚ)/21122500000),((-44715708027:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3575375901:ℚ)/10000000000),((18508412680474878039075470581948435621856247044955028372097:ℚ)/267719974393460791015625000000000000000000000000000000000000),((4714200681224941127474511:ℚ)/8192000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7134244973:ℚ)/10000000000),((1806681847:ℚ)/2500000000),((-4940045541:ℚ)/5292500000),((-14939904937:ℚ)/17681250000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((879772253:ℚ)/2500000000),((7118939691666557676100879792571254535021639201289997441253:ℚ)/102990227125544885253906250000000000000000000000000000000000),((106413337268603281423895559:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7149103019:ℚ)/10000000000),((14483159:ℚ)/20000000),((-4401053:ℚ)/4715000),((-44923721133:ℚ)/53162500000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3461926009:ℚ)/10000000000),((102370907894692781291227721868077786252780979704549:ℚ)/1481241553913306933593750000000000000000000000000000),((6813601765935742706631:ℚ)/11829248000000000000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-15:ℚ)/16),((-7:ℚ)/8),((3581980501:ℚ)/5000000000),((290257263:ℚ)/400000000),((-793971789:ℚ)/850600000),((-22513863507:ℚ)/26640625000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((3403842679:ℚ)/10000000000),((87802069137414485505126934595138259251738018097675447:ℚ)/1270639192765885937500000000000000000000000000000000000),((2726700130368528050171319:ℚ)/4731699200000000000000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((3589409461:ℚ)/5000000000),((1817820903:ℚ)/2500000000),((-4973462709:ℚ)/5328125000),((-7521955409:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((334479101:ℚ)/1000000000),((940665801718873643369619806271245528031932427311661547:ℚ)/13615091243267059326171875000000000000000000000000000000),((106560926014568993945699559:ℚ)/184832000000000000000000000)⟩
theorem valid12 : Valid source17 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source17 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3596838389:ℚ)/5000000000),((7286135613:ℚ)/10000000000),((-6646135613:ℚ)/7120000000),((-22617868723:ℚ)/26759375000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((3284718717:ℚ)/10000000000),((17139995171177332736186701655334736930441601139244336290855983:ℚ)/248120784340612800000000000000000000000000000000000000000000000),((1705762145847544399220315919:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid source17 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7208534571:ℚ)/10000000000),((7300987577:ℚ)/10000000000),((-19982962731:ℚ)/21407500000),((-45339741997:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((3223568669:ℚ)/10000000000),((9747329951390125851696215116735509501271202948040397311688867:ℚ)/141125312788373602380371093750000000000000000000000000000000000),((1706549570269926375097607079:ℚ)/2957312000000000000000000000)⟩
theorem valid14 : Valid source17 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source17 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7223392303:ℚ)/10000000000),((1463167901:ℚ)/2000000000),((-4005503703:ℚ)/4291000000),((-45443746121:ℚ)/53756250000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((395159781:ℚ)/1250000000),((26837372644179750440010802691558348776762868819316667558457:ℚ)/388620407360353415625000000000000000000000000000000000000000),((68293483582102183028195151:ℚ)/118292480000000000000000000)⟩
theorem valid15 : Valid source17 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((1809562493:ℚ)/2500000000),((1832672849:ℚ)/2500000000),((-1672672849:ℚ)/1791875000),((-11386937451:ℚ)/13468750000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3097778603:ℚ)/10000000000),((230608955903898029006171701562942949129294565344298472577:ℚ)/3339855619628328704833984375000000000000000000000000000000),((106757793977605676803076151:ℚ)/184832000000000000000000000)⟩
theorem valid16 : Valid source17 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source17 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source17 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((362655379:ℚ)/500000000),((1836385813:ℚ)/2500000000),((-5029157439:ℚ)/5387500000),((-2282587653:ℚ)/2699687500),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((379124213:ℚ)/1250000000),((15446646508449746728642282479371240462800316154557617688389:ℚ)/223743905640850830078125000000000000000000000000000000000000),((106807025790168370014721119:ℚ)/184832000000000000000000000)⟩
theorem valid17 : Valid source17 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source17 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7267965127:ℚ)/10000000000),((7360395073:ℚ)/10000000000),((-20161185219:ℚ)/21597500000),((-45755755889:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1483419643:ℚ)/5000000000),((40724295468976279597717498542163742068826200254356645088409147:ℚ)/589977760946667464794921875000000000000000000000000000000000000),((1709700216554879718276091479:ℚ)/2957312000000000000000000000)⟩
theorem valid18 : Valid source17 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source17 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7282822613:ℚ)/10000000000),((7390098607:ℚ)/10000000000),((-2250032869:ℚ)/2405000000),((-45859758291:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2899221527:ℚ)/10000000000),((10762004302490629910923303285134210556563436517744457875311:ℚ)/154090408572338671875000000000000000000000000000000000000000),((1711276108950881258110828599:ℚ)/2957312000000000000000000000)⟩
theorem valid19 : Valid source17 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1462507481:ℚ)/2000000000),((3709901001:ℚ)/5000000000),((-10169703003:ℚ)/10870000000),((-9213552367:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((2759163033:ℚ)/10000000000),((30363460918665986294710379946634052243279242170957111904729:ℚ)/434902966442499414062500000000000000000000000000000000000000),((428213095259099870939721351:ℚ)/739328000000000000000000000)⟩
theorem valid20 : Valid source17 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source17 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source17 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((183556299:ℚ)/250000000),((7449505259:ℚ)/10000000000),((-20428515777:ℚ)/21835000000),((-1156894093:ℚ)/1370625000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((2611806437:ℚ)/10000000000),((23084901961340988102136843865421809026754382654910968671537:ℚ)/330769710438015234375000000000000000000000000000000000000000),((1714429032859087108199374431:ℚ)/2957312000000000000000000000)⟩
theorem valid21 : Valid source17 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source17 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7371966279:ℚ)/10000000000),((938613921:ℚ)/1250000000),((-858613921:ℚ)/913750000),((-46483763953:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((613959421:ℚ)/2500000000),((172910085996266077723902947765324854439159333460552533:ℚ)/2422233234368896484375000000000000000000000000000000000),((26837241815193836381757591:ℚ)/46208000000000000000000000)⟩
theorem valid22 : Valid source17 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((7431394227:ℚ)/10000000000),((3813861003:ℚ)/5000000000),((-10481583009:ℚ)/11060000000),((-46899759589:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((527582787:ℚ)/2500000000),((1214947525056005832667150957310325668746533107457293197:ℚ)/16307264925000000000000000000000000000000000000000000000),((119281389:ℚ)/204800000)⟩
theorem valid23 : Valid source17 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((1510049487:ℚ)/2000000000),((7746530629:ℚ)/10000000000),((-2368843543:ℚ)/2500000000),((-9546346409:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1144862017:ℚ)/10000000000),((6744068321279669413626399217804476060578247863654693349:ℚ)/90771484375000000000000000000000000000000000000000000000),((119281389:ℚ)/204800000)⟩
theorem valid24 : Valid source17 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((7669097211:ℚ)/10000000000),((1739387539:ℚ)/2000000000),(-1:ℚ),((-48563680477:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((531213224110586237693785497197781653:ℚ)/5248800000000000000000000000000000000),((119281389:ℚ)/204800000)⟩
theorem valid25 : Valid source17 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8619789989:ℚ)/10000000000),((2119503939:ℚ)/2000000000),(-1:ℚ),((-55218529923:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((652498528239343169316581958297122491:ℚ)/6000000000000000000000000000000000000),((119281389:ℚ)/204800000)⟩
theorem valid26 : Valid source17 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10520780357:ℚ)/10000000000),((449943837:ℚ)/312500000),(-1:ℚ),((-22841820833:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((20737130398911405611884587:ℚ)/169280000000000000000000000),((119281389:ℚ)/204800000)⟩
theorem valid27 : Valid source17 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet27 valid27
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2079:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source17 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source17 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source17 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((8487:ℚ)/12800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((341:ℚ)/512) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source17 nn0 nn1 Qcell ((341:ℚ)/512) ((8563:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source17 nn0 nn1 Qcell ((8487:ℚ)/12800) ((8563:ℚ)/12800) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source17 nn0 nn1 Qcell ((843:ℚ)/1280) ((8563:ℚ)/12800) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((8563:ℚ)/12800) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source17 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source17 nn0 nn1 Qcell ((8563:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source17 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source17 nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source17 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4367:ℚ)/6400) :=
  cell_join node14_17 node17_21
private theorem node22_24 :
    CellBound source17 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf21 node22_24
private theorem node24_26 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node24_26 node26_28
private theorem node21_28 :
    CellBound source17 nn0 nn1 Qcell ((4367:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node21_24 node24_28
private theorem node14_28 :
    CellBound source17 nn0 nn1 Qcell ((8563:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node14_21 node21_28
private theorem node0_28 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_28
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_28
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27]
theorem packet_count : packets.length = 28 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC02
#check @N11Formalization.C450Source17GroupedC02.bound
#print axioms N11Formalization.C450Source17GroupedC02.valid0
#print axioms N11Formalization.C450Source17GroupedC02.valid1
#print axioms N11Formalization.C450Source17GroupedC02.valid2
#print axioms N11Formalization.C450Source17GroupedC02.valid3
#print axioms N11Formalization.C450Source17GroupedC02.valid4
#print axioms N11Formalization.C450Source17GroupedC02.valid5
#print axioms N11Formalization.C450Source17GroupedC02.valid6
#print axioms N11Formalization.C450Source17GroupedC02.valid7
#print axioms N11Formalization.C450Source17GroupedC02.valid8
#print axioms N11Formalization.C450Source17GroupedC02.valid9
#print axioms N11Formalization.C450Source17GroupedC02.valid10
#print axioms N11Formalization.C450Source17GroupedC02.valid11
#print axioms N11Formalization.C450Source17GroupedC02.valid12
#print axioms N11Formalization.C450Source17GroupedC02.valid13
#print axioms N11Formalization.C450Source17GroupedC02.valid14
#print axioms N11Formalization.C450Source17GroupedC02.valid15
#print axioms N11Formalization.C450Source17GroupedC02.valid16
#print axioms N11Formalization.C450Source17GroupedC02.valid17
#print axioms N11Formalization.C450Source17GroupedC02.valid18
#print axioms N11Formalization.C450Source17GroupedC02.valid19
#print axioms N11Formalization.C450Source17GroupedC02.valid20
#print axioms N11Formalization.C450Source17GroupedC02.valid21
#print axioms N11Formalization.C450Source17GroupedC02.valid22
#print axioms N11Formalization.C450Source17GroupedC02.valid23
#print axioms N11Formalization.C450Source17GroupedC02.valid24
#print axioms N11Formalization.C450Source17GroupedC02.valid25
#print axioms N11Formalization.C450Source17GroupedC02.valid26
#print axioms N11Formalization.C450Source17GroupedC02.valid27
#print axioms N11Formalization.C450Source17GroupedC02.bound
#print axioms N11Formalization.C450Source17GroupedC02.endpoint_checks
