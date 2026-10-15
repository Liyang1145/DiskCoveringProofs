import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((796794033:ℚ)/1250000000),((6656363097:ℚ)/10000000000),((-6144363097:ℚ)/9920000000),((-6451146297:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((143962123:ℚ)/250000000),((4975123507945316556486516563191016661688916254257273087841:ℚ)/194182790553600000000000000000000000000000000000000000000000),((2339231789556541138969366923:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3306030403:ℚ)/5000000000),((1355044871:ℚ)/2000000000),((-1252644871:ℚ)/2060000000),((-26874273627:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((20139757:ℚ)/39062500),((370648078254181820100373332242452392199737973600757528109:ℚ)/15030473544087500000000000000000000000000000000000000000000),((93402186824619494500036427:ℚ)/591462400000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((1346181881:ℚ)/2000000000),((430880103:ℚ)/625000000),((-398880103:ℚ)/655625000),((-3654545643:ℚ)/7120000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((193165221:ℚ)/400000000),((2752752184907227234418532298906166445275846885550112169:ℚ)/111613450448352050781250000000000000000000000000000000000),((9115255340640662257409323:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((6849754491:ℚ)/10000000000),((55628071:ℚ)/80000000),((-17177357:ℚ)/28480000),((-55887790419:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((112018321:ℚ)/250000000),((7612571696897204712969659298047329752660690035069:ℚ)/314293791381600000000000000000000000000000000000000),((149211718837315705638027:ℚ)/946339840000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((276367031:ℚ)/400000000),((7012935187:ℚ)/10000000000),((-6500935187:ℚ)/10775000000),((-2256903279:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2148364307:ℚ)/5000000000),((223818832202457821211055336825476822998892712472514949604457:ℚ)/9238276192663964843750000000000000000000000000000000000000000),((2330670019536986337445352243:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((6968596249:ℚ)/10000000000),((221011269:ℚ)/312500000),((-205011269:ℚ)/339687500),((-18985788747:ℚ)/36550000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4105021163:ℚ)/10000000000),((198263048729660867252791344665088236594127759754796461:ℚ)/8181510383469855785369873046875000000000000000000000000),((2275304247374277477652267:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((3514007967:ℚ)/5000000000),((7102072993:ℚ)/10000000000),((-6590072993:ℚ)/10965000000),((-28746071703:ℚ)/55062500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((122014757:ℚ)/312500000),((38407850582855733199603391423043922757524276484771381995403:ℚ)/1598813294571128320312500000000000000000000000000000000000000),((2328881805901136693780331003:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((7057725487:ℚ)/10000000000),((7131785163:ℚ)/10000000000),((-6619785163:ℚ)/11012500000),((-57759529383:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((760089207:ℚ)/2000000000),((5749769628564064936350034743363466113020810436062553286397:ℚ)/239309159040491867065429687500000000000000000000000000000000),((2328505460369734986909977443:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7087434851:ℚ)/10000000000),((3580748561:ℚ)/5000000000),((-3324748561:ℚ)/5530000000),((-19342304553:ℚ)/37025000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1846818993:ℚ)/5000000000),((5968796029115195722434070723076000915929001999974220970799:ℚ)/248386936827520312500000000000000000000000000000000000000000),((582032567204244991849132187:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7117144027:ℚ)/10000000000),((898901109:ℚ)/1250000000),((-834901109:ℚ)/1388437500),((-58294296243:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((358379887:ℚ)/1000000000),((2001156434779413766742443994463850042974681354424797785411:ℚ)/83264171041361966514587402343750000000000000000000000000000),((36371191112736629848580707:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((3573426509:ℚ)/5000000000),((7220920417:ℚ)/10000000000),((-6708920417:ℚ)/11155000000),((-29280838581:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((8676601:ℚ)/25000000),((167488291454856971329581741605276544212577624601070284549387:ℚ)/6967847232520067218750000000000000000000000000000000000000000),((122493860395355037589585657:ℚ)/778240000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((1794140457:ℚ)/2500000000),((3625315879:ℚ)/5000000000),((-3369315879:ℚ)/5601250000),((-1634140457:ℚ)/3125000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((134153043:ℚ)/400000000),((103143486819672063635032261922982267079674537326059:ℚ)/4290371734666824340820312500000000000000000000000000),((581752904401147245953228427:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((900783807:ℚ)/1250000000),((3640171449:ℚ)/5000000000),((-3384171449:ℚ)/5625000000),((-7387054263:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((25257493:ℚ)/78125000),((182061073559337824084207955557795312204482501097225664768497:ℚ)/7572007328796386718750000000000000000000000000000000000000000),((30613697914742105362180713:ℚ)/194560000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1808994727:ℚ)/2500000000),((7310053841:ℚ)/10000000000),((-6798053841:ℚ)/11297500000),((-14840952543:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((310756607:ℚ)/1000000000),((2789327417426247944311582983697746719577306855244009030379:ℚ)/115994144936326073974609375000000000000000000000000000000000),((2326271619142231310581300507:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7265687183:ℚ)/10000000000),((7339764587:ℚ)/10000000000),((-6827764587:ℚ)/11345000000),((-19877061549:ℚ)/37975000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((2977074551:ℚ)/10000000000),((506440054646205063311616766112758143509901451088136976175857:ℚ)/21057609404135428906250000000000000000000000000000000000000000),((2325903350469127277541345443:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((1459079057:ℚ)/2000000000),((7369475141:ℚ)/10000000000),((-2285825047:ℚ)/3797500000),((-1089064683:ℚ)/2080000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((2840781417:ℚ)/10000000000),((6411698630886792456120351189968185908929877851805761:ℚ)/266563287402343750000000000000000000000000000000000000),((2325536235438438370850960707:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((457818951:ℚ)/625000000),((7428895677:ℚ)/10000000000),((-6916895677:ℚ)/11440000000),((-1253456853:ℚ)/2403125000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((539561377:ℚ)/2000000000),((15731633575436311883894736872105826365306096517947724421:ℚ)/648473240897625000000000000000000000000000000000000000000),((2325457662109507552193558163:ℚ)/14786560000000000000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1846129643:ℚ)/2500000000),((7488315469:ℚ)/10000000000),((-6976315469:ℚ)/11535000000),((-15175166787:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2386957153:ℚ)/10000000000),((104932532829495660079586254917489270238654959558213288554653:ℚ)/4324849396020850781250000000000000000000000000000000000000000),((2324731499492463045101988467:ℚ)/14786560000000000000000000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((1860983317:ℚ)/2500000000),((760715289:ℚ)/1000000000),((-709515289:ℚ)/1163000000),((-5102949951:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1015031169:ℚ)/5000000000),((2352338192269655848321106194141385416682324937379916651:ℚ)/95387534255192187500000000000000000000000000000000000000),((9558085592289323:ℚ)/60800000000000000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((1512552149:ℚ)/2000000000),((3922409777:ℚ)/5000000000),((-3666409777:ℚ)/5910000000),((-12460969341:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((990344257:ℚ)/10000000000),((6001985488360552454979849124403059611426607741309419949:ℚ)/236098674956250000000000000000000000000000000000000000000),((7637887204986931:ℚ)/48640000000000000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((7800408451:ℚ)/10000000000),((1664024707:ℚ)/2000000000),((-1561624707:ℚ)/2440000000),((-795600939:ℚ)/1600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2434817585262846556524798714197073439200537695691433:ℚ)/90792400000000000000000000000000000000000000000000000),((160741009:ℚ)/1024000000)⟩
theorem valid20 : Valid tenth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((8275677857:ℚ)/10000000000),((10221050473:ℚ)/10000000000),((-9709050473:ℚ)/12960000000),((-68721100713:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1398569022456675681728729778329252764819358810766853361:ℚ)/40814668800000000000000000000000000000000000000000000000),((160741009:ℚ)/1024000000)⟩
theorem valid21 : Valid tenth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((2035299877:ℚ)/2000000000),((14022138293:ℚ)/10000000000),((-13510138293:ℚ)/16000000000),((-5721899631:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((141181091667632149210018331143700348423352719062143307823:ℚ)/3385600000000000000000000000000000000000000000000000000000),((160741009:ℚ)/1024000000)⟩
theorem valid22 : Valid tenth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC07
#check @N11Formalization.C450TenthGroupedC07.bound
#print axioms N11Formalization.C450TenthGroupedC07.valid0
#print axioms N11Formalization.C450TenthGroupedC07.valid1
#print axioms N11Formalization.C450TenthGroupedC07.valid2
#print axioms N11Formalization.C450TenthGroupedC07.valid3
#print axioms N11Formalization.C450TenthGroupedC07.valid4
#print axioms N11Formalization.C450TenthGroupedC07.valid5
#print axioms N11Formalization.C450TenthGroupedC07.valid6
#print axioms N11Formalization.C450TenthGroupedC07.valid7
#print axioms N11Formalization.C450TenthGroupedC07.valid8
#print axioms N11Formalization.C450TenthGroupedC07.valid9
#print axioms N11Formalization.C450TenthGroupedC07.valid10
#print axioms N11Formalization.C450TenthGroupedC07.valid11
#print axioms N11Formalization.C450TenthGroupedC07.valid12
#print axioms N11Formalization.C450TenthGroupedC07.valid13
#print axioms N11Formalization.C450TenthGroupedC07.valid14
#print axioms N11Formalization.C450TenthGroupedC07.valid15
#print axioms N11Formalization.C450TenthGroupedC07.valid16
#print axioms N11Formalization.C450TenthGroupedC07.valid17
#print axioms N11Formalization.C450TenthGroupedC07.valid18
#print axioms N11Formalization.C450TenthGroupedC07.valid19
#print axioms N11Formalization.C450TenthGroupedC07.valid20
#print axioms N11Formalization.C450TenthGroupedC07.valid21
#print axioms N11Formalization.C450TenthGroupedC07.valid22
#print axioms N11Formalization.C450TenthGroupedC07.bound
#print axioms N11Formalization.C450TenthGroupedC07.endpoint_checks
