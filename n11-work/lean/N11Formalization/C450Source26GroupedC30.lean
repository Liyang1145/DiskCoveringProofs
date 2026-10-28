import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((5306069889:ℚ)/10000000000),((1408281913:ℚ)/2500000000),((84338908557:ℚ)/103000000000),((11857973391:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7979621993:ℚ)/10000000000),((-1857340455387201556923547869249613469313:ℚ)/5463635000000000000000000000000000000000),((-6968717677951294731169287:ℚ)/18483200000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5544270303:ℚ)/10000000000),((2935748977:ℚ)/5000000000),((29145171313:ℚ)/35600000000),((24550242839:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7531921519:ℚ)/10000000000),((-374302943595178536584986835262924925267857782272531353:ℚ)/1101514062500000000000000000000000000000000000000000000),((-27298379896549638629057367:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((5782420669:ℚ)/10000000000),((5990660167:ℚ)/10000000000),((90531468697:ℚ)/108700000000),((16644873723:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3530911689:ℚ)/5000000000),((-8598809789980817034555143714970264510905999991068836957619:ℚ)/24081853181250000000000000000000000000000000000000000000000),((-108035796006062531854096647:ℚ)/295731200000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((2950739367:ℚ)/5000000000),((3054904073:ℚ)/5000000000),((46039611771:ℚ)/55300000000),((25384328511:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((852109701:ℚ)/1250000000),((-23555174039527572783037558776616195748106614682210272739:ℚ)/66059522265625000000000000000000000000000000000000000000),((-26718725625402293595281767:ℚ)/73932800000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((3010263087:ℚ)/5000000000),((778617827:ℚ)/1250000000),((15604473377:ℚ)/18750000000),((6450324789:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3282162481:ℚ)/5000000000),((-4890395375138860857314857284142519436509592402437478459:ℚ)/13732910156250000000000000000000000000000000000000000000),((-1651731768192764841851567:ℚ)/4620800000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6139563531:ℚ)/10000000000),((6288504999:ℚ)/10000000000),((95174325903:ℚ)/113450000000),((52019534993:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1575806931:ℚ)/2500000000),((-3323036677715726612307895442142611077754124098151169978223:ℚ)/9126274303906250000000000000000000000000000000000000000000),((-315382817442777777654960469:ℚ)/887193600000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6199078587:ℚ)/10000000000),((12398563:ℚ)/19531250),((8722547421:ℚ)/10400000000),((819319528:ℚ)/886328125),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3084564969:ℚ)/5000000000),((-605369862757861798996467590261407748339496087840061:ℚ)/1664000000000000000000000000000000000000000000000000),((-12462566191731644191:ℚ)/35253906250000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6258591309:ℚ)/10000000000),((6407620463:ℚ)/10000000000),((32240562339:ℚ)/38450000000),((52853343241:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((94257073:ℚ)/156250000),((-32285778817537019030263277164630095331535222557520448579:ℚ)/88819650195312500000000000000000000000000000000000000000),((-103958762474361592455889687:ℚ)/295731200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1263620351:ℚ)/2000000000),((6467173697:ℚ)/10000000000),((19499064563:ℚ)/23260000000),((53270215879:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((736626687:ℚ)/1250000000),((-1142653857564478439965296739491121966315548520338344387:ℚ)/3146075494000000000000000000000000000000000000000000000),((-286352202872972055315487:ℚ)/819200000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((318880499:ℚ)/500000000),((652672403:ℚ)/1000000000),((4913446487:ℚ)/5862500000),((5368706821:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2875304257:ℚ)/5000000000),((-6995052980639931158031381031616367984305069699402989:ℚ)/19274972534179687500000000000000000000000000000000000),((-1027867301590924249342607:ℚ)/2957312000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((160927901:ℚ)/250000000),((1646567883:ℚ)/2500000000),((2476062713:ℚ)/2955000000),((13525975181:ℚ)/14656250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1401252161:ℚ)/2500000000),((-1624452445547414871672740215095573199411711537544657:ℚ)/4479710742187500000000000000000000000000000000000000),((-19162409375663060723542141:ℚ)/55449600000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3248309993:ℚ)/5000000000),((415363517:ℚ)/625000000),((49908029909:ℚ)/59575000000),((3407544619:ℚ)/3693750000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5455955041:ℚ)/10000000000),((-1436541260734619583719544626687484778017758975683281007447:ℚ)/3964545670019531250000000000000000000000000000000000000000),((-396919938306478994868847:ℚ)/1155200000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6556121869:ℚ)/10000000000),((1341071663:ℚ)/2000000000),((100589584297:ℚ)/120100000000),((10987501641:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5303153371:ℚ)/10000000000),((-245012935701146483550793225195629982154563052773740710073:ℚ)/676688906640625000000000000000000000000000000000000000000),((-4040907689583686643227287:ℚ)/11829248000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3307810869:ℚ)/5000000000),((270595909:ℚ)/400000000),((16893847099:ℚ)/20175000000),((2214171363:ℚ)/2402000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1029253321:ℚ)/2000000000),((-2063292400961569014702821553815061689481877444485876971:ℚ)/5702668652343750000000000000000000000000000000000000000),((-160692928396213990295263:ℚ)/473169920000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((3337559821:ℚ)/5000000000),((1706108641:ℚ)/2500000000),((51068277673:ℚ)/61000000000),((4647586829:ℚ)/5043750000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((498490581:ℚ)/1000000000),((-512911029071172543264878902130821970462566987525860891337:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-6240166732806514030739063:ℚ)/18483200000000000000000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((2155077:ℚ)/3200000),((6943500767:ℚ)/10000000000),((10977067:ℚ)/13216000),((56604505369:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((602327279:ℚ)/1250000000),((-1275820286407803526397532120274686815962085803:ℚ)/3606783846400000000000000000000000000000000000),((-98659439146703756286585847:ℚ)/295731200000000000000000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((685360201:ℚ)/1000000000),((3531278691:ℚ)/5000000000),((10445682613:ℚ)/12580000000),((28718950837:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4469033057:ℚ)/10000000000),((-4294160260848394194823815035660521839439956623445253:ℚ)/12151278759765625000000000000000000000000000000000000),((-73104752078024969203512589:ℚ)/221798400000000000000000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((6972581233:ℚ)/10000000000),((7300643541:ℚ)/10000000000),((106003556029:ℚ)/129600000000),((59104504787:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4091862211:ℚ)/10000000000),((-170842915270061898707915549678318700671339457956088702703:ℚ)/503884800000000000000000000000000000000000000000000000000),((-285271478485478404907411389:ℚ)/887193600000000000000000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((7210519461:ℚ)/10000000000),((8252679561:ℚ)/10000000000),((109096752993:ℚ)/144800000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((64306291:ℚ)/200000000),((-319874025581269918416145762944340151768244033199127976433:ℚ)/1185948200000000000000000000000000000000000000000000000000),((-159411549:ℚ)/512000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((326481673:ℚ)/400000000),((9204327721:ℚ)/10000000000),((4858661749:ℚ)/6400000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-113076993497120800407420414550513233127642047275265141:ℚ)/409600000000000000000000000000000000000000000000000000),((-159411549:ℚ)/512000000)⟩
theorem valid19 : Valid source26 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source26 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9113274373:ℚ)/10000000000),((13008647507:ℚ)/10000000000),((133832566849:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-328819342475709686129741645031715338523:ℚ)/2691145728000000000000000000000000000000),((-159411549:ℚ)/512000000)⟩
theorem valid20 : Valid source26 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source26 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source26 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source26 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source26 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source26 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC30
#check @N11Formalization.C450Source26GroupedC30.bound
#print axioms N11Formalization.C450Source26GroupedC30.valid0
#print axioms N11Formalization.C450Source26GroupedC30.valid1
#print axioms N11Formalization.C450Source26GroupedC30.valid2
#print axioms N11Formalization.C450Source26GroupedC30.valid3
#print axioms N11Formalization.C450Source26GroupedC30.valid4
#print axioms N11Formalization.C450Source26GroupedC30.valid5
#print axioms N11Formalization.C450Source26GroupedC30.valid6
#print axioms N11Formalization.C450Source26GroupedC30.valid7
#print axioms N11Formalization.C450Source26GroupedC30.valid8
#print axioms N11Formalization.C450Source26GroupedC30.valid9
#print axioms N11Formalization.C450Source26GroupedC30.valid10
#print axioms N11Formalization.C450Source26GroupedC30.valid11
#print axioms N11Formalization.C450Source26GroupedC30.valid12
#print axioms N11Formalization.C450Source26GroupedC30.valid13
#print axioms N11Formalization.C450Source26GroupedC30.valid14
#print axioms N11Formalization.C450Source26GroupedC30.valid15
#print axioms N11Formalization.C450Source26GroupedC30.valid16
#print axioms N11Formalization.C450Source26GroupedC30.valid17
#print axioms N11Formalization.C450Source26GroupedC30.valid18
#print axioms N11Formalization.C450Source26GroupedC30.valid19
#print axioms N11Formalization.C450Source26GroupedC30.valid20
#print axioms N11Formalization.C450Source26GroupedC30.bound
#print axioms N11Formalization.C450Source26GroupedC30.endpoint_checks
