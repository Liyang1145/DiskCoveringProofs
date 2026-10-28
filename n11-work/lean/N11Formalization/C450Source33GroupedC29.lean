import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((2557466489:ℚ)/5000000000),((681879711:ℚ)/1250000000),((10152399467:ℚ)/12875000000),((11424436243:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1665030631:ℚ)/2000000000),((-1658134473767008855584865784439097519:ℚ)/4909556800000000000000000000000000000),((-1835490480011028945485829:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((1338526787:ℚ)/2500000000),((1138883769:ℚ)/2000000000),((5255580361:ℚ)/6675000000),((18901488997:ℚ)/20600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1578190323:ℚ)/2000000000),((-1940126045753712550699478156842793655398135918243905063:ℚ)/5698400566406250000000000000000000000000000000000000000),((-12821261104590573924849:ℚ)/25600000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((5593161009:ℚ)/10000000000),((5814059541:ℚ)/10000000000),((21739483027:ℚ)/27175000000),((96062774033:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3718695017:ℚ)/5000000000),((-886590951525019164848715196390445226089770739970281264139749:ℚ)/2482816221720000000000000000000000000000000000000000000000000),((-114816164628191832140987169:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((5712646817:ℚ)/10000000000),((2966834651:ℚ)/5000000000),((22097940451:ℚ)/27650000000),((48808850463:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3601074161:ℚ)/5000000000),((-177223045548963242368052587481185725761892822284788326209:ℚ)/495433958676757812500000000000000000000000000000000000000),((-28477450181485036066308049:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1458026779:ℚ)/2500000000),((2996731541:ℚ)/5000000000),((5614080337:ℚ)/6971875000),((7028215719:ℚ)/7900000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3480237201:ℚ)/5000000000),((-250941587546575430020375234329716548451032277264414294257:ℚ)/687481255625000000000000000000000000000000000000000000000),((-28363156232239794393033169:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((368239257:ℚ)/625000000),((1513312429:ℚ)/2500000000),((1414717771:ℚ)/1757812500),((1077959199:ℚ)/1212500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6837005169:ℚ)/10000000000),((-3661766980186287528409291814735505046972854617372207:ℚ)/10026925048828125000000000000000000000000000000000000),((-7062049121993083827158809:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1190308643:ℚ)/2000000000),((3056514693:ℚ)/5000000000),((4562925929:ℚ)/5672500000),((49974691009:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3355824149:ℚ)/5000000000),((-92215811937497434561546679113957655240482649147772968637293:ℚ)/252395782470703125000000000000000000000000000000000000000000),((-28132570839245718259108401:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((3005626287:ℚ)/5000000000),((3086401133:ℚ)/5000000000),((884375297:ℚ)/1100000000),((50363214729:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6584292891:ℚ)/10000000000),((-18347194330911122697445684353270633259277711254585871107:ℚ)/50194508671484375000000000000000000000000000000000000000),((-28016279183932766643192961:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6070956333:ℚ)/10000000000),((6232568529:ℚ)/10000000000),((23172868999:ℚ)/28837500000),((101503390877:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6454817553:ℚ)/10000000000),((-65783712261886052768900435552286797169658213149985977751949:ℚ)/179897214640000000000000000000000000000000000000000000000000),((-111597285655738608888120009:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((766331829:ℚ)/1250000000),((393270521:ℚ)/625000000),((2918995487:ℚ)/3634375000),((6392516773:ℚ)/7209375000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6323088939:ℚ)/10000000000),((-1328484796531724115430563679734979695627192936818035229:ℚ)/3631544057009124755859375000000000000000000000000000000),((-434089022452397655123659:ℚ)/902500000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((773793451:ℚ)/1250000000),((6352081849:ℚ)/10000000000),((2941380353:ℚ)/3664062500),((103057064037:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((773620003:ℚ)/1250000000),((-6026454914455890258609380191952937516543671485712649180703:ℚ)/16467738913906250000000000000000000000000000000000000000000),((-110653628605466543284041049:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6250035389:ℚ)/10000000000),((6411829219:ℚ)/10000000000),((23710106167:ℚ)/29550000000),((14833397121:ℚ)/16750000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1513067017:ℚ)/2500000000),((-158867237108172014486388332350205620243246217055081805903:ℚ)/433962238769531250000000000000000000000000000000000000000),((-110177801880529311507675889:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((788714763:ℚ)/1250000000),((6471570597:ℚ)/10000000000),((2986144289:ℚ)/3723437500),((104610417761:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5912832117:ℚ)/10000000000),((-2702133732978453159099815538811889466867991768001341707607373:ℚ)/7378664162895000000000000000000000000000000000000000000000000),((-109699309197309744031682241:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((50955167:ℚ)/80000000),((3265653063:ℚ)/5000000000),((192545501:ℚ)/240200000),((52693489819:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5770450033:ℚ)/10000000000),((-3633821804140142488508933220658604522413010482187829547363:ℚ)/9919623645194702148437500000000000000000000000000000000000),((-75635838100566377069121:ℚ)/160000000000000000000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6429068819:ℚ)/10000000000),((6650760189:ℚ)/10000000000),((24247206457:ℚ)/30500000000),((106939882457:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1406223709:ℚ)/2500000000),((-23807504442827302078314318021616168501246400325988039448821:ℚ)/66044837288125000000000000000000000000000000000000000000000),((-108247832045141058903846129:ℚ)/231040000000000000000000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1309680137:ℚ)/2000000000),((846274059:ℚ)/1250000000),((703005773:ℚ)/885000000),((13561562767:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5323204793:ℚ)/10000000000),((-35390248116196840921515798928809438404694184645771910567:ℚ)/98085051269531250000000000000000000000000000000000000000),((-1676044450011161372749869:ℚ)/3610000000000000000000000)⟩
theorem valid15 : Valid source33 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6667714579:ℚ)/10000000000),((6889603973:ℚ)/10000000000),((24963143737:ℚ)/31450000000),((110044851649:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5005247437:ℚ)/10000000000),((-37670437631193374581749080187696974629077362946218116379:ℚ)/104314957454223632812500000000000000000000000000000000000),((-106275186083866855480385921:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid source33 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source33 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((169675283:ℚ)/250000000),((1782092081:ℚ)/2500000000),((633025849:ℚ)/810000000),((28287197053:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4667670053:ℚ)/10000000000),((-551467074945966324425680701621110660244117946320547475861:ℚ)/1574805727265625000000000000000000000000000000000000000000),((-6516240334337347090450289:ℚ)/14440000000000000000000000)⟩
theorem valid17 : Valid source33 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((1405111279:ℚ)/2000000000),((8082757627:ℚ)/10000000000),((5207333837:ℚ)/7240000000),((41851949717:ℚ)/43200000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((1956483199:ℚ)/5000000000),((-487247222683170613379887187467027854919565155392345656147:ℚ)/1710059040000000000000000000000000000000000000000000000000),((-11097127:ℚ)/25600000)⟩
theorem valid18 : Valid source33 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((1595837021:ℚ)/2000000000),((4518154123:ℚ)/5000000000),((5779511063:ℚ)/8000000000),((68976003599:ℚ)/72400000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-17558056613125766726257602815004875458844946789094929687:ℚ)/59297410000000000000000000000000000000000000000000000000),((-11097127:ℚ)/25600000)⟩
theorem valid19 : Valid source33 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source33 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((558257571:ℚ)/625000000),((3211401313:ℚ)/2500000000),((1984772713:ℚ)/3450000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-158782009448999:ℚ)/862500000000000),((-11097127:ℚ)/25600000)⟩
theorem valid20 : Valid source33 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source33 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source33 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source33 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC29
#check @N11Formalization.C450Source33GroupedC29.bound
#print axioms N11Formalization.C450Source33GroupedC29.valid0
#print axioms N11Formalization.C450Source33GroupedC29.valid1
#print axioms N11Formalization.C450Source33GroupedC29.valid2
#print axioms N11Formalization.C450Source33GroupedC29.valid3
#print axioms N11Formalization.C450Source33GroupedC29.valid4
#print axioms N11Formalization.C450Source33GroupedC29.valid5
#print axioms N11Formalization.C450Source33GroupedC29.valid6
#print axioms N11Formalization.C450Source33GroupedC29.valid7
#print axioms N11Formalization.C450Source33GroupedC29.valid8
#print axioms N11Formalization.C450Source33GroupedC29.valid9
#print axioms N11Formalization.C450Source33GroupedC29.valid10
#print axioms N11Formalization.C450Source33GroupedC29.valid11
#print axioms N11Formalization.C450Source33GroupedC29.valid12
#print axioms N11Formalization.C450Source33GroupedC29.valid13
#print axioms N11Formalization.C450Source33GroupedC29.valid14
#print axioms N11Formalization.C450Source33GroupedC29.valid15
#print axioms N11Formalization.C450Source33GroupedC29.valid16
#print axioms N11Formalization.C450Source33GroupedC29.valid17
#print axioms N11Formalization.C450Source33GroupedC29.valid18
#print axioms N11Formalization.C450Source33GroupedC29.valid19
#print axioms N11Formalization.C450Source33GroupedC29.valid20
#print axioms N11Formalization.C450Source33GroupedC29.bound
#print axioms N11Formalization.C450Source33GroupedC29.endpoint_checks
