import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5898999917:ℚ)/10000000000),((200894483:ℚ)/312500000),((43532999419:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1364410449:ℚ)/2000000000),((-6939672932571276549736052171798951473:ℚ)/237927037500000000000000000000000000000),((-506956686003559369277887:ℚ)/2888000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3187035547:ℚ)/5000000000),((6666170761:ℚ)/10000000000),((3347035547:ℚ)/3950000000),((21022512283:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1439791069:ℚ)/2500000000),((-38206878596098271830794691469000885922787172441466217:ℚ)/1155560156250000000000000000000000000000000000000000000),((-515744232612661080891605143:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((6611603013:ℚ)/10000000000),((3392471607:ℚ)/5000000000),((48521221091:ℚ)/56250000000),((10689414821:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5156999391:ℚ)/10000000000),((-12947104800861774356607239354758217385914031607338209969:ℚ)/370788574218750000000000000000000000000000000000000000000),((-128512431475887959393542167:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((1682592041:ℚ)/2500000000),((3451857461:ℚ)/5000000000),((12338144287:ℚ)/14300000000),((10867572383:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4830663933:ℚ)/10000000000),((-57999034785474065200641611853728392713283688364039061:ℚ)/1661481250000000000000000000000000000000000000000000000),((-128088004661093798846679343:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1712283203:ℚ)/2500000000),((1740775127:ℚ)/2500000000),((12545982421:ℚ)/14418750000),((5478325381:ℚ)/5720000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((448262061:ℚ)/1000000000),((-78590407976730052333328006658391571579823807548759:ℚ)/2195554097235202789306640625000000000000000000000000),((-31968872791530912742795607:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1381702991:ℚ)/2000000000),((43890537:ℚ)/62500000),((10119920937:ℚ)/11630000000),((138071611:ℚ)/144187500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2149407703:ℚ)/5000000000),((-351790846936365256684412789371796432219286497693252609:ℚ)/9831485918750000000000000000000000000000000000000000000),((-19947308999759877085527:ℚ)/115520000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((6967896981:ℚ)/10000000000),((1770467791:ℚ)/2500000000),((7287896981:ℚ)/8375000000),((5567403373:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2053663069:ℚ)/5000000000),((-393975296445127581672744355158330211362041438288067919:ℚ)/11014270019531250000000000000000000000000000000000000000),((-31862465984588672577167623:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((7027278893:ℚ)/10000000000),((7141256243:ℚ)/10000000000),((51430952251:ℚ)/59100000000),((22447768729:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((97675487:ℚ)/250000000),((-3844413919066090292371359308304364041688523151167928689:ℚ)/107513057812500000000000000000000000000000000000000000000),((-508947000706921070369347967:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((3543330347:ℚ)/5000000000),((3585474361:ℚ)/5000000000),((25923312429:ℚ)/29668750000),((11268423083:ℚ)/11820000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((924114617:ℚ)/2500000000),((-5906115775122360540590015685724550952216228344966258693:ℚ)/163221650273132324218750000000000000000000000000000000000),((-127130118253433287620978743:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3558175777:ℚ)/5000000000),((7200641161:ℚ)/10000000000),((26027230439:ℚ)/29787500000),((22625923483:ℚ)/23735000000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((3586770479:ℚ)/10000000000),((-17928128035124220470106626212647966873159672420480539221:ℚ)/495568208752441406250000000000000000000000000000000000000),((-508093745203551310216315543:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((7146042387:ℚ)/10000000000),((7230333561:ℚ)/10000000000),((52262296709:ℚ)/59812500000),((22715000683:ℚ)/23830000000),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((3473774883:ℚ)/10000000000),((-9287484273626242097930014889057396802958778548034071:ℚ)/256777585839843750000000000000000000000000000000000000),((-507666817262804893655957943:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7175733193:ℚ)/10000000000),((7260025923:ℚ)/10000000000),((52470132351:ℚ)/60050000000),((2073097979:ℚ)/2175000000),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((1678568599:ℚ)/5000000000),((-12235216190370769896580566037780628674534460728116596727:ℚ)/338344453320312500000000000000000000000000000000000000000),((-507239689177896207836447007:ℚ)/2957312000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3602711987:ℚ)/5000000000),((7319410531:ℚ)/10000000000),((8779661303:ℚ)/10087500000),((22982231593:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3236463143:ℚ)/10000000000),((-171898764666274154150206052905813648243679028781741237:ℚ)/4811626675415039062500000000000000000000000000000000000),((-506384832607478155183904863:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((7264805457:ℚ)/10000000000),((7378794989:ℚ)/10000000000),((53093638199:ℚ)/61000000000),((23160384967:ℚ)/24210000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((298102717:ℚ)/1000000000),((-152004592148020635659488115731686233971279744004748034789:ℚ)/4255893750000000000000000000000000000000000000000000000000),((-1400357826706039669231463:ℚ)/8192000000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((7324186839:ℚ)/10000000000),((3719089651:ℚ)/5000000000),((53509307873:ℚ)/61475000000),((11669268953:ℚ)/12200000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((108093091:ℚ)/400000000),((-3240512213879852920431362956495811369588340434486774161:ℚ)/90751883416748046875000000000000000000000000000000000000),((-126168179403010130074915583:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((7383568123:ℚ)/10000000000),((7497563471:ℚ)/10000000000),((2567856041:ℚ)/2950000000),((23516690413:ℚ)/24590000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2392240769:ℚ)/10000000000),((-5727999978079653027555099459282511516776860132741393:ℚ)/160452343750000000000000000000000000000000000000000000),((-503815459112396468329040903:ℚ)/2957312000000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((744294931:ℚ)/1000000000),((3808165697:ℚ)/5000000000),((5434064517:ℚ)/6290000000),((11936497091:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((509118479:ℚ)/2500000000),((-52985283666919722347965121718296158753093218700941:ℚ)/1518909844970703125000000000000000000000000000000000),((-173938649:ℚ)/1024000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((1512342281:ℚ)/2000000000),((122716651:ℚ)/156250000),((3678131989:ℚ)/4320000000),((384149953:ℚ)/393125000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1004212023:ℚ)/10000000000),((-622554369912026614206943444401688044829766511974159:ℚ)/18662400000000000000000000000000000000000000000000000),((-173938649:ℚ)/1024000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((7799234529:ℚ)/10000000000),((975408121:ℚ)/1000000000),((56834641703:ℚ)/80000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-11060033089577288205582387171753787178263116849938873677:ℚ)/600000000000000000000000000000000000000000000000000000000),((-173938649:ℚ)/1024000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((4849689989:ℚ)/5000000000),((6777167113:ℚ)/5000000000),((11689276641:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-16484468038910486860767731451140131:ℚ)/1557376000000000000000000000000000000),((-173938649:ℚ)/1024000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((2383:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2459:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound ninth nn0 nn1 Qcell ((2459:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC31
#check @N11Formalization.C450NinthGroupedC31.bound
#print axioms N11Formalization.C450NinthGroupedC31.valid0
#print axioms N11Formalization.C450NinthGroupedC31.valid1
#print axioms N11Formalization.C450NinthGroupedC31.valid2
#print axioms N11Formalization.C450NinthGroupedC31.valid3
#print axioms N11Formalization.C450NinthGroupedC31.valid4
#print axioms N11Formalization.C450NinthGroupedC31.valid5
#print axioms N11Formalization.C450NinthGroupedC31.valid6
#print axioms N11Formalization.C450NinthGroupedC31.valid7
#print axioms N11Formalization.C450NinthGroupedC31.valid8
#print axioms N11Formalization.C450NinthGroupedC31.valid9
#print axioms N11Formalization.C450NinthGroupedC31.valid10
#print axioms N11Formalization.C450NinthGroupedC31.valid11
#print axioms N11Formalization.C450NinthGroupedC31.valid12
#print axioms N11Formalization.C450NinthGroupedC31.valid13
#print axioms N11Formalization.C450NinthGroupedC31.valid14
#print axioms N11Formalization.C450NinthGroupedC31.valid15
#print axioms N11Formalization.C450NinthGroupedC31.valid16
#print axioms N11Formalization.C450NinthGroupedC31.valid17
#print axioms N11Formalization.C450NinthGroupedC31.valid18
#print axioms N11Formalization.C450NinthGroupedC31.valid19
#print axioms N11Formalization.C450NinthGroupedC31.bound
#print axioms N11Formalization.C450NinthGroupedC31.endpoint_checks
