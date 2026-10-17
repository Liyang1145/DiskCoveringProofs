import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((5269522633:ℚ)/10000000000),((2799275017:ℚ)/5000000000),((84503794229:ℚ)/103000000000),((23754925119:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((32186291:ℚ)/40000000),((-1944062749921361704887014821016741720637:ℚ)/5463635000000000000000000000000000000000),((-1470944239693424025324756197:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2753890237:ℚ)/5000000000),((2918497407:ℚ)/5000000000),((14600191027:ℚ)/17800000000),((24589481849:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((475116161:ℚ)/625000000),((-48968448692135554340315253543162119480651297956129661:ℚ)/137689257812500000000000000000000000000000000000000000),((-4324668040871589020825106431:ℚ)/11089920000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((5745984147:ℚ)/10000000000),((1489048073:ℚ)/2500000000),((90697793911:ℚ)/108700000000),((4167778837:ℚ)/4450000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((445961633:ℚ)/625000000),((-2990457287609318939547260324584982975303442626231283165473:ℚ)/8027284393750000000000000000000000000000000000000000000000),((-356699348738284301449894117:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((91641679:ℚ)/156250000),((759421789:ℚ)/1250000000),((1441341827:ℚ)/1728125000),((6355952523:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((861569967:ℚ)/1250000000),((-750021952250738787789328503042957343578859544255061:ℚ)/2015976631641387939453125000000000000000000000000000),((-88249728411852261574911933:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((2992069633:ℚ)/5000000000),((6134959773:ℚ)/10000000000),((46896905229:ℚ)/55775000000),((51264718411:ℚ)/55300000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((6642380167:ℚ)/10000000000),((-412143374531987168156216298904325830335405975235974338203:ℚ)/1084423085058593750000000000000000000000000000000000000000),((-16854943060633712549710228151:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((6043671043:ℚ)/10000000000),((3097270831:ℚ)/5000000000),((94567723559:ℚ)/112500000000),((25840895817:ℚ)/27887500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3257130987:ℚ)/5000000000),((-375462393858390413128533915639889455595540753672874387353:ℚ)/988769531250000000000000000000000000000000000000000000000),((-1397150711743926603410260853:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6103200163:ℚ)/10000000000),((6254120067:ℚ)/10000000000),((95341602119:ℚ)/113450000000),((52098840469:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((398997473:ℚ)/625000000),((-3462546551533340180752258784016696985014220803047997371753:ℚ)/9126274303906250000000000000000000000000000000000000000000),((-16676544188299054088231398391:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((1540681673:ℚ)/2500000000),((3156847539:ℚ)/5000000000),((24028861749:ℚ)/28600000000),((26257932773:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6251333477:ℚ)/10000000000),((-15503992882158137413076848726155761869066867621962461:ℚ)/40898000000000000000000000000000000000000000000000000),((-4146787472822531902538659799:ℚ)/11089920000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3111125347:ℚ)/5000000000),((6373266777:ℚ)/10000000000),((16148209837:ℚ)/19225000000),((52932867439:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((764528703:ℚ)/1250000000),((-4205409907699413097924486711595736263349782163950570259:ℚ)/11102456274414062500000000000000000000000000000000000000),((-16497625549655143162089575951:ℚ)/44359680000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6281772233:ℚ)/10000000000),((402052203:ℚ)/625000000),((97663039029:ℚ)/116300000000),((3334365421:ℚ)/3604687500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5978477079:ℚ)/10000000000),((-148841595085758507716714148375026797558333804180053230027:ℚ)/393259436750000000000000000000000000000000000000000000000),((-64093636950749484748992071:ℚ)/173280000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((634129137:ℚ)/1000000000),((811550071:ℚ)/1250000000),((9843678781:ℚ)/11725000000),((6720850497:ℚ)/7268750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2918942683:ℚ)/5000000000),((-136072224312683788179953702645584992679259541981237141:ℚ)/359799487304687500000000000000000000000000000000000000),((-84990553782784704320529893:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3200404081:ℚ)/5000000000),((3275981407:ℚ)/5000000000),((16535084351:ℚ)/19700000000),((27091869849:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((711780147:ℚ)/1250000000),((-4514389962289012684748717059034850425881561187362958257:ℚ)/11945895312500000000000000000000000000000000000000000000),((-1352355937954897899163683477:ℚ)/3696640000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6460322667:ℚ)/10000000000),((330576103:ℚ)/500000000),((99984194671:ℚ)/119150000000),((910010907:ℚ)/985000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5547304327:ℚ)/10000000000),((-3992283377277117467229690093077916183380348281485875718753:ℚ)/10572121786718750000000000000000000000000000000000000000000),((-13448521463182847838535557:ℚ)/36966400000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((325991747:ℚ)/500000000),((6671078379:ℚ)/10000000000),((5037892711:ℚ)/6005000000),((55017548653:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((674600347:ℚ)/1250000000),((-31918634291485485588237802893057238930891526955593673:ℚ)/84586113330078125000000000000000000000000000000000000),((-16048049737155323503270219079:ℚ)/44359680000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6579345033:ℚ)/10000000000),((3365315919:ℚ)/5000000000),((101531485429:ℚ)/121050000000),((27717211433:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5119557:ℚ)/9765625),((-154827774838151838861346467570649068958601511427819096841:ℚ)/410592142968750000000000000000000000000000000000000000000),((-3989435779421949636760678559:ℚ)/11089920000000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((6638852999:ℚ)/10000000000),((3395091253:ℚ)/5000000000),((102305088987:ℚ)/122000000000),((9308546257:ℚ)/10087500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((50838189:ℚ)/100000000),((-4276589131771478210123261772192000153622587555318945754989:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-1322275484332534492480963757:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((837294861:ℚ)/1250000000),((276371029:ℚ)/400000000),((12884833193:ℚ)/15487500000),((2267397203:ℚ)/2440000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2460283981:ℚ)/5000000000),((-714221543991046624264806526295486668227044311690034837:ℚ)/1934829629516601562500000000000000000000000000000000000),((-8365887374696500778157293:ℚ)/23658496000000000000000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6817364623:ℚ)/10000000000),((7028358533:ℚ)/10000000000),((104625740099:ℚ)/125800000000),((19172836577:ℚ)/20650000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4578121121:ℚ)/10000000000),((-4481323830307052588777924188347575502849481095538448733:ℚ)/12151278759765625000000000000000000000000000000000000000),((-14316018626294267605111877:ℚ)/40960000000000000000000000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((693636261:ℚ)/1000000000),((7266494757:ℚ)/10000000000),((10617271393:ℚ)/12960000000),((59185463299:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4210035057:ℚ)/10000000000),((-59576796876506930981290620616945565905300640068059679:ℚ)/167961600000000000000000000000000000000000000000000000),((-15139093583862402995122309031:ℚ)/44359680000000000000000000000)⟩
theorem valid18 : Valid source27 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((1434867341:ℚ)/2000000000),((8218704587:ℚ)/10000000000),((21853275433:ℚ)/28960000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((3362710293:ℚ)/10000000000),((-2718419350195986180560951223602313746302403687549119799:ℚ)/9487585600000000000000000000000000000000000000000000000),((-337582527:ℚ)/1024000000)⟩
theorem valid19 : Valid source27 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((8125983619:ℚ)/10000000000),((4585246677:ℚ)/5000000000),((121637787047:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1873001893220753773599396895643727182384391143328258782481:ℚ)/6400000000000000000000000000000000000000000000000000000000),((-337582527:ℚ)/1024000000)⟩
theorem valid20 : Valid source27 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source27 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((1815463391:ℚ)/2000000000),((519007253:ℚ)/400000000),((26801024083:ℚ)/44160000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1012253460171184597282635081079436189:ℚ)/7176388608000000000000000000000000000),((-337582527:ℚ)/1024000000)⟩
theorem valid21 : Valid source27 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source27 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source27 nn0 nn1 Qcell ((2231:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source27 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source27 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC30
#check @N11Formalization.C450Source27GroupedC30.bound
#print axioms N11Formalization.C450Source27GroupedC30.valid0
#print axioms N11Formalization.C450Source27GroupedC30.valid1
#print axioms N11Formalization.C450Source27GroupedC30.valid2
#print axioms N11Formalization.C450Source27GroupedC30.valid3
#print axioms N11Formalization.C450Source27GroupedC30.valid4
#print axioms N11Formalization.C450Source27GroupedC30.valid5
#print axioms N11Formalization.C450Source27GroupedC30.valid6
#print axioms N11Formalization.C450Source27GroupedC30.valid7
#print axioms N11Formalization.C450Source27GroupedC30.valid8
#print axioms N11Formalization.C450Source27GroupedC30.valid9
#print axioms N11Formalization.C450Source27GroupedC30.valid10
#print axioms N11Formalization.C450Source27GroupedC30.valid11
#print axioms N11Formalization.C450Source27GroupedC30.valid12
#print axioms N11Formalization.C450Source27GroupedC30.valid13
#print axioms N11Formalization.C450Source27GroupedC30.valid14
#print axioms N11Formalization.C450Source27GroupedC30.valid15
#print axioms N11Formalization.C450Source27GroupedC30.valid16
#print axioms N11Formalization.C450Source27GroupedC30.valid17
#print axioms N11Formalization.C450Source27GroupedC30.valid18
#print axioms N11Formalization.C450Source27GroupedC30.valid19
#print axioms N11Formalization.C450Source27GroupedC30.valid20
#print axioms N11Formalization.C450Source27GroupedC30.valid21
#print axioms N11Formalization.C450Source27GroupedC30.bound
#print axioms N11Formalization.C450Source27GroupedC30.endpoint_checks
