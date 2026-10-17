import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2679999999:ℚ)/5000000000),((739899029:ℚ)/1250000000),((9319999997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7880020539:ℚ)/10000000000),((-238724190694891438771406616506441765816314968203363971:ℚ)/951708150000000000000000000000000000000000000000000000),((-116968418258567385200575223:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2917499999:ℚ)/5000000000),((6156891941:ℚ)/10000000000),((10032499997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6954535789:ℚ)/10000000000),((-55676815764004974914263207717814615048441067448395097:ℚ)/198178566796875000000000000000000000000000000000000000),((-114038589211939142035575223:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((3036249999:ℚ)/5000000000),((627573673:ℚ)/1000000000),((10388749997:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1612860119:ℚ)/2500000000),((-15409644089213122303619655242076557920136707852708153:ℚ)/52142143249511718750000000000000000000000000000000000),((-112598088050257183033075223:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3095624999:ℚ)/5000000000),((6394578367:ℚ)/10000000000),((10566874997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6186913047:ℚ)/10000000000),((-1381195540622701238091873876138161113667128762176315771:ℚ)/4678731200000000000000000000000000000000000000000000000),((-110960375959598451856825223:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3154999999:ℚ)/5000000000),((1613499513:ℚ)/2500000000),((10744999997:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2956083341:ℚ)/5000000000),((-169883297984232052684176913294346193491705143459057:ℚ)/562061848892211914062500000000000000000000000000000),((-110250306921003168150575223:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3184687499:ℚ)/5000000000),((3256708503:ℚ)/5000000000),((10834062497:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2885250193:ℚ)/5000000000),((-1484718291509228755895056259214435647385372852886230759:ℚ)/4915742959375000000000000000000000000000000000000000000),((-109435028655442634938700223:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3214374999:ℚ)/5000000000),((6572835247:ℚ)/10000000000),((10923124997:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((562568141:ℚ)/1000000000),((-4561077708207038747614180647933951157671348251319140977:ℚ)/15111578466796875000000000000000000000000000000000000000),((-108620775414829419594325223:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3244062499:ℚ)/5000000000),((829031599:ℚ)/1250000000),((11012187497:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((547745683:ℚ)/1000000000),((-129716641881231155711600701796015583071994538329618317:ℚ)/430052231250000000000000000000000000000000000000000000),((-107807546934934844997450223:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3273749999:ℚ)/5000000000),((3345834829:ℚ)/5000000000),((11101249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((8520863:ℚ)/16000000),((-4780337333470407844272074352943425615580957269002993377:ℚ)/15858182680078125000000000000000000000000000000000000000),((-106995342951530234028075223:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3303437499:ℚ)/5000000000),((6751085861:ℚ)/10000000000),((11190312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1033920103:ℚ)/2000000000),((-1223177682357035112153430591118357360475499574041577893:ℚ)/4060133439843750000000000000000000000000000000000000000),((-106184163215929772926200223:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3333124999:ℚ)/5000000000),((6810501417:ℚ)/10000000000),((11279374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5009261669:ℚ)/10000000000),((-1251734430682727821495004277720893239076302034722002793:ℚ)/4157245447558593750000000000000000000000000000000000000),((-105374007479447647931825223:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3362812499:ℚ)/5000000000),((6869916341:ℚ)/10000000000),((11368437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((302755177:ℚ)/625000000),((-5123036823816633693809025857839085477755069872815872933:ℚ)/17023575000000000000000000000000000000000000000000000000),((-104564875508940908644950223:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3392499999:ℚ)/5000000000),((6929330647:ℚ)/10000000000),((11457499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((934709533:ℚ)/2000000000),((-109188054725272376416706523558922719620958155370414299:ℚ)/363007533666992187500000000000000000000000000000000000),((-103756767086809468025575223:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3422187499:ℚ)/5000000000),((6988744349:ℚ)/10000000000),((11546562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((449704357:ℚ)/1000000000),((-1786975269902965321381155168552957438552518656867700599:ℚ)/5943796621875000000000000000000000000000000000000000000),((-102949681995453239033700223:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3451874999:ℚ)/5000000000),((7107569999:ℚ)/10000000000),((11635624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4313834561:ℚ)/10000000000),((-1371516667965698398039051172646674496932744336040305017:ℚ)/4666091043750000000000000000000000000000000000000000000),((-101220179057267326949325223:ℚ)/369664000000000000000000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3511249999:ℚ)/5000000000),((1806598349:ℚ)/2500000000),((11813749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((1961748777:ℚ)/5000000000),((-119504377588222173547012224859074527764671313948692331:ℚ)/406726744726562500000000000000000000000000000000000000),((-99611140869237063423075223:ℚ)/369664000000000000000000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3570624999:ℚ)/5000000000),((3672607319:ℚ)/5000000000),((11991874997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1746125277:ℚ)/5000000000),((-666032702036773545265021807113123971992007940164684017:ℚ)/2267481600000000000000000000000000000000000000000000000),((-98006191947620309446825223:ℚ)/369664000000000000000000000)⟩
theorem valid16 : Valid source22 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source22 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3629999999:ℚ)/5000000000),((7820479861:ℚ)/10000000000),((12169999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((1501240223:ℚ)/5000000000),((-81851147347190727636421847527496395708042378670379:ℚ)/315262554687500000000000000000000000000000000000000),((-94292027058523881020575223:ℚ)/369664000000000000000000000)⟩
theorem valid17 : Valid source22 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3867499999:ℚ)/5000000000),((8295717221:ℚ)/10000000000),((12882499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-2482579117555450617110879477896232426206505029392611651:ℚ)/9487585600000000000000000000000000000000000000000000000),((-131604697:ℚ)/512000000)⟩
theorem valid18 : Valid source22 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source22 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4104999999:ℚ)/5000000000),((9246124251:ℚ)/10000000000),((13594999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-731567032381501543657938120843119040036478270112807211:ℚ)/3200000000000000000000000000000000000000000000000000000),((-131604697:ℚ)/512000000)⟩
theorem valid19 : Valid source22 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source22 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4579999999:ℚ)/5000000000),((6523595873:ℚ)/5000000000),((15019999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-136911465345147281020902586819421633:ℚ)/1345572864000000000000000000000000000),((-131604697:ℚ)/512000000)⟩
theorem valid20 : Valid source22 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source22 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source22 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source22 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source22 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source22 nn0 nn1 Qcell ((1277:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((343:ℚ)/400) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source22 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source22 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC32
#check @N11Formalization.C450Source22GroupedC32.bound
#print axioms N11Formalization.C450Source22GroupedC32.valid0
#print axioms N11Formalization.C450Source22GroupedC32.valid1
#print axioms N11Formalization.C450Source22GroupedC32.valid2
#print axioms N11Formalization.C450Source22GroupedC32.valid3
#print axioms N11Formalization.C450Source22GroupedC32.valid4
#print axioms N11Formalization.C450Source22GroupedC32.valid5
#print axioms N11Formalization.C450Source22GroupedC32.valid6
#print axioms N11Formalization.C450Source22GroupedC32.valid7
#print axioms N11Formalization.C450Source22GroupedC32.valid8
#print axioms N11Formalization.C450Source22GroupedC32.valid9
#print axioms N11Formalization.C450Source22GroupedC32.valid10
#print axioms N11Formalization.C450Source22GroupedC32.valid11
#print axioms N11Formalization.C450Source22GroupedC32.valid12
#print axioms N11Formalization.C450Source22GroupedC32.valid13
#print axioms N11Formalization.C450Source22GroupedC32.valid14
#print axioms N11Formalization.C450Source22GroupedC32.valid15
#print axioms N11Formalization.C450Source22GroupedC32.valid16
#print axioms N11Formalization.C450Source22GroupedC32.valid17
#print axioms N11Formalization.C450Source22GroupedC32.valid18
#print axioms N11Formalization.C450Source22GroupedC32.valid19
#print axioms N11Formalization.C450Source22GroupedC32.valid20
#print axioms N11Formalization.C450Source22GroupedC32.bound
#print axioms N11Formalization.C450Source22GroupedC32.endpoint_checks
