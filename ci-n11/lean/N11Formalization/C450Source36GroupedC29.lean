import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((313034251:ℚ)/625000000),((2677169837:ℚ)/5000000000),((1279102753:ℚ)/1609375000),((46003207881:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8512819823:ℚ)/10000000000),((-470620030959653785466341359464378300781:ℚ)/1571058176000000000000000000000000000000),((-7966727271920407708177151:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((1049610997:ℚ)/2000000000),((559410803:ℚ)/1000000000),((4236832991:ℚ)/5340000000),((9512340439:ℚ)/10300000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((323427949:ℚ)/400000000),((-1087463832623029491368178492949252293156612906856305997:ℚ)/3561500354003906250000000000000000000000000000000000000),((-314351108699246472385111:ℚ)/577600000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((109748349:ℚ)/200000000),((5713931919:ℚ)/10000000000),((438045047:ℚ)/543500000),((96681114947:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3820331883:ℚ)/5000000000),((-4114147356754237375836975180483138748032376743893609687251183:ℚ)/12414081108600000000000000000000000000000000000000000000000000),((-31215027891480645123575619:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((5607049301:ℚ)/10000000000),((1458429607:ℚ)/2500000000),((22261147903:ℚ)/27650000000),((24559584891:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3705179671:ℚ)/5000000000),((-721804165728761898358734994370689570390454431519300215107:ℚ)/2167523569210815429687500000000000000000000000000000000000),((-5365677672858020271461:ℚ)/10000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((178957829:ℚ)/312500000),((5893598271:ℚ)/10000000000),((706873487:ℚ)/871484375),((99016777523:ℚ)/110600000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3587083187:ℚ)/5000000000),((-463993298217569926124350792904348150620502360051408808454899:ℚ)/1347463261025000000000000000000000000000000000000000000000000),((-30879670603348355641823139:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((723305019:ℚ)/1250000000),((5953469481:ℚ)/10000000000),((2849915057:ℚ)/3515625000),((99795103253:ℚ)/111550000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((7053669507:ℚ)/10000000000),((-585438972186151126105499825904167969178900046328142819811:ℚ)/1697357872265625000000000000000000000000000000000000000000),((-85225731131620814426379:ℚ)/160000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((2923111351:ℚ)/5000000000),((3006666139:ℚ)/5000000000),((11489334053:ℚ)/14181250000),((50286659807:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6931457287:ℚ)/10000000000),((-435959165082742941457838311650048416147895467720873993902763:ℚ)/1261978912353515625000000000000000000000000000000000000000000),((-7663152283261358812627159:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((5905998357:ℚ)/10000000000),((1510815147:ℚ)/2500000000),((23157995071:ℚ)/28481250000),((25240596911:ℚ)/28362500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((6807434197:ℚ)/10000000000),((-4557701662521441673309366703001248758270124961739819956203:ℚ)/12996385000906494140625000000000000000000000000000000000000),((-1912212962161601017136061:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((2967941827:ℚ)/5000000000),((3036593437:ℚ)/5000000000),((11623825481:ℚ)/14300000000),((50675714681:ℚ)/56962500000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3372355719:ℚ)/5000000000),((-1035133242748834828133228731486727354567415355959228198721:ℚ)/2949817532588195800781250000000000000000000000000000000000),((-7634507770219866973542751:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((3:ℚ)/4),((13:ℚ)/16),((5965767291:ℚ)/10000000000),((3051555581:ℚ)/5000000000),((23337301873:ℚ)/28718750000),((50870222553:ℚ)/57200000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((6681496251:ℚ)/10000000000),((-47180988021367137954506380957742924186433216532652562112063:ℚ)/134367311650000000000000000000000000000000000000000000000000),((-7620120044512645157913119:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((5995649291:ℚ)/10000000000),((6133033477:ℚ)/10000000000),((23426947873:ℚ)/28837500000),((102129435201:ℚ)/114875000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((661777413:ℚ)/1000000000),((-959963132385882137697430483655320689108694123353544429815163:ℚ)/2732210764485168457031250000000000000000000000000000000000000),((-30422754673532231833386491:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((3012764837:ℚ)/5000000000),((6162953843:ℚ)/10000000000),((286787671:ℚ)/353125000),((102518399959:ℚ)/115350000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((3276764949:ℚ)/5000000000),((-2540516900530116690571333766788258625749321735085750524829:ℚ)/7226366739890625000000000000000000000000000000000000000000),((-30364854556097295470342971:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6055408459:ℚ)/10000000000),((1238574457:ℚ)/2000000000),((23606225377:ℚ)/29075000000),((20581467941:ℚ)/23165000000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((324437383:ℚ)/500000000),((-39730624132780368925354297767229419195905335192959627863:ℚ)/112944908702471679687500000000000000000000000000000000000),((-1212271192479999202672771:ℚ)/2310400000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((3042642833:ℚ)/5000000000),((3111394413:ℚ)/5000000000),((11847928499:ℚ)/14596875000),((51648127369:ℚ)/58150000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((802926343:ℚ)/1250000000),((-252557022125689621994624581927196163447100022315726129145991:ℚ)/717544855101269531250000000000000000000000000000000000000000),((-7562132607699061806209151:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((1223032263:ℚ)/2000000000),((625270349:ℚ)/1000000000),((4757096789:ℚ)/5862500000),((10368514537:ℚ)/11677500000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((1271500331:ℚ)/2000000000),((-2465760823983808440007697933765624191250413687569150581231:ℚ)/7001542784246923828125000000000000000000000000000000000000),((-301901063995354995840079:ℚ)/577600000000000000000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((3072517713:ℚ)/5000000000),((62826163:ℚ)/100000000),((11937553139:ℚ)/14715625000),((1040740119:ℚ)/1172500000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((3145501007:ℚ)/5000000000),((-2089568159051017773767327357896283145663127122823238139:ℚ)/5930035250012207031250000000000000000000000000000000000),((-3013150770665479429901:ℚ)/5776000000000000000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((385931751:ℚ)/625000000),((3156263639:ℚ)/5000000000),((1497795253:ℚ)/1846875000),((52231427307:ℚ)/58862500000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2489557:ℚ)/4000000),((-33199406748868101402071934850352822689656342697850066776853:ℚ)/94165891329862976074218750000000000000000000000000000000000),((-7518183585502182459422159:ℚ)/14440000000000000000000000)⟩
theorem valid16 : Valid source36 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source36 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((3102389553:ℚ)/5000000000),((198201139:ℚ)/312500000),((12027168659:ℚ)/14834375000),((3276614807:ℚ)/3693750000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((1231230553:ℚ)/2000000000),((-791156893705831751290120125403095056113213028292394213183:ℚ)/2242812680138397216796875000000000000000000000000000000000),((-117241352699131565141761:ℚ)/225625000000000000000000)⟩
theorem valid17 : Valid source36 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6234648711:ℚ)/10000000000),((637234383:ℚ)/1000000000),((24143946133:ℚ)/29787500000),((10524046979:ℚ)/11867500000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((6087761381:ℚ)/10000000000),((-1098221402111618075781632558093303856214015962907501970117:ℚ)/3111657540806994628906250000000000000000000000000000000000),((-299546635462873329983631:ℚ)/577600000000000000000000)⟩
theorem valid18 : Valid source36 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source36 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((3:ℚ)/4),((13:ℚ)/16),((1566129213:ℚ)/2500000000),((6402249447:ℚ)/10000000000),((6058387639:ℚ)/7476562500),((105629242811:ℚ)/119150000000),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((3009347863:ℚ)/5000000000),((-111646832684826656843862994618696838363020540157822002642687:ℚ)/316172517184057617187500000000000000000000000000000000000000),((-29895366094227345896626611:ℚ)/57760000000000000000000000)⟩
theorem valid19 : Valid source36 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source36 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source36 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1258876709:ℚ)/2000000000),((160803833:ℚ)/250000000),((4864630127:ℚ)/6005000000),((2650449829:ℚ)/2990625000),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((2974465959:ℚ)/5000000000),((-118222437656381529213207712527807248652412769395518503:ℚ)/334624436408042907714843750000000000000000000000000000),((-9323716851412761473903:ℚ)/18050000000000000000000)⟩
theorem valid20 : Valid source36 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source36 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((790531101:ℚ)/1250000000),((1622988979:ℚ)/2500000000),((3051593303:ℚ)/3782812500),((26698856727:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1175688939:ℚ)/2000000000),((-71500996667461517622534344908490513398965511807453147203803:ℚ)/204782980372119140625000000000000000000000000000000000000000),((-1857276587034785642571389:ℚ)/3610000000000000000000000)⟩
theorem valid21 : Valid source36 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((797996889:ℚ)/1250000000),((6551751781:ℚ)/10000000000),((3073990667:ℚ)/3812500000),((35857591051:ℚ)/40350000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5735191401:ℚ)/10000000000),((-4377388000188821918961012651546535800810211428424533203231:ℚ)/12523060360546875000000000000000000000000000000000000000000),((-29596257868283911961948219:ℚ)/57760000000000000000000000)⟩
theorem valid22 : Valid source36 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source36 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((805461987:ℚ)/1250000000),((264461643:ℚ)/400000000),((3096385961:ℚ)/3842187500),((4334001359:ℚ)/4880000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((5588701647:ℚ)/10000000000),((-78123473912257961536346424689192877227749776546201835701:ℚ)/223258511600000000000000000000000000000000000000000000000),((-47160626028607015056171:ℚ)/92416000000000000000000)⟩
theorem valid23 : Valid source36 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6503411291:ℚ)/10000000000),((133426479:ℚ)/200000000),((24950233873:ℚ)/30975000000),((2182544227:ℚ)/2459000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((2719355269:ℚ)/5000000000),((-20166140322806620613218919629433015146863090305781203357:ℚ)/57570090779315625000000000000000000000000000000000000000),((-11741530206473813352639:ℚ)/23104000000000000000000)⟩
theorem valid24 : Valid source36 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source36 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6563121421:ℚ)/10000000000),((6790871033:ℚ)/10000000000),((25129364263:ℚ)/31450000000),((110681323429:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5284916541:ℚ)/10000000000),((-1249913470810388656952499849720277806705765893582654465809:ℚ)/3651023510897827148437500000000000000000000000000000000000),((-29108596259094745974581731:ℚ)/57760000000000000000000000)⟩
theorem valid25 : Valid source36 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source36 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((1670631593:ℚ)/2500000000),((1757473603:ℚ)/2500000000),((6371894779:ℚ)/8100000000),((1673362167:ℚ)/1850000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1241120819:ℚ)/2500000000),((-523784679189398610665888523858108436442961840570545807:ℚ)/1602692578125000000000000000000000000000000000000000000),((-1788109047635618635816061:ℚ)/3610000000000000000000000)⟩
theorem valid26 : Valid source36 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source36 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((27036243:ℚ)/39062500),((1876921449:ℚ)/2500000000),((102358729:ℚ)/133984375),((29999978837:ℚ)/32400000000),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((26614631:ℚ)/62500000),((-2030444762735450892671417085247915563487117203178782363433:ℚ)/6835659862500000000000000000000000000000000000000000000000),((-1723653484711205839007529:ℚ)/3610000000000000000000000)⟩
theorem valid27 : Valid source36 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((7398572353:ℚ)/10000000000),((1996295461:ℚ)/2500000000),((27635717059:ℚ)/36200000000),((31551840993:ℚ)/34300000000),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((92297859:ℚ)/400000000),((-39529094678154372534790826608636377467208969691577153731:ℚ)/130428622625000000000000000000000000000000000000000000000),((-60662509:ℚ)/128000000)⟩
theorem valid28 : Valid source36 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source36 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7875624109:ℚ)/10000000000),((8939457819:ℚ)/10000000000),((29066872327:ℚ)/40000000000),((138612951647:ℚ)/144800000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-593097277558345674789890641952225552951153553930813010527:ℚ)/2371896400000000000000000000000000000000000000000000000000),((-60662509:ℚ)/128000000)⟩
theorem valid29 : Valid source36 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source36 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((551821229:ℚ)/625000000),((12750649951:ℚ)/10000000000),((1995463687:ℚ)/3450000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-36885503947907:ℚ)/345000000000000),((-60662509:ℚ)/128000000)⟩
theorem valid30 : Valid source36 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet30 valid30
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_7 node7_15
private theorem node15_17 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node17_19 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node15_19 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join node15_17 node17_19
private theorem node19_21 :
    CellBound source36 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf19 leaf20
private theorem node21_23 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf21 leaf22
private theorem node19_23 :
    CellBound source36 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join node19_21 node21_23
private theorem node15_23 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node15_19 node19_23
private theorem node23_25 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source36 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join node23_25 node25_27
private theorem node27_29 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf27 leaf28
private theorem node29_31 :
    CellBound source36 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf29 leaf30
private theorem node27_31 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node27_29 node29_31
private theorem node23_31 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node23_27 node27_31
private theorem node15_31 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node15_23 node23_31
private theorem node0_31 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_31
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_31
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30]
theorem packet_count : packets.length = 31 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC29
#check @N11Formalization.C450Source36GroupedC29.bound
#print axioms N11Formalization.C450Source36GroupedC29.valid0
#print axioms N11Formalization.C450Source36GroupedC29.valid1
#print axioms N11Formalization.C450Source36GroupedC29.valid2
#print axioms N11Formalization.C450Source36GroupedC29.valid3
#print axioms N11Formalization.C450Source36GroupedC29.valid4
#print axioms N11Formalization.C450Source36GroupedC29.valid5
#print axioms N11Formalization.C450Source36GroupedC29.valid6
#print axioms N11Formalization.C450Source36GroupedC29.valid7
#print axioms N11Formalization.C450Source36GroupedC29.valid8
#print axioms N11Formalization.C450Source36GroupedC29.valid9
#print axioms N11Formalization.C450Source36GroupedC29.valid10
#print axioms N11Formalization.C450Source36GroupedC29.valid11
#print axioms N11Formalization.C450Source36GroupedC29.valid12
#print axioms N11Formalization.C450Source36GroupedC29.valid13
#print axioms N11Formalization.C450Source36GroupedC29.valid14
#print axioms N11Formalization.C450Source36GroupedC29.valid15
#print axioms N11Formalization.C450Source36GroupedC29.valid16
#print axioms N11Formalization.C450Source36GroupedC29.valid17
#print axioms N11Formalization.C450Source36GroupedC29.valid18
#print axioms N11Formalization.C450Source36GroupedC29.valid19
#print axioms N11Formalization.C450Source36GroupedC29.valid20
#print axioms N11Formalization.C450Source36GroupedC29.valid21
#print axioms N11Formalization.C450Source36GroupedC29.valid22
#print axioms N11Formalization.C450Source36GroupedC29.valid23
#print axioms N11Formalization.C450Source36GroupedC29.valid24
#print axioms N11Formalization.C450Source36GroupedC29.valid25
#print axioms N11Formalization.C450Source36GroupedC29.valid26
#print axioms N11Formalization.C450Source36GroupedC29.valid27
#print axioms N11Formalization.C450Source36GroupedC29.valid28
#print axioms N11Formalization.C450Source36GroupedC29.valid29
#print axioms N11Formalization.C450Source36GroupedC29.valid30
#print axioms N11Formalization.C450Source36GroupedC29.bound
#print axioms N11Formalization.C450Source36GroupedC29.endpoint_checks
