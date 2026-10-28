import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((128323463:ℚ)/200000000),((1340666073:ℚ)/2000000000),((-1212666073:ℚ)/1984000000),((-1014111167:ℚ)/2060000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5656632333:ℚ)/10000000000),((1204306225765130095835088637959547071424421582501723719:ℚ)/32363798425600000000000000000000000000000000000000000000),((22351531430596011189125097:ℚ)/118292480000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((6653999239:ℚ)/10000000000),((170556167:ℚ)/250000000),((-154556167:ℚ)/257500000),((-52845993151:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2521362471:ℚ)/5000000000),((65741544465133694134453005084952466662952720116026961:ℚ)/1834774602549743652343750000000000000000000000000000000),((348327105723832732107177:ℚ)/1848320000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((6772903407:ℚ)/10000000000),((3470578533:ℚ)/5000000000),((-3150578533:ℚ)/5245000000),((-53916130663:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4708753761:ℚ)/10000000000),((11999736887667916607705713846321797283631560295264655803:ℚ)/334840351345056152343750000000000000000000000000000000000),((139163057296421765198725777:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((6891802079:ℚ)/10000000000),((3500305067:ℚ)/5000000000),((-1060101689:ℚ)/1780000000),((-54986218711:ℚ)/107750000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((870256149:ℚ)/2000000000),((56272615108454158267768422792311869669209199158963767:ℚ)/1598580888781738281250000000000000000000000000000000000),((138980420616932877581268977:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3475624723:ℚ)/5000000000),((3530030917:ℚ)/5000000000),((-3210030917:ℚ)/5387500000),((-27760622507:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2080922689:ℚ)/5000000000),((2541317114007494524553463673286748893398794651119758297211:ℚ)/72174032755187225341796875000000000000000000000000000000000),((138896860240649162850404177:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((1402139109:ℚ)/2000000000),((7089787183:ℚ)/10000000000),((-6449787183:ℚ)/10870000000),((-11211251981:ℚ)/21835000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3963922001:ℚ)/10000000000),((20873031514688134344773618866790216859221860481959512350649:ℚ)/597991578858436694335937500000000000000000000000000000000000),((555222643132658931138461977:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((704041813:ℚ)/1000000000),((7119512203:ℚ)/10000000000),((-6479512203:ℚ)/10917500000),((-5632376317:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3861370437:ℚ)/10000000000),((7111991969156093067341575511832974499704687949334784266423:ℚ)/203716240933829695129394531250000000000000000000000000000000),((555055853964714348950789937:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-5:ℚ)/8),((-9:ℚ)/16),((707014041:ℚ)/1000000000),((7149236899:ℚ)/10000000000),((-2169745633:ℚ)/3655000000),((-5659126369:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((469520643:ℚ)/1250000000),((129226812118538330407045853965479014602207723670689747399:ℚ)/3700956700396130371093750000000000000000000000000000000000),((554889196536454705462440193:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((709986239:ℚ)/1000000000),((287158451:ℚ)/400000000),((-261558451:ℚ)/440500000),((-5685876151:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((912019009:ℚ)/2500000000),((3183754573298282016320848889620270488761472747544381:ℚ)/91165393920187377929687500000000000000000000000000000),((887556273303307859197793:ℚ)/4731699200000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7129584073:ℚ)/10000000000),((1441737067:ℚ)/2000000000),((-1313737067:ℚ)/2212000000),((-57126256657:ℚ)/111075000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3536838217:ℚ)/10000000000),((242921106825211593419202524549592110458399293449707093207:ℚ)/6954834231170568750000000000000000000000000000000000000000),((22182251071164982652452977:ℚ)/118292480000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7159305463:ℚ)/10000000000),((7238409083:ℚ)/10000000000),((-6598409083:ℚ)/11107500000),((-57393749167:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3422144127:ℚ)/10000000000),((215461538170510951344249971801823122949561104142109161147:ℚ)/6167716373434219741821289062500000000000000000000000000000),((554390014403610989747124177:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((1797256641:ℚ)/2500000000),((3634066261:ℚ)/5000000000),((-3314066261:ℚ)/5577500000),((-14415309769:ℚ)/28006250000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3303633261:ℚ)/10000000000),((1901949302338234452819134512233541836692229862250329733147:ℚ)/54436306504063025146484375000000000000000000000000000000000),((138555970915127944591264753:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-5:ℚ)/8),((-9:ℚ)/16),((7218747379:ℚ)/10000000000),((3648927829:ℚ)/5000000000),((-3328927829:ℚ)/5601250000),((-57928726411:ℚ)/112500000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((1590439241:ℚ)/5000000000),((16191681540147593187357717971498104169241689452714451:ℚ)/463360147344017028808593750000000000000000000000000000),((138514471133061079003964913:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-5:ℚ)/8),((-9:ℚ)/16),((7248467913:ℚ)/10000000000),((3663789247:ℚ)/5000000000),((-3343789247:ℚ)/5625000000),((-58196211217:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1526683697:ℚ)/5000000000),((1837735048712305665460377312893610844373921853978416291083:ℚ)/52583384227752685546875000000000000000000000000000000000000),((7288052855062905684109123:ℚ)/38912000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7278188169:ℚ)/10000000000),((7357301033:ℚ)/10000000000),((-6717301033:ℚ)/11297500000),((-58463693521:ℚ)/113450000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((584095293:ℚ)/2000000000),((253401786453998409747258952022512692443093995300187711719:ℚ)/7249634058520379623413085937500000000000000000000000000000),((553726280997460733657680777:ℚ)/2957312000000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((146158163:ℚ)/200000000),((7416745237:ℚ)/10000000000),((-6776745237:ℚ)/11345000000),((-1174623467:ℚ)/2288000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((556286813:ℚ)/2000000000),((411211096677801996681612248254593650716561056637452416811:ℚ)/11663948952536181640625000000000000000000000000000000000000),((553593057248959394966735217:ℚ)/2957312000000000000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((7367347301:ℚ)/10000000000),((74761883:ℚ)/100000000),((-68361883:ℚ)/114400000),((-59266125709:ℚ)/115350000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2480712373:ℚ)/10000000000),((476362327483470510770888071941473179764913424949:ℚ)/13509859185367187500000000000000000000000000000000),((55326250230899845138577:ℚ)/295731200000000000000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3713392697:ℚ)/5000000000),((941953781:ℚ)/1250000000),((-287317927:ℚ)/480625000),((-29900534273:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2139088603:ℚ)/10000000000),((1034323896837111008125573953792396964265444869217923427:ℚ)/29329762071538972854614257812500000000000000000000000000),((8639569894597601421357873:ℚ)/46208000000000000000000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((3743111227:ℚ)/5000000000),((7654510911:ℚ)/10000000000),((-7014510911:ℚ)/11630000000),((-30168001043:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1732526099:ℚ)/10000000000),((213666193087707164913474638751667776484660908784622704337:ℚ)/5961720890949511718750000000000000000000000000000000000000),((22722388226025721:ℚ)/121600000000000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/8),((-9:ℚ)/16),((3802546789:ℚ)/5000000000),((7892260009:ℚ)/10000000000),((-2417420003:ℚ)/3940000000),((-30702921101:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((3283782486710404545863380661849804435799194380263085061:ℚ)/88901352915625000000000000000000000000000000000000000000),((191084151:ℚ)/1024000000)⟩
theorem valid19 : Valid source12 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((784282449:ℚ)/1000000000),((4183857159:ℚ)/5000000000),((-3863857159:ℚ)/6100000000),((-6354542041:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((123825769561553930942285603268428107226365356098902279:ℚ)/3178838671875000000000000000000000000000000000000000000),((191084151:ℚ)/1024000000)⟩
theorem valid20 : Valid source12 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4159122819:ℚ)/5000000000),((1283637439:ℚ)/1250000000),((-1203637439:ℚ)/1620000000),((-33912105371:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((27528714572196580264664517443740817435310210188539:ℚ)/553584375000000000000000000000000000000000000000000),((191084151:ℚ)/1024000000)⟩
theorem valid21 : Valid source12 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10219529751:ℚ)/10000000000),((3517681221:ℚ)/2500000000),((-3357681221:ℚ)/4000000000),((-84935767759:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((601217994227484583081582932261438122250907504540528481:ℚ)/9918750000000000000000000000000000000000000000000000000),((191084151:ℚ)/1024000000)⟩
theorem valid22 : Valid source12 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source12 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC07
#check @N11Formalization.C450Source12GroupedC07.bound
#print axioms N11Formalization.C450Source12GroupedC07.valid0
#print axioms N11Formalization.C450Source12GroupedC07.valid1
#print axioms N11Formalization.C450Source12GroupedC07.valid2
#print axioms N11Formalization.C450Source12GroupedC07.valid3
#print axioms N11Formalization.C450Source12GroupedC07.valid4
#print axioms N11Formalization.C450Source12GroupedC07.valid5
#print axioms N11Formalization.C450Source12GroupedC07.valid6
#print axioms N11Formalization.C450Source12GroupedC07.valid7
#print axioms N11Formalization.C450Source12GroupedC07.valid8
#print axioms N11Formalization.C450Source12GroupedC07.valid9
#print axioms N11Formalization.C450Source12GroupedC07.valid10
#print axioms N11Formalization.C450Source12GroupedC07.valid11
#print axioms N11Formalization.C450Source12GroupedC07.valid12
#print axioms N11Formalization.C450Source12GroupedC07.valid13
#print axioms N11Formalization.C450Source12GroupedC07.valid14
#print axioms N11Formalization.C450Source12GroupedC07.valid15
#print axioms N11Formalization.C450Source12GroupedC07.valid16
#print axioms N11Formalization.C450Source12GroupedC07.valid17
#print axioms N11Formalization.C450Source12GroupedC07.valid18
#print axioms N11Formalization.C450Source12GroupedC07.valid19
#print axioms N11Formalization.C450Source12GroupedC07.valid20
#print axioms N11Formalization.C450Source12GroupedC07.valid21
#print axioms N11Formalization.C450Source12GroupedC07.valid22
#print axioms N11Formalization.C450Source12GroupedC07.bound
#print axioms N11Formalization.C450Source12GroupedC07.endpoint_checks
