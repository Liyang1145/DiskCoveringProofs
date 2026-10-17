import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((6408279241:ℚ)/10000000000),((1673813837:ℚ)/2500000000),((-13304324533:ℚ)/24800000000),((-5448279241:ℚ)/12875000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1135196389:ℚ)/2000000000),((11191829510325769081855747487732268529182624506562898757:ℚ)/248104519042968750000000000000000000000000000000000000000),((1212777683423370497045221:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((415388277:ℚ)/625000000),((340711377:ℚ)/500000000),((-2714402393:ℚ)/5150000000),((-355388277:ℚ)/819531250),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1012777943:ℚ)/2000000000),((386880145536128756555730562297985855164811486111217:ℚ)/8858369800969958305358886718750000000000000000000000),((3012697542390929602071:ℚ)/18050000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6765167227:ℚ)/10000000000),((1386638361:ℚ)/2000000000),((-11071745249:ℚ)/20980000000),((-5805167227:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2365571069:ℚ)/5000000000),((34057260711647312799922566760039458307071451772765860363:ℚ)/779954569804687500000000000000000000000000000000000000000),((48054992680280279574229:ℚ)/288800000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((6884114717:ℚ)/10000000000),((6992671097:ℚ)/10000000000),((-55894039873:ℚ)/106800000000),((-5924114717:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1093803787:ℚ)/2500000000),((136993835487757125318953409187139119797699127746001519:ℚ)/3185394197255373001098632812500000000000000000000000000),((1197530417703500003928791:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1735896461:ℚ)/2500000000),((88151857:ℚ)/125000000),((-705366713:ℚ)/1346875000),((-1495896461:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4186718147:ℚ)/10000000000),((908238446654120659480507894281218482464693062621668179:ℚ)/21116696616859436035156250000000000000000000000000000000),((11956815946394880918689:ℚ)/72200000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7003055287:ℚ)/10000000000),((1777906061:ℚ)/2500000000),((-14241154549:ℚ)/27175000000),((-6043055287:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((1994939623:ℚ)/5000000000),((12540646079107944675959896402868833722904510708113699083:ℚ)/291550813877334594726562500000000000000000000000000000000),((1193834054714153636994139:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((706252309:ℚ)/1000000000),((7141361433:ℚ)/10000000000),((-57232252897:ℚ)/109650000000),((-610252309:ℚ)/1376562500),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((236462043:ℚ)/625000000),((76333341054018539225896143185000088057911973832802537:ℚ)/1787625152245759963989257812500000000000000000000000000),((148989217622082060181667:ℚ)/902500000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7092256389:ℚ)/10000000000),((3585549097:ℚ)/5000000000),((-28749941873:ℚ)/55062500000),((-876036627:ℚ)/1975000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3676025229:ℚ)/10000000000),((5660802541680848637038906235994309520104773578166443:ℚ)/132558398132324218750000000000000000000000000000000000),((1190990785383682114865289:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3560994647:ℚ)/5000000000),((7200834533:ℚ)/10000000000),((-57767510797:ℚ)/110600000000),((-3080994647:ℚ)/6942187500),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((111424331:ℚ)/312500000),((7407776580850313169209727729615615518029589487847858993:ℚ)/173454441718236207962036132812500000000000000000000000000),((297517037418108970795309:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((715172181:ℚ)/1000000000),((3615285227:ℚ)/5000000000),((-29017567043:ℚ)/55537500000),((-619172181:ℚ)/1394375000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1725878343:ℚ)/5000000000),((40191851720713151097403110970747038864168813250382263:ℚ)/941033548225650787353515625000000000000000000000000000),((594572916836111427605217:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3590726971:ℚ)/5000000000),((1815076491:ℚ)/2500000000),((-14575688419:ℚ)/27887500000),((-3110726971:ℚ)/7001562500),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3334213313:ℚ)/10000000000),((1635372312043237114299380537741716068678951157102607441:ℚ)/38287277360166740417480468750000000000000000000000000000),((594111918610046806188127:ℚ)/3610000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((3605592847:ℚ)/5000000000),((1822510267:ℚ)/2500000000),((-14642592403:ℚ)/28006250000),((-3125592847:ℚ)/7031250000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((401567431:ℚ)/1250000000),((974662095718437859757585775734715956927571203798461501:ℚ)/22817279677838087081909179687500000000000000000000000000),((31244793688995962891377:ℚ)/190000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((452557317:ℚ)/625000000),((731977577:ℚ)/1000000000),((-5883798193:ℚ)/11250000000),((-785114634:ℚ)/1765234375),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((3086246013:ℚ)/10000000000),((5286968697689062221806769217180116447456290329314977:ℚ)/123762663190215826034545898437500000000000000000000000),((5931904011769382342073:ℚ)/36100000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((90883101:ℚ)/125000000),((7349510077:ℚ)/10000000000),((-59105590693:ℚ)/112975000000),((-78883101:ℚ)/177265625),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((2954740109:ℚ)/10000000000),((13442150495762115778309322147957655938032152155051:ℚ)/314648693690127134323120117187500000000000000000000),((592729881803740076120823:ℚ)/3610000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7300378723:ℚ)/10000000000),((92612219:ℚ)/125000000),((-745509971:ℚ)/1418125000),((-6340378723:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1408645637:ℚ)/5000000000),((356826576029313351983059452672549108094586072046581159247:ℚ)/8293782103750000000000000000000000000000000000000000000000),((47384622104566474198159:ℚ)/288800000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7359838931:ℚ)/10000000000),((7527907867:ℚ)/10000000000),((-60711170803:ℚ)/114400000000),((-6399838931:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1260317137:ℚ)/5000000000),((2177314675758772176355599223278388581430654618950492623:ℚ)/49925514431152343750000000000000000000000000000000000000),((1182930846861285997940261:ℚ)/7220000000000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((1869688791:ℚ)/2500000000),((3823416201:ℚ)/5000000000),((-30890745809:ℚ)/58150000000),((-543229597:ℚ)/1231250000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((447155833:ℚ)/2500000000),((29575767219462597391938625334913433800132060466682191:ℚ)/678372863693237304687500000000000000000000000000000000),((39718168802614521:ℚ)/243200000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((7597666041:ℚ)/10000000000),((788466513:ℚ)/1000000000),((-6392198617:ℚ)/11820000000),((-6637666041:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3097961:ℚ)/125000000),((117076455896096111050107390339560887604397224050133767039:ℚ)/2620034589843750000000000000000000000000000000000000000000),((158335439554409271:ℚ)/972800000000000000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((3917736367:ℚ)/5000000000),((8360271939:ℚ)/10000000000),((-68202447451:ℚ)/122000000000),((-3437736367:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((630079032915126951189162328895765829629058727312251929:ℚ)/13507458750000000000000000000000000000000000000000000000),((20832223:ℚ)/128000000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((831103207:ℚ)/1000000000),((10262121899:ℚ)/10000000000),((-85319097091:ℚ)/129600000000),((-735103207:ℚ)/2000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((465830123631215276905030958767863070285311233600714184977:ℚ)/8162933760000000000000000000000000000000000000000000000000),((20832223:ℚ)/128000000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((127659217:ℚ)/125000000),((140642923:ℚ)/100000000),((-1195386307:ℚ)/1600000000),((-115659217:ℚ)/345000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((416433017444339410834960813315120530308836705908201227:ℚ)/6094080000000000000000000000000000000000000000000000000),((20832223:ℚ)/128000000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source13 nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC08
#check @N11Formalization.C450Source13GroupedC08.bound
#print axioms N11Formalization.C450Source13GroupedC08.valid0
#print axioms N11Formalization.C450Source13GroupedC08.valid1
#print axioms N11Formalization.C450Source13GroupedC08.valid2
#print axioms N11Formalization.C450Source13GroupedC08.valid3
#print axioms N11Formalization.C450Source13GroupedC08.valid4
#print axioms N11Formalization.C450Source13GroupedC08.valid5
#print axioms N11Formalization.C450Source13GroupedC08.valid6
#print axioms N11Formalization.C450Source13GroupedC08.valid7
#print axioms N11Formalization.C450Source13GroupedC08.valid8
#print axioms N11Formalization.C450Source13GroupedC08.valid9
#print axioms N11Formalization.C450Source13GroupedC08.valid10
#print axioms N11Formalization.C450Source13GroupedC08.valid11
#print axioms N11Formalization.C450Source13GroupedC08.valid12
#print axioms N11Formalization.C450Source13GroupedC08.valid13
#print axioms N11Formalization.C450Source13GroupedC08.valid14
#print axioms N11Formalization.C450Source13GroupedC08.valid15
#print axioms N11Formalization.C450Source13GroupedC08.valid16
#print axioms N11Formalization.C450Source13GroupedC08.valid17
#print axioms N11Formalization.C450Source13GroupedC08.valid18
#print axioms N11Formalization.C450Source13GroupedC08.valid19
#print axioms N11Formalization.C450Source13GroupedC08.valid20
#print axioms N11Formalization.C450Source13GroupedC08.bound
#print axioms N11Formalization.C450Source13GroupedC08.endpoint_checks
