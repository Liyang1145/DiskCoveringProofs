import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2659999999:ℚ)/5000000000),((117621933:ℚ)/200000000),((3107999999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1988497077:ℚ)/2500000000),((-5461206732124676881721130835972773126748635188058967:ℚ)/17624225000000000000000000000000000000000000000000000),((-27828594500201048280192621:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2897499999:ℚ)/5000000000),((6118816857:ℚ)/10000000000),((10036499997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3518139517:ℚ)/5000000000),((-11368443469742679588939806859758724933840260773333821:ℚ)/33029761132812500000000000000000000000000000000000000),((-27076527653651554665192621:ℚ)/92416000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((3016249999:ℚ)/5000000000),((49901371:ℚ)/80000000),((3464249999:ℚ)/3750000000),(1:ℚ),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1634616521:ℚ)/2500000000),((-116127332364906099836561778012818216669979078345127:ℚ)/321865081787109375000000000000000000000000000000000),((-26708666645922586317692621:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3075624999:ℚ)/5000000000),((6297097319:ℚ)/10000000000),((10570874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6277092003:ℚ)/10000000000),((-2104561201620094690770691034656323755126582064374181:ℚ)/5703921439941406250000000000000000000000000000000000),((-26526778901470865318942621:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3105312499:ℚ)/5000000000),((397282651:ℚ)/625000000),((969085227:ℚ)/1040000000),(1:ℚ),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3071409939:ℚ)/5000000000),((-648028772047120813299900895875609489039533215632939:ℚ)/1757600000000000000000000000000000000000000000000000),((-26310568043794008413317621:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3134999999:ℚ)/5000000000),((6415946687:ℚ)/10000000000),((3582999999:ℚ)/3845000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1501485319:ℚ)/2500000000),((-1278331249697243652156091161785289790424671057263:ℚ)/3469517585754394531250000000000000000000000000000),((-26094700214844008090192621:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3164687499:ℚ)/5000000000),((809421269:ℚ)/1250000000),((10838062497:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((586627099:ℚ)/1000000000),((-904996871099433776936900125647015962133704645325783561:ℚ)/2457871479687500000000000000000000000000000000000000000),((-25879175329957593949567621:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3194374999:ℚ)/5000000000),((6534792831:ℚ)/10000000000),((10927124997:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5723601857:ℚ)/10000000000),((-926772842651445818533611237108958247895292806819092661:ℚ)/2518596411132812500000000000000000000000000000000000000),((-25663993304471495591442621:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3224062499:ℚ)/5000000000),((6564503881:ℚ)/10000000000),((11016187497:ℚ)/11772500000),(1:ℚ),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((2788850463:ℚ)/5000000000),((-55766790593962198802759875803441570683396836741348137:ℚ)/149960611254882812500000000000000000000000000000000000),((-25574924995121760375817621:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3238906249:ℚ)/5000000000),((3297107371:ℚ)/5000000000),((3686906249:ℚ)/3940000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2751728773:ℚ)/5000000000),((-8881701365522752317177327229515687443602231177099177:ℚ)/23891790625000000000000000000000000000000000000000000),((-25467633098564520946442621:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3253749999:ℚ)/5000000000),((827990677:ℚ)/1250000000),((11105249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((5428304727:ℚ)/10000000000),((-970504695024210594309026290864171679274936872552140869:ℚ)/2611546404370117187500000000000000000000000000000000000),((-25360426876642307022692621:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3268593749:ℚ)/5000000000),((1330727181:ℚ)/2000000000),((11149781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((26761019:ℚ)/50000000),((-981878741366938726977252063964071695351449431861432111:ℚ)/2643030446679687500000000000000000000000000000000000000),((-25253306320888791564567621:ℚ)/92416000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3283437499:ℚ)/5000000000),((6683346211:ℚ)/10000000000),((3731437499:ℚ)/3987500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((5275113367:ℚ)/10000000000),((-214054431449629574609978564467343249073158173993:ℚ)/576380664062500000000000000000000000000000000000),((-25146271422837647532067621:ℚ)/92416000000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3298281249:ℚ)/5000000000),((419566021:ℚ)/625000000),((11238843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((5196989027:ℚ)/10000000000),((-251226992325167749977786329808950571191216945694176499:ℚ)/676688906640625000000000000000000000000000000000000000),((-25039322174022547885192621:ℚ)/92416000000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3313124999:ℚ)/5000000000),((6772476053:ℚ)/10000000000),((1253708333:ℚ)/1345000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((255889153:ℚ)/500000000),((-348959577366842103197210564180349864411352232116181:ℚ)/950444775390625000000000000000000000000000000000000),((-24806692247192411663942621:ℚ)/92416000000000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3342812499:ℚ)/5000000000),((3415947537:ℚ)/5000000000),((11372437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4955916579:ℚ)/10000000000),((-1041205131743288385704262066127544141641866135042294969:ℚ)/2837262500000000000000000000000000000000000000000000000),((-24593223367287414778317621:ℚ)/92416000000000000000000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3372499999:ℚ)/5000000000),((6891313413:ℚ)/10000000000),((11461499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((4789050857:ℚ)/10000000000),((-66576737263542615389533500680272777659685522024699221:ℚ)/181503766833496093750000000000000000000000000000000000),((-24380096906533727595192621:ℚ)/92416000000000000000000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3402187499:ℚ)/5000000000),((6950731087:ℚ)/10000000000),((3850187499:ℚ)/4130000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((461664063:ℚ)/1000000000),((-40356957097760681185733243969158912067718710012956923:ℚ)/110070307812500000000000000000000000000000000000000000),((-24167312792967570274567621:ℚ)/92416000000000000000000000)⟩
theorem valid17 : Valid source23 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source23 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3431874999:ℚ)/5000000000),((7069564499:ℚ)/10000000000),((11639624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4438036453:ℚ)/10000000000),((-16422982108256642954245765124067394092639959373428493:ℚ)/45745990625000000000000000000000000000000000000000000),((-23703351676919724256442621:ℚ)/92416000000000000000000000)⟩
theorem valid18 : Valid source23 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3491249999:ℚ)/5000000000),((7307223979:ℚ)/10000000000),((1313083333:ℚ)/1440000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((811786873:ℚ)/2000000000),((-178724738988474989040510462763171230170391589663589:ℚ)/518400000000000000000000000000000000000000000000000),((-22776479129578290287692621:ℚ)/92416000000000000000000000)⟩
theorem valid19 : Valid source23 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3609999999:ℚ)/5000000000),((7782516411:ℚ)/10000000000),((12173999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((198475269:ℚ)/625000000),((-50411812196829889688737001277774988393681279361541:ℚ)/157631277343750000000000000000000000000000000000000),((-21699542530709276380192621:ℚ)/92416000000000000000000000)⟩
theorem valid20 : Valid source23 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3847499999:ℚ)/5000000000),((8257778121:ℚ)/10000000000),((12886499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-1528104440526546632596794574943702195113421650527230829:ℚ)/4743792800000000000000000000000000000000000000000000000),((-30430379:ℚ)/128000000)⟩
theorem valid21 : Valid source23 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source23 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4084999999:ℚ)/5000000000),((4604113451:ℚ)/5000000000),((13598999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-454698141337847030916716474965608464935968517850904069:ℚ)/1600000000000000000000000000000000000000000000000000000),((-30430379:ℚ)/128000000)⟩
theorem valid22 : Valid source23 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source23 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4559999999:ℚ)/5000000000),((13009403867:ℚ)/10000000000),((5007999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-3436523509916952779046475535989341:ℚ)/24918016000000000000000000000000000),((-30430379:ℚ)/128000000)⟩
theorem valid23 : Valid source23 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet23 valid23
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4709:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4709:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((4709:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((2307:ℚ)/3200) ((2383:ℚ)/3200) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2383:ℚ)/3200) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source23 nn0 nn1 Qcell ((957:ℚ)/1280) ((2421:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source23 nn0 nn1 Qcell ((2421:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((343:ℚ)/400) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf18 node19_21
private theorem node22_24 :
    CellBound source23 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source23 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf21 node22_24
private theorem node18_24 :
    CellBound source23 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node18_21 node21_24
private theorem node12_24 :
    CellBound source23 nn0 nn1 Qcell ((2383:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node12_18 node18_24
private theorem node0_24 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_24
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_24
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23]
theorem packet_count : packets.length = 24 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC32
#check @N11Formalization.C450Source23GroupedC32.bound
#print axioms N11Formalization.C450Source23GroupedC32.valid0
#print axioms N11Formalization.C450Source23GroupedC32.valid1
#print axioms N11Formalization.C450Source23GroupedC32.valid2
#print axioms N11Formalization.C450Source23GroupedC32.valid3
#print axioms N11Formalization.C450Source23GroupedC32.valid4
#print axioms N11Formalization.C450Source23GroupedC32.valid5
#print axioms N11Formalization.C450Source23GroupedC32.valid6
#print axioms N11Formalization.C450Source23GroupedC32.valid7
#print axioms N11Formalization.C450Source23GroupedC32.valid8
#print axioms N11Formalization.C450Source23GroupedC32.valid9
#print axioms N11Formalization.C450Source23GroupedC32.valid10
#print axioms N11Formalization.C450Source23GroupedC32.valid11
#print axioms N11Formalization.C450Source23GroupedC32.valid12
#print axioms N11Formalization.C450Source23GroupedC32.valid13
#print axioms N11Formalization.C450Source23GroupedC32.valid14
#print axioms N11Formalization.C450Source23GroupedC32.valid15
#print axioms N11Formalization.C450Source23GroupedC32.valid16
#print axioms N11Formalization.C450Source23GroupedC32.valid17
#print axioms N11Formalization.C450Source23GroupedC32.valid18
#print axioms N11Formalization.C450Source23GroupedC32.valid19
#print axioms N11Formalization.C450Source23GroupedC32.valid20
#print axioms N11Formalization.C450Source23GroupedC32.valid21
#print axioms N11Formalization.C450Source23GroupedC32.valid22
#print axioms N11Formalization.C450Source23GroupedC32.valid23
#print axioms N11Formalization.C450Source23GroupedC32.bound
#print axioms N11Formalization.C450Source23GroupedC32.endpoint_checks
