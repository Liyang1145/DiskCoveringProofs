import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((201763981:ℚ)/400000000),((2694008713:ℚ)/5000000000),((816491943:ℚ)/1030000000),((45902113269:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8450454243:ℚ)/10000000000),((-1053934586275501321048935089907708185529:ℚ)/3142116352000000000000000000000000000000),((-960854615845624612940547:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5283492093:ℚ)/10000000000),((1406913133:ℚ)/2500000000),((7043492093:ℚ)/8900000000),((23729870729:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1002629171:ℚ)/1250000000),((-12601296489952121955919642386084370467339283527278348729:ℚ)/37098962020874023437500000000000000000000000000000000000),((-946977043686776457679953:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1380687121:ℚ)/2500000000),((5747413383:ℚ)/10000000000),((5462061363:ℚ)/6793750000),((96476373979:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7573233233:ℚ)/10000000000),((-996750297643614162309994393622984563520017453445937653460631:ℚ)/2758684690800000000000000000000000000000000000000000000000000),((-7519262790470270928014289:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((5642330141:ℚ)/10000000000),((2933569537:ℚ)/5000000000),((22206990423:ℚ)/27650000000),((49016403981:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1468266039:ℚ)/2000000000),((-12568379671307517179360311575745196303810071125329620951677:ℚ)/34680377107373046875000000000000000000000000000000000000000),((-932751668376404922592047:ℚ)/1805000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((5761882933:ℚ)/10000000000),((1185397861:ℚ)/2000000000),((22565648799:ℚ)/27887500000),((19762172193:ℚ)/22120000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1420673:ℚ)/2000000),((-8017064457040896372731740293585035126334219943761924639489:ℚ)/21559412176400000000000000000000000000000000000000000000000),((-297325103542626873367221:ℚ)/577600000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((1455412243:ℚ)/2500000000),((1197366283:ℚ)/2000000000),((631804081:ℚ)/781250000),((19917761679:ℚ)/22310000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1745477039:ℚ)/2500000000),((-1123183360187319373573645359857580706460933853327897473:ℚ)/3017525106250000000000000000000000000000000000000000000),((-296162710603766724205689:ℚ)/577600000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((2940704171:ℚ)/5000000000),((6046665611:ℚ)/10000000000),((11462112513:ℚ)/14181250000),((11151850327:ℚ)/12500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6858681211:ℚ)/10000000000),((-10319238789995067396727100886884199847809485569275769520523:ℚ)/27697753906250000000000000000000000000000000000000000000000),((-7374833847608832046382721:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((2970580607:ℚ)/5000000000),((3053246047:ℚ)/5000000000),((11551741821:ℚ)/14300000000),((50572198611:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3366791933:ℚ)/5000000000),((-2433262342170674063674011736503554807377567337991067461477:ℚ)/6525286127292968750000000000000000000000000000000000000000),((-57386139121940186452287:ℚ)/112812500000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((3:ℚ)/4),((13:ℚ)/16),((6000907751:ℚ)/10000000000),((6136402503:ℚ)/10000000000),((23282723253:ℚ)/28718750000),((101533232539:ℚ)/114400000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3303253371:ℚ)/5000000000),((-810950307514060443200768992472009922568861197323390420524701:ℚ)/2149876986400000000000000000000000000000000000000000000000000),((-7330656483554792481222609:ℚ)/14440000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6030778693:ℚ)/10000000000),((385394441:ℚ)/625000000),((7790778693:ℚ)/9612500000),((6370127733:ℚ)/7179687500),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((817773601:ℚ)/1250000000),((-167800065506777567948124497513487809296282752012662922657:ℚ)/444695762448757886886596679687500000000000000000000000000),((-228620113082999854131423:ℚ)/451250000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((6060648111:ℚ)/10000000000),((247848711:ℚ)/400000000),((23461944333:ℚ)/28956250000),((4092433243:ℚ)/4614000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((25302071:ℚ)/39062500),((-4771631828001170576146115492236706021463965978438821739:ℚ)/12641324216982000000000000000000000000000000000000000000),((-32358946084180259961:ℚ)/64000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6090516023:ℚ)/10000000000),((1245224537:ℚ)/2000000000),((23551548069:ℚ)/29075000000),((20539918981:ℚ)/23165000000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((6411914051:ℚ)/10000000000),((-85292930075978689373995561635996742343136221231803650543:ℚ)/225889817404943359375000000000000000000000000000000000000),((-291443490160771025888469:ℚ)/577600000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((382523903:ℚ)/625000000),((3128012903:ℚ)/5000000000),((492523903:ℚ)/608203125),((51544167739:ℚ)/58150000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((6345922801:ℚ)/10000000000),((-180681247277405264206616560194600385844081812476271270189207:ℚ)/478363236734179687500000000000000000000000000000000000000000),((-227223242126266225111173:ℚ)/451250000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((1230049481:ℚ)/2000000000),((6285927161:ℚ)/10000000000),((4746148443:ℚ)/5862500000),((34492351031:ℚ)/38925000000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((6279337899:ℚ)/10000000000),((-21772515948288795355477145895303488808738063135125636863793:ℚ)/57625866537011718750000000000000000000000000000000000000000),((-7256156688737862195451821:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((6180110911:ℚ)/10000000000),((1578956693:ℚ)/2500000000),((23820332733:ℚ)/29431250000),((25966437009:ℚ)/29312500000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((6212139867:ℚ)/10000000000),((-70037614366655223770236638114513415071640162577328321504069:ℚ)/185313601562881469726562500000000000000000000000000000000000),((-905140759113565773464073:ℚ)/1805000000000000000000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6209972983:ℚ)/10000000000),((317286233:ℚ)/500000000),((7969972983:ℚ)/9850000000),((5212721029:ℚ)/5886250000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1228861639:ℚ)/2000000000),((-23733206599348076754129011785650241897756747999482645393:ℚ)/62777260886575317382812500000000000000000000000000000000),((-36130259488617216594153:ℚ)/72200000000000000000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6239833641:ℚ)/10000000000),((6405515351:ℚ)/10000000000),((23999500923:ℚ)/29787500000),((35010566521:ℚ)/39400000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3037910629:ℚ)/5000000000),((-341024209831904530953446100760032354075672153934416732654903:ℚ)/910946192950000000000000000000000000000000000000000000000000),((-7195772857343488834139601:ℚ)/14440000000000000000000000)⟩
theorem valid16 : Valid source35 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3149775389:ℚ)/5000000000),((6465299397:ℚ)/10000000000),((12089326167:ℚ)/15012500000),((105808892161:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((593678907:ℚ)/1000000000),((-297288186791849322559477019856022073185623599006498702565681:ℚ)/793569891615576171875000000000000000000000000000000000000000),((-7165319545014968601473709:ℚ)/14440000000000000000000000)⟩
theorem valid17 : Valid source35 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source35 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6359262457:ℚ)/10000000000),((3262538479:ℚ)/5000000000),((2706420819:ℚ)/3362500000),((53293000227:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((724355591:ℚ)/1250000000),((-136474570380142131880866579853497987120974429060754046694847:ℚ)/364058631772656250000000000000000000000000000000000000000000),((-111479561527382921250951:ℚ)/225625000000000000000000)⟩
theorem valid18 : Valid source35 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6418968807:ℚ)/10000000000),((3292424093:ℚ)/5000000000),((24536906421:ℚ)/30500000000),((53681513209:ℚ)/60525000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1412441361:ℚ)/2500000000),((-3523129427899326670881970548780449274396268567794962592301:ℚ)/9392295270410156250000000000000000000000000000000000000000),((-887986251849693713233437:ℚ)/1805000000000000000000000)⟩
theorem valid19 : Valid source35 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source35 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6478669953:ℚ)/10000000000),((1676093059:ℚ)/2500000000),((8238669953:ℚ)/10325000000),((27229209767:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((687662483:ℚ)/1250000000),((-6738703044857360353813198682784519283327051498674898197139:ℚ)/18309209570312500000000000000000000000000000000000000000000),((-880220392194625517727387:ℚ)/1805000000000000000000000)⟩
theorem valid20 : Valid source35 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3299028561:ℚ)/5000000000),((3411936341:ℚ)/5000000000),((12537085683:ℚ)/15725000000),((7890738919:ℚ)/8850000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1038605531:ℚ)/2000000000),((-36332819500249004648020905086773635548741806764167857:ℚ)/98559105682373046875000000000000000000000000000000000),((-872367344260237461366153:ℚ)/1805000000000000000000000)⟩
theorem valid21 : Valid source35 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source35 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((6717424893:ℚ)/10000000000),((7062806967:ℚ)/10000000000),((8477424893:ℚ)/10800000000),((113576490571:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((973440283:ℚ)/2000000000),((-119311967455491459415058771780838542310373036796676487286513:ℚ)/335958555150000000000000000000000000000000000000000000000000),((-6851196877443182081908689:ℚ)/14440000000000000000000000)⟩
theorem valid22 : Valid source35 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((6956105691:ℚ)/10000000000),((377021761:ℚ)/500000000),((26148317073:ℚ)/34300000000),((665475877:ℚ)/720000000),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((1036502847:ℚ)/2500000000),((-5490236771183677667610208060578321706821224929528537:ℚ)/16669800000000000000000000000000000000000000000000000),((-32936685111417942540417:ℚ)/72200000000000000000000)⟩
theorem valid23 : Valid source35 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((7433269729:ℚ)/10000000000),((2004446381:ℚ)/2500000000),((27579809187:ℚ)/36200000000),((31497802953:ℚ)/34300000000),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((419703517:ℚ)/2000000000),((-87103302341810138484676481397827340973236721212073244931:ℚ)/260857245250000000000000000000000000000000000000000000000),((-58093173:ℚ)/128000000)⟩
theorem valid24 : Valid source35 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source35 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7910205209:ℚ)/10000000000),((8971812087:ℚ)/10000000000),((29010615627:ℚ)/40000000000),((138393557131:ℚ)/144800000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1368104072585746496356695144943583673430644130441293054219:ℚ)/4743792800000000000000000000000000000000000000000000000000),((-58093173:ℚ)/128000000)⟩
theorem valid25 : Valid source35 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source35 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((8863521703:ℚ)/10000000000),((12782352743:ℚ)/10000000000),((10623521703:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1813682793039:ℚ)/11500000000000),((-58093173:ℚ)/128000000)⟩
theorem valid26 : Valid source35 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((919:ℚ)/1280) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((919:ℚ)/1280) ((4633:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4671:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source35 nn0 nn1 Qcell ((919:ℚ)/1280) ((4671:ℚ)/6400) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((4671:ℚ)/6400) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((4671:ℚ)/6400) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source35 nn0 nn1 Qcell ((4671:ℚ)/6400) ((591:ℚ)/800) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound source35 nn0 nn1 Qcell ((4671:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound source35 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source35 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound source35 nn0 nn1 Qcell ((4671:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC29
#check @N11Formalization.C450Source35GroupedC29.bound
#print axioms N11Formalization.C450Source35GroupedC29.valid0
#print axioms N11Formalization.C450Source35GroupedC29.valid1
#print axioms N11Formalization.C450Source35GroupedC29.valid2
#print axioms N11Formalization.C450Source35GroupedC29.valid3
#print axioms N11Formalization.C450Source35GroupedC29.valid4
#print axioms N11Formalization.C450Source35GroupedC29.valid5
#print axioms N11Formalization.C450Source35GroupedC29.valid6
#print axioms N11Formalization.C450Source35GroupedC29.valid7
#print axioms N11Formalization.C450Source35GroupedC29.valid8
#print axioms N11Formalization.C450Source35GroupedC29.valid9
#print axioms N11Formalization.C450Source35GroupedC29.valid10
#print axioms N11Formalization.C450Source35GroupedC29.valid11
#print axioms N11Formalization.C450Source35GroupedC29.valid12
#print axioms N11Formalization.C450Source35GroupedC29.valid13
#print axioms N11Formalization.C450Source35GroupedC29.valid14
#print axioms N11Formalization.C450Source35GroupedC29.valid15
#print axioms N11Formalization.C450Source35GroupedC29.valid16
#print axioms N11Formalization.C450Source35GroupedC29.valid17
#print axioms N11Formalization.C450Source35GroupedC29.valid18
#print axioms N11Formalization.C450Source35GroupedC29.valid19
#print axioms N11Formalization.C450Source35GroupedC29.valid20
#print axioms N11Formalization.C450Source35GroupedC29.valid21
#print axioms N11Formalization.C450Source35GroupedC29.valid22
#print axioms N11Formalization.C450Source35GroupedC29.valid23
#print axioms N11Formalization.C450Source35GroupedC29.valid24
#print axioms N11Formalization.C450Source35GroupedC29.valid25
#print axioms N11Formalization.C450Source35GroupedC29.valid26
#print axioms N11Formalization.C450Source35GroupedC29.bound
#print axioms N11Formalization.C450Source35GroupedC29.endpoint_checks
