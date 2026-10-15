import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((325584871:ℚ)/500000000),((3404821251:ℚ)/5000000000),((-1073968831:ℚ)/1600000000),((-280784871:ℚ)/515000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5417603531:ℚ)/10000000000),((14965098875687372143108991379421571745656338692234216081:ℚ)/271590400000000000000000000000000000000000000000000000000),((10308414300250232698368177:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((843711149:ℚ)/1250000000),((6928625837:ℚ)/10000000000),((-67894884207:ℚ)/103000000000),((-731711149:ℚ)/1311250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1193911007:ℚ)/2500000000),((98741347739012129350366370679907078624048765213751591284940473:ℚ)/1878809193010937500000000000000000000000000000000000000000000000),((64347303119774136829523497:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3434335839:ℚ)/5000000000),((3494057177:ℚ)/5000000000),((-34274628947:ℚ)/52450000000),((-2986335839:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4422930403:ℚ)/10000000000),((2843398220036958615192190093422542676556508279327858656899861:ℚ)/55365005940669531250000000000000000000000000000000000000000000),((1028908304640639951846974337:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((3464079891:ℚ)/5000000000),((3523800423:ℚ)/5000000000),((-34601804653:ℚ)/52925000000),((-3016079891:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((169454711:ℚ)/400000000),((1291495586301722604548898234802734757403450984283294119251:ℚ)/25133894006372070312500000000000000000000000000000000000000),((1028582467455493854524396457:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((1746911467:ℚ)/2500000000),((3553542683:ℚ)/5000000000),((-34928969513:ℚ)/53400000000),((-1522911467:ℚ)/2693750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4041751577:ℚ)/10000000000),((11834450363530501317509626501828856496618808684645400384941:ℚ)/230195647984570312500000000000000000000000000000000000000000),((257063896744059903115888633:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((704712999:ℚ)/1000000000),((892103363:ℚ)/1250000000),((-8773136993:ℚ)/13468750000),((-615112999:ℚ)/1082250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1918926427:ℚ)/5000000000),((909341385511854864171799825556396171814928230377810064685127:ℚ)/17886158782492053508758544921875000000000000000000000000000000),((41117106520480339774082097:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((7076871331:ℚ)/10000000000),((7166567967:ℚ)/10000000000),((-5424019049:ℚ)/8325000000),((-6180871331:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((932987139:ℚ)/2500000000),((216903374911260200922830027565698032369617061796750041961:ℚ)/4265071772167968750000000000000000000000000000000000000000),((4111053238657625270291665417:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((35533061:ℚ)/50000000),((1799077141:ℚ)/2500000000),((-17709848551:ℚ)/27175000000),((-31053061:ℚ)/54587500),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3623100603:ℚ)/10000000000),((7605043882706257022148806218016010559385001009093321710498801:ℚ)/149497894714609173583984375000000000000000000000000000000000000),((102759869537917877166937:ℚ)/369664000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7136352603:ℚ)/10000000000),((7226048699:ℚ)/10000000000),((-71166535689:ℚ)/109175000000),((-6240352603:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((3511034703:ℚ)/10000000000),((497573076252006467324748251135627287109768519771230134278351759:ℚ)/9778379564823825366210937500000000000000000000000000000000000000),((4109735280542336181589970073:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7166092547:ℚ)/10000000000),((7255788379:ℚ)/10000000000),((-71493672169:ℚ)/109650000000),((-6270092547:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1697715851:ℚ)/5000000000),((9042015932800710524797563741801511415826424251067893369264151:ℚ)/177645921619014257812500000000000000000000000000000000000000000),((4109074735628441431851315273:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7195832037:ℚ)/10000000000),((7285527609:ℚ)/10000000000),((-71820803699:ℚ)/110125000000),((-6299832037:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1637958303:ℚ)/5000000000),((2030649230212032947267278267816401447659656282530207883571901:ℚ)/39884859840081977844238281250000000000000000000000000000000000),((4108413146712518242066304793:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7225571079:ℚ)/10000000000),((1828816599:ℚ)/2500000000),((-18036982589:ℚ)/27650000000),((-6329571079:ℚ)/11107500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3152043869:ℚ)/10000000000),((33204621908163063691580851464946022813329566742122486502633699:ℚ)/652015709172240820312500000000000000000000000000000000000000000),((4107750513709045093431115377:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7255309679:ℚ)/10000000000),((1469000949:ℚ)/2000000000),((-14495010439:ℚ)/22215000000),((-6359309679:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((30232773:ℚ)/100000000),((120644247250193851106737208842012863152082424524330551186521:ℚ)/2368403087398740380859375000000000000000000000000000000000000),((4107086836531649107042618977:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((7285047843:ℚ)/10000000000),((925560019:ℚ)/1250000000),((-9141160209:ℚ)/13943750000),((-6389047843:ℚ)/11250000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2888961969:ℚ)/10000000000),((2209606819906799507470332263783591795699678902430916463:ℚ)/42889780219602584838867187500000000000000000000000000000),((4106422115093106075719602953:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1468904577:ℚ)/2000000000),((466497117:ℚ)/625000000),((-4611468287:ℚ)/7031250000),((-1289704577:ℚ)/2269000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1300104789:ℚ)/5000000000),((160123239197140093213623207645063280422844294430823263177:ℚ)/3107020564377307891845703125000000000000000000000000000000),((164203581564972309798562113:ℚ)/591462400000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((3701998123:ℚ)/5000000000),((7523425949:ℚ)/10000000000),((-74437685439:ℚ)/113450000000),((-3253998123:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2276031203:ℚ)/10000000000),((9620878805207970676561289822250376768557196598990432541533489:ℚ)/186623183240578906250000000000000000000000000000000000000000000),((1025938196311460007680859513:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((746346797:ℚ)/1000000000),((7761298617:ℚ)/10000000000),((-77054284787:ℚ)/114400000000),((-218915599:ℚ)/394000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1898356587:ℚ)/10000000000),((4976119435795304428501091194688901232631558351207828376678853:ℚ)/90788439570400000000000000000000000000000000000000000000000000),((41024118528215096550879273:ℚ)/147865600000000000000000000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((7701339283:ℚ)/10000000000),((3999574009:ℚ)/5000000000),((-13278438033:ℚ)/19700000000),((-6805339283:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((9730265506651244631778059429865558296614722456962735262383:ℚ)/177802705831250000000000000000000000000000000000000000000000),((283886251:ℚ)/1024000000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7939187413:ℚ)/10000000000),((2118696307:ℚ)/2500000000),((-21225659377:ℚ)/30500000000),((-7043187413:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((68100138636364679926867814838415786753152463473487059082807:ℚ)/1163454953906250000000000000000000000000000000000000000000000),((283886251:ℚ)/1024000000)⟩
theorem valid18 : Valid source15 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8414822307:ℚ)/10000000000),((10376727831:ℚ)/10000000000),((-105824006141:ℚ)/129600000000),((-7518822307:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((359445045827545790624359525234919106257891283342675533113:ℚ)/4534963200000000000000000000000000000000000000000000000000),((283886251:ℚ)/1024000000)⟩
theorem valid19 : Valid source15 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((10316757851:ℚ)/10000000000),((14179006853:ℚ)/10000000000),((-147649075383:ℚ)/160000000000),((-3140252617:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((54777714634143542103300250572986123388851:ℚ)/541696000000000000000000000000000000000000),((283886251:ℚ)/1024000000)⟩
theorem valid20 : Valid source15 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((881:ℚ)/1280) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((881:ℚ)/1280) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((881:ℚ)/1280) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((2269:ℚ)/3200) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source15 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC06
#check @N11Formalization.C450Source15GroupedC06.bound
#print axioms N11Formalization.C450Source15GroupedC06.valid0
#print axioms N11Formalization.C450Source15GroupedC06.valid1
#print axioms N11Formalization.C450Source15GroupedC06.valid2
#print axioms N11Formalization.C450Source15GroupedC06.valid3
#print axioms N11Formalization.C450Source15GroupedC06.valid4
#print axioms N11Formalization.C450Source15GroupedC06.valid5
#print axioms N11Formalization.C450Source15GroupedC06.valid6
#print axioms N11Formalization.C450Source15GroupedC06.valid7
#print axioms N11Formalization.C450Source15GroupedC06.valid8
#print axioms N11Formalization.C450Source15GroupedC06.valid9
#print axioms N11Formalization.C450Source15GroupedC06.valid10
#print axioms N11Formalization.C450Source15GroupedC06.valid11
#print axioms N11Formalization.C450Source15GroupedC06.valid12
#print axioms N11Formalization.C450Source15GroupedC06.valid13
#print axioms N11Formalization.C450Source15GroupedC06.valid14
#print axioms N11Formalization.C450Source15GroupedC06.valid15
#print axioms N11Formalization.C450Source15GroupedC06.valid16
#print axioms N11Formalization.C450Source15GroupedC06.valid17
#print axioms N11Formalization.C450Source15GroupedC06.valid18
#print axioms N11Formalization.C450Source15GroupedC06.valid19
#print axioms N11Formalization.C450Source15GroupedC06.valid20
#print axioms N11Formalization.C450Source15GroupedC06.bound
#print axioms N11Formalization.C450Source15GroupedC06.endpoint_checks
