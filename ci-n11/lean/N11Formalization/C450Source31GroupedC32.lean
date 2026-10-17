import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2499999999:ℚ)/5000000000),((5212238:ℚ)/9765625),((9355999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((426388209:ℚ)/500000000),((-193979501724150004029314615737537171:ℚ)/530450000000000000000000000000000000),((-374781736584254527163946041:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2618749999:ℚ)/5000000000),((5575283299:ℚ)/10000000000),((9712249997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((25327757:ℚ)/31250000),((-11661243568560975232895675589620429:ℚ)/31684000000000000000000000000000000),((-369502892848537777086446041:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2737499999:ℚ)/5000000000),((5694247219:ℚ)/10000000000),((10068499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3832125171:ℚ)/5000000000),((-223610216429803914536518871536399639:ℚ)/590784500000000000000000000000000000),((-368174448357190125448946041:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2796874999:ℚ)/5000000000),((5813203771:ℚ)/10000000000),((1463803571:ℚ)/1580000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((7436245303:ℚ)/10000000000),((-591764258630538661258473052404307:ℚ)/1560250000000000000000000000000000),((-365633026663348307065196041:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2856249999:ℚ)/5000000000),((5872679401:ℚ)/10000000000),((10424749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((360122061:ℚ)/500000000),((-59753516730830462817391752630415183:ℚ)/155542531250000000000000000000000000),((-365038565333343634971446041:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2885937499:ℚ)/5000000000),((370759583:ℚ)/625000000),((10513812497:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3541589621:ℚ)/5000000000),((-187727311650613143948267711162979:ℚ)/488281250000000000000000000000000),((-363792339643773072303321041:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2915624999:ℚ)/5000000000),((2995812797:ℚ)/5000000000),((10602874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1392446623:ℚ)/2000000000),((-12380423854219011025656129706855867:ℚ)/32177256250000000000000000000000000),((-362553123213943033967696041:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((2945312499:ℚ)/5000000000),((6051096241:ℚ)/10000000000),((10691937497:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((273580437:ℚ)/400000000),((-251955641456823990350874930167293261:ℚ)/654368000000000000000000000000000000),((-361320914688733586524571041:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2974999999:ℚ)/5000000000),((1527641327:ℚ)/2500000000),((10780999997:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6714912707:ℚ)/10000000000),((-267016686743676795794164441901773:ℚ)/693001171875000000000000000000000),((-360095712809819077493946041:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3004687499:ℚ)/5000000000),((3070149631:ℚ)/5000000000),((10870062497:ℚ)/11582500000),(1:ℚ),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((6588329417:ℚ)/10000000000),((-51995837603532520668853925399990081:ℚ)/134154306250000000000000000000000000),((-359836862892911317435821041:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3019531249:ℚ)/5000000000),((1234006567:ℚ)/2000000000),((10914593747:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((6524256519:ℚ)/10000000000),((-262194185395375604186555351971689653:ℚ)/676284500000000000000000000000000000),((-359230379153233278991446041:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3034374999:ℚ)/5000000000),((387485377:ℚ)/625000000),((10959124997:ℚ)/11677500000),(1:ℚ),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((50465951:ℚ)/78125000),((-11017393866307367846161054391460857:ℚ)/28409167968750000000000000000000000),((-358625646462098529070196041:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3049218749:ℚ)/5000000000),((6229498859:ℚ)/10000000000),((11003656247:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((6394468289:ℚ)/10000000000),((-266648981154297313591023570665903053:ℚ)/687378125000000000000000000000000000),((-358022664625918505752071041:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3064062499:ℚ)/5000000000),((6259231319:ℚ)/10000000000),((11048187497:ℚ)/11772500000),(1:ℚ),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((3164359307:ℚ)/5000000000),((-268888761392749010600234323411609001:ℚ)/692958781250000000000000000000000000),((-357421433547898928077071041:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3078906249:ℚ)/5000000000),((6288963417:ℚ)/10000000000),((11092718747:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3131187111:ℚ)/5000000000),((-45189464059265162736927948329557717:ℚ)/116427000000000000000000000000000000),((-356821953066715994445196041:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3093749999:ℚ)/5000000000),((6318695157:ℚ)/10000000000),((11137249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((6195415677:ℚ)/10000000000),((-5816873209612872816963560237488073:ℚ)/14982718750000000000000000000000000),((-356224223053310663576446041:ℚ)/739328000000000000000000000)⟩
theorem valid15 : Valid source31 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source31 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3108593749:ℚ)/5000000000),((6348426543:ℚ)/10000000000),((11181781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((612782251:ℚ)/1000000000),((-275657521669474463287680267756826103:ℚ)/709836125000000000000000000000000000),((-355628243378623894190821041:ℚ)/739328000000000000000000000)⟩
theorem valid16 : Valid source31 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source31 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3123437499:ℚ)/5000000000),((400493017:ℚ)/625000000),((11226312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((6059573149:ℚ)/10000000000),((-139366808842616560844767859860696691:ℚ)/360600250000000000000000000000000000),((-354074760229804143248321041:ℚ)/739328000000000000000000000)⟩
theorem valid17 : Valid source31 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source31 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3153124999:ℚ)/5000000000),((6467348637:ℚ)/10000000000),((11315374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1184202699:ℚ)/2000000000),((-1748838089608330532992097799384211:ℚ)/4522562500000000000000000000000000),((-352891573126675735732696041:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source31 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3182812499:ℚ)/5000000000),((652680767:ℚ)/1000000000),((11404437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1444884629:ℚ)/2500000000),((-287922628087232956830843184553349881:ℚ)/744200000000000000000000000000000000),((-351715384668181707269571041:ℚ)/739328000000000000000000000)⟩
theorem valid19 : Valid source31 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source31 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3212499999:ℚ)/5000000000),((6645721861:ℚ)/10000000000),((1641928571:ℚ)/1770000000),(1:ℚ),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5634925811:ℚ)/10000000000),((-2001484005149751172711633593313969:ℚ)/5221500000000000000000000000000000),((-348627845455003581058946041:ℚ)/739328000000000000000000000)⟩
theorem valid20 : Valid source31 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3271874999:ℚ)/5000000000),((6764631083:ℚ)/10000000000),((11671624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1067049891:ℚ)/2000000000),((-151817349325804613716852641587330183:ℚ)/395641000000000000000000000000000000),((-346310532227423958275196041:ℚ)/739328000000000000000000000)⟩
theorem valid21 : Valid source31 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source31 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3331249999:ℚ)/5000000000),((3501217747:ℚ)/5000000000),((11849749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1254881639:ℚ)/2500000000),((-105532593531759826305794505969556933:ℚ)/279936000000000000000000000000000000),((-340184916895452766261446041:ℚ)/739328000000000000000000000)⟩
theorem valid22 : Valid source31 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3449999999:ℚ)/5000000000),((7953493103:ℚ)/10000000000),((12205999997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((1081405049:ℚ)/2500000000),((-357028088692780983445594338216146501:ℚ)/1048352000000000000000000000000000000),((-324082283333272317103946041:ℚ)/739328000000000000000000000)⟩
theorem valid23 : Valid source31 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3924999999:ℚ)/5000000000),((8904349493:ℚ)/10000000000),((13630999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-442761367404415029480399013583782741:ℚ)/1280000000000000000000000000000000000),((-462735959:ℚ)/1024000000)⟩
theorem valid24 : Valid source31 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source31 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4399999999:ℚ)/5000000000),((635329749:ℚ)/500000000),((15055999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-20250023224626144992063027:ℚ)/81254400000000000000000000),((-462735959:ℚ)/1024000000)⟩
theorem valid25 : Valid source31 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source31 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source31 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source31 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((2421:ℚ)/3200) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source31 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source31 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source31 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC32
#check @N11Formalization.C450Source31GroupedC32.bound
#print axioms N11Formalization.C450Source31GroupedC32.valid0
#print axioms N11Formalization.C450Source31GroupedC32.valid1
#print axioms N11Formalization.C450Source31GroupedC32.valid2
#print axioms N11Formalization.C450Source31GroupedC32.valid3
#print axioms N11Formalization.C450Source31GroupedC32.valid4
#print axioms N11Formalization.C450Source31GroupedC32.valid5
#print axioms N11Formalization.C450Source31GroupedC32.valid6
#print axioms N11Formalization.C450Source31GroupedC32.valid7
#print axioms N11Formalization.C450Source31GroupedC32.valid8
#print axioms N11Formalization.C450Source31GroupedC32.valid9
#print axioms N11Formalization.C450Source31GroupedC32.valid10
#print axioms N11Formalization.C450Source31GroupedC32.valid11
#print axioms N11Formalization.C450Source31GroupedC32.valid12
#print axioms N11Formalization.C450Source31GroupedC32.valid13
#print axioms N11Formalization.C450Source31GroupedC32.valid14
#print axioms N11Formalization.C450Source31GroupedC32.valid15
#print axioms N11Formalization.C450Source31GroupedC32.valid16
#print axioms N11Formalization.C450Source31GroupedC32.valid17
#print axioms N11Formalization.C450Source31GroupedC32.valid18
#print axioms N11Formalization.C450Source31GroupedC32.valid19
#print axioms N11Formalization.C450Source31GroupedC32.valid20
#print axioms N11Formalization.C450Source31GroupedC32.valid21
#print axioms N11Formalization.C450Source31GroupedC32.valid22
#print axioms N11Formalization.C450Source31GroupedC32.valid23
#print axioms N11Formalization.C450Source31GroupedC32.valid24
#print axioms N11Formalization.C450Source31GroupedC32.valid25
#print axioms N11Formalization.C450Source31GroupedC32.bound
#print axioms N11Formalization.C450Source31GroupedC32.endpoint_checks
