import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2639999999:ℚ)/5000000000),((2802606191:ℚ)/5000000000),((9327999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1003427953:ℚ)/1250000000),((-4139935560158504937597607945845130434732940223188654651:ℚ)/10244315625000000000000000000000000000000000000000000000),((-9009643908477449772870257:ℚ)/29573120000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2758749999:ℚ)/5000000000),((2921485979:ℚ)/5000000000),((9684249997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3791640233:ℚ)/5000000000),((-384370945538350005428899047172668429288800060838763177:ℚ)/951708150000000000000000000000000000000000000000000000),((-8705172259355215105770257:ℚ)/29573120000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2877499999:ℚ)/5000000000),((5961844929:ℚ)/10000000000),((10040499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3558621121:ℚ)/5000000000),((-1702181019996781197597440526341981413701536595959024177:ℚ)/4013642196875000000000000000000000000000000000000000000),((-8577448859166282846670257:ℚ)/29573120000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2936874999:ℚ)/5000000000),((6080713669:ℚ)/10000000000),((1459803571:ℚ)/1580000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((274983047:ℚ)/400000000),((-244735569581325994279690363285599910037227852781173:ℚ)/577780078125000000000000000000000000000000000000000),((-8426963059071857548920257:ℚ)/29573120000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2996249999:ℚ)/5000000000),((153503663:ℚ)/250000000),((10396749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3312257187:ℚ)/5000000000),((-117473122099073505796804507529927253805549897037649793:ℚ)/271105771264648437500000000000000000000000000000000000),((-8364345118644256835570257:ℚ)/29573120000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((3025937499:ℚ)/5000000000),((6199578393:ℚ)/10000000000),((10485812497:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3248218783:ℚ)/5000000000),((-22576010131022375716304549229469770011345513557502911:ℚ)/52142143249511718750000000000000000000000000000000000),((-8289539335155976651645257:ℚ)/29573120000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3055624999:ℚ)/5000000000),((195594041:ℚ)/312500000),((10574874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3183081927:ℚ)/5000000000),((-4935541719213258276250438706288762629086777817434193:ℚ)/11407842879882812500000000000000000000000000000000000),((-8214858795760132738620257:ℚ)/29573120000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3085312499:ℚ)/5000000000),((63184393:ℚ)/100000000),((10663937497:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6233552829:ℚ)/10000000000),((-2022769761033066010876835268559798972977578016004667277:ℚ)/4678731200000000000000000000000000000000000000000000000),((-8140303466646053275695257:ℚ)/29573120000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3114999999:ℚ)/5000000000),((6348153953:ℚ)/10000000000),((10752999997:ℚ)/11487500000),(1:ℚ),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1219689863:ℚ)/2000000000),((-6210800268204055327797385691433621823465364681017629139:ℚ)/14211759503173828125000000000000000000000000000000000000),((-8109554389639593341270257:ℚ)/29573120000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3129843749:ℚ)/5000000000),((3188934191:ℚ)/5000000000),((10797531247:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3014954897:ℚ)/5000000000),((-245534124560193643624996146461512417250674288177609:ℚ)/562061848892211914062500000000000000000000000000000),((-8072385917123056057245257:ℚ)/29573120000000000000000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3144687499:ℚ)/5000000000),((640758259:ℚ)/1000000000),((10842062497:ℚ)/11582500000),(1:ℚ),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((5960681097:ℚ)/10000000000),((-84815722982316532922462499559531561582211689957319557:ℚ)/194230281517578125000000000000000000000000000000000000),((-8035248729904116672945257:ℚ)/29573120000000000000000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3159531249:ℚ)/5000000000),((6437296579:ℚ)/10000000000),((10886593747:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((1178147717:ℚ)/2000000000),((-2145773449210017970604969362877792051547587365834910583:ℚ)/4915742959375000000000000000000000000000000000000000000),((-7998142825042716769170257:ℚ)/29573120000000000000000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3174374999:ℚ)/5000000000),((404188147:ℚ)/625000000),((10931124997:ℚ)/11677500000),(1:ℚ),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((5820056179:ℚ)/10000000000),((-530118826623812411303547794601951079143001090484753:ℚ)/1214897676837444305419921875000000000000000000000000),((-7961068198128768717120257:ℚ)/29573120000000000000000000)⟩
theorem valid12 : Valid source24 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3189218749:ℚ)/5000000000),((6496723913:ℚ)/10000000000),((10975656247:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((5748606241:ℚ)/10000000000),((-941645970417439194616398941660547532633000433509279807:ℚ)/2158796923828125000000000000000000000000000000000000000),((-7924024843282155678395257:ℚ)/29573120000000000000000000)⟩
theorem valid13 : Valid source24 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source24 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source24 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3204062499:ℚ)/5000000000),((3263218631:ℚ)/5000000000),((11020187497:ℚ)/11772500000),(1:ℚ),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((5676359441:ℚ)/10000000000),((-392328735074269669925497146120349013124307457790114383:ℚ)/899763667529296875000000000000000000000000000000000000),((-7887012760502877652995257:ℚ)/29573120000000000000000000)⟩
theorem valid14 : Valid source24 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source24 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3218906249:ℚ)/5000000000),((1639037601:ℚ)/2500000000),((11064718747:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5603284603:ℚ)/10000000000),((-187452873681758753369472126501299804615249591423845229:ℚ)/430052231250000000000000000000000000000000000000000000),((-7850031942440788592920257:ℚ)/29573120000000000000000000)⟩
theorem valid15 : Valid source24 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source24 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3233749999:ℚ)/5000000000),((329293167:ℚ)/500000000),((11109249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((2764674273:ℚ)/5000000000),((-2275889956269611172627232543074449745915190267665593457:ℚ)/5223092808740234375000000000000000000000000000000000000),((-7813082387625859288570257:ℚ)/29573120000000000000000000)⟩
theorem valid16 : Valid source24 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3248593749:ℚ)/5000000000),((6615576073:ℚ)/10000000000),((11153781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((545451589:ℚ)/1000000000),((-6907690959844473313986259034306562589292737841752247449:ℚ)/15858182680078125000000000000000000000000000000000000000),((-7776164091648002111145257:ℚ)/29573120000000000000000000)⟩
theorem valid17 : Valid source24 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source24 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3263437499:ℚ)/5000000000),((3322644303:ℚ)/5000000000),((11198312497:ℚ)/11962500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((2689374427:ℚ)/5000000000),((-447255676549152630605755274144493285832941550691239:ℚ)/1027110343359375000000000000000000000000000000000000),((-7739277050097129431845257:ℚ)/29573120000000000000000000)⟩
theorem valid18 : Valid source24 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source24 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source24 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3278281249:ℚ)/5000000000),((333750047:ℚ)/500000000),((11242843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((5302007017:ℚ)/10000000000),((-1767427513890167034069511576269717908035355523827439541:ℚ)/4060133439843750000000000000000000000000000000000000000),((-7702421261503212041070257:ℚ)/29573120000000000000000000)⟩
theorem valid19 : Valid source24 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source24 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1201:ℚ)/1600),((4823:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3293124999:ℚ)/5000000000),((3352356539:ℚ)/5000000000),((11287374997:ℚ)/12057500000),(1:ℚ),((9444767421:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1673989387:ℚ)/5000000000),((5224247057:ℚ)/10000000000),((-1021673503197981016586585170930293775873713872997575173:ℚ)/2347713234521484375000000000000000000000000000000000000),((-7665596721456162310020257:ℚ)/29573120000000000000000000)⟩
theorem valid20 : Valid source24 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source24 nn0 nn1 Qcell ((1201:ℚ)/1600) ((4823:ℚ)/6400) :=
  cell_of_packet source24 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4823:ℚ)/6400),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3307968749:ℚ)/5000000000),((6734425023:ℚ)/10000000000),((11331906247:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((4722383713:ℚ)/5000000000),((674104879:ℚ)/2000000000),((1286355611:ℚ)/2500000000),((-1808596646800222173750300597385348555061942458647285841:ℚ)/4157245447558593750000000000000000000000000000000000000),((-7628803425545892609895257:ℚ)/29573120000000000000000000)⟩
theorem valid21 : Valid source24 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source24 nn0 nn1 Qcell ((4823:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3322812499:ℚ)/5000000000),((6793848341:ℚ)/10000000000),((11376437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2532741551:ℚ)/5000000000),((-7325458413748138082430140003924780155916690378528862271:ℚ)/17023575000000000000000000000000000000000000000000000000),((-7548364503889444707095257:ℚ)/29573120000000000000000000)⟩
theorem valid22 : Valid source24 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source24 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3352499999:ℚ)/5000000000),((6853270911:ℚ)/10000000000),((11465499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((2451019903:ℚ)/5000000000),((-156134799701885828532200049254244453364173307090645313:ℚ)/363007533666992187500000000000000000000000000000000000),((-7474934654613174869470257:ℚ)/29573120000000000000000000)⟩
theorem valid23 : Valid source24 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source24 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3382187499:ℚ)/5000000000),((6912692751:ℚ)/10000000000),((11554562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((4733429309:ℚ)/10000000000),((-365057431130698109983509161145439228296734871497909059:ℚ)/849113803125000000000000000000000000000000000000000000),((-7401629720142798352345257:ℚ)/29573120000000000000000000)⟩
theorem valid24 : Valid source24 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source24 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3411874999:ℚ)/5000000000),((1406306861:ℚ)/2000000000),((11643624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((142471097:ℚ)/312500000),((-1964473823286854999247869241951986239422085551116784379:ℚ)/4666091043750000000000000000000000000000000000000000000),((-7241099912150914093320257:ℚ)/29573120000000000000000000)⟩
theorem valid25 : Valid source24 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3471249999:ℚ)/5000000000),((908651169:ℚ)/1250000000),((11821749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2095115549:ℚ)/5000000000),((-916973351258860677327961355906395296519805231869432379:ℚ)/2267481600000000000000000000000000000000000000000000000),((-6920423671126315098370257:ℚ)/29573120000000000000000000)⟩
theorem valid26 : Valid source24 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source24 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3589999999:ℚ)/5000000000),((968066291:ℚ)/1250000000),((12177999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((3340053833:ℚ)/10000000000),((-16903274342982129659916725113313653545541117260039:ℚ)/45037507812500000000000000000000000000000000000000),((-6493063897435554740070257:ℚ)/29573120000000000000000000)⟩
theorem valid27 : Valid source24 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3827499999:ℚ)/5000000000),((8219817579:ℚ)/10000000000),((12890499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-3586358350584395741539738836725962336373289036428377337:ℚ)/9487585600000000000000000000000000000000000000000000000),((-228604423:ℚ)/1024000000)⟩
theorem valid28 : Valid source24 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source24 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4064999999:ℚ)/5000000000),((9170310153:ℚ)/10000000000),((13602999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-1068162067982445169341148224899597674377754778474763057:ℚ)/3200000000000000000000000000000000000000000000000000000),((-228604423:ℚ)/1024000000)⟩
theorem valid29 : Valid source24 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4539999999:ℚ)/5000000000),((12971601939:ℚ)/10000000000),((15027999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-219907282932753386011638809731289171:ℚ)/1345572864000000000000000000000000000),((-228604423:ℚ)/1024000000)⟩
theorem valid30 : Valid source24 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet30 valid30
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source24 nn0 nn1 Qcell ((919:ℚ)/1280) ((4633:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source24 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source24 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4671:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source24 nn0 nn1 Qcell ((4671:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source24 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source24 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4709:ℚ)/6400) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((4709:ℚ)/6400) :=
  cell_join node0_7 node7_15
private theorem node15_17 :
    CellBound source24 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf15 leaf16
private theorem node17_19 :
    CellBound source24 nn0 nn1 Qcell ((4747:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join leaf17 leaf18
private theorem node15_19 :
    CellBound source24 nn0 nn1 Qcell ((4709:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join node15_17 node17_19
private theorem node19_21 :
    CellBound source24 nn0 nn1 Qcell ((957:ℚ)/1280) ((4823:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node21_23 :
    CellBound source24 nn0 nn1 Qcell ((4823:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join leaf21 leaf22
private theorem node19_23 :
    CellBound source24 nn0 nn1 Qcell ((957:ℚ)/1280) ((61:ℚ)/80) :=
  cell_join node19_21 node21_23
private theorem node15_23 :
    CellBound source24 nn0 nn1 Qcell ((4709:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node15_19 node19_23
private theorem node23_25 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source24 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join node23_25 node25_27
private theorem node27_29 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf27 leaf28
private theorem node29_31 :
    CellBound source24 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf29 leaf30
private theorem node27_31 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node27_29 node29_31
private theorem node23_31 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node23_27 node27_31
private theorem node15_31 :
    CellBound source24 nn0 nn1 Qcell ((4709:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node15_23 node23_31
private theorem node0_31 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_31
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_31
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30]
theorem packet_count : packets.length = 31 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC32
#check @N11Formalization.C450Source24GroupedC32.bound
#print axioms N11Formalization.C450Source24GroupedC32.valid0
#print axioms N11Formalization.C450Source24GroupedC32.valid1
#print axioms N11Formalization.C450Source24GroupedC32.valid2
#print axioms N11Formalization.C450Source24GroupedC32.valid3
#print axioms N11Formalization.C450Source24GroupedC32.valid4
#print axioms N11Formalization.C450Source24GroupedC32.valid5
#print axioms N11Formalization.C450Source24GroupedC32.valid6
#print axioms N11Formalization.C450Source24GroupedC32.valid7
#print axioms N11Formalization.C450Source24GroupedC32.valid8
#print axioms N11Formalization.C450Source24GroupedC32.valid9
#print axioms N11Formalization.C450Source24GroupedC32.valid10
#print axioms N11Formalization.C450Source24GroupedC32.valid11
#print axioms N11Formalization.C450Source24GroupedC32.valid12
#print axioms N11Formalization.C450Source24GroupedC32.valid13
#print axioms N11Formalization.C450Source24GroupedC32.valid14
#print axioms N11Formalization.C450Source24GroupedC32.valid15
#print axioms N11Formalization.C450Source24GroupedC32.valid16
#print axioms N11Formalization.C450Source24GroupedC32.valid17
#print axioms N11Formalization.C450Source24GroupedC32.valid18
#print axioms N11Formalization.C450Source24GroupedC32.valid19
#print axioms N11Formalization.C450Source24GroupedC32.valid20
#print axioms N11Formalization.C450Source24GroupedC32.valid21
#print axioms N11Formalization.C450Source24GroupedC32.valid22
#print axioms N11Formalization.C450Source24GroupedC32.valid23
#print axioms N11Formalization.C450Source24GroupedC32.valid24
#print axioms N11Formalization.C450Source24GroupedC32.valid25
#print axioms N11Formalization.C450Source24GroupedC32.valid26
#print axioms N11Formalization.C450Source24GroupedC32.valid27
#print axioms N11Formalization.C450Source24GroupedC32.valid28
#print axioms N11Formalization.C450Source24GroupedC32.valid29
#print axioms N11Formalization.C450Source24GroupedC32.valid30
#print axioms N11Formalization.C450Source24GroupedC32.bound
#print axioms N11Formalization.C450Source24GroupedC32.endpoint_checks
