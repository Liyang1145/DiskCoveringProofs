import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2459999999:ℚ)/5000000000),((657565259:ℚ)/1250000000),((9363999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8666696879:ℚ)/10000000000),((-880548321645331:ℚ)/2575000000000000),((-407751085324911437484181661:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2578749999:ℚ)/5000000000),((85914661:ℚ)/156250000),((9720249997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((8249163331:ℚ)/10000000000),((-900584098828664513864831:ℚ)/2607421875000000000000000),((-402853910706732703096681661:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2697499999:ℚ)/5000000000),((5617532843:ℚ)/10000000000),((10076499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7814849489:ℚ)/10000000000),((-2901452015215205904348261877:ℚ)/8152500000000000000000000000),((-401774733073679051309181661:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((5513749997:ℚ)/10000000000),((2868259477:ℚ)/5000000000),((20509249991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((759045261:ℚ)/1000000000),((-13224026491781781804427741:ℚ)/37031250000000000000000000),((-1597720094992529921305134949:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2816249999:ℚ)/5000000000),((1159201797:ℚ)/2000000000),((10432749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7360616291:ℚ)/10000000000),((-2018812246980310927665612823:ℚ)/5577500000000000000000000000),((-398964369910865054921681661:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2845937499:ℚ)/5000000000),((1463874267:ℚ)/2500000000),((10521812497:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3621745331:ℚ)/5000000000),((-8155165744918074279884593:ℚ)/22500000000000000000000000),((-397817968315222713981056661:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2875624999:ℚ)/5000000000),((1478745813:ℚ)/2500000000),((10610874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1781198383:ℚ)/2500000000),((-2058704201415136312676739117:ℚ)/5672500000000000000000000000),((-396678996748574333902931661:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((2905312499:ℚ)/5000000000),((5974467583:ℚ)/10000000000),((10699937497:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((7004442461:ℚ)/10000000000),((-5196377773562342933793919:ℚ)/14300000000000000000000000),((-395547453780904887487306661:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((2934999999:ℚ)/5000000000),((6004209069:ℚ)/10000000000),((10788999997:ℚ)/11487500000),(1:ℚ),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((172058703:ℚ)/250000000),((-630059041380111443700429709:ℚ)/1723125000000000000000000000),((-395347906053167309134181661:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2949843749:ℚ)/5000000000),((6033950109:ℚ)/10000000000),((10833531247:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((341030861:ℚ)/500000000),((-527514584998635120537142531:ℚ)/1441875000000000000000000000),((-394788619178032596081056661:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2964687499:ℚ)/5000000000),((6063690709:ℚ)/10000000000),((10878062497:ℚ)/11582500000),(1:ℚ),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((135168269:ℚ)/200000000),((-169592307386284879871940401:ℚ)/463300000000000000000000000),((-394231188729863282043556661:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2979531249:ℚ)/5000000000),((3046715437:ℚ)/5000000000),((10922593747:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((669572331:ℚ)/1000000000),((-2662166712723789452427211:ℚ)/7268750000000000000000000),((-393675614553222951021681661:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2994374999:ℚ)/5000000000),((6123170609:ℚ)/10000000000),((10967124997:ℚ)/11677500000),(1:ℚ),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((6632532687:ℚ)/10000000000),((-1069773490247508175723699463:ℚ)/2919375000000000000000000000),((-393121896492675187015431661:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3009218749:ℚ)/5000000000),((38455687:ℚ)/62500000),((11011656247:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((1642206703:ℚ)/2500000000),((-184229548190728842157331257:ℚ)/502500000000000000000000000),((-392570034361696290824806661:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3024062499:ℚ)/5000000000),((1545662203:ℚ)/2500000000),((11056187497:ℚ)/11772500000),(1:ℚ),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((6504590223:ℚ)/10000000000),((-1079563334791675626401563877:ℚ)/2943125000000000000000000000),((-392020028004849846449806661:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3038906249:ℚ)/5000000000),((621238729:ℚ)/1000000000),((11100718747:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((6439806711:ℚ)/10000000000),((-135555803449433577246280927:ℚ)/369375000000000000000000000),((-391471877266699437890431661:ℚ)/739328000000000000000000000)⟩
theorem valid15 : Valid source33 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3053749999:ℚ)/5000000000),((3121062679:ℚ)/5000000000),((11145249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((6374459273:ℚ)/10000000000),((-13071860022264244190423212897:ℚ)/35602500000000000000000000000),((-390925582022895932346681661:ℚ)/739328000000000000000000000)⟩
theorem valid16 : Valid source33 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3068593749:ℚ)/5000000000),((6271863023:ℚ)/10000000000),((11189781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((788566257:ℚ)/1250000000),((-547094541340903362072739911:ℚ)/1489375000000000000000000000),((-390381142055828347418556661:ℚ)/739328000000000000000000000)⟩
theorem valid17 : Valid source33 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source33 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3083437499:ℚ)/5000000000),((196925009:ℚ)/312500000),((11234312497:ℚ)/11962500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((6242000293:ℚ)/10000000000),((-54952434714498302286505549:ℚ)/149531250000000000000000000),((-389838557272234833506056661:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source33 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source33 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3098281249:ℚ)/5000000000),((3165668579:ℚ)/5000000000),((11278843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((6174850241:ℚ)/10000000000),((-11039005271297744908242497:ℚ)/30025000000000000000000000),((-389297827516678974609181661:ℚ)/739328000000000000000000000)⟩
theorem valid19 : Valid source33 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source33 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3113124999:ℚ)/5000000000),((6390809733:ℚ)/10000000000),((11323374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((6107059103:ℚ)/10000000000),((-2215677540705037354319885317:ℚ)/6052500000000000000000000000),((-387834538227197250727931661:ℚ)/739328000000000000000000000)⟩
theorem valid20 : Valid source33 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3142812499:ℚ)/5000000000),((1290056157:ℚ)/2000000000),((11412437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5969464639:ℚ)/10000000000),((-55875372463611780341175197:ℚ)/152500000000000000000000000),((-386762376021506729612306661:ℚ)/739328000000000000000000000)⟩
theorem valid21 : Valid source33 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source33 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3172499999:ℚ)/5000000000),((130195007:ℚ)/200000000),((11501499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((5829026247:ℚ)/10000000000),((-563572594757902163790911203:ℚ)/1536875000000000000000000000),((-385697631036849490959181661:ℚ)/739328000000000000000000000)⟩
theorem valid22 : Valid source33 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3202187499:ℚ)/5000000000),((328460923:ℚ)/500000000),((11590562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((5685530379:ℚ)/10000000000),((-162393165496678587153974489:ℚ)/442500000000000000000000000),((-384640302278432472368556661:ℚ)/739328000000000000000000000)⟩
theorem valid23 : Valid source33 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source33 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3231874999:ℚ)/5000000000),((6688150453:ℚ)/10000000000),((11679624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1384684139:ℚ)/2500000000),((-558859564333687527591747:ℚ)/1535644531250000000000000),((-381741773943265952240431661:ℚ)/739328000000000000000000000)⟩
theorem valid24 : Valid source33 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source33 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3291249999:ℚ)/5000000000),((1385199679:ℚ)/2000000000),((11857749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((5234127119:ℚ)/10000000000),((-72504557808282062970362993:ℚ)/202500000000000000000000000),((-375967329020034064971681661:ℚ)/739328000000000000000000000)⟩
theorem valid25 : Valid source33 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3409999999:ℚ)/5000000000),((3700818171:ℚ)/5000000000),((12213999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((228513469:ℚ)/500000000),((-7974672106433985084140851:ℚ)/22968750000000000000000000),((-364508692208415017584181661:ℚ)/739328000000000000000000000)⟩
theorem valid26 : Valid source33 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3647499999:ℚ)/5000000000),((3938603601:ℚ)/5000000000),((12926499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((2842636573:ℚ)/10000000000),((-6325861748814707006319597:ℚ)/18100000000000000000000000),((-365351222214126033009181661:ℚ)/739328000000000000000000000)⟩
theorem valid27 : Valid source33 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source33 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3884999999:ℚ)/5000000000),((8828185977:ℚ)/10000000000),((13638999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-206510293698353016080713:ℚ)/625000000000000000000000),((-102520919:ℚ)/204800000)⟩
theorem valid28 : Valid source33 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source33 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4359999999:ℚ)/5000000000),((6315376101:ℚ)/5000000000),((15063999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1295383111645331:ℚ)/5520000000000000),((-102520919:ℚ)/204800000)⟩
theorem valid29 : Valid source33 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet29 valid29
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((919:ℚ)/1280) ((4633:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source33 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4671:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source33 nn0 nn1 Qcell ((4671:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source33 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4709:ℚ)/6400) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((4709:ℚ)/6400) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node15_18 node18_22
private theorem node22_24 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source33 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join node22_24 node24_26
private theorem node26_28 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf26 leaf27
private theorem node28_30 :
    CellBound source33 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf28 leaf29
private theorem node26_30 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node26_28 node28_30
private theorem node22_30 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node22_26 node26_30
private theorem node15_30 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC32
#check @N11Formalization.C450Source33GroupedC32.bound
#print axioms N11Formalization.C450Source33GroupedC32.valid0
#print axioms N11Formalization.C450Source33GroupedC32.valid1
#print axioms N11Formalization.C450Source33GroupedC32.valid2
#print axioms N11Formalization.C450Source33GroupedC32.valid3
#print axioms N11Formalization.C450Source33GroupedC32.valid4
#print axioms N11Formalization.C450Source33GroupedC32.valid5
#print axioms N11Formalization.C450Source33GroupedC32.valid6
#print axioms N11Formalization.C450Source33GroupedC32.valid7
#print axioms N11Formalization.C450Source33GroupedC32.valid8
#print axioms N11Formalization.C450Source33GroupedC32.valid9
#print axioms N11Formalization.C450Source33GroupedC32.valid10
#print axioms N11Formalization.C450Source33GroupedC32.valid11
#print axioms N11Formalization.C450Source33GroupedC32.valid12
#print axioms N11Formalization.C450Source33GroupedC32.valid13
#print axioms N11Formalization.C450Source33GroupedC32.valid14
#print axioms N11Formalization.C450Source33GroupedC32.valid15
#print axioms N11Formalization.C450Source33GroupedC32.valid16
#print axioms N11Formalization.C450Source33GroupedC32.valid17
#print axioms N11Formalization.C450Source33GroupedC32.valid18
#print axioms N11Formalization.C450Source33GroupedC32.valid19
#print axioms N11Formalization.C450Source33GroupedC32.valid20
#print axioms N11Formalization.C450Source33GroupedC32.valid21
#print axioms N11Formalization.C450Source33GroupedC32.valid22
#print axioms N11Formalization.C450Source33GroupedC32.valid23
#print axioms N11Formalization.C450Source33GroupedC32.valid24
#print axioms N11Formalization.C450Source33GroupedC32.valid25
#print axioms N11Formalization.C450Source33GroupedC32.valid26
#print axioms N11Formalization.C450Source33GroupedC32.valid27
#print axioms N11Formalization.C450Source33GroupedC32.valid28
#print axioms N11Formalization.C450Source33GroupedC32.valid29
#print axioms N11Formalization.C450Source33GroupedC32.bound
#print axioms N11Formalization.C450Source33GroupedC32.endpoint_checks
