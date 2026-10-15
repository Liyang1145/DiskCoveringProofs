import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6832982727:ℚ)/10000000000),((3519375001:ℚ)/5000000000),(-1:ℚ),((-6064982727:ℚ)/6740000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((566425569:ℚ)/1250000000),((4225062757254129699196642126272959:ℚ)/45427600000000000000000000000000000),((1373533549330828575418837:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6951817681:ℚ)/10000000000),((3549062501:ℚ)/5000000000),(-1:ℚ),((-18551453043:ℚ)/20410000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1039998889:ℚ)/2500000000),((5570571290292188170228891852223:ℚ)/61622500000000000000000000000000),((1377052207291732178543837:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7011233971:ℚ)/10000000000),((3563906251:ℚ)/5000000000),(-1:ℚ),((-6243233971:ℚ)/6835000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((495260833:ℚ)/1250000000),((6245159824604246681714881561509701:ℚ)/70075837500000000000000000000000000),((1378812970885831441043837:ℚ)/1805000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((7040941829:ℚ)/10000000000),((3578750001:ℚ)/5000000000),(-1:ℚ),((-18818825487:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((1929770177:ℚ)/5000000000),((37786564541610882428491575947651387:ℚ)/424360000000000000000000000000000000),((4141724072667087032506511:ℚ)/5415000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3535324749:ℚ)/5000000000),((3593593751:ℚ)/5000000000),(-1:ℚ),((-9453974247:ℚ)/10347500000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((469292343:ℚ)/1250000000),((952594384578367046058085874611753:ℚ)/10707075625000000000000000000000000),((1382337367301324887918837:ℚ)/1805000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7100356983:ℚ)/10000000000),((1800507813:ℚ)/2500000000),(-1:ℚ),((-18997070949:ℚ)/20742500000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((911562877:ℚ)/2500000000),((38010945626962328986501442568922331:ℚ)/430251306250000000000000000000000000),((1037414298120663518771159:ℚ)/1353750000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((222350333:ℚ)/312500000),((3608437501:ℚ)/5000000000),(-1:ℚ),((-198350333:ℚ)/216562500),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((3591044477:ℚ)/10000000000),((175311984352112279467813817243:ℚ)/1985156250000000000000000000000),((1384101000122719072293837:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((1782516071:ℚ)/2500000000),((225991211:ℚ)/312500000),(-1:ℚ),((-4771548213:ℚ)/5209375000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((883753367:ℚ)/2500000000),((19165055055565738372928127530315679:ℚ)/217100703125000000000000000000000000),((5410090528073546991077:ℚ)/7050781250000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7144917867:ℚ)/10000000000),((3623281251:ℚ)/5000000000),(-1:ℚ),((-19130753601:ℚ)/20885000000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1739059299:ℚ)/5000000000),((19245146379175187936597428234895143:ℚ)/218091612500000000000000000000000000),((4157596768059634691881511:ℚ)/5415000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4177:ℚ)/6400),((16727:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((1431954281:ℚ)/2000000000),((7253984377:ℚ)/10000000000),(-1:ℚ),((-3835062843:ℚ)/4181750000),((1962859787:ℚ)/2000000000),((9818033467:ℚ)/10000000000),((482543621:ℚ)/2500000000),((1710158347:ℚ)/5000000000),((615104130690852098549820053453481:ℚ)/6994813225000000000000000000000000),((5545227544399025189565973:ℚ)/7220000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((4177:ℚ)/6400) ((16727:ℚ)/25600) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((16727:ℚ)/25600),((8373:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3583599079:ℚ)/5000000000),((1815351563:ℚ)/2500000000),(-1:ℚ),((-3199599079:ℚ)/3488750000),((4905290651:ℚ)/5000000000),((490714947:ℚ)/500000000),((194946007:ℚ)/1000000000),((678212223:ℚ)/2000000000),((1605178843006677194769808982780069:ℚ)/18257064843750000000000000000000000),((346687060655467418757053:ℚ)/451250000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((16727:ℚ)/25600) ((8373:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8373:ℚ)/12800),((3353:ℚ)/5120),(-1:ℚ),((-15:ℚ)/16),((7174624899:ℚ)/10000000000),((7268828127:ℚ)/10000000000),(-1:ℚ),((-19219874697:ℚ)/20956250000),((2451720127:ℚ)/2500000000),((9810581307:ℚ)/10000000000),((123029563:ℚ)/625000000),((3361560899:ℚ)/10000000000),((231628057484244413956815067296282821:ℚ)/2634986484375000000000000000000000000),((16646275907034620362447919:ℚ)/21660000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((8373:ℚ)/12800) ((3353:ℚ)/5120) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((3353:ℚ)/5120),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7182051629:ℚ)/10000000000),((3638125001:ℚ)/5000000000),(-1:ℚ),((-19242154887:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((9806880513:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((666361907:ℚ)/2000000000),((58027740310937686427509430740015637:ℚ)/660240600000000000000000000000000000),((1387631134992802362918837:ℚ)/1805000000000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((3353:ℚ)/5120) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1049:ℚ)/1600),((16803:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7189478349:ℚ)/10000000000),((7283671877:ℚ)/10000000000),(-1:ℚ),((-2140492783:ℚ)/2333750000),((2449882301:ℚ)/2500000000),((9803196499:ℚ)/10000000000),((250714111:ℚ)/1250000000),((103181257:ℚ)/312500000),((957178866320334525339152793389511:ℚ)/10892778125000000000000000000000000),((5552290683366486692690973:ℚ)/7220000000000000000000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((16803:ℚ)/25600) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((16803:ℚ)/25600),((8411:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7196905057:ℚ)/10000000000),((911386719:ℚ)/1250000000),(-1:ℚ),((-19286715171:ℚ)/21027500000),((9795878581:ℚ)/10000000000),((9799529209:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((654305173:ℚ)/2000000000),((38846427915398746078346142482055163:ℚ)/442155756250000000000000000000000000),((260346424962376805181071:ℚ)/338437500000000000000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((16803:ℚ)/25600) ((8411:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8411:ℚ)/12800),((16841:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((3602165877:ℚ)/5000000000),((7298515627:ℚ)/10000000000),(-1:ℚ),((-9654497631:ℚ)/10525625000),((9792244569:ℚ)/10000000000),((4897939293:ℚ)/5000000000),((2041954043:ℚ)/10000000000),((162048951:ℚ)/500000000),((58390817513466637877392370487842987:ℚ)/664732689843750000000000000000000000),((5555823687463864905190973:ℚ)/7220000000000000000000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell ((8411:ℚ)/12800) ((16841:ℚ)/25600) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((16841:ℚ)/25600),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7211758441:ℚ)/10000000000),((3652968751:ℚ)/5000000000),(-1:ℚ),((-6443758441:ℚ)/7025000000),((978862711:ℚ)/1000000000),((4896122287:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3210151897:ℚ)/10000000000),((433423281710004516332204898334823:ℚ)/4935062500000000000000000000000000),((1389397637041491469168837:ℚ)/1805000000000000000000000)⟩
theorem valid16 : Valid source19 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source19 nn0 nn1 Qcell ((16841:ℚ)/25600) ((843:ℚ)/1280) :=
  cell_of_packet source19 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((843:ℚ)/1280),((16879:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((1804796279:ℚ)/2500000000),((7313359377:ℚ)/10000000000),(-1:ℚ),((-4838388837:ℚ)/5274687500),((9785026151:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((2077250707:ℚ)/10000000000),((1589518171:ℚ)/5000000000),((234534473800131127996450365289218197:ℚ)/2670943509375000000000000000000000000),((16678072943911024274947919:ℚ)/21660000000000000000000000)⟩
theorem valid17 : Valid source19 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source19 nn0 nn1 Qcell ((843:ℚ)/1280) ((16879:ℚ)/25600) :=
  cell_of_packet source19 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((16879:ℚ)/25600),((8449:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7226611781:ℚ)/10000000000),((1830195313:ℚ)/2500000000),(-1:ℚ),((-19375835343:ℚ)/21122500000),((4890720817:ℚ)/5000000000),((2446256539:ℚ)/2500000000),((83782417:ℚ)/400000000),((1573811893:ℚ)/5000000000),((19585081247536848985650471417123249:ℚ)/223080003125000000000000000000000000),((347570311679811971882053:ℚ)/451250000000000000000000)⟩
theorem valid18 : Valid source19 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source19 nn0 nn1 Qcell ((16879:ℚ)/25600) ((8449:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1446807687:ℚ)/2000000000),((3667812501:ℚ)/5000000000),(-1:ℚ),((-3879623061:ℚ)/4234000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((77897631:ℚ)/250000000),((1578391700509171390213877057761237:ℚ)/17926756000000000000000000000000000),((4173495286497836648131511:ℚ)/5415000000000000000000000)⟩
theorem valid19 : Valid source19 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source19 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7248891711:ℚ)/10000000000),((459404297:ℚ)/625000000),(-1:ℚ),((-2160297237:ℚ)/2357500000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3051511883:ℚ)/10000000000),((1467510230037161796339220736040103:ℚ)/16673418750000000000000000000000000),((21750768490337257104933:ℚ)/28203125000000000000000)⟩
theorem valid20 : Valid source19 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((453984059:ℚ)/625000000),((3682656251:ℚ)/5000000000),(-1:ℚ),((-1217952177:ℚ)/1329062500),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1492887267:ℚ)/5000000000),((1243317498857390254447370350293471:ℚ)/14131257031250000000000000000000000),((1392933510366164603543837:ℚ)/1805000000000000000000000)⟩
theorem valid21 : Valid source19 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source19 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),(-1:ℚ),((-15:ℚ)/16),((1455719627:ℚ)/2000000000),((1845039063:ℚ)/2500000000),(-1:ℚ),((-3906358881:ℚ)/4262500000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((2918602303:ℚ)/10000000000),((31959954994979609347399114157161:ℚ)/363378125000000000000000000000000),((1045363557339764496896159:ℚ)/1353750000000000000000000)⟩
theorem valid22 : Valid source19 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source19 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((1823362821:ℚ)/2500000000),((3697500001:ℚ)/5000000000),(-1:ℚ),((-1631362821:ℚ)/1780000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((569978731:ℚ)/2000000000),((139285165047005864053918487286213:ℚ)/1584200000000000000000000000000000),((1394702881642148631668837:ℚ)/1805000000000000000000000)⟩
theorem valid23 : Valid source19 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source19 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7308304391:ℚ)/10000000000),((3712343751:ℚ)/5000000000),(-1:ℚ),((-19620913173:ℚ)/21455000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((138976729:ℚ)/500000000),((7631103306382547422912245958474063:ℚ)/86309442187500000000000000000000000),((4189419627981692901256511:ℚ)/5415000000000000000000000)⟩
theorem valid24 : Valid source19 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((91725131:ℚ)/125000000),((3727187501:ℚ)/5000000000),(-1:ℚ),((-246375393:ℚ)/269375000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((526666521:ℚ)/2000000000),((153865740323301210383006443526213:ℚ)/1741509375000000000000000000000000),((1398244493421411609793837:ℚ)/1805000000000000000000000)⟩
theorem valid25 : Valid source19 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1473543281:ℚ)/2000000000),((3756875001:ℚ)/5000000000),(-1:ℚ),((-3959829843:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1239366809:ℚ)/5000000000),((1688480396913127936477790344549623:ℚ)/18905104000000000000000000000000000),((4205369792511203451256511:ℚ)/5415000000000000000000000)⟩
theorem valid26 : Valid source19 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((1856781943:ℚ)/2500000000),((3816250001:ℚ)/5000000000),(-1:ℚ),((-4994345829:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1068482697:ℚ)/5000000000),((149336296547903237915054518797551:ℚ)/1638262500000000000000000000000000),((48717:ℚ)/62500)⟩
theorem valid27 : Valid source19 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7545948629:ℚ)/10000000000),((3935000001:ℚ)/5000000000),(-1:ℚ),((-20333845887:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((298338497:ℚ)/2500000000),((49493069686823730757753641944569917:ℚ)/523494400000000000000000000000000000),((48717:ℚ)/62500)⟩
theorem valid28 : Valid source19 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((3891791639:ℚ)/5000000000),((4410000001:ℚ)/5000000000),(-1:ℚ),((-3507791639:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((693179388531785710576907299811309:ℚ)/6220800000000000000000000000000000),((48717:ℚ)/62500)⟩
theorem valid29 : Valid source19 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((1746808571:ℚ)/2000000000),((5360000001:ℚ)/5000000000),(-1:ℚ),((-4779625713:ℚ)/6400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((15091556368953108070390914897061831:ℚ)/122880000000000000000000000000000000),((48717:ℚ)/62500)⟩
theorem valid30 : Valid source19 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((5317349959:ℚ)/5000000000),((14520000003:ℚ)/10000000000),(-1:ℚ),((-4933349959:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((768656800490227527959393:ℚ)/5416960000000000000000000),((48717:ℚ)/62500)⟩
theorem valid31 : Valid source19 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet31 valid31
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source19 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((8297:ℚ)/12800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((8297:ℚ)/12800) ((1667:ℚ)/2560) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1667:ℚ)/2560) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1667:ℚ)/2560) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source19 nn0 nn1 Qcell ((1667:ℚ)/2560) ((16727:ℚ)/25600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((16727:ℚ)/25600) ((3353:ℚ)/5120) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source19 nn0 nn1 Qcell ((1667:ℚ)/2560) ((3353:ℚ)/5120) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source19 nn0 nn1 Qcell ((3353:ℚ)/5120) ((16803:ℚ)/25600) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source19 nn0 nn1 Qcell ((16803:ℚ)/25600) ((16841:ℚ)/25600) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source19 nn0 nn1 Qcell ((3353:ℚ)/5120) ((16841:ℚ)/25600) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source19 nn0 nn1 Qcell ((1667:ℚ)/2560) ((16841:ℚ)/25600) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((16841:ℚ)/25600) :=
  cell_join node0_8 node8_16
private theorem node16_18 :
    CellBound source19 nn0 nn1 Qcell ((16841:ℚ)/25600) ((16879:ℚ)/25600) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source19 nn0 nn1 Qcell ((16879:ℚ)/25600) ((2117:ℚ)/3200) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source19 nn0 nn1 Qcell ((16841:ℚ)/25600) ((2117:ℚ)/3200) :=
  cell_join node16_18 node18_20
private theorem node20_22 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf20 leaf21
private theorem node22_24 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf22 leaf23
private theorem node20_24 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join node20_22 node22_24
private theorem node16_24 :
    CellBound source19 nn0 nn1 Qcell ((16841:ℚ)/25600) ((267:ℚ)/400) :=
  cell_join node16_20 node20_24
private theorem node24_26 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node24_26 node26_28
private theorem node28_30 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf28 leaf29
private theorem node30_32 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf30 leaf31
private theorem node28_32 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node28_30 node30_32
private theorem node24_32 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node24_28 node28_32
private theorem node16_32 :
    CellBound source19 nn0 nn1 Qcell ((16841:ℚ)/25600) ((69:ℚ)/50) :=
  cell_join node16_24 node24_32
private theorem node0_32 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_16 node16_32
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_32
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31]
theorem packet_count : packets.length = 32 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC01
#check @N11Formalization.C450Source19GroupedC01.bound
#print axioms N11Formalization.C450Source19GroupedC01.valid0
#print axioms N11Formalization.C450Source19GroupedC01.valid1
#print axioms N11Formalization.C450Source19GroupedC01.valid2
#print axioms N11Formalization.C450Source19GroupedC01.valid3
#print axioms N11Formalization.C450Source19GroupedC01.valid4
#print axioms N11Formalization.C450Source19GroupedC01.valid5
#print axioms N11Formalization.C450Source19GroupedC01.valid6
#print axioms N11Formalization.C450Source19GroupedC01.valid7
#print axioms N11Formalization.C450Source19GroupedC01.valid8
#print axioms N11Formalization.C450Source19GroupedC01.valid9
#print axioms N11Formalization.C450Source19GroupedC01.valid10
#print axioms N11Formalization.C450Source19GroupedC01.valid11
#print axioms N11Formalization.C450Source19GroupedC01.valid12
#print axioms N11Formalization.C450Source19GroupedC01.valid13
#print axioms N11Formalization.C450Source19GroupedC01.valid14
#print axioms N11Formalization.C450Source19GroupedC01.valid15
#print axioms N11Formalization.C450Source19GroupedC01.valid16
#print axioms N11Formalization.C450Source19GroupedC01.valid17
#print axioms N11Formalization.C450Source19GroupedC01.valid18
#print axioms N11Formalization.C450Source19GroupedC01.valid19
#print axioms N11Formalization.C450Source19GroupedC01.valid20
#print axioms N11Formalization.C450Source19GroupedC01.valid21
#print axioms N11Formalization.C450Source19GroupedC01.valid22
#print axioms N11Formalization.C450Source19GroupedC01.valid23
#print axioms N11Formalization.C450Source19GroupedC01.valid24
#print axioms N11Formalization.C450Source19GroupedC01.valid25
#print axioms N11Formalization.C450Source19GroupedC01.valid26
#print axioms N11Formalization.C450Source19GroupedC01.valid27
#print axioms N11Formalization.C450Source19GroupedC01.valid28
#print axioms N11Formalization.C450Source19GroupedC01.valid29
#print axioms N11Formalization.C450Source19GroupedC01.valid30
#print axioms N11Formalization.C450Source19GroupedC01.valid31
#print axioms N11Formalization.C450Source19GroupedC01.bound
#print axioms N11Formalization.C450Source19GroupedC01.endpoint_checks
