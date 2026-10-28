import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1726714201:ℚ)/2500000000),((3529687501:ℚ)/5000000000),(-1:ℚ),((-4540142603:ℚ)/5007500000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((172161899:ℚ)/400000000),((655654375456571770318101187244769:ℚ)/5015011250000000000000000000000000),((3176951684952605394799613:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3483142691:ℚ)/5000000000),((3559375001:ℚ)/5000000000),(-1:ℚ),((-9169428073:ℚ)/10110000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((4112633761:ℚ)/10000000000),((22226418477644822920067795448140383:ℚ)/170353500000000000000000000000000000),((3186592666545687885424613:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((878214119:ℚ)/1250000000),((3574218751:ℚ)/5000000000),(-1:ℚ),((-2314642357:ℚ)/2539375000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3056583:ℚ)/7812500),((1036743881367600533861071048917109:ℚ)/8060531738281250000000000000000000),((3191418409953923466674613:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((110241037:ℚ)/156250000),((3589062501:ℚ)/5000000000),(-1:ℚ),((-290723111:ℚ)/318906250),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((3808592627:ℚ)/10000000000),((9898547671361764955546859494813:ℚ)/77028125000000000000000000000000),((9588742965309865815648839:ℚ)/10830000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3542569771:ℚ)/5000000000),((3603906251:ℚ)/5000000000),(-1:ℚ),((-9347709313:ℚ)/10252500000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((1850997251:ℚ)/5000000000),((5623303184940633735673731581892943:ℚ)/43797398437500000000000000000000000),((3201080401993783301049613:ℚ)/3610000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3557426239:ℚ)/5000000000),((1805664063:ℚ)/2500000000),(-1:ℚ),((-9392278717:ℚ)/10276250000),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((359238527:ℚ)/1000000000),((134632476796111433760478594080693829:ℚ)/1056013140625000000000000000000000000),((2402623566443965674712991:ℚ)/2707500000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((3564854429:ℚ)/5000000000),((3618750001:ℚ)/5000000000),(-1:ℚ),((-9414563287:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((707272827:ℚ)/2000000000),((67600364565231114999695934436812257:ℚ)/530450000000000000000000000000000000),((3205916650625407554174613:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7144565179:ℚ)/10000000000),((906542969:ℚ)/1250000000),(-1:ℚ),((-18873695537:ℚ)/20647500000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((434934983:ℚ)/1250000000),((90513612482118968242372884111170609:ℚ)/710532093750000000000000000000000000),((200521005505883954045093:ℚ)/225625000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7159421443:ℚ)/10000000000),((3633593751:ℚ)/5000000000),(-1:ℚ),((-18918264329:ℚ)/20695000000),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((3421689339:ℚ)/10000000000),((27268309062791222716662428097337067:ℚ)/214141512500000000000000000000000000),((9632269202994484093773839:ℚ)/10830000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4139:ℚ)/6400),((663:ℚ)/1024),(-1:ℚ),((-15:ℚ)/16),((448392353:ℚ)/625000000),((7274609377:ℚ)/10000000000),(-1:ℚ),((-1185177059:ℚ)/1294921875),((9844653101:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1764940707:ℚ)/10000000000),((1681472891:ℚ)/5000000000),((544714518205479759529369436651343601:ℚ)/4292666015625000000000000000000000000),((12847867542953605242089077:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((4139:ℚ)/6400) ((663:ℚ)/1024) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((663:ℚ)/1024),((8297:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((718170573:ℚ)/1000000000),((1820507813:ℚ)/2500000000),(-1:ℚ),((-1898511719:ℚ)/2074250000),((9840798677:ℚ)/10000000000),((4922326553:ℚ)/5000000000),((1786759881:ℚ)/10000000000),((833300219:ℚ)/2500000000),((2729297734003869215807217615558801:ℚ)/21512565312500000000000000000000000),((803294397334365463445997:ℚ)/902500000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((663:ℚ)/1024) ((8297:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8297:ℚ)/12800),((16613:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7189133797:ℚ)/10000000000),((7289453127:ℚ)/10000000000),(-1:ℚ),((-19007401391:ℚ)/20766250000),((9836961557:ℚ)/10000000000),((4920399341:ℚ)/5000000000),((1808222361:ℚ)/10000000000),((3303198271:ℚ)/10000000000),((273503005411587970442157438694308561:ℚ)/2156185695312500000000000000000000000),((38572662141544115932517231:ℚ)/43320000000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((8297:ℚ)/12800) ((16613:ℚ)/25600) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((16613:ℚ)/25600),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((143931237:ℚ)/200000000),((3648437501:ℚ)/5000000000),(-1:ℚ),((-380593711:ℚ)/415800000),((4916570841:ℚ)/5000000000),((4918480781:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((818232717:ℚ)/2500000000),((124297938757526365615072173667:ℚ)/980100000000000000000000000000),((3215599653112044732299613:ℚ)/3610000000000000000000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((16613:ℚ)/25600) ((2079:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2079:ℚ)/3200),((16651:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7203989889:ℚ)/10000000000),((7304296877:ℚ)/10000000000),(-1:ℚ),((-19051969667:ℚ)/20813750000),((4914669497:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((92506391:ℚ)/500000000),((3242391243:ℚ)/10000000000),((549303244017402341685152502676982981:ℚ)/4332121890625000000000000000000000000),((12867244053150268270214077:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((2079:ℚ)/3200) ((16651:ℚ)/25600) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((16651:ℚ)/25600),((1667:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((3605708957:ℚ)/5000000000),((228491211:ℚ)/312500000),(-1:ℚ),((-9537126871:ℚ)/10418750000),((4912776717:ℚ)/5000000000),((9829338999:ℚ)/10000000000),((935297099:ℚ)/5000000000),((3211571623:ℚ)/10000000000),((137613503276880091980019573391020029:ℚ)/1085503515625000000000000000000000000),((37711202253772382814119:ℚ)/42304687500000000000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((16651:ℚ)/25600) ((1667:ℚ)/2560) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1667:ℚ)/2560),((16689:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((288753837:ℚ)/400000000),((7319140627:ℚ)/10000000000),(-1:ℚ),((-763861511:ℚ)/834450000),((4910892471:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((945375407:ℚ)/5000000000),((1590231929:ℚ)/5000000000),((98063327496092242353817367126669:ℚ)/773674225000000000000000000000000),((12876937560860294120214077:ℚ)/14440000000000000000000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell ((1667:ℚ)/2560) ((16689:ℚ)/25600) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((16689:ℚ)/25600),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3613136961:ℚ)/5000000000),((3663281251:ℚ)/5000000000),(-1:ℚ),((-9559410883:ℚ)/10442500000),((4909016731:ℚ)/5000000000),((9821784947:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1574529701:ℚ)/5000000000),((17273745500071225958430889060664961:ℚ)/136307257812500000000000000000000000),((3220446406967057657299613:ℚ)/3610000000000000000000000)⟩
theorem valid16 : Valid source21 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source21 nn0 nn1 Qcell ((16689:ℚ)/25600) ((4177:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4177:ℚ)/6400),((16727:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((1446740381:ℚ)/2000000000),((7333984377:ℚ)/10000000000),(-1:ℚ),((-3828221143:ℚ)/4181750000),((1962859787:ℚ)/2000000000),((9818033467:ℚ)/10000000000),((482543621:ℚ)/2500000000),((3117349279:ℚ)/10000000000),((4431319437540153456469426838039503:ℚ)/34974066125000000000000000000000000),((38659903710934348582517231:ℚ)/43320000000000000000000000)⟩
theorem valid17 : Valid source21 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((16727:ℚ)/25600) :=
  cell_of_packet source21 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((16727:ℚ)/25600),((8373:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3620564937:ℚ)/5000000000),((1835351563:ℚ)/2500000000),(-1:ℚ),((-9581694811:ℚ)/10466250000),((4905290651:ℚ)/5000000000),((490714947:ℚ)/500000000),((194946007:ℚ)/1000000000),((617064811:ℚ)/2000000000),((34691964885738350010660202374605693:ℚ)/273855972656250000000000000000000000),((805717774261871925945997:ℚ)/902500000000000000000000)⟩
theorem valid18 : Valid source21 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source21 nn0 nn1 Qcell ((16727:ℚ)/25600) ((8373:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8373:ℚ)/12800),((3353:ℚ)/5120),(-1:ℚ),((-15:ℚ)/16),((7248557829:ℚ)/10000000000),((7348828127:ℚ)/10000000000),(-1:ℚ),((-19185673487:ℚ)/20956250000),((2451720127:ℚ)/2500000000),((9810581307:ℚ)/10000000000),((123029563:ℚ)/625000000),((3052973807:ℚ)/10000000000),((79461340179492935854639542290941951:ℚ)/627377734375000000000000000000000000),((12896335081503734492089077:ℚ)/14440000000000000000000000)⟩
theorem valid19 : Valid source21 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source21 nn0 nn1 Qcell ((8373:ℚ)/12800) ((3353:ℚ)/5120) :=
  cell_of_packet source21 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((3353:ℚ)/5120),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((725598577:ℚ)/1000000000),((3678125001:ℚ)/5000000000),(-1:ℚ),((-1920795731:ℚ)/2098000000),((4901598247:ℚ)/5000000000),((9806880513:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((37753601:ℚ)/125000000),((1393471897643299842767325847192061:ℚ)/11004010000000000000000000000000000),((9675889987689600418773839:ℚ)/10830000000000000000000000)⟩
theorem valid20 : Valid source21 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source21 nn0 nn1 Qcell ((3353:ℚ)/5120) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3631706849:ℚ)/5000000000),((921386719:ℚ)/1250000000),(-1:ℚ),((-9615120547:ℚ)/10513750000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((59745117:ℚ)/200000000),((140379656705509594487894630510663039:ℚ)/1105389390625000000000000000000000000),((201732693969637185295093:ℚ)/225625000000000000000000)⟩
theorem valid21 : Valid source21 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((909783689:ℚ)/1250000000),((3692968751:ℚ)/5000000000),(-1:ℚ),((-2409351067:ℚ)/2634375000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((1460052349:ℚ)/5000000000),((1762028431747227543549427126502953:ℚ)/13879863281250000000000000000000000),((3230150419900472179174613:ℚ)/3610000000000000000000000)⟩
theorem valid22 : Valid source21 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source21 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source21 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((911640659:ℚ)/1250000000),((1850195313:ℚ)/2500000000),(-1:ℚ),((-2414921977:ℚ)/2640312500),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((1425709509:ℚ)/5000000000),((20220904020411519554906580361811663:ℚ)/159342859375000000000000000000000000),((2424433958791523837212991:ℚ)/2707500000000000000000000)⟩
theorem valid23 : Valid source21 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source21 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3653990489:ℚ)/5000000000),((3707812501:ℚ)/5000000000),(-1:ℚ),((-9681971467:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((34763563:ℚ)/125000000),((71065908714715266529440982985815783:ℚ)/560211125000000000000000000000000000),((3235007678978873776049613:ℚ)/3610000000000000000000000)⟩
theorem valid24 : Valid source21 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((732283663:ℚ)/1000000000),((3722656251:ℚ)/5000000000),(-1:ℚ),((-1940850989:ℚ)/2126500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1354487151:ℚ)/5000000000),((2884278422625601425390687678816493:ℚ)/22610011250000000000000000000000000),((9719605319395214790648839:ℚ)/10830000000000000000000000)⟩
theorem valid25 : Valid source21 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((3676273887:ℚ)/5000000000),((3737500001:ℚ)/5000000000),(-1:ℚ),((-9748821661:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((2558817723:ℚ)/10000000000),((36349163217917693109577982733593183:ℚ)/285156000000000000000000000000000000),((3244732702359065641674613:ℚ)/3610000000000000000000000)⟩
theorem valid26 : Valid source21 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((1845564677:ℚ)/2500000000),((3767187501:ℚ)/5000000000),(-1:ℚ),((-4896694031:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2399501213:ℚ)/10000000000),((9350005794480389562271679013508449:ℚ)/72562890625000000000000000000000000),((9763415198111327209398839:ℚ)/10830000000000000000000000)⟩
theorem valid27 : Valid source21 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3720839977:ℚ)/5000000000),((3796875001:ℚ)/5000000000),(-1:ℚ),((-9882519931:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((204471589:ℚ)/1000000000),((76006391070665342529194624897322997:ℚ)/590784500000000000000000000000000000),((3264224770013004060424613:ℚ)/3610000000000000000000000)⟩
theorem valid28 : Valid source21 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((937637549:ℚ)/1250000000),((3856250001:ℚ)/5000000000),(-1:ℚ),((-2492912647:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((807509387:ℚ)/5000000000),((12801202128244500220486177889409:ℚ)/97515625000000000000000000000000),((452251:ℚ)/500000)⟩
theorem valid29 : Valid source21 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((3809969461:ℚ)/5000000000),((3975000001:ℚ)/5000000000),(-1:ℚ),((-10149908383:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((89055329478800209932972194964998647:ℚ)/654368000000000000000000000000000000),((452251:ℚ)/500000)⟩
theorem valid30 : Valid source21 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((491100447:ℚ)/625000000),((4450000001:ℚ)/5000000000),(-1:ℚ),((-1313301341:ℚ)/1620000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2101289448429036379023175349678317:ℚ)/13122000000000000000000000000000000),((452251:ℚ)/500000)⟩
theorem valid31 : Valid source21 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((8808181331:ℚ)/10000000000),((5400000001:ℚ)/5000000000),(-1:ℚ),((-23864543993:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((902871499962766595509583168052535287:ℚ)/5120000000000000000000000000000000000),((452251:ℚ)/500000)⟩
theorem valid32 : Valid source21 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((5354501099:ℚ)/5000000000),((14600000003:ℚ)/10000000000),(-1:ℚ),((-14783503297:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((49583800418804586686828947:ℚ)/243763200000000000000000000),((452251:ℚ)/500000)⟩
theorem valid33 : Valid source21 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet33 valid33
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8221:ℚ)/12800) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((8221:ℚ)/12800) ((8259:ℚ)/12800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source21 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8259:ℚ)/12800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((8259:ℚ)/12800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source21 nn0 nn1 Qcell ((8259:ℚ)/12800) ((663:ℚ)/1024) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((663:ℚ)/1024) ((16613:ℚ)/25600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source21 nn0 nn1 Qcell ((8259:ℚ)/12800) ((16613:ℚ)/25600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source21 nn0 nn1 Qcell ((16613:ℚ)/25600) ((16651:ℚ)/25600) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source21 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source21 nn0 nn1 Qcell ((16651:ℚ)/25600) ((4177:ℚ)/6400) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source21 nn0 nn1 Qcell ((16613:ℚ)/25600) ((4177:ℚ)/6400) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source21 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4177:ℚ)/6400) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_8 node8_17
private theorem node17_19 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source21 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join node17_19 node19_21
private theorem node21_23 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source21 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join node21_23 node23_25
private theorem node17_25 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join node17_21 node21_25
private theorem node25_27 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join node25_27 node27_29
private theorem node29_31 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf29 leaf30
private theorem node32_34 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf32 leaf33
private theorem node31_34 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf31 node32_34
private theorem node29_34 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node29_31 node31_34
private theorem node25_34 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node25_29 node29_34
private theorem node17_34 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node17_25 node25_34
private theorem node0_34 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_17 node17_34
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_34
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33]
theorem packet_count : packets.length = 34 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC01
#check @N11Formalization.C450Source21GroupedC01.bound
#print axioms N11Formalization.C450Source21GroupedC01.valid0
#print axioms N11Formalization.C450Source21GroupedC01.valid1
#print axioms N11Formalization.C450Source21GroupedC01.valid2
#print axioms N11Formalization.C450Source21GroupedC01.valid3
#print axioms N11Formalization.C450Source21GroupedC01.valid4
#print axioms N11Formalization.C450Source21GroupedC01.valid5
#print axioms N11Formalization.C450Source21GroupedC01.valid6
#print axioms N11Formalization.C450Source21GroupedC01.valid7
#print axioms N11Formalization.C450Source21GroupedC01.valid8
#print axioms N11Formalization.C450Source21GroupedC01.valid9
#print axioms N11Formalization.C450Source21GroupedC01.valid10
#print axioms N11Formalization.C450Source21GroupedC01.valid11
#print axioms N11Formalization.C450Source21GroupedC01.valid12
#print axioms N11Formalization.C450Source21GroupedC01.valid13
#print axioms N11Formalization.C450Source21GroupedC01.valid14
#print axioms N11Formalization.C450Source21GroupedC01.valid15
#print axioms N11Formalization.C450Source21GroupedC01.valid16
#print axioms N11Formalization.C450Source21GroupedC01.valid17
#print axioms N11Formalization.C450Source21GroupedC01.valid18
#print axioms N11Formalization.C450Source21GroupedC01.valid19
#print axioms N11Formalization.C450Source21GroupedC01.valid20
#print axioms N11Formalization.C450Source21GroupedC01.valid21
#print axioms N11Formalization.C450Source21GroupedC01.valid22
#print axioms N11Formalization.C450Source21GroupedC01.valid23
#print axioms N11Formalization.C450Source21GroupedC01.valid24
#print axioms N11Formalization.C450Source21GroupedC01.valid25
#print axioms N11Formalization.C450Source21GroupedC01.valid26
#print axioms N11Formalization.C450Source21GroupedC01.valid27
#print axioms N11Formalization.C450Source21GroupedC01.valid28
#print axioms N11Formalization.C450Source21GroupedC01.valid29
#print axioms N11Formalization.C450Source21GroupedC01.valid30
#print axioms N11Formalization.C450Source21GroupedC01.valid31
#print axioms N11Formalization.C450Source21GroupedC01.valid32
#print axioms N11Formalization.C450Source21GroupedC01.valid33
#print axioms N11Formalization.C450Source21GroupedC01.bound
#print axioms N11Formalization.C450Source21GroupedC01.endpoint_checks
