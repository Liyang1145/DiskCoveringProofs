import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1735936711:ℚ)/2500000000),((3549687501:ℚ)/5000000000),(-1:ℚ),((-4535810133:ℚ)/5007500000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((52327463:ℚ)/125000000),((879852315142634480663723457048467:ℚ)/5015011250000000000000000000000000),((5006127794336040124392431:ℚ)/5415000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7003181219:ℚ)/10000000000),((3579375001:ℚ)/5000000000),(-1:ℚ),((-6107181219:ℚ)/6740000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((3989452697:ℚ)/10000000000),((39788844302120978636269736782813903:ℚ)/227138000000000000000000000000000000),((1674445127412000290422477:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7062614477:ℚ)/10000000000),((3594218751:ℚ)/5000000000),(-1:ℚ),((-18499843431:ℚ)/20315000000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((1891533569:ℚ)/5000000000),((178360110135491505441346507460469491:ℚ)/1031748062500000000000000000000000000),((5031950698264228315017431:ℚ)/5415000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((886541337:ℚ)/1250000000),((3609062501:ℚ)/5000000000),(-1:ℚ),((-2323624011:ℚ)/2551250000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((91893829:ℚ)/250000000),((19960954227838355963260450009729:ℚ)/115542187500000000000000000000000),((1680191231892651268547477:ℚ)/1805000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((8183:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((890255831:ℚ)/1250000000),((452060547:ℚ)/625000000),(-1:ℚ),((-2334767493:ℚ)/2557187500),((9888211123:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((37416203:ℚ)/250000000),((3565362383:ℚ)/10000000000),((785286573280465977273123422115683:ℚ)/4575539062500000000000000000000000),((78826376170380911227079:ℚ)/84609375000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8183:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((8183:ℚ)/12800),((4101:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((285476181:ℚ)/400000000),((3623906251:ℚ)/5000000000),(-1:ℚ),((-249636181:ℚ)/273400000),((4940065779:ℚ)/5000000000),((1236026391:ℚ)/1250000000),((774947369:ℚ)/5000000000),((701784521:ℚ)/2000000000),((96186600315499711899866025513241:ℚ)/560606700000000000000000000000000),((1683068124825725781047477:ℚ)/1805000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((8183:ℚ)/12800) ((4101:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((223492573:ℚ)/312500000),((1815664063:ℚ)/2500000000),(-1:ℚ),((-586477719:ℚ)/642265625),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((3451599089:ℚ)/10000000000),((90566405531645525161984818124106079:ℚ)/528006570312500000000000000000000000),((421126882866362573289213:ℚ)/451250000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((3583310041:ℚ)/5000000000),((3638750001:ℚ)/5000000000),(-1:ℚ),((-9405930123:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((169667349:ℚ)/500000000),((90958834460589608291595256263237771:ℚ)/530450000000000000000000000000000000),((5057842734661898927517431:ℚ)/5415000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((103:ℚ)/160),((16499:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7181477763:ℚ)/10000000000),((7284921877:ℚ)/10000000000),(-1:ℚ),((-18856433289:ℚ)/20623750000),((9860245043:ℚ)/10000000000),((616511681:ℚ)/625000000),((836904117:ℚ)/5000000000),((1667058771:ℚ)/5000000000),((51927212620719949780737447209843181:ℚ)/303813617187500000000000000000000000),((6746671366566084524580533:ℚ)/7220000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((16499:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((16499:ℚ)/25600),((8259:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((359445329:ℚ)/500000000),((911542969:ℚ)/1250000000),(-1:ℚ),((-314645329:ℚ)/344125000),((9856320801:ℚ)/10000000000),((1232530631:ℚ)/1250000000),((1697201141:ℚ)/10000000000),((330411991:ℚ)/1000000000),((101188106023581911123792156066649:ℚ)/592110078125000000000000000000000),((105461766568204614318397:ℚ)/112812500000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((16499:ℚ)/25600) ((8259:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8259:ℚ)/12800),((16537:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((359816769:ℚ)/500000000),((7299765627:ℚ)/10000000000),(-1:ℚ),((-945050307:ℚ)/1033562500),((9852414103:ℚ)/10000000000),((4928160403:ℚ)/5000000000),((3440353:ℚ)/20000000),((163692883:ℚ)/500000000),((3650648348548160496333040282426907:ℚ)/21365028828125000000000000000000000),((20257306182838692836241599:ℚ)/21660000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((8259:ℚ)/12800) ((16537:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((16537:ℚ)/25600),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1440752833:ℚ)/2000000000),((3653593751:ℚ)/5000000000),(-1:ℚ),((-3784658499:ℚ)/4139000000),((984852489:ℚ)/1000000000),((2463103527:ℚ)/2500000000),((1742751127:ℚ)/10000000000),((324332337:ℚ)/1000000000),((4390241368672869454641403061090123:ℚ)/25696981500000000000000000000000000),((1688829592077372852922477:ℚ)/1805000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((16537:ℚ)/25600) ((4139:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4139:ℚ)/6400),((663:ℚ)/1024),(-1:ℚ),((-15:ℚ)/16),((3605596467:ℚ)/5000000000),((7314609377:ℚ)/10000000000),(-1:ℚ),((-3157596467:ℚ)/3453125000),((9844653101:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1764940707:ℚ)/10000000000),((1606254639:ℚ)/5000000000),((40738113261032974856310079129887259:ℚ)/238481445312500000000000000000000000),((6758201982454876715205533:ℚ)/7220000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((4139:ℚ)/6400) ((663:ℚ)/1024) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((663:ℚ)/1024),((8297:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7218621687:ℚ)/10000000000),((1830507813:ℚ)/2500000000),(-1:ℚ),((-18967865061:ℚ)/20742500000),((9840798677:ℚ)/10000000000),((4922326553:ℚ)/5000000000),((1786759881:ℚ)/10000000000),((636281449:ℚ)/2000000000),((367433550570089579784687384579775013:ℚ)/2151256531250000000000000000000000000),((1267703669384197535492639:ℚ)/1353750000000000000000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((663:ℚ)/1024) ((8297:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8297:ℚ)/12800),((16613:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((903256303:ℚ)/1250000000),((7329453127:ℚ)/10000000000),(-1:ℚ),((-2373768909:ℚ)/2595781250),((9836961557:ℚ)/10000000000),((4920399341:ℚ)/5000000000),((1808222361:ℚ)/10000000000),((3150008733:ℚ)/10000000000),((92056260242668241694518039859999183:ℚ)/539046423828125000000000000000000000),((6763971131092021833955533:ℚ)/7220000000000000000000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((8297:ℚ)/12800) ((16613:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((16613:ℚ)/25600),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1446695829:ℚ)/2000000000),((3668437501:ℚ)/5000000000),(-1:ℚ),((-1267495829:ℚ)/1386000000),((4916570841:ℚ)/5000000000),((4918480781:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((3118304779:ℚ)/10000000000),((1859498565806189214017957636449:ℚ)/10890000000000000000000000000000),((1691714166395945412297477:ℚ)/1805000000000000000000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell ((16613:ℚ)/25600) ((2079:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2079:ℚ)/3200),((16651:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7240907851:ℚ)/10000000000),((7344296877:ℚ)/10000000000),(-1:ℚ),((-19034723553:ℚ)/20813750000),((4914669497:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((92506391:ℚ)/500000000),((771571489:ℚ)/2500000000),((369810898532499241084876092690830169:ℚ)/2166060945312500000000000000000000000),((20309228520572998904991599:ℚ)/21660000000000000000000000)⟩
theorem valid16 : Valid source22 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((16651:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((16651:ℚ)/25600),((1667:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((7248336541:ℚ)/10000000000),((229741211:ℚ)/312500000),(-1:ℚ),((-19057009623:ℚ)/20837500000),((4912776717:ℚ)/5000000000),((9829338999:ℚ)/10000000000),((935297099:ℚ)/5000000000),((3053942357:ℚ)/10000000000),((555907898188850127904879153788727081:ℚ)/3256510546875000000000000000000000000),((6613896147376636515017:ℚ)/7050781250000000000000)⟩
theorem valid17 : Valid source22 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source22 nn0 nn1 Qcell ((16651:ℚ)/25600) ((1667:ℚ)/2560) :=
  cell_of_packet source22 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1667:ℚ)/2560),((16689:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((226742663:ℚ)/312500000),((7359140627:ℚ)/10000000000),(-1:ℚ),((-397485326:ℚ)/434609375),((4910892471:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((945375407:ℚ)/5000000000),((3021263537:ℚ)/10000000000),((41266732324479488311053758615765703:ℚ)/241773195312500000000000000000000000),((6775517109751810118330533:ℚ)/7220000000000000000000000)⟩
theorem valid18 : Valid source22 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source22 nn0 nn1 Qcell ((1667:ℚ)/2560) ((16689:ℚ)/25600) :=
  cell_of_packet source22 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((16689:ℚ)/25600),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((58105551:ℚ)/80000000),((3683281251:ℚ)/5000000000),(-1:ℚ),((-152812653:ℚ)/167080000),((4909016731:ℚ)/5000000000),((9821784947:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1494119247:ℚ)/5000000000),((297757499883130099891741779163691:ℚ)/1744732900000000000000000000000000),((5083803903529051961892431:ℚ)/5415000000000000000000000)⟩
theorem valid19 : Valid source22 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source22 nn0 nn1 Qcell ((16689:ℚ)/25600) ((4177:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7270622519:ℚ)/10000000000),((1845351563:ℚ)/2500000000),(-1:ℚ),((-6374622519:ℚ)/6977500000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((2954855607:ℚ)/10000000000),((20829494923314451998327725594072529:ℚ)/121713765625000000000000000000000000),((424011457184935132664213:ℚ)/451250000000000000000000)⟩
theorem valid20 : Valid source22 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((91068497:ℚ)/125000000),((3698125001:ℚ)/5000000000),(-1:ℚ),((-239605491:ℚ)/262250000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2886966483:ℚ)/10000000000),((176499067023034414335536672351063:ℚ)/1031625937500000000000000000000000),((1697490996418588577922477:ℚ)/1805000000000000000000000)⟩
theorem valid21 : Valid source22 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source22 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((365016847:ℚ)/500000000),((926386719:ℚ)/1250000000),(-1:ℚ),((-960650541:ℚ)/1051375000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((2817489017:ℚ)/10000000000),((3781356123505911877973219449127691:ℚ)/22107787812500000000000000000000000),((318550650789917774205191:ℚ)/338437500000000000000000)⟩
theorem valid22 : Valid source22 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7315194059:ℚ)/10000000000),((3712968751:ℚ)/5000000000),(-1:ℚ),((-6419194059:ℚ)/7025000000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((549260517:ℚ)/2000000000),((12658123858049302353576384305380997:ℚ)/74025937500000000000000000000000000),((1700383252122659184172477:ℚ)/1805000000000000000000000)⟩
theorem valid23 : Valid source22 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source22 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source22 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3665025559:ℚ)/5000000000),((3727812501:ℚ)/5000000000),(-1:ℚ),((-9651076677:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((334158823:ℚ)/1250000000),((288943474774190804532415552029788087:ℚ)/1680633375000000000000000000000000000),((5109834204865687418142431:ℚ)/5415000000000000000000000)⟩
theorem valid24 : Valid source22 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7359765057:ℚ)/10000000000),((3742656251:ℚ)/5000000000),(-1:ℚ),((-19391295171:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1260511993:ℚ)/5000000000),((1165517133073319341785589999194439997:ℚ)/6783003375000000000000000000000000000),((1706175444916298443547477:ℚ)/1805000000000000000000000)⟩
theorem valid25 : Valid source22 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7389478759:ℚ)/10000000000),((3757500001:ℚ)/5000000000),(-1:ℚ),((-6493478759:ℚ)/7120000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((2359194763:ℚ)/10000000000),((21764933421991524260254099867525429:ℚ)/126736000000000000000000000000000000),((1709075382005867096672477:ℚ)/1805000000000000000000000)⟩
theorem valid26 : Valid source22 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((7419192227:ℚ)/10000000000),((3816875001:ℚ)/5000000000),(-1:ℚ),((-19569576681:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((273206829:ℚ)/1250000000),((1256404806003624122813446973846146853:ℚ)/7089414000000000000000000000000000000),((118933:ℚ)/125000)⟩
theorem valid27 : Valid source22 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7538043829:ℚ)/10000000000),((3876250001:ℚ)/5000000000),(-1:ℚ),((-19926131487:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1277750221:ℚ)/10000000000),((3308955655264552536805095233571481:ℚ)/18723000000000000000000000000000000),((118933:ℚ)/125000)⟩
theorem valid28 : Valid source22 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((239277873:ℚ)/312500000),((3995000001:ℚ)/5000000000),(-1:ℚ),((-633833619:ℚ)/715000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((467768728431690556362522067744749:ℚ)/2556125000000000000000000000000000),((118933:ℚ)/125000)⟩
theorem valid29 : Valid source22 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((3947289181:ℚ)/5000000000),((4470000001:ℚ)/5000000000),(-1:ℚ),((-129603303:ℚ)/160000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((82159130050037179489498973153837:ℚ)/384000000000000000000000000000000),((118933:ℚ)/125000)⟩
theorem valid30 : Valid source22 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((8845214633:ℚ)/10000000000),((5420000001:ℚ)/5000000000),(-1:ℚ),((-23847643899:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3611869330989648802747749968590997687:ℚ)/15360000000000000000000000000000000000),((118933:ℚ)/125000)⟩
theorem valid31 : Valid source22 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((5373062123:ℚ)/5000000000),((14640000003:ℚ)/10000000000),(-1:ℚ),((-4925062123:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((7269933866476231180223681:ℚ)/27084800000000000000000000),((118933:ℚ)/125000)⟩
theorem valid32 : Valid source22 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet32 valid32
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source22 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source22 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source22 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_8 node8_16
private theorem node16_18 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source22 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join node16_18 node18_20
private theorem node20_22 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf20 leaf21
private theorem node22_24 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf22 leaf23
private theorem node20_24 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join node20_22 node22_24
private theorem node16_24 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join node16_20 node20_24
private theorem node24_26 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((1087:ℚ)/1600) :=
  cell_join node24_26 node26_28
private theorem node28_30 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf28 leaf29
private theorem node31_33 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf31 leaf32
private theorem node30_33 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf30 node31_33
private theorem node28_33 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node28_30 node30_33
private theorem node24_33 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node24_28 node28_33
private theorem node16_33 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node16_24 node24_33
private theorem node0_33 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_16 node16_33
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_33
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32]
theorem packet_count : packets.length = 33 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC01
#check @N11Formalization.C450Source22GroupedC01.bound
#print axioms N11Formalization.C450Source22GroupedC01.valid0
#print axioms N11Formalization.C450Source22GroupedC01.valid1
#print axioms N11Formalization.C450Source22GroupedC01.valid2
#print axioms N11Formalization.C450Source22GroupedC01.valid3
#print axioms N11Formalization.C450Source22GroupedC01.valid4
#print axioms N11Formalization.C450Source22GroupedC01.valid5
#print axioms N11Formalization.C450Source22GroupedC01.valid6
#print axioms N11Formalization.C450Source22GroupedC01.valid7
#print axioms N11Formalization.C450Source22GroupedC01.valid8
#print axioms N11Formalization.C450Source22GroupedC01.valid9
#print axioms N11Formalization.C450Source22GroupedC01.valid10
#print axioms N11Formalization.C450Source22GroupedC01.valid11
#print axioms N11Formalization.C450Source22GroupedC01.valid12
#print axioms N11Formalization.C450Source22GroupedC01.valid13
#print axioms N11Formalization.C450Source22GroupedC01.valid14
#print axioms N11Formalization.C450Source22GroupedC01.valid15
#print axioms N11Formalization.C450Source22GroupedC01.valid16
#print axioms N11Formalization.C450Source22GroupedC01.valid17
#print axioms N11Formalization.C450Source22GroupedC01.valid18
#print axioms N11Formalization.C450Source22GroupedC01.valid19
#print axioms N11Formalization.C450Source22GroupedC01.valid20
#print axioms N11Formalization.C450Source22GroupedC01.valid21
#print axioms N11Formalization.C450Source22GroupedC01.valid22
#print axioms N11Formalization.C450Source22GroupedC01.valid23
#print axioms N11Formalization.C450Source22GroupedC01.valid24
#print axioms N11Formalization.C450Source22GroupedC01.valid25
#print axioms N11Formalization.C450Source22GroupedC01.valid26
#print axioms N11Formalization.C450Source22GroupedC01.valid27
#print axioms N11Formalization.C450Source22GroupedC01.valid28
#print axioms N11Formalization.C450Source22GroupedC01.valid29
#print axioms N11Formalization.C450Source22GroupedC01.valid30
#print axioms N11Formalization.C450Source22GroupedC01.valid31
#print axioms N11Formalization.C450Source22GroupedC01.valid32
#print axioms N11Formalization.C450Source22GroupedC01.bound
#print axioms N11Formalization.C450Source22GroupedC01.endpoint_checks
