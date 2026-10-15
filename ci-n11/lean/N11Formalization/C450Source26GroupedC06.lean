import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1350908607:ℚ)/2000000000),((6964382813:ℚ)/10000000000),((-61248210943:ℚ)/99200000000),((-1030908607:ℚ)/2022000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1190432443:ℚ)/2500000000),((1515902831871138404789055902103457011322379911867528863973286927:ℚ)/6236161374412800000000000000000000000000000000000000000000000000),((40051166219854104240299:ℚ)/98304000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((6874153451:ℚ)/10000000000),((1756037531:ℚ)/2500000000),((-15476412841:ℚ)/25275000000),((-5274153451:ℚ)/10205000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4406048341:ℚ)/10000000000),((62663405276685566850884412826091631956243800579838977300369:ℚ)/262735971662866882324218750000000000000000000000000000000000),((119888551665148692370730137:ℚ)/295731200000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((6933946517:ℚ)/10000000000),((7083910129:ℚ)/10000000000),((-62563011419:ℚ)/102050000000),((-5333946517:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4217807251:ℚ)/10000000000),((50488996663275201647451880643742913807729635600400570933361497:ℚ)/211404753648958593750000000000000000000000000000000000000000000),((119585994515175153809962393:ℚ)/295731200000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((6993731791:ℚ)/10000000000),((3556893727:ℚ)/5000000000),((-31445830997:ℚ)/51500000000),((-5393731791:ℚ)/10347500000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((2010670147:ℚ)/5000000000),((103817762342782497115433120146247753656329184657773911126768311:ℚ)/438746648492976562500000000000000000000000000000000000000000000),((119281301133237087953330497:ℚ)/295731200000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3511810787:ℚ)/5000000000),((1785915757:ℚ)/2500000000),((-15805073327:ℚ)/25868750000),((-129133847:ℚ)/247500000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((979909039:ℚ)/2500000000),((5706730354968952437395129656788534869900309454054046580237:ℚ)/24100389487659072875976562500000000000000000000000000000000),((29782038318018150523085353:ℚ)/73932800000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((705350949:ℚ)/1000000000),((11477659:ℚ)/16000000),((-101678249:ℚ)/166320000),((-545350949:ℚ)/1044250000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((953843039:ℚ)/2500000000),((245617858198570123467305383693215736865120623606906049:ℚ)/1036566180412408800000000000000000000000000000000000000),((3569234137565543133693611:ℚ)/8871936000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1770848891:ℚ)/2500000000),((7203409019:ℚ)/10000000000),((-63877499209:ℚ)/104425000000),((-1370848891:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((185416589:ℚ)/500000000),((464238607837983450732216091364331395275166661985248762315950849:ℚ)/1957872715602696118164062500000000000000000000000000000000000000),((7426265940389608575291897:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((7113279821:ℚ)/10000000000),((7233279483:ℚ)/10000000000),((-64206074313:ℚ)/104900000000),((-5513279821:ℚ)/10537500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3598266649:ℚ)/10000000000),((12164848826897410475402412215492257366182230241445211547408617:ℚ)/51269800930700062500000000000000000000000000000000000000000000),((118665504625054346792759817:ℚ)/295731200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((446447643:ℚ)/625000000),((7263148289:ℚ)/10000000000),((-64534631179:ℚ)/105375000000),((-346447643:ℚ)/661562500),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((1742444769:ℚ)/5000000000),((2593827564920561359721640705650934719257649037378122451998441753:ℚ)/10924793622207531738281250000000000000000000000000000000000000000),((1388791640006779821872939:ℚ)/3465600000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7173042987:ℚ)/10000000000),((7293015461:ℚ)/10000000000),((-64863170071:ℚ)/105850000000),((-5573042987:ℚ)/10632500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1683932669:ℚ)/5000000000),((31852871890420267839097580391253106204012347505245143042369999191:ℚ)/134073630591847278906250000000000000000000000000000000000000000000),((355063202986661047404406859:ℚ)/887193600000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((7202921943:ℚ)/10000000000),((366144051:ℚ)/500000000),((-3259584561:ℚ)/5316250000),((-5602921943:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((649359809:ℚ)/2000000000),((3978652550905009555594320528849826226372973338469997160191:ℚ)/16736272403030557250976562500000000000000000000000000000000),((354594143206184816761510739:ℚ)/887193600000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((361639959:ℚ)/500000000),((1838186247:ℚ)/2500000000),((-5460016239:ℚ)/8900000000),((-281639959:ℚ)/536375000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((62424393:ℚ)/200000000),((301530472347091001384826952570556563897358043564547409078631:ℚ)/1267614190614160156250000000000000000000000000000000000000000),((885308701017150867585491:ℚ)/2217984000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((7262674721:ℚ)/10000000000),((7382607387:ℚ)/10000000000),((-65848681257:ℚ)/107275000000),((-5662674721:ℚ)/10775000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2990557953:ℚ)/10000000000),((1332588284537274629702666914236103014204856324980805725688377:ℚ)/5598738223731663131713867187500000000000000000000000000000000),((117883738168607486788624417:ℚ)/295731200000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1823137147:ℚ)/2500000000),((7442327559:ℚ)/10000000000),((-66505603149:ℚ)/107750000000),((-1423137147:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((89191103:ℚ)/312500000),((2222024496889484780745377168753046365543487381741052829605207069:ℚ)/9238276192663964843750000000000000000000000000000000000000000000),((7357861363147101868426233:ℚ)/18483200000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7352291391:ℚ)/10000000000),((3780874981:ℚ)/5000000000),((-33909624791:ℚ)/54350000000),((-821755913:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((320018781:ℚ)/1250000000),((72044587844568007415982068625627338625411047584840198243573:ℚ)/293544620515979003906250000000000000000000000000000000000000),((352224797400251220781510691:ℚ)/887193600000000000000000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7471757869:ℚ)/10000000000),((975065903:ℚ)/1250000000),((-8805724933:ℚ)/13825000000),((-5871757869:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((919827007:ℚ)/5000000000),((6619976774304808974197437198482691740983975387518169548449:ℚ)/25977907130957031250000000000000000000000000000000000000000),((116766819892931640663213257:ℚ)/295731200000000000000000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7710618817:ℚ)/10000000000),((1750976449:ℚ)/2000000000),((-16188740939:ℚ)/22880000000),((-2036872939:ℚ)/4320000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((38911697181777895317257424627616035963026659362848682511:ℚ)/127209139200000000000000000000000000000000000000000000000),((200949771:ℚ)/512000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((2166314707:ℚ)/2500000000),((5330548981:ℚ)/5000000000),((-50956038791:ℚ)/64800000000),((-1766314707:ℚ)/4000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1828751609716306800041649990754309788462855722263821598357:ℚ)/5101833600000000000000000000000000000000000000000000000000),((200949771:ℚ)/512000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((5285940231:ℚ)/5000000000),((144683801:ℚ)/100000000),((-1437921811:ℚ)/1600000000),((-4485940231:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2209349269604624321407476344313286657:ℚ)/4875264000000000000000000000000000000),((200949771:ℚ)/512000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4139:ℚ)/6400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((4139:ℚ)/6400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2117:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source26 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC06
#check @N11Formalization.C450Source26GroupedC06.bound
#print axioms N11Formalization.C450Source26GroupedC06.valid0
#print axioms N11Formalization.C450Source26GroupedC06.valid1
#print axioms N11Formalization.C450Source26GroupedC06.valid2
#print axioms N11Formalization.C450Source26GroupedC06.valid3
#print axioms N11Formalization.C450Source26GroupedC06.valid4
#print axioms N11Formalization.C450Source26GroupedC06.valid5
#print axioms N11Formalization.C450Source26GroupedC06.valid6
#print axioms N11Formalization.C450Source26GroupedC06.valid7
#print axioms N11Formalization.C450Source26GroupedC06.valid8
#print axioms N11Formalization.C450Source26GroupedC06.valid9
#print axioms N11Formalization.C450Source26GroupedC06.valid10
#print axioms N11Formalization.C450Source26GroupedC06.valid11
#print axioms N11Formalization.C450Source26GroupedC06.valid12
#print axioms N11Formalization.C450Source26GroupedC06.valid13
#print axioms N11Formalization.C450Source26GroupedC06.valid14
#print axioms N11Formalization.C450Source26GroupedC06.valid15
#print axioms N11Formalization.C450Source26GroupedC06.valid16
#print axioms N11Formalization.C450Source26GroupedC06.valid17
#print axioms N11Formalization.C450Source26GroupedC06.valid18
#print axioms N11Formalization.C450Source26GroupedC06.bound
#print axioms N11Formalization.C450Source26GroupedC06.endpoint_checks
