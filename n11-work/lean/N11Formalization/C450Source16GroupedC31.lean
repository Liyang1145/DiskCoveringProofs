import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((45071867:ℚ)/80000000),((386218257:ℚ)/625000000),((351343069:ℚ)/427200000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1839427159:ℚ)/2500000000),((-1220170512022485415642384980768761:ℚ)/15227330400000000000000000000000000),((-1870761581412626622843:ℚ)/6225920000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6109233749:ℚ)/10000000000),((6417181501:ℚ)/10000000000),((6749233749:ℚ)/7900000000),((7057181501:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3185312589:ℚ)/5000000000),((-3497677372531335096172244884067176251631660797576627:ℚ)/38518671875000000000000000000000000000000000000000000),((-28892753320186903182932187:ℚ)/97280000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6346846023:ℚ)/10000000000),((3327429147:ℚ)/5000000000),((48907922161:ℚ)/57200000000),((10942287441:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((364038253:ℚ)/625000000),((-102206409841666581130133171670292325803567630155931619:ℚ)/1124695000000000000000000000000000000000000000000000000),((-85660533200406875300701769:ℚ)/291840000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6584450833:ℚ)/10000000000),((6773692353:ℚ)/10000000000),((50571155831:ℚ)/58150000000),((22241077059:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((26144947:ℚ)/50000000),((-1470646426239460305964187892477402449920300958202370753:ℚ)/15361696748046875000000000000000000000000000000000000000),((-28384724883533123649620243:ℚ)/97280000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1675812667:ℚ)/2500000000),((6892523707:ℚ)/10000000000),((12850688669:ℚ)/14775000000),((22597571121:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2453463263:ℚ)/5000000000),((-2009004607578425319782278399789536795660926918485561:ℚ)/20998644104003906250000000000000000000000000000000000),((-1763447826293472890803243:ℚ)/6080000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((68220489:ℚ)/100000000),((695193841:ℚ)/1000000000),((522343423:ℚ)/595750000),((759193841:ℚ)/788000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((4564156283:ℚ)/10000000000),((-4857044717215866786678371782346749333090982204083:ℚ)/49556820875244140625000000000000000000000000000000),((-8439243646445605527881:ℚ)/29184000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6881447439:ℚ)/10000000000),((1402270497:ℚ)/2000000000),((52650132073:ℚ)/60050000000),((4590811491:ℚ)/4766000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2191745537:ℚ)/5000000000),((-1242900507805510393512881293081736467971008338494248797:ℚ)/12687916999511718750000000000000000000000000000000000000),((-84138142385438775887263481:ℚ)/291840000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1388169121:ℚ)/2000000000),((1414153189:ℚ)/2000000000),((3537727949:ℚ)/4035000000),((4626459567:ℚ)/4804000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((524447263:ℚ)/1250000000),((-376890179600719772584921868964386934068867643066209:ℚ)/3849301340332031250000000000000000000000000000000000),((-1118451492782773847210867:ℚ)/3891200000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((437515213:ℚ)/625000000),((3565089403:ℚ)/5000000000),((3342606491:ℚ)/3812500000),((1295029801:ℚ)/1345000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3999392259:ℚ)/10000000000),((-1271071295112464619020685922028192280995652995185991:ℚ)/12987957000732421875000000000000000000000000000000000),((-108892701973245075880753:ℚ)/380000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1411928171:ℚ)/2000000000),((7189591081:ℚ)/10000000000),((10779497197:ℚ)/12295000000),((23488773243:ℚ)/24400000000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((3793646501:ℚ)/10000000000),((-887748500822350758486617292422308442367663851368699:ℚ)/9075188341674804687500000000000000000000000000000000),((-1111671223996069838527067:ℚ)/3891200000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1423807591:ℚ)/2000000000),((1449800557:ℚ)/2000000000),((517269197:ℚ)/590000000),((4733401671:ℚ)/4918000000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((715337493:ℚ)/2000000000),((-1568897122491234702433011329531501816320991444499:ℚ)/16045234375000000000000000000000000000000000000000),((-1108281359292637759180547:ℚ)/3891200000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1794608679:ℚ)/2500000000),((7367824527:ℚ)/10000000000),((13682260753:ℚ)/15725000000),((8007824527:ℚ)/8260000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3346330631:ℚ)/10000000000),((-1279769484393664403442121842329858516571771274033949:ℚ)/13402145690917968750000000000000000000000000000000000),((-271747782182034867812579:ℚ)/960000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((7297227251:ℚ)/10000000000),((3802730847:ℚ)/5000000000),((6173398973:ℚ)/7200000000),((12368192541:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((88505257:ℚ)/312500000),((-295529559002297228418614670796176207617380726954171:ℚ)/3240000000000000000000000000000000000000000000000000),((-27205108889795940827846187:ℚ)/97280000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((3767404289:ℚ)/5000000000),((9506324327:ℚ)/10000000000),((28611830023:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1310733383:ℚ)/10000000000),((-46643938849002022695654539454894540056908150669438387:ℚ)/937500000000000000000000000000000000000000000000000000),((-6801735612018282234869427:ℚ)/24320000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((1179415009:ℚ)/1250000000),((6653668351:ℚ)/5000000000),((2938635021:ℚ)/4600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-8483968711591835297076684251681:ℚ)/304175000000000000000000000000000),((-8949821:ℚ)/32000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC31
#check @N11Formalization.C450Source16GroupedC31.bound
#print axioms N11Formalization.C450Source16GroupedC31.valid0
#print axioms N11Formalization.C450Source16GroupedC31.valid1
#print axioms N11Formalization.C450Source16GroupedC31.valid2
#print axioms N11Formalization.C450Source16GroupedC31.valid3
#print axioms N11Formalization.C450Source16GroupedC31.valid4
#print axioms N11Formalization.C450Source16GroupedC31.valid5
#print axioms N11Formalization.C450Source16GroupedC31.valid6
#print axioms N11Formalization.C450Source16GroupedC31.valid7
#print axioms N11Formalization.C450Source16GroupedC31.valid8
#print axioms N11Formalization.C450Source16GroupedC31.valid9
#print axioms N11Formalization.C450Source16GroupedC31.valid10
#print axioms N11Formalization.C450Source16GroupedC31.valid11
#print axioms N11Formalization.C450Source16GroupedC31.valid12
#print axioms N11Formalization.C450Source16GroupedC31.valid13
#print axioms N11Formalization.C450Source16GroupedC31.valid14
#print axioms N11Formalization.C450Source16GroupedC31.bound
#print axioms N11Formalization.C450Source16GroupedC31.endpoint_checks
