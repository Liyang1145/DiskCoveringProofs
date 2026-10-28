import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((1495883541:ℚ)/2500000000),((3148581463:ℚ)/5000000000),((5495883541:ℚ)/25750000000),((7308581463:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6643671609:ℚ)/10000000000),((3847971350959645516582285487616846288557:ℚ)/40454748032000000000000000000000000000000),((-157153197774878305468398561:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6224266773:ℚ)/10000000000),((6537464491:ℚ)/10000000000),((22224266773:ℚ)/106800000000),((14857464491:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1527902049:ℚ)/2500000000),((22208574321840925305672683001735133964428906925005285561427:ℚ)/237730148629760742187500000000000000000000000000000000000000),((-648612243341358842886708489:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6464764967:ℚ)/10000000000),((208048143:ℚ)/312500000),((22464764967:ℚ)/108700000000),((468048143:ℚ)/1668750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((276809851:ℚ)/500000000),((1029596506835776254039208258618308243018071979457354080437:ℚ)/11439095531080627441406250000000000000000000000000000000000),((-1963136869335969491946743:ℚ)/5415000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((658493403:ℚ)/1000000000),((169439259:ℚ)/250000000),((2258493403:ℚ)/11060000000),((377439259:ℚ)/1358750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1045543229:ℚ)/2000000000),((3833103494077982179297366512111896317713132451326455259:ℚ)/42808590491913604736328125000000000000000000000000000000),((-1274989842205757884185467:ℚ)/3465600000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((670505349:ℚ)/1000000000),((6897556239:ℚ)/10000000000),((2270505349:ℚ)/11250000000),((15217556239:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2450945153:ℚ)/5000000000),((1090323036687721070874665065224621243115206179539176614521:ℚ)/12230448693750000000000000000000000000000000000000000000000),((-2069616731590677917280473747:ℚ)/5544960000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6825125917:ℚ)/10000000000),((1754375111:ℚ)/2500000000),((2075011447:ℚ)/10400000000),((426041679:ℚ)/1562500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4554961379:ℚ)/10000000000),((178950712820687155174852534059107445584836960154419489:ℚ)/2014636993408203125000000000000000000000000000000000000),((-43732330130159558735938049:ℚ)/115520000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3472576853:ℚ)/5000000000),((3568702529:ℚ)/5000000000),((11472576853:ℚ)/58150000000),((7728702529:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4181640869:ℚ)/10000000000),((4378760001196828616474789147965451953125917859123911667688977:ℚ)/49439896722287500000000000000000000000000000000000000000000000),((-177382481743960140257598929:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((706513909:ℚ)/1000000000),((1814318007:ℚ)/2500000000),((2306513909:ℚ)/11820000000),((3894318007:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3774063077:ℚ)/10000000000),((16463742700762997913285424124632477541081368248516500685191:ℚ)/186303777842172241210937500000000000000000000000000000000000),((-134870698648428764599449443:ℚ)/346560000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((1796271039:ℚ)/2500000000),((3748450097:ℚ)/5000000000),((5796271039:ℚ)/30500000000),((7908450097:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3319587497:ℚ)/10000000000),((17999277814219441601605992956623307794210835002436523982147:ℚ)/200028044060156250000000000000000000000000000000000000000000),((-181820725700834555610438321:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((1484972203:ℚ)/2000000000),((797577757:ℚ)/1000000000),((57839163:ℚ)/320000000),((1629577757:ℚ)/6100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2150983973:ℚ)/10000000000),((32966029110773279719336132775100239370959283061950061:ℚ)/354657812500000000000000000000000000000000000000000000),((-985149208017913:ℚ)/2432000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((7904008959:ℚ)/10000000000),((2471892667:ℚ)/2500000000),((23904008959:ℚ)/160000000000),((4551892667:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((59448857972269916970435751536859618671064411353845633:ℚ)/553584375000000000000000000000000000000000000000000000),((-53012459:ℚ)/128000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((490831127:ℚ)/500000000),((13701362333:ℚ)/10000000000),((1290831127:ℚ)/11040000000),((22021362333:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((85076398460929681262496771536435608337263:ℚ)/609408000000000000000000000000000000000000),((-53012459:ℚ)/128000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC18
#check @N11Formalization.C450Source27GroupedC18.bound
#print axioms N11Formalization.C450Source27GroupedC18.valid0
#print axioms N11Formalization.C450Source27GroupedC18.valid1
#print axioms N11Formalization.C450Source27GroupedC18.valid2
#print axioms N11Formalization.C450Source27GroupedC18.valid3
#print axioms N11Formalization.C450Source27GroupedC18.valid4
#print axioms N11Formalization.C450Source27GroupedC18.valid5
#print axioms N11Formalization.C450Source27GroupedC18.valid6
#print axioms N11Formalization.C450Source27GroupedC18.valid7
#print axioms N11Formalization.C450Source27GroupedC18.valid8
#print axioms N11Formalization.C450Source27GroupedC18.valid9
#print axioms N11Formalization.C450Source27GroupedC18.valid10
#print axioms N11Formalization.C450Source27GroupedC18.valid11
#print axioms N11Formalization.C450Source27GroupedC18.bound
#print axioms N11Formalization.C450Source27GroupedC18.endpoint_checks
