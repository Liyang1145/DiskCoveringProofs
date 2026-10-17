import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6096355197:ℚ)/10000000000),((661655997:ℚ)/1000000000),((15056355197:ℚ)/106800000000),((1141655997:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6399058179:ℚ)/10000000000),((1281107642834319156496471579178493463:ℚ)/27184263667200000000000000000000000000),((-413750310033039743121671:ℚ)/2918400000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6573402061:ℚ)/10000000000),((428429251:ℚ)/625000000),((15533402061:ℚ)/110600000000),((728429251:ℚ)/3337500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5258027309:ℚ)/10000000000),((119254773410326287011245477951047334657212510773469284729:ℚ)/2664559182525787353515625000000000000000000000000000000000),((-57245481127898996308673:ℚ)/380000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6811819383:ℚ)/10000000000),((6974001469:ℚ)/10000000000),((15771819383:ℚ)/112500000000),((11774001469:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4594601689:ℚ)/10000000000),((6697584419475351746225010692191101265633738602042987611:ℚ)/152880608671875000000000000000000000000000000000000000000),((-15086083959381116003470253:ℚ)/97280000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((6931004677:ℚ)/10000000000),((56744977:ℚ)/80000000),((15891004677:ℚ)/114400000000),((95144977:ℚ)/450000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((845450511:ℚ)/2000000000),((6340626364115497718907349701000014953283020837738441:ℚ)/145579306640625000000000000000000000000000000000000000),((-979115847364490276517:ℚ)/6225920000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/16),((1:ℚ)/8),((3525087717:ℚ)/5000000000),((3576338927:ℚ)/5000000000),((8005087717:ℚ)/57675000000),((459718379:ℚ)/2200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((765427337:ℚ)/2000000000),((15924486244917827383645281868903044187314845577144696809:ℚ)/368953823906250000000000000000000000000000000000000000000),((-3878537454352518288586917:ℚ)/24320000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((1777438897:ℚ)/2500000000),((901528827:ℚ)/1250000000),((4017438897:ℚ)/29075000000),((500509609:ℚ)/2403125000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((361141321:ℚ)/1000000000),((2525697135341647084461006177247237974150948663187503817:ℚ)/58659524143077945709228515625000000000000000000000000000),((-732204652135344245668151:ℚ)/4560000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/16),((1:ℚ)/8),((7169332373:ℚ)/10000000000),((1454356097:ℚ)/2000000000),((2304190339:ℚ)/16750000000),((2414356097:ℚ)/11630000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1691304501:ℚ)/5000000000),((17774006892101300265836354583035326961421669319329947803:ℚ)/413751940211894531250000000000000000000000000000000000000),((-629062047926714009866757:ℚ)/3891200000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7228905871:ℚ)/10000000000),((7331327531:ℚ)/10000000000),((5396301957:ℚ)/39400000000),((12131327531:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3137859039:ℚ)/10000000000),((6546527053154834205098244255532981331444002934189587967827:ℚ)/152725325186958312988281250000000000000000000000000000000000),((-833300306609227409385487:ℚ)/5120000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((1822119041:ℚ)/2500000000),((3725206711:ℚ)/5000000000),((4062119041:ℚ)/30025000000),((6125206711:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2873085799:ℚ)/10000000000),((374488405780876955522658191184878067437873224148844984249341:ℚ)/8723077993226689453125000000000000000000000000000000000000000),((-3983935670702852605114133:ℚ)/24320000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((1481521487:ℚ)/2000000000),((946186101:ℚ)/1250000000),((3273521487:ℚ)/24400000000),((1546186101:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((450975341:ℚ)/2000000000),((21031591335513615594337267552531082329150284778564848623:ℚ)/491788949533157348632812500000000000000000000000000000000),((-756930500582378329201319:ℚ)/4560000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((301069071:ℚ)/400000000),((8045694589:ℚ)/10000000000),((659469071:ℚ)/5184000000),((12845694589:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((13897299:ℚ)/100000000),((1264086010209364375230918321217392013868467766096040282533:ℚ)/29086373847656250000000000000000000000000000000000000000000),((-327291364525163:ℚ)/1945600000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((8003095379:ℚ)/10000000000),((2487342259:ℚ)/2500000000),((16963095379:ℚ)/160000000000),((3687342259:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2838627431320711642128771368166269734365191218776881:ℚ)/62278242187500000000000000000000000000000000000000000),((-21709041:ℚ)/128000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((4953632761:ℚ)/5000000000),((13753677423:ℚ)/10000000000),((9433632761:ℚ)/110400000000),((18553677423:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((403687616000666012244969936226922755973:ℚ)/7617600000000000000000000000000000000000),((-21709041:ℚ)/128000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC18
#check @N11Formalization.C450Source16GroupedC18.bound
#print axioms N11Formalization.C450Source16GroupedC18.valid0
#print axioms N11Formalization.C450Source16GroupedC18.valid1
#print axioms N11Formalization.C450Source16GroupedC18.valid2
#print axioms N11Formalization.C450Source16GroupedC18.valid3
#print axioms N11Formalization.C450Source16GroupedC18.valid4
#print axioms N11Formalization.C450Source16GroupedC18.valid5
#print axioms N11Formalization.C450Source16GroupedC18.valid6
#print axioms N11Formalization.C450Source16GroupedC18.valid7
#print axioms N11Formalization.C450Source16GroupedC18.valid8
#print axioms N11Formalization.C450Source16GroupedC18.valid9
#print axioms N11Formalization.C450Source16GroupedC18.valid10
#print axioms N11Formalization.C450Source16GroupedC18.valid11
#print axioms N11Formalization.C450Source16GroupedC18.valid12
#print axioms N11Formalization.C450Source16GroupedC18.bound
#print axioms N11Formalization.C450Source16GroupedC18.endpoint_checks
