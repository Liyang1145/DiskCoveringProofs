import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((2997470599:ℚ)/5000000000),((652533107:ℚ)/1000000000),((14112411797:ℚ)/53400000000),((924533107:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6619290127:ℚ)/10000000000),((6556101966713105478645843427854065317:ℚ)/135921318336000000000000000000000000000),((-25885689965318450601211:ℚ)/115520000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3236224359:ℚ)/5000000000),((1352770951:ℚ)/2000000000),((14828673077:ℚ)/55300000000),((1896770951:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5516937673:ℚ)/10000000000),((19338995236902287295852074244985111224795011895318735352721:ℚ)/436561376465025000000000000000000000000000000000000000000000),((-108170338463550963249939:ℚ)/462080000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((1677768079:ℚ)/2500000000),((6883090503:ℚ)/10000000000),((7593304237:ℚ)/28125000000),((9603090503:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2442521027:ℚ)/5000000000),((412855159616116267264099454232839019352058074169979323:ℚ)/9675987890625000000000000000000000000000000000000000000),((-2761999945115843234812051:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6830355457:ℚ)/10000000000),((7002310021:ℚ)/10000000000),((30731066371:ℚ)/114400000000),((1080256669:ℚ)/3125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4539294469:ℚ)/10000000000),((82598552244308659110473117213088996622075984959278785757:ℚ)/1950168609619140625000000000000000000000000000000000000000),((-2789465183124188489047499:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((3474810387:ℚ)/5000000000),((712151411:ℚ)/1000000000),((15544431161:ℚ)/58150000000),((984151411:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2083571521:ℚ)/5000000000),((3120138137301190434195708060968991451275419783376989592181:ℚ)/74159845083431250000000000000000000000000000000000000000000),((-28168790546989154580219:ℚ)/115520000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7068869147:ℚ)/10000000000),((3620351759:ℚ)/5000000000),((31446607441:ℚ)/118200000000),((4980351759:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((940180557:ℚ)/2500000000),((11687387944039893014033102231310794712188889953903968794661:ℚ)/279455666763258361816406250000000000000000000000000000000000),((-711060445771186796431459:ℚ)/2888000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((35940507:ℚ)/50000000),((147197579:ℚ)/200000000),((159021521:ℚ)/600500000),((67199193:ℚ)/197000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1653691947:ℚ)/5000000000),((1433579893686642645927608081388453463061846225189819741:ℚ)/34461542689290625000000000000000000000000000000000000000),((-60453759520122635721:ℚ)/243200000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((228353697:ℚ)/312500000),((373952053:ℚ)/500000000),((1005061091:ℚ)/3812500000),((509952053:ℚ)/1501250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((696064827:ℚ)/2500000000),((1628959895357466974651197954821678178841019635794877801:ℚ)/39343115962652587890625000000000000000000000000000000000),((-381422977988137984329:ℚ)/1520000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7426520583:ℚ)/10000000000),((964665969:ℚ)/1250000000),((1912915397:ℚ)/7400000000),((1304665969:ℚ)/3812500000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((2140729369:ℚ)/10000000000),((2488011783944128987661991144030869544402979920839105073:ℚ)/59268377113342285156250000000000000000000000000000000000),((-7699945928901387:ℚ)/30400000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7664883931:ℚ)/10000000000),((3977784047:ℚ)/5000000000),((33234651793:ℚ)/129600000000),((5337784047:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1661490085377979185808905544784347746997104328264600027513:ℚ)/39862269971411132812500000000000000000000000000000000000000),((-2056733:ℚ)/8000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7903196391:ℚ)/10000000000),((9860220441:ℚ)/10000000000),((33949589173:ℚ)/160000000000),((12580220441:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((980847711523087255488895818619168092873256920859367831:ℚ)/19929037500000000000000000000000000000000000000000000000),((-2056733:ℚ)/8000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((613018841:ℚ)/625000000),((6832836863:ℚ)/5000000000),((2479056523:ℚ)/13800000000),((8192836863:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((294930957103253412223238061751529299057:ℚ)/4761000000000000000000000000000000000000),((-2056733:ℚ)/8000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC20
#check @N11Formalization.C450Source18GroupedC20.bound
#print axioms N11Formalization.C450Source18GroupedC20.valid0
#print axioms N11Formalization.C450Source18GroupedC20.valid1
#print axioms N11Formalization.C450Source18GroupedC20.valid2
#print axioms N11Formalization.C450Source18GroupedC20.valid3
#print axioms N11Formalization.C450Source18GroupedC20.valid4
#print axioms N11Formalization.C450Source18GroupedC20.valid5
#print axioms N11Formalization.C450Source18GroupedC20.valid6
#print axioms N11Formalization.C450Source18GroupedC20.valid7
#print axioms N11Formalization.C450Source18GroupedC20.valid8
#print axioms N11Formalization.C450Source18GroupedC20.valid9
#print axioms N11Formalization.C450Source18GroupedC20.valid10
#print axioms N11Formalization.C450Source18GroupedC20.valid11
#print axioms N11Formalization.C450Source18GroupedC20.bound
#print axioms N11Formalization.C450Source18GroupedC20.endpoint_checks
