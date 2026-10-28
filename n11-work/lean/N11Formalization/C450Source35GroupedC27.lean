import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((1296458829:ℚ)/2500000000),((2764748467:ℚ)/5000000000),((1824458829:ℚ)/2575000000),((41292233137:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((512392673:ℚ)/625000000),((-28389888490087366001521787615844617104898769486600580785111:ℚ)/78552908800000000000000000000000000000000000000000000000000),((-2834561586963847026548233:ℚ)/5776000000000000000000000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5426291631:ℚ)/10000000000),((1153997347:ℚ)/2000000000),((2512763877:ℚ)/3560000000),((17045970817:ℚ)/20600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((310248761:ℚ)/400000000),((-440835288305755640743853871850291496101895112297844106793:ℚ)/1215658787500000000000000000000000000000000000000000000000),((-447125364223638483163273:ℚ)/924160000000000000000000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((566653391:ℚ)/1000000000),((589015183:ℚ)/1000000000),((777853391:ℚ)/1087000000),((2885055671:ℚ)/3560000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7293667217:ℚ)/10000000000),((-115561591424708406273198939275913435913841976358352678593:ℚ)/306520521200000000000000000000000000000000000000000000000),((-111015978052244023003033:ℚ)/231040000000000000000000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((5786581959:ℚ)/10000000000),((6010267463:ℚ)/10000000000),((7898581959:ℚ)/11060000000),((87872942093:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((110209089:ℚ)/156250000),((-26152079180877741022635795033553804247074038163608087887901:ℚ)/69360754214746093750000000000000000000000000000000000000000),((-11017041355135215662449393:ℚ)/23104000000000000000000000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((5906584701:ℚ)/10000000000),((3035153769:ℚ)/5000000000),((8018584701:ℚ)/11155000000),((44266691459:ℚ)/55300000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1701552067:ℚ)/2500000000),((-8072670593485718628247241894938441642468077672526613100387:ℚ)/21054113453515625000000000000000000000000000000000000000000),((-2744298878617373045797917:ℚ)/5776000000000000000000000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((298328491:ℚ)/500000000),((1532584049:ℚ)/2500000000),((403928491:ℚ)/562500000),((22298424539:ℚ)/27887500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1669947907:ℚ)/2500000000),((-1826814521816023032608302458811633301774347472081861899:ℚ)/4765531135511398315429687500000000000000000000000000000),((-683362053418778000645797:ℚ)/1444000000000000000000000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((6026544479:ℚ)/10000000000),((96724277:ℚ)/156250000),((8138544479:ℚ)/11345000000),((1403967047:ℚ)/1757812500),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1310267721:ℚ)/2000000000),((-8200024498940809407696007083425973065741636147461663:ℚ)/21395855583250522613525390625000000000000000000000000),((-680621296388412929298253:ℚ)/1444000000000000000000000)⟩
theorem valid6 : Valid source35 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((380406809:ℚ)/625000000),((6250360417:ℚ)/10000000000),((512406809:ℚ)/715000000),((90513964587:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6420723477:ℚ)/10000000000),((-500054387166209670029227472079847066317962179558716140603021:ℚ)/1305057225458593750000000000000000000000000000000000000000000),((-10845639220558058016806833:ℚ)/23104000000000000000000000)⟩
theorem valid7 : Valid source35 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((1536615869:ℚ)/2500000000),((3155178269:ℚ)/5000000000),((2064615869:ℚ)/2883750000),((45586960959:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((314390399:ℚ)/500000000),((-40379952455209662863298379690714986154927108476362410133:ℚ)/105408524203125000000000000000000000000000000000000000000),((-2700222082689201725317417:ℚ)/5776000000000000000000000)⟩
theorem valid8 : Valid source35 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source35 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1551602081:ℚ)/2500000000),((1274068471:ℚ)/2000000000),((2079602081:ℚ)/2907500000),((18366753181:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6152439491:ℚ)/10000000000),((-3797982585656142430098023170824133985056748030617457105327:ℚ)/9916536305006250000000000000000000000000000000000000000000),((-430227524547604003262977:ℚ)/924160000000000000000000)⟩
theorem valid9 : Valid source35 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((6266343731:ℚ)/10000000000),((3215159061:ℚ)/5000000000),((8378343731:ℚ)/11725000000),((46246749671:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3007224411:ℚ)/5000000000),((-220698142506474908642472772046289505974458783481999102537539:ℚ)/576370861986718750000000000000000000000000000000000000000000),((-2677509652501756563573837:ℚ)/5776000000000000000000000)⟩
theorem valid10 : Valid source35 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source35 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source35 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6326269929:ℚ)/10000000000),((811285511:ℚ)/1250000000),((2812756643:ℚ)/3940000000),((11644140621:ℚ)/14656250000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((183551487:ℚ)/312500000),((-370984943691750407689275664755016664682923350229690925473:ℚ)/969069322252273559570312500000000000000000000000000000000),((-666496241008143134689423:ℚ)/1444000000000000000000000)⟩
theorem valid11 : Valid source35 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1277237429:ℚ)/2000000000),((6610187563:ℚ)/10000000000),((1699637429:ℚ)/2402000000),((31490687731:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((572982497:ℚ)/1000000000),((-43273324864402982512312826692296098835104342259518841521899:ℚ)/114776162162500000000000000000000000000000000000000000000000),((-10567292523330014034581593:ℚ)/23104000000000000000000000)⟩
theorem valid12 : Valid source35 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source35 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source35 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((13011991:ℚ)/20000000),((3365027301:ℚ)/5000000000),((17235991:ℚ)/24400000),((47895300311:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5432135779:ℚ)/10000000000),((-31123915687533302219431348736405683077337152143493400057619:ℚ)/82556046610156250000000000000000000000000000000000000000000),((-2617987928798922598052697:ℚ)/5776000000000000000000000)⟩
theorem valid13 : Valid source35 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source35 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6625770461:ℚ)/10000000000),((6969686093:ℚ)/10000000000),((8737770461:ℚ)/12580000000),((98426547023:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((5119071319:ℚ)/10000000000),((-653412315511333164646901659026637506815399235481663735747763:ℚ)/1784638112500000000000000000000000000000000000000000000000000),((-10269680669791508075724553:ℚ)/23104000000000000000000000)⟩
theorem valid14 : Valid source35 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source35 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source35 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((1716306589:ℚ)/2500000000),((7209191001:ℚ)/10000000000),((2244306589:ℚ)/3240000000),((101061101011:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1108377533:ℚ)/2500000000),((-9985802421594326906007443351446834514591758441575560484007:ℚ)/27239882850000000000000000000000000000000000000000000000000),((-10066429832798057919790497:ℚ)/23104000000000000000000000)⟩
theorem valid15 : Valid source35 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7104566217:ℚ)/10000000000),((9121769579:ℚ)/10000000000),((9216566217:ℚ)/16000000000),((122099465369:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3630688423:ℚ)/10000000000),((-63219789870779142834838682141142228013980041559094446707:ℚ)/283435200000000000000000000000000000000000000000000000000),((-16355866533483221:ℚ)/38912000000000000)⟩
theorem valid16 : Valid source35 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((70438373:ℚ)/78125000),((6468238061:ℚ)/5000000000),((86938373:ℚ)/172500000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-26083180873:ℚ)/215625000000),((-2157773:ℚ)/5120000)⟩
theorem valid17 : Valid source35 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source35 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source35 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source35 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source35 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source35 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source35 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source35 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC27
#check @N11Formalization.C450Source35GroupedC27.bound
#print axioms N11Formalization.C450Source35GroupedC27.valid0
#print axioms N11Formalization.C450Source35GroupedC27.valid1
#print axioms N11Formalization.C450Source35GroupedC27.valid2
#print axioms N11Formalization.C450Source35GroupedC27.valid3
#print axioms N11Formalization.C450Source35GroupedC27.valid4
#print axioms N11Formalization.C450Source35GroupedC27.valid5
#print axioms N11Formalization.C450Source35GroupedC27.valid6
#print axioms N11Formalization.C450Source35GroupedC27.valid7
#print axioms N11Formalization.C450Source35GroupedC27.valid8
#print axioms N11Formalization.C450Source35GroupedC27.valid9
#print axioms N11Formalization.C450Source35GroupedC27.valid10
#print axioms N11Formalization.C450Source35GroupedC27.valid11
#print axioms N11Formalization.C450Source35GroupedC27.valid12
#print axioms N11Formalization.C450Source35GroupedC27.valid13
#print axioms N11Formalization.C450Source35GroupedC27.valid14
#print axioms N11Formalization.C450Source35GroupedC27.valid15
#print axioms N11Formalization.C450Source35GroupedC27.valid16
#print axioms N11Formalization.C450Source35GroupedC27.valid17
#print axioms N11Formalization.C450Source35GroupedC27.bound
#print axioms N11Formalization.C450Source35GroupedC27.endpoint_checks
