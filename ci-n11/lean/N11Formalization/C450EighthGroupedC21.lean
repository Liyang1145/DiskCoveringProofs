import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6106792229:ℚ)/10000000000),((826369229:ℚ)/1250000000),((7066792229:ℚ)/26700000000),((938369229:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1275204779:ℚ)/2000000000),((2232962738837880921462553140371416799:ℚ)/271842636672000000000000000000000000000),((-16729428217484878386709573:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1316439747:ℚ)/2000000000),((6848592931:ℚ)/10000000000),((1508439747:ℚ)/5530000000),((2581530977:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5234920117:ℚ)/10000000000),((15237855545778280330283770318224284710147663455286723934027:ℚ)/2069624303241600000000000000000000000000000000000000000000000),((-2056101084418007019020831:ℚ)/27724800000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6819881013:ℚ)/10000000000),((6967408953:ℚ)/10000000000),((2593293671:ℚ)/9375000000),((7863408953:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((91412483:ℚ)/200000000),((608827631953243919987799380464037848791126610999008407:ℚ)/86972079600000000000000000000000000000000000000000000000),((-52013452157191985216500271:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((693871753:ℚ)/1000000000),((1405363227:ℚ)/2000000000),((789871753:ℚ)/2836250000),((1584563227:ℚ)/4500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2101223321:ℚ)/5000000000),((20035056144195182977030957719954983005270795058733694171739:ℚ)/2932152475781250000000000000000000000000000000000000000000000),((-174399556804242424197277:ℚ)/2310400000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((69981347:ℚ)/100000000),((7086222781:ℚ)/10000000000),((79581347:ℚ)/286000000),((7982222781:ℚ)/22690000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2003256157:ℚ)/5000000000),((31234832102422517375264461539350448860253770777213518649:ℚ)/4593801433614250000000000000000000000000000000000000000000),((-1749110424157774571477:ℚ)/23104000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((7057551169:ℚ)/10000000000),((3572814453:ℚ)/5000000000),((8017551169:ℚ)/28837500000),((4020814453:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3801064287:ℚ)/10000000000),((28085960577009064541384569651114657748937778098390939279407:ℚ)/4150228741744800000000000000000000000000000000000000000000000),((-17542305763919607814553933:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((1423393391:ℚ)/2000000000),((3602517261:ℚ)/5000000000),((1615393391:ℚ)/5815000000),((4050517261:ℚ)/11535000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3584463057:ℚ)/10000000000),((1165425398210188270659850013349606183553464242946179022631:ℚ)/172993975840834031250000000000000000000000000000000000000000),((-703742410443584548950893:ℚ)/9241600000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((7176382073:ℚ)/10000000000),((7264439641:ℚ)/10000000000),((8136382073:ℚ)/29312500000),((8160439641:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3354544621:ℚ)/10000000000),((29011432479249193311476690767637966906324299966412939828553:ℚ)/4325086948348337500000000000000000000000000000000000000000000),((-17644867744200497855410237:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7235796541:ℚ)/10000000000),((1830961069:ℚ)/2500000000),((8195796541:ℚ)/29550000000),((293565867:ℚ)/837500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3108350713:ℚ)/10000000000),((2141548003569336129591615973206725768975940743420952739:ℚ)/320589603890991210937500000000000000000000000000000000000),((-17696228227013788724858293:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((3647605187:ℚ)/5000000000),((3691624219:ℚ)/5000000000),((4127605187:ℚ)/14893750000),((4139624219:ℚ)/11820000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1420824693:ℚ)/5000000000),((1169946696314138645303279711717280880245596717361615559472921:ℚ)/175833567001787850000000000000000000000000000000000000000000000),((-4436910430189637992263157:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7354623587:ℚ)/10000000000),((3721326069:ℚ)/5000000000),((8314623587:ℚ)/30025000000),((4169326069:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2548003793:ℚ)/10000000000),((6317698666531184135690401412493686947345580454059230090573:ℚ)/953077439830306982421875000000000000000000000000000000000000),((-17799108236717959848387957:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((3707018097:ℚ)/5000000000),((1890364549:ℚ)/2500000000),((4187018097:ℚ)/15250000000),((2114364549:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2216725793:ℚ)/10000000000),((33696816606393904832434225149208879641511985961154277893:ℚ)/5035918843219531250000000000000000000000000000000000000000),((-13387970839021268001567431:ℚ)/173280000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((7532859651:ℚ)/10000000000),((779906523:ℚ)/1000000000),((8492859651:ℚ)/31450000000),((869506523:ℚ)/2440000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1330210101:ℚ)/10000000000),((61164307885678867282381558246440758273145284501198595779:ℚ)/8980298982100000000000000000000000000000000000000000000000),((-53861478081541000225548959:ℚ)/693120000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((3885249951:ℚ)/5000000000),((8036665983:ℚ)/10000000000),((1455083317:ℚ)/5400000000),((8932665983:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((488311435058999945942525371075700148668529281118614310199:ℚ)/72567047912400000000000000000000000000000000000000000000000),((-2494769:ℚ)/32000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((4004065961:ℚ)/5000000000),((4968649819:ℚ)/5000000000),((4484065961:ℚ)/20000000000),((5416649819:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((21370785221515674583229044232207886236622428330979161:ℚ)/2550916800000000000000000000000000000000000000000000000),((-2494769:ℚ)/32000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((1238620273:ℚ)/1250000000),((6869021671:ℚ)/5000000000),((1358620273:ℚ)/6900000000),((7317021671:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((52225944977235237437851667543275792549:ℚ)/4875264000000000000000000000000000000000),((-2494769:ℚ)/32000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC21
#check @N11Formalization.C450EighthGroupedC21.bound
#print axioms N11Formalization.C450EighthGroupedC21.valid0
#print axioms N11Formalization.C450EighthGroupedC21.valid1
#print axioms N11Formalization.C450EighthGroupedC21.valid2
#print axioms N11Formalization.C450EighthGroupedC21.valid3
#print axioms N11Formalization.C450EighthGroupedC21.valid4
#print axioms N11Formalization.C450EighthGroupedC21.valid5
#print axioms N11Formalization.C450EighthGroupedC21.valid6
#print axioms N11Formalization.C450EighthGroupedC21.valid7
#print axioms N11Formalization.C450EighthGroupedC21.valid8
#print axioms N11Formalization.C450EighthGroupedC21.valid9
#print axioms N11Formalization.C450EighthGroupedC21.valid10
#print axioms N11Formalization.C450EighthGroupedC21.valid11
#print axioms N11Formalization.C450EighthGroupedC21.valid12
#print axioms N11Formalization.C450EighthGroupedC21.valid13
#print axioms N11Formalization.C450EighthGroupedC21.valid14
#print axioms N11Formalization.C450EighthGroupedC21.valid15
#print axioms N11Formalization.C450EighthGroupedC21.bound
#print axioms N11Formalization.C450EighthGroupedC21.endpoint_checks
