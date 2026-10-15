import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((2804793681:ℚ)/5000000000),((6159490967:ℚ)/10000000000),((12204243497:ℚ)/17800000000),((21518472901:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3702705451:ℚ)/5000000000),((-34732258324148514860778106778269141:ℚ)/704969000000000000000000000000000000),((-5513009336794582961561799047:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6086044243:ℚ)/10000000000),((3198848839:ℚ)/5000000000),((78466486673:ℚ)/110600000000),((11116546517:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3210872217:ℚ)/5000000000),((-760799152286289968123932632998128277549719326862078506221:ℚ)/12683428275000000000000000000000000000000000000000000000000),((-1371258569986235901571870183:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((3162098643:ℚ)/5000000000),((1658964311:ℚ)/2500000000),((40543085073:ℚ)/57200000000),((5736892933:ℚ)/6912500000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5878566937:ℚ)/10000000000),((-35244702148219260406053608964830035743318396970372312583:ℚ)/584841400000000000000000000000000000000000000000000000000),((-341033041734724362507576583:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6562306777:ℚ)/10000000000),((6754920799:ℚ)/10000000000),((83705374547:ℚ)/116300000000),((23304762397:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1321760491:ℚ)/2500000000),((-239416822161960979980972179122077004024107216609708129359:ℚ)/3686807219531250000000000000000000000000000000000000000000),((-5442076825907545569100171223:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1670336633:ℚ)/2500000000),((1718493559:ℚ)/2500000000),((21253702963:ℚ)/29550000000),((5915480677:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4967741593:ℚ)/10000000000),((-3926791492289302109918513945821653978283402045452228319:ℚ)/60476095019531250000000000000000000000000000000000000000),((-339218266001447496411637063:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3400188469:ℚ)/5000000000),((1398603607:ℚ)/2000000000),((43162073159:ℚ)/60050000000),((4803810821:ℚ)/5910000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2314218297:ℚ)/5000000000),((-131782768017555602582828199898226314781032940100821015987:ℚ)/2030066719921875000000000000000000000000000000000000000000),((-216510997305697386393432327:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((3459699221:ℚ)/5000000000),((7112052651:ℚ)/10000000000),((43816691431:ℚ)/61000000000),((24376157953:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4264324651:ℚ)/10000000000),((-46028702764213313636923571907689630087531089634221107521:ℚ)/709315625000000000000000000000000000000000000000000000000),((-16193774493826498478625842269:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((7038411461:ℚ)/10000000000),((7231078507:ℚ)/10000000000),((12706075153:ℚ)/17700000000),((24733235521:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3868375197:ℚ)/10000000000),((-31220960592472494285971202671143575879444514093999703:ℚ)/481357031250000000000000000000000000000000000000000000),((-5382941929428739913232820127:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7157416387:ℚ)/10000000000),((7350096003:ℚ)/10000000000),((90251580257:ℚ)/125800000000),((25090288009:ℚ)/30975000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3429543533:ℚ)/10000000000),((-393832445101177977800744241490230633317828164126751247:ℚ)/6075639379882812500000000000000000000000000000000000000),((-16103478616911147122940160621:ℚ)/44359680000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((7276413589:ℚ)/10000000000),((1897026847:ℚ)/2500000000),((91560549479:ℚ)/129600000000),((6451080541:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2928575533:ℚ)/10000000000),((-15324099983757632761164545919392171350531138693118215363:ℚ)/251942400000000000000000000000000000000000000000000000000),((-333574763364802336780184407:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7514386183:ℚ)/10000000000),((4745660949:ℚ)/5000000000),((94178248013:ℚ)/160000000000),((15756982847:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((375602677:ℚ)/2500000000),((-52441518706956224288407387263091656784106009968966577609:ℚ)/2400000000000000000000000000000000000000000000000000000000),((-73900993:ℚ)/204800000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((1883471401:ℚ)/2000000000),((6647545777:ℚ)/5000000000),((23022185411:ℚ)/44160000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((41814070399277405038707434574608273:ℚ)/10764582912000000000000000000000000000),((-73900993:ℚ)/204800000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC28
#check @N11Formalization.C450Source20GroupedC28.bound
#print axioms N11Formalization.C450Source20GroupedC28.valid0
#print axioms N11Formalization.C450Source20GroupedC28.valid1
#print axioms N11Formalization.C450Source20GroupedC28.valid2
#print axioms N11Formalization.C450Source20GroupedC28.valid3
#print axioms N11Formalization.C450Source20GroupedC28.valid4
#print axioms N11Formalization.C450Source20GroupedC28.valid5
#print axioms N11Formalization.C450Source20GroupedC28.valid6
#print axioms N11Formalization.C450Source20GroupedC28.valid7
#print axioms N11Formalization.C450Source20GroupedC28.valid8
#print axioms N11Formalization.C450Source20GroupedC28.valid9
#print axioms N11Formalization.C450Source20GroupedC28.valid10
#print axioms N11Formalization.C450Source20GroupedC28.valid11
#print axioms N11Formalization.C450Source20GroupedC28.bound
#print axioms N11Formalization.C450Source20GroupedC28.endpoint_checks
