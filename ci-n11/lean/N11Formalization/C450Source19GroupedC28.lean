import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((705210327:ℚ)/1250000000),((3094604747:ℚ)/5000000000),((9117313597:ℚ)/13350000000),((10723814241:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((917825233:ℚ)/1250000000),((-27578014025287386479518572326896997:ℚ)/594817593750000000000000000000000000),((-646924890133294891221746727:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6117989559:ℚ)/10000000000),((3213669779:ℚ)/5000000000),((11168269307:ℚ)/15800000000),((3693669779:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1270246349:ℚ)/2000000000),((-4191613080189930052907708429087771024790292943141532803:ℚ)/73955850000000000000000000000000000000000000000000000000),((-644079229025522224757936823:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6356075421:ℚ)/10000000000),((666542761:ℚ)/1000000000),((80796829631:ℚ)/114400000000),((2287628283:ℚ)/2765000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5802498261:ℚ)/10000000000),((-533247389903796082505306013286073215093009708230096512253:ℚ)/9357462400000000000000000000000000000000000000000000000000),((-25647440941853344457643663:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1648530557:ℚ)/2500000000),((3392228587:ℚ)/5000000000),((20853836127:ℚ)/29075000000),((11616685761:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((325215679:ℚ)/625000000),((-2361161692231412258937509257343971347621501464288002821:ℚ)/38404241870117187500000000000000000000000000000000000000),((-639721583648090299695042407:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6713132187:ℚ)/10000000000),((6903477719:ℚ)/10000000000),((84724454057:ℚ)/118200000000),((23590433157:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4879263663:ℚ)/10000000000),((-476015023832153228519141234211048787129178759820890523737:ℚ)/7740940162500000000000000000000000000000000000000000000000),((-2552980993801757616321335183:ℚ)/7393280000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6832133763:ℚ)/10000000000),((1755622419:ℚ)/2500000000),((86033471393:ℚ)/120100000000),((1995622419:ℚ)/2462500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4533955461:ℚ)/10000000000),((-1997444845875098472806385503815632817641571709400762698057:ℚ)/32481067518750000000000000000000000000000000000000000000000),((-477567761453487632729862949:ℚ)/1386240000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6951127353:ℚ)/10000000000),((892686681:ℚ)/1250000000),((87342400883:ℚ)/122000000000),((3038060043:ℚ)/3753125000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((260140171:ℚ)/625000000),((-697849114445042106890962828564526216067503725694222595249:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-119110665301677700388900749:ℚ)/346560000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3535056667:ℚ)/5000000000),((1815122353:ℚ)/2500000000),((14775207779:ℚ)/20650000000),((6165367059:ℚ)/7625000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1878131129:ℚ)/5000000000),((-845828501382234342120329027629798115116004216001494313:ℚ)/13758788476562500000000000000000000000000000000000000000),((-158436211282620504253294527:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7189092057:ℚ)/10000000000),((1844869481:ℚ)/2500000000),((89960012627:ℚ)/125800000000),((2084869481:ℚ)/2581250000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((660673519:ℚ)/2000000000),((-746739610304434671135059508621819826895462144687257769:ℚ)/12151278759765625000000000000000000000000000000000000000),((-158055225905210516001754383:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((7308063851:ℚ)/10000000000),((1904358477:ℚ)/2500000000),((10140966929:ℚ)/14400000000),((6433075431:ℚ)/7862500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1390343911:ℚ)/5000000000),((-1475911271801890720499349578131343632598851152253323:ℚ)/25600000000000000000000000000000000000000000000000000),((-174339293:ℚ)/512000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((3772993939:ℚ)/5000000000),((9520300373:ℚ)/10000000000),((46942933329:ℚ)/80000000000),((10480300373:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((596460061:ℚ)/5000000000),((-4096615118061311794215488162585957609973404656312851987:ℚ)/200000000000000000000000000000000000000000000000000000000),((-174339293:ℚ)/512000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((236216339:ℚ)/250000000),((6661831127:ℚ)/5000000000),((956793243:ℚ)/1840000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6348443255962394877719360750877:ℚ)/1557376000000000000000000000000000),((-174339293:ℚ)/512000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC28
#check @N11Formalization.C450Source19GroupedC28.bound
#print axioms N11Formalization.C450Source19GroupedC28.valid0
#print axioms N11Formalization.C450Source19GroupedC28.valid1
#print axioms N11Formalization.C450Source19GroupedC28.valid2
#print axioms N11Formalization.C450Source19GroupedC28.valid3
#print axioms N11Formalization.C450Source19GroupedC28.valid4
#print axioms N11Formalization.C450Source19GroupedC28.valid5
#print axioms N11Formalization.C450Source19GroupedC28.valid6
#print axioms N11Formalization.C450Source19GroupedC28.valid7
#print axioms N11Formalization.C450Source19GroupedC28.valid8
#print axioms N11Formalization.C450Source19GroupedC28.valid9
#print axioms N11Formalization.C450Source19GroupedC28.valid10
#print axioms N11Formalization.C450Source19GroupedC28.valid11
#print axioms N11Formalization.C450Source19GroupedC28.bound
#print axioms N11Formalization.C450Source19GroupedC28.endpoint_checks
