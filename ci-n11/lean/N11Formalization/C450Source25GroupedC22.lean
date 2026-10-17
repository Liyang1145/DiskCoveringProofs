import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((1443949151:ℚ)/2500000000),((791255431:ℚ)/1250000000),((726649717:ℚ)/1780000000),((3333766293:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1768810973:ℚ)/2500000000),((2010195209734867514861:ℚ)/99012500000000000000000),((-2190223971364587017509051:ℚ)/5776000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1563852037:ℚ)/2500000000),((32847669:ℚ)/50000000),((328550291:ℚ)/790000000),((45647669:ℚ)/89000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6039831477:ℚ)/10000000000),((1766763737612726661736637528273:ℚ)/195031250000000000000000000000000),((-3632630803279938992851:ℚ)/9241600000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((6494973101:ℚ)/10000000000),((6689227947:ℚ)/10000000000),((1048774789:ℚ)/2500000000),((27747683841:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((34125809:ℚ)/62500000),((8308648973920674183454430458441:ℚ)/1953125000000000000000000000000000),((-147847342332835065139348819:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((1653675653:ℚ)/2500000000),((680889037:ℚ)/1000000000),((2389675653:ℚ)/5720000000),((936889037:ℚ)/1875000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1029744621:ℚ)/2000000000),((1184910833900475116756706004296370582960734610255417091:ℚ)/280824279785156250000000000000000000000000000000000000000),((-1487289065284554605039779:ℚ)/3696640000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6734399197:ℚ)/10000000000),((6928522647:ℚ)/10000000000),((9678399197:ℚ)/23260000000),((28465567941:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((301202043:ℚ)/625000000),((1673669839566329267411969129100028731282633427745172874103169:ℚ)/395519173778300000000000000000000000000000000000000000000000000),((-149596666789289468758302619:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3427032247:ℚ)/5000000000),((3524063127:ℚ)/5000000000),((1633010749:ℚ)/3940000000),((14412189381:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4467624783:ℚ)/10000000000),((6390354790405273240310430495194764423469417002812789723441:ℚ)/1490430222737377929687500000000000000000000000000000000000000),((-37612661506074070714006939:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((1743425009:ℚ)/2500000000),((7167702569:ℚ)/10000000000),((2479425009:ℚ)/6005000000),((9727702569:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4088160589:ℚ)/10000000000),((302264121206057380026750634809323146436974591480733499111789:ℚ)/68923085378581250000000000000000000000000000000000000000000000),((-151290865693239949870273051:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((3546653627:ℚ)/5000000000),((3643626443:ℚ)/5000000000),((5018653627:ℚ)/12200000000),((14770879329:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3672175789:ℚ)/10000000000),((2847550152831270233005116142908352161289307914045633632269:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-38029336451802617223507859:ℚ)/92416000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1803221873:ℚ)/2500000000),((3763140149:ℚ)/5000000000),((2539221873:ℚ)/6290000000),((15129420447:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((400680039:ℚ)/1250000000),((149386850038230050568026622115174989594560542254757570909403:ℚ)/17539646449414062500000000000000000000000000000000000000000000),((-38021457156151237383027091:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((372598599:ℚ)/500000000),((7765217323:ℚ)/10000000000),((519798599:ℚ)/1296000000),((30975651969:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1976913229:ℚ)/10000000000),((90143678941878611030713112313179535142148058422672602463861:ℚ)/10204741112681250000000000000000000000000000000000000000000000),((-5093572060257529:ℚ)/12160000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7690962673:ℚ)/10000000000),((4837119811:ℚ)/5000000000),((10634962673:ℚ)/32000000000),((226559993:ℚ)/400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3846148408246941680887288509654791:ℚ)/80000000000000000000000000000000000),((-54321089:ℚ)/128000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9600321277:ℚ)/10000000000),((1685600041:ℚ)/1250000000),((12544321277:ℚ)/44160000000),((6016800123:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5687386126697377887971221:ℚ)/60940800000000000000000000),((-54321089:ℚ)/128000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC22
#check @N11Formalization.C450Source25GroupedC22.bound
#print axioms N11Formalization.C450Source25GroupedC22.valid0
#print axioms N11Formalization.C450Source25GroupedC22.valid1
#print axioms N11Formalization.C450Source25GroupedC22.valid2
#print axioms N11Formalization.C450Source25GroupedC22.valid3
#print axioms N11Formalization.C450Source25GroupedC22.valid4
#print axioms N11Formalization.C450Source25GroupedC22.valid5
#print axioms N11Formalization.C450Source25GroupedC22.valid6
#print axioms N11Formalization.C450Source25GroupedC22.valid7
#print axioms N11Formalization.C450Source25GroupedC22.valid8
#print axioms N11Formalization.C450Source25GroupedC22.valid9
#print axioms N11Formalization.C450Source25GroupedC22.valid10
#print axioms N11Formalization.C450Source25GroupedC22.valid11
#print axioms N11Formalization.C450Source25GroupedC22.bound
#print axioms N11Formalization.C450Source25GroupedC22.endpoint_checks
