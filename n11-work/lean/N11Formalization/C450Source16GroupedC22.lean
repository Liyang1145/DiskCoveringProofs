import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((2974999999:ℚ)/5000000000),((6478769611:ℚ)/10000000000),((1290333333:ℚ)/3560000000),((24236308833:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6714912707:ℚ)/10000000000),((73356870123819456797924194199130214483:ℚ)/3020473740800000000000000000000000000000),((-21452581936297192556781263:ℚ)/97280000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((100418523:ℚ)/156250000),((3358500627:ℚ)/5000000000),((128418523:ℚ)/345625000),((4158500627:ℚ)/8900000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1407631499:ℚ)/2500000000),((1046237694615455333352650273712234805886452137287322165457:ℚ)/50527937090859375000000000000000000000000000000000000000000),((-5518405305814281957957087:ℚ)/24320000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((6665085719:ℚ)/10000000000),((6836098459:ℚ)/10000000000),((939676191:ℚ)/2500000000),((25308295377:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((626556339:ℚ)/1250000000),((36154739375256275659230947122708151312243806497524447:ℚ)/1887414921875000000000000000000000000000000000000000000),((-22383647109195148506799343:ℚ)/97280000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((424013467:ℚ)/625000000),((6955184081:ℚ)/10000000000),((48728497:ℚ)/130000000),((2851728027:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4675838401:ℚ)/10000000000),((61055168350406527633779307269084314693093618127638371:ℚ)/3223419189453125000000000000000000000000000000000000000),((-22531367960973474200762983:ℚ)/97280000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((6903332551:ℚ)/10000000000),((7074258693:ℚ)/10000000000),((8695332551:ℚ)/23260000000),((26022776079:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4315148021:ℚ)/10000000000),((7130615439139184440959662591040268430041158746181353553699:ℚ)/380306897863750000000000000000000000000000000000000000000000),((-22678826261165235664438447:ℚ)/97280000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7022437583:ℚ)/10000000000),((7193322827:ℚ)/10000000000),((2938145861:ℚ)/7880000000),((26379968481:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((980928083:ℚ)/2500000000),((2769222847965061062083179453356058684213548063107717339577:ℚ)/149043022273737792968750000000000000000000000000000000000000),((-1201369624435446981685973:ℚ)/5120000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((446345697:ℚ)/625000000),((914047123:ℚ)/1250000000),((558345697:ℚ)/1501250000),((1114047123:ℚ)/2462500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((872792309:ℚ)/2500000000),((31013971828780218598094840822148117887490668304993096579:ℚ)/1682692514125518798828125000000000000000000000000000000000),((-358952477591493872709087:ℚ)/1520000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((1815153451:ℚ)/2500000000),((116115963:ℚ)/156250000),((2263153451:ℚ)/6100000000),((423347889:ℚ)/938281250),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((374968561:ℚ)/1250000000),((562544803701144161382180587437288176070001000363981059:ℚ)/30736809345822334289550781250000000000000000000000000000),((-2822220960681537969341:ℚ)/11875000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7379686053:ℚ)/10000000000),((7669484131:ℚ)/10000000000),((9171686053:ℚ)/25160000000),((27808452393:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1206851843:ℚ)/5000000000),((33463934343071504222412093499252223995584153826771294593169:ℚ)/1753964644941406250000000000000000000000000000000000000000000),((-11629761132051297:ℚ)/48640000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((1523560247:ℚ)/2000000000),((1581502707:ℚ)/2000000000),((1881960247:ℚ)/5184000000),((5704508121:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1133254180758181430416438701278706786668984304119276929:ℚ)/60027888898125000000000000000000000000000000000000000000),((-30998851:ℚ)/128000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7855880209:ℚ)/10000000000),((9810841229:ℚ)/10000000000),((9647880209:ℚ)/32000000000),((3803613743:ℚ)/7200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((13222837431357185238279485358928661:ℚ)/480000000000000000000000000000000000),((-30998851:ℚ)/128000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((1951903853:ℚ)/2000000000),((6807371737:ℚ)/5000000000),((2310303853:ℚ)/8832000000),((22822115211:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((189066722062381015111733:ℚ)/4875264000000000000000000),((-30998851:ℚ)/128000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC22
#check @N11Formalization.C450Source16GroupedC22.bound
#print axioms N11Formalization.C450Source16GroupedC22.valid0
#print axioms N11Formalization.C450Source16GroupedC22.valid1
#print axioms N11Formalization.C450Source16GroupedC22.valid2
#print axioms N11Formalization.C450Source16GroupedC22.valid3
#print axioms N11Formalization.C450Source16GroupedC22.valid4
#print axioms N11Formalization.C450Source16GroupedC22.valid5
#print axioms N11Formalization.C450Source16GroupedC22.valid6
#print axioms N11Formalization.C450Source16GroupedC22.valid7
#print axioms N11Formalization.C450Source16GroupedC22.valid8
#print axioms N11Formalization.C450Source16GroupedC22.valid9
#print axioms N11Formalization.C450Source16GroupedC22.valid10
#print axioms N11Formalization.C450Source16GroupedC22.valid11
#print axioms N11Formalization.C450Source16GroupedC22.bound
#print axioms N11Formalization.C450Source16GroupedC22.endpoint_checks
