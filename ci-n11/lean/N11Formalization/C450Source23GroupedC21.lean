import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((73354859:ℚ)/125000000),((1603816037:ℚ)/2500000000),((115354859:ℚ)/333750000),((2307816037:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6885685269:ℚ)/10000000000),((11055347180993009543124905911055995499:ℚ)/181228424448000000000000000000000000000),((-7925389507957859682797183:ℚ)/23104000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((126949009:ℚ)/200000000),((6654485143:ℚ)/10000000000),((194149009:ℚ)/553000000),((3156828381:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1164633221:ℚ)/2000000000),((9031280722379047936005747498064117156702894898230597486027:ℚ)/172468691936800000000000000000000000000000000000000000000000),((-132317784205911796306884743:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((329338477:ℚ)/500000000),((6774051589:ℚ)/10000000000),((497338477:ℚ)/1406250000),((9590051589:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5222876891:ℚ)/10000000000),((1058567228949818414842322161169993277082838310620868181:ℚ)/21743019900000000000000000000000000000000000000000000000),((-7108259093932958352437413:ℚ)/19456000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((3353191247:ℚ)/5000000000),((1723397661:ℚ)/2500000000),((5033191247:ℚ)/14300000000),((2427397661:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4898174661:ℚ)/10000000000),((7062998025083796126959280507369442403245961410260189157:ℚ)/145812606811523437500000000000000000000000000000000000000),((-25529219685358867436898541:ℚ)/69312000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6825966481:ℚ)/10000000000),((1753275917:ℚ)/2500000000),((10185966481:ℚ)/29075000000),((2457275917:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4552446559:ℚ)/10000000000),((433646403853946357540027615735356513277461536344297548681:ℚ)/8989072131325000000000000000000000000000000000000000000000),((-8577824480007602208303823:ℚ)/23104000000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((347276147:ℚ)/500000000),((1783147983:ℚ)/2500000000),((515276147:ℚ)/1477500000),((2487147983:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4180444317:ℚ)/10000000000),((430056411912691212578299432085235168984326666928785538043:ℚ)/8942581336424267578125000000000000000000000000000000000000),((-25935937995064088978216869:ℚ)/69312000000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((220782913:ℚ)/312500000),((7252056627:ℚ)/10000000000),((325782913:ℚ)/938281250),((10068056627:ℚ)/23640000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((943592421:ℚ)/2500000000),((1428731851343521279058402569699092315164502055401511451719709:ℚ)/29774772883547100000000000000000000000000000000000000000000000),((-418185869051350268569610509:ℚ)/1108992000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((898069821:ℚ)/1250000000),((1474299773:ℚ)/2000000000),((1318069821:ℚ)/3812500000),((2037499773:ℚ)/4804000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((830427221:ℚ)/2500000000),((30889592940572910807111288943945976250695759092848740091:ℚ)/644597611932100000000000000000000000000000000000000000000),((-5618242805093304602404303:ℚ)/14786560000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3652020087:ℚ)/5000000000),((7610320089:ℚ)/10000000000),((144108651:ℚ)/425000000),((10426320089:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1399955143:ℚ)/5000000000),((82675742946166050110100913504169420078406415501202362743:ℚ)/1639937725000000000000000000000000000000000000000000000000),((-92745060341420621:ℚ)/243200000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((3771468253:ℚ)/5000000000),((7849063223:ℚ)/10000000000),((5451468253:ℚ)/16200000000),((10665063223:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1226194867:ℚ)/10000000000),((17920948437293612587562473324861466408895904372728000451:ℚ)/355720823100000000000000000000000000000000000000000000000),((-94886560865299599:ℚ)/243200000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((7781750273:ℚ)/10000000000),((9756870123:ℚ)/10000000000),((11141750273:ℚ)/40000000000),((12572870123:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((128973294958553058505119938623021150781771266164953909:ℚ)/1700611200000000000000000000000000000000000000000000000),((-50209519:ℚ)/128000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((4844999999:ℚ)/5000000000),((6783005881:ℚ)/5000000000),((6524999999:ℚ)/27600000000),((8191005881:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((432798574277054331248479:ℚ)/3967500000000000000000000),((-50209519:ℚ)/128000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source23 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source23 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC21
#check @N11Formalization.C450Source23GroupedC21.bound
#print axioms N11Formalization.C450Source23GroupedC21.valid0
#print axioms N11Formalization.C450Source23GroupedC21.valid1
#print axioms N11Formalization.C450Source23GroupedC21.valid2
#print axioms N11Formalization.C450Source23GroupedC21.valid3
#print axioms N11Formalization.C450Source23GroupedC21.valid4
#print axioms N11Formalization.C450Source23GroupedC21.valid5
#print axioms N11Formalization.C450Source23GroupedC21.valid6
#print axioms N11Formalization.C450Source23GroupedC21.valid7
#print axioms N11Formalization.C450Source23GroupedC21.valid8
#print axioms N11Formalization.C450Source23GroupedC21.valid9
#print axioms N11Formalization.C450Source23GroupedC21.valid10
#print axioms N11Formalization.C450Source23GroupedC21.valid11
#print axioms N11Formalization.C450Source23GroupedC21.bound
#print axioms N11Formalization.C450Source23GroupedC21.endpoint_checks
