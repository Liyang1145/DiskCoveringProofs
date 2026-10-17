import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((2939093717:ℚ)/5000000000),((3205489259:ℚ)/5000000000),((8351218673:ℚ)/17800000000),((3805489259:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((858171249:ℚ)/1250000000),((134571844710341314334573:ℚ)/19802500000000000000000000),((-2502889659535153871841:ℚ)/10000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3177372273:ℚ)/5000000000),((6649133831:ℚ)/10000000000),((3817372273:ℚ)/7900000000),((7849133831:ℚ)/13350000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5805691657:ℚ)/10000000000),((290078779646349678716550703171673:ℚ)/117018750000000000000000000000000000),((-193510527021126710582299:ℚ)/760000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6592942493:ℚ)/10000000000),((6887245441:ℚ)/10000000000),((4239276727:ℚ)/8800000000),((8087245441:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5206572191:ℚ)/10000000000),((97042867855786333533534761472617:ℚ)/48400000000000000000000000000000000),((-195031399597639653853579:ℚ)/760000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6831093883:ℚ)/10000000000),((7006286203:ℚ)/10000000000),((56777657181:ℚ)/116300000000),((8206286203:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4537078203:ℚ)/10000000000),((3315726408913876273543683424225303:ℚ)/12680334375000000000000000000000000000),((-196668577336478370314131:ℚ)/760000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((434384597:ℚ)/625000000),((445332349:ℚ)/625000000),((3600692179:ℚ)/7387500000),((520332349:ℚ)/908593750),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2082705373:ℚ)/5000000000),((728803341644522595521936685151:ℚ)/5684912109375000000000000000000000),((-771185473298547278459:ℚ)/2968750000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1767300807:ℚ)/2500000000),((7244340031:ℚ)/10000000000),((14611105649:ℚ)/30025000000),((8444340031:ℚ)/14775000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3759525161:ℚ)/10000000000),((21713978030845018655656379043317:ℚ)/1690313671875000000000000000000000000),((-198176214379307984981899:ℚ)/760000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((7188243387:ℚ)/10000000000),((1840838491:ℚ)/2500000000),((59277703709:ℚ)/122000000000),((2140838491:ℚ)/3753125000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1653404271:ℚ)/5000000000),((-795208999029251612694635411201881:ℚ)/9302500000000000000000000000000000000),((-12432923782099985281979:ℚ)/47500000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7307274477:ℚ)/10000000000),((233823743:ℚ)/312500000),((8587274477:ℚ)/17700000000),((271323743:ℚ)/476562500),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2784469119:ℚ)/10000000000),((-16411759251362623243476256096981:ℚ)/97903125000000000000000000000000000),((-1559962366352500344403:ℚ)/5937500000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1485259383:ℚ)/2000000000),((1900339459:ℚ)/2500000000),((12188815681:ℚ)/25160000000),((2200339459:ℚ)/3871875000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((8568457:ℚ)/40000000),((-2897898338589330177878584149717:ℚ)/12363781250000000000000000000000000),((-160338367139629:ℚ)/608000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7545311097:ℚ)/10000000000),((7839332071:ℚ)/10000000000),((61777177679:ℚ)/129600000000),((9039332071:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((300094883:ℚ)/2500000000),((9708006021793862764787765122280647:ℚ)/10497600000000000000000000000000000000),((-805210251960611:ℚ)/3040000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((7783316149:ℚ)/10000000000),((1948462641:ℚ)/2000000000),((63443213043:ℚ)/160000000000),((729487547:ℚ)/1080000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((163802318488989146815242776654622269:ℚ)/12000000000000000000000000000000000000),((-2123229:ℚ)/8000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((9686490873:ℚ)/10000000000),((6772904721:ℚ)/5000000000),((3337627657:ℚ)/9600000000),((7372904721:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((152916169137891818633213:ℚ)/5760000000000000000000000),((-2123229:ℚ)/8000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC24
#check @N11Formalization.C450Source16GroupedC24.bound
#print axioms N11Formalization.C450Source16GroupedC24.valid0
#print axioms N11Formalization.C450Source16GroupedC24.valid1
#print axioms N11Formalization.C450Source16GroupedC24.valid2
#print axioms N11Formalization.C450Source16GroupedC24.valid3
#print axioms N11Formalization.C450Source16GroupedC24.valid4
#print axioms N11Formalization.C450Source16GroupedC24.valid5
#print axioms N11Formalization.C450Source16GroupedC24.valid6
#print axioms N11Formalization.C450Source16GroupedC24.valid7
#print axioms N11Formalization.C450Source16GroupedC24.valid8
#print axioms N11Formalization.C450Source16GroupedC24.valid9
#print axioms N11Formalization.C450Source16GroupedC24.valid10
#print axioms N11Formalization.C450Source16GroupedC24.valid11
#print axioms N11Formalization.C450Source16GroupedC24.bound
#print axioms N11Formalization.C450Source16GroupedC24.endpoint_checks
