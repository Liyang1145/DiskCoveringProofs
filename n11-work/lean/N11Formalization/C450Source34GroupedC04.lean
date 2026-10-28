import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7101921521:ℚ)/10000000000),((7344218891:ℚ)/10000000000),((-74994845583:ℚ)/99200000000),((-5341921521:ℚ)/8425000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((182023713:ℚ)/500000000),((8272234766737758338026137660589924904823:ℚ)/18390057816500000000000000000000000000000),((10881288488403015075590145229:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((3610886517:ℚ)/5000000000),((373192139:ℚ)/500000000),((-3827497807:ℚ)/5055000000),((-8192659551:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1584062199:ℚ)/5000000000),((42473112962819672896668250434548138627931923544822006342847:ℚ)/94680719499969482421875000000000000000000000000000000000000),((8161912703583110094640225423:ℚ)/11089920000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7341583363:ℚ)/10000000000),((303337387:ℚ)/400000000),((-3124186031:ℚ)/4120000000),((-16744750089:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2615211163:ℚ)/10000000000),((2090380645580989898135301643692055915240306413800675560217:ℚ)/4671549898239517211914062500000000000000000000000000000000),((10883442208698536109257154261:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((233167337:ℚ)/312500000),((7702996307:ℚ)/10000000000),((-79658951991:ℚ)/104900000000),((-178167337:ℚ)/278125000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((478258947:ℚ)/2500000000),((66057116509197593532331891595100194582057289946292187621:ℚ)/147962301744270324707031250000000000000000000000000000000),((10609150554608374516038461:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7581089409:ℚ)/10000000000),((4090485371:ℚ)/5000000000),((-42936309823:ℚ)/53400000000),((-17463268227:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((14111749:ℚ)/200000000),((1647548649219231287203076596295682991274532863993733693367217:ℚ)/3474396547050000000000000000000000000000000000000000000000000),((32521459480865679617320330567:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((4029848587:ℚ)/5000000000),((570991567:ℚ)/625000000),((-6142890371:ℚ)/7150000000),((-1049949529:ℚ)/1800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((281410186036270695565862387944074447411112324020115738619:ℚ)/559024537500000000000000000000000000000000000000000000000),((750469199:ℚ)/1024000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((563476973:ℚ)/625000000),((2208569771:ℚ)/2000000000),((-24615407023:ℚ)/25920000000),((-1360430919:ℚ)/2500000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((817542215247769246245039572806981609776971949795922669:ℚ)/1483154296875000000000000000000000000000000000000000000),((750469199:ℚ)/1024000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10924095541:ℚ)/10000000000),((2970205763:ℚ)/2000000000),(-1:ℚ),((-9164095541:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((74687:ℚ)/125000),((750469199:ℚ)/1024000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_8
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_8
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7]
theorem packet_count : packets.length = 8 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC04
#check @N11Formalization.C450Source34GroupedC04.bound
#print axioms N11Formalization.C450Source34GroupedC04.valid0
#print axioms N11Formalization.C450Source34GroupedC04.valid1
#print axioms N11Formalization.C450Source34GroupedC04.valid2
#print axioms N11Formalization.C450Source34GroupedC04.valid3
#print axioms N11Formalization.C450Source34GroupedC04.valid4
#print axioms N11Formalization.C450Source34GroupedC04.valid5
#print axioms N11Formalization.C450Source34GroupedC04.valid6
#print axioms N11Formalization.C450Source34GroupedC04.valid7
#print axioms N11Formalization.C450Source34GroupedC04.bound
#print axioms N11Formalization.C450Source34GroupedC04.endpoint_checks
