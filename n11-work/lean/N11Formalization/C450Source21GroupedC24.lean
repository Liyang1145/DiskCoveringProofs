import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((2880584359:ℚ)/5000000000),((6307423289:ℚ)/10000000000),((8748030171:ℚ)/17800000000),((7907423289:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7104806027:ℚ)/10000000000),((2325462352679514152085403:ℚ)/158420000000000000000000000),((-5123622651591374363825627:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((311947379:ℚ)/500000000),((204566703:ℚ)/312500000),((2791631653:ℚ)/5530000000),((254566703:ℚ)/417187500),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((759732897:ℚ)/1250000000),((6514342082809810006226286454589476423670628635628003:ℚ)/1056952356250000000000000000000000000000000000000000000),((-15314897119035077082649:ℚ)/42304687500000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((1619423163:ℚ)/2500000000),((6784764663:ℚ)/10000000000),((14375962141:ℚ)/28600000000),((8384764663:ℚ)/13825000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5503759063:ℚ)/10000000000),((786661413599518617276500996307457959230018180182977811:ℚ)/146210350000000000000000000000000000000000000000000000000),((-831519403573774524653611:ℚ)/2280000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6716354401:ℚ)/10000000000),((3452025931:ℚ)/5000000000),((59174480807:ℚ)/116300000000),((4252025931:ℚ)/7150000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((974042401:ℚ)/2000000000),((4812228610282441695265907079582252270529931916051669657:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-1329343701650064773611507:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3417828303:ℚ)/5000000000),((7023321677:ℚ)/10000000000),((30004798121:ℚ)/59100000000),((8623321677:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4523361517:ℚ)/10000000000),((572405731015295812523906206487307816101070426976703591:ℚ)/322539173437500000000000000000000000000000000000000000000),((-5336197747095088565656323:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((6954940939:ℚ)/10000000000),((7142574939:ℚ)/10000000000),((60844586573:ℚ)/120100000000),((8742574939:ℚ)/14775000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2074907149:ℚ)/5000000000),((17594234733775630725166827359062418134399238343300300003:ℚ)/10827022506250000000000000000000000000000000000000000000000),((-16064375075042821278145081:ℚ)/43320000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((3537104127:ℚ)/5000000000),((726181243:ℚ)/1000000000),((30839728889:ℚ)/61000000000),((886181243:ℚ)/1501250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3741547661:ℚ)/10000000000),((2138279259615442013316181672453309629239893356644112351:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-53731568734518234618963:ℚ)/144400000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3596729677:ℚ)/5000000000),((7500242977:ℚ)/10000000000),((31257107739:ℚ)/62900000000),((9100242977:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1642802709:ℚ)/5000000000),((39534841894304184697876912145393029:ℚ)/9891025000000000000000000000000000000),((-5377196964451431316243723:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((7431915871:ℚ)/10000000000),((1934654663:ℚ)/2500000000),((64183411097:ℚ)/129600000000),((2334654663:ℚ)/3931250000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((84282077:ℚ)/400000000),((319783375490687917151350411319461577:ℚ)/83980800000000000000000000000000000000),((-357186361740989:ℚ)/950000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((958789497:ℚ)/1250000000),((1928824097:ℚ)/2000000000),((8231526479:ℚ)/20000000000),((2248824097:ℚ)/3240000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14929038689459529546207053221197113:ℚ)/500000000000000000000000000000000000),((-6065761:ℚ)/16000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((1196996391:ℚ)/1250000000),((672528387:ℚ)/500000000),((9898974737:ℚ)/27600000000),((752528387:ℚ)/1000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((21745933826876008439296627:ℚ)/380880000000000000000000000),((-6065761:ℚ)/16000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC24
#check @N11Formalization.C450Source21GroupedC24.bound
#print axioms N11Formalization.C450Source21GroupedC24.valid0
#print axioms N11Formalization.C450Source21GroupedC24.valid1
#print axioms N11Formalization.C450Source21GroupedC24.valid2
#print axioms N11Formalization.C450Source21GroupedC24.valid3
#print axioms N11Formalization.C450Source21GroupedC24.valid4
#print axioms N11Formalization.C450Source21GroupedC24.valid5
#print axioms N11Formalization.C450Source21GroupedC24.valid6
#print axioms N11Formalization.C450Source21GroupedC24.valid7
#print axioms N11Formalization.C450Source21GroupedC24.valid8
#print axioms N11Formalization.C450Source21GroupedC24.valid9
#print axioms N11Formalization.C450Source21GroupedC24.valid10
#print axioms N11Formalization.C450Source21GroupedC24.bound
#print axioms N11Formalization.C450Source21GroupedC24.endpoint_checks
