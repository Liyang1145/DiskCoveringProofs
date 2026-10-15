import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((1230648609:ℚ)/2000000000),((417575469:ℚ)/625000000),((100808177:ℚ)/2225000000),((19:ℚ)/155),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3136312669:ℚ)/5000000000),((1406304627530163131050766989:ℚ)/18435508671875000000000000000),((-30184849392496159:ℚ)/194560000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6631592943:ℚ)/10000000000),((692004773:ℚ)/1000000000),((459995227:ℚ)/11060000000),((152:ℚ)/1335),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5103409381:ℚ)/10000000000),((642273687809247644069721974653551849220997:ℚ)/8731227529300500000000000000000000000000000),((-165438316128451793:ℚ)/972800000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((1374118717:ℚ)/2000000000),((1407886723:ℚ)/2000000000),((896113277:ℚ)/22500000000),((304:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2208509211:ℚ)/5000000000),((1108406184060622444568462332599193134133801:ℚ)/15288060867187500000000000000000000000000000),((-34538012379396867:ℚ)/194560000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((1398011109:ℚ)/2000000000),((3579399107:ℚ)/5000000000),((2180600893:ℚ)/57200000000),((608:ℚ)/5625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4033681553:ℚ)/10000000000),((3360612689929233664163793259547766509791583:ℚ)/46585378125000000000000000000000000000000000),((-35262954166733659:ℚ)/194560000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((142189873:ℚ)/200000000),((7278142581:ℚ)/10000000000),((4241857419:ℚ)/116300000000),((76:ℚ)/715),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3612388499:ℚ)/10000000000),((5325394994033756624010351316509075419451983:ℚ)/74159845083431250000000000000000000000000000),((-3598775119262223:ℚ)/19456000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7228909083:ℚ)/10000000000),((73974677:ℚ)/100000000),((41225323:ℚ)/1182000000),((608:ℚ)/5815),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1568922673:ℚ)/5000000000),((163712624355185310110975166963521297210047:ℚ)/2289300822124612500000000000000000000000000),((-183562053179840933:ℚ)/972800000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((1837075737:ℚ)/2500000000),((1909015957:ℚ)/2500000000),((970984043:ℚ)/30500000000),((304:ℚ)/2955),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1290396561:ℚ)/5000000000),((51432017031240441769889071732872815362754389:ℚ)/720100958616562500000000000000000000000000000),((-46796173995342887:ℚ)/243200000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7587030049:ℚ)/10000000000),((8113062037:ℚ)/10000000000),((3406937963:ℚ)/129600000000),((152:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((146076099:ℚ)/2500000000),((169832739865038405290605928795761547402081:ℚ)/2382755745600000000000000000000000000000000),((-10233060104330821:ℚ)/51200000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((4032133429:ℚ)/5000000000),((2504786959:ℚ)/2500000000),((375213041:ℚ)/40000000000),((38:ℚ)/405),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((57374778414411020925563997455875426525523:ℚ)/797161500000000000000000000000000000000000),((-25634431:ℚ)/128000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((4985539087:ℚ)/5000000000),((6913319223:ℚ)/5000000000),((-1153319223:ℚ)/80000000000),((19:ℚ)/250),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6340448004720681:ℚ)/80000000000000000),((-25634431:ℚ)/128000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC16
#check @N11Formalization.C450Source20GroupedC16.bound
#print axioms N11Formalization.C450Source20GroupedC16.valid0
#print axioms N11Formalization.C450Source20GroupedC16.valid1
#print axioms N11Formalization.C450Source20GroupedC16.valid2
#print axioms N11Formalization.C450Source20GroupedC16.valid3
#print axioms N11Formalization.C450Source20GroupedC16.valid4
#print axioms N11Formalization.C450Source20GroupedC16.valid5
#print axioms N11Formalization.C450Source20GroupedC16.valid6
#print axioms N11Formalization.C450Source20GroupedC16.valid7
#print axioms N11Formalization.C450Source20GroupedC16.valid8
#print axioms N11Formalization.C450Source20GroupedC16.valid9
#print axioms N11Formalization.C450Source20GroupedC16.bound
#print axioms N11Formalization.C450Source20GroupedC16.endpoint_checks
