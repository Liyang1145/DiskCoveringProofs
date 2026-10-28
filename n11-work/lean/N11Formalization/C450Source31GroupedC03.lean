import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1776377783:ℚ)/2500000000),((3670993547:ℚ)/5000000000),((-21056954829:ℚ)/24800000000),((-18292911179:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((906796489:ℚ)/2500000000),((1541121689492934903372809483907498706511:ℚ)/3707672946875000000000000000000000000000),((394407118495687669200646717:ℚ)/462080000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7224960329:ℚ)/10000000000),((7401612279:ℚ)/10000000000),((-42531285953:ℚ)/50550000000),((-74724484277:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1577317533:ℚ)/5000000000),((171865384700487289395992149339894509824092915247813556654389:ℚ)/419710870367724609375000000000000000000000000000000000000000),((4377919080689284040631853:ℚ)/5120000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((7284675079:ℚ)/10000000000),((7461232821:ℚ)/10000000000),((-42948629747:ℚ)/51025000000),((-75500776027:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((180667693:ℚ)/625000000),((228127428055090345945252248858168359672188798382272990059761:ℚ)/557563951750000000000000000000000000000000000000000000000000),((1583230867856561255412473533:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7344383509:ℚ)/10000000000),((7580460481:ℚ)/10000000000),((-43783223367:ℚ)/51500000000),((-76276985617:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2600922781:ℚ)/10000000000),((1201912400424021702934459062573263284422324884169003969093:ℚ)/2902710616381835937500000000000000000000000000000000000000),((1588840345979615458465486693:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((932972763:ℚ)/1250000000),((7699671047:ℚ)/10000000000),((-44617697329:ℚ)/52450000000),((-3242881973:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((948082439:ℚ)/5000000000),((238816602511858772840844319320036589029433239623764861511:ℚ)/577744125781250000000000000000000000000000000000000000000),((110094211:ℚ)/128000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7583157439:ℚ)/10000000000),((4088179761:ℚ)/5000000000),((-23977258327:ℚ)/26700000000),((-79381046707:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((332937343:ℚ)/5000000000),((1103303887012455998018536665398922748751965222435481602100203:ℚ)/2498442460800000000000000000000000000000000000000000000000000),((110094211:ℚ)/128000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((8060449579:ℚ)/10000000000),((285285619:ℚ)/312500000),((-131307641:ℚ)/137500000),((-85585844527:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((652692539495002851152339168526306416036508293872739589677:ℚ)/1385683200000000000000000000000000000000000000000000000000),((110094211:ℚ)/128000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((901422263:ℚ)/1000000000),((551655537:ℚ)/500000000),(-1:ℚ),((-9798489419:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((792018997679762026734715207330734200025669486920854273:ℚ)/1600000000000000000000000000000000000000000000000000000),((110094211:ℚ)/128000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((1091960911:ℚ)/1000000000),((14837766319:ℚ)/10000000000),(-1:ℚ),((-12275491843:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((152572732232412031256776306560352123:ℚ)/299016192000000000000000000000000000),((110094211:ℚ)/128000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
private theorem node0_2 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source31 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_9
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_9
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8]
theorem packet_count : packets.length = 9 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC03
#check @N11Formalization.C450Source31GroupedC03.bound
#print axioms N11Formalization.C450Source31GroupedC03.valid0
#print axioms N11Formalization.C450Source31GroupedC03.valid1
#print axioms N11Formalization.C450Source31GroupedC03.valid2
#print axioms N11Formalization.C450Source31GroupedC03.valid3
#print axioms N11Formalization.C450Source31GroupedC03.valid4
#print axioms N11Formalization.C450Source31GroupedC03.valid5
#print axioms N11Formalization.C450Source31GroupedC03.valid6
#print axioms N11Formalization.C450Source31GroupedC03.valid7
#print axioms N11Formalization.C450Source31GroupedC03.valid8
#print axioms N11Formalization.C450Source31GroupedC03.bound
#print axioms N11Formalization.C450Source31GroupedC03.endpoint_checks
