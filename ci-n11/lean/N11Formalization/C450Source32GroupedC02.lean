import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7222722249:ℚ)/10000000000),((7466499353:ℚ)/10000000000),((-18559498059:ℚ)/19840000000),((-40639055743:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((3164112923:ℚ)/10000000000),((180308511092958334371046585875176487325829:ℚ)/400428678262500000000000000000000000000000),((1540116830800222148499457159:ℚ)/1478656000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7341987089:ℚ)/10000000000),((948190259:ℚ)/1250000000),((-788190259:ℚ)/842500000),((-41473909623:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2613155769:ℚ)/10000000000),((1616326440736657807975409589373627203852233073689418870963:ℚ)/3596181630859375000000000000000000000000000000000000000000),((24209990990048792610454031:ℚ)/23104000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((466327051:ℚ)/625000000),((61121393:ℚ)/78125000),((-153364179:ℚ)/160937500),((-2644289357:ℚ)/3337500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1913879641:ℚ)/10000000000),((8621428308085757233798968490551435021442521262398127:ℚ)/18696964159011840820312500000000000000000000000000000),((536903521:ℚ)/512000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3849835521:ℚ)/5000000000),((8299467583:ℚ)/10000000000),((-7019467583:ℚ)/7120000000),((-21988848647:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((3763019745922881303348209174236899833570021735578478763617:ℚ)/7807632690000000000000000000000000000000000000000000000000),((536903521:ℚ)/512000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((8176359517:ℚ)/10000000000),((1850199679:ℚ)/2000000000),(-1:ℚ),((-47314516619:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((126469265416816999980615852943316892349537852638079112509:ℚ)/255091680000000000000000000000000000000000000000000000000),((536903521:ℚ)/512000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((9129139803:ℚ)/10000000000),((11153185977:ℚ)/10000000000),(-1:ℚ),((-53983978621:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((60330723727240772226611769976817714747262621024450033299:ℚ)/120000000000000000000000000000000000000000000000000000000),((536903521:ℚ)/512000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2206622147:ℚ)/2000000000),((7477876101:ℚ)/5000000000),(-1:ℚ),((-13462355029:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((280476325011956505896159530951620211:ℚ)/538229145600000000000000000000000000),((536903521:ℚ)/512000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC02
#check @N11Formalization.C450Source32GroupedC02.bound
#print axioms N11Formalization.C450Source32GroupedC02.valid0
#print axioms N11Formalization.C450Source32GroupedC02.valid1
#print axioms N11Formalization.C450Source32GroupedC02.valid2
#print axioms N11Formalization.C450Source32GroupedC02.valid3
#print axioms N11Formalization.C450Source32GroupedC02.valid4
#print axioms N11Formalization.C450Source32GroupedC02.valid5
#print axioms N11Formalization.C450Source32GroupedC02.valid6
#print axioms N11Formalization.C450Source32GroupedC02.bound
#print axioms N11Formalization.C450Source32GroupedC02.endpoint_checks
