import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7048983653:ℚ)/10000000000),((1821191289:ℚ)/2500000000),((-18875486757:ℚ)/24800000000),((-16186950959:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((3831333663:ℚ)/10000000000),((10212007380785859770169316325205247151:ℚ)/25026792391406250000000000000000000000),((5283873915743947117912998841:ℚ)/7393280000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7168700147:ℚ)/10000000000),((3672264431:ℚ)/5000000000),((-38139437603:ℚ)/50550000000),((-1272776957:ℚ)/1962500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((846278729:ℚ)/2500000000),((80153091228262627488840449586842227908529662789893577:ℚ)/198998098907470703125000000000000000000000000000000000),((5279394910015982591252501641:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((7228544737:ℚ)/10000000000),((462767833:ℚ)/625000000),((-4815981829:ℚ)/6378125000),((-16725634211:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((1569699073:ℚ)/5000000000),((2103405471008562099985096077428154418547426068667807564269:ℚ)/5227162047656250000000000000000000000000000000000000000000),((277899792211388457058523899:ℚ)/389120000000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((7288380563:ℚ)/10000000000),((3761888669:ℚ)/5000000000),((-381597599:ℚ)/500000000),((-16905141689:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2873529673:ℚ)/10000000000),((35782207341163584117465442311703529626292818418300797:ℚ)/88067676467895507812500000000000000000000000000000000),((278250727612351169299147699:ℚ)/389120000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((1852006723:ℚ)/2500000000),((1910810677:ℚ)/2500000000),((-20040538801:ℚ)/26225000000),((-4316020169:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((45048137:ℚ)/200000000),((17572664053736180235958377287882126418732094041135254917:ℚ)/43330809433593750000000000000000000000000000000000000000),((330224615041338635230684521:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7527640981:ℚ)/10000000000),((64966917:ℚ)/80000000),((-230323307:ℚ)/284800000),((-17622922943:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((1381019193:ℚ)/10000000000),((3347006475557932885595823477867967338390600525144312288953:ℚ)/7807632690000000000000000000000000000000000000000000000000),((5272581603486907612435956889:ℚ)/7393280000000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((4002903741:ℚ)/5000000000),((4537589867:ℚ)/5000000000),((-49388668271:ℚ)/57200000000),((-9528711223:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((258274894072864590478385949873831828380995985040190252231:ℚ)/569970472500000000000000000000000000000000000000000000000),((364669963:ℚ)/512000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8961017303:ℚ)/10000000000),((5490669297:ℚ)/5000000000),((-20592900287:ℚ)/21600000000),((-21923051909:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((22174559259770288759275463318655603000642014803945638833:ℚ)/45000000000000000000000000000000000000000000000000000000),((364669963:ℚ)/512000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((2717112557:ℚ)/2500000000),((14788554253:ℚ)/10000000000),(-1:ℚ),((-6911337671:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((69238603924398759085372956221367689:ℚ)/131403600000000000000000000000000000),((364669963:ℚ)/512000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
private theorem node0_2 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source32 nn0 nn1 Qcell ((2041:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_9
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_9
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8]
theorem packet_count : packets.length = 9 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC04
#check @N11Formalization.C450Source32GroupedC04.bound
#print axioms N11Formalization.C450Source32GroupedC04.valid0
#print axioms N11Formalization.C450Source32GroupedC04.valid1
#print axioms N11Formalization.C450Source32GroupedC04.valid2
#print axioms N11Formalization.C450Source32GroupedC04.valid3
#print axioms N11Formalization.C450Source32GroupedC04.valid4
#print axioms N11Formalization.C450Source32GroupedC04.valid5
#print axioms N11Formalization.C450Source32GroupedC04.valid6
#print axioms N11Formalization.C450Source32GroupedC04.valid7
#print axioms N11Formalization.C450Source32GroupedC04.valid8
#print axioms N11Formalization.C450Source32GroupedC04.bound
#print axioms N11Formalization.C450Source32GroupedC04.endpoint_checks
