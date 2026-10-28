import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((3582607589:ℚ)/5000000000),((463018177:ℚ)/625000000),((-2621127239:ℚ)/3100000000),((-36333898657:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1699448091:ℚ)/5000000000),((1416987768225648120156321547378252033547:ℚ)/3103322256534375000000000000000000000000),((6355501202161416764495417:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((7284765151:ℚ)/10000000000),((7527605347:ℚ)/10000000000),((-42773237429:ℚ)/50550000000),((-74221946963:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2890267301:ℚ)/10000000000),((6623660897110751318339146823598923232760448464561410914692393:ℚ)/14542958515195312500000000000000000000000000000000000000000000),((1632461451096250991323200257:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7404285323:ℚ)/10000000000),((7646899271:ℚ)/10000000000),((-43608294897:ℚ)/51500000000),((-75775709199:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1137172449:ℚ)/5000000000),((13585522543798881421234459861983763560416660176767004737063:ℚ)/29897919348732910156250000000000000000000000000000000000000),((113280767:ℚ)/128000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7523777333:ℚ)/10000000000),((3883086857:ℚ)/5000000000),((-22221607999:ℚ)/26225000000),((-25776368443:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((11339761:ℚ)/80000000),((14069677872890743352140871081648580592238162337808315608014291:ℚ)/31029943702760000000000000000000000000000000000000000000000000),((113280767:ℚ)/128000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7643242703:ℚ)/10000000000),((8243096239:ℚ)/10000000000),((-47781673673:ℚ)/53400000000),((-78882155139:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((10766066789420102487550124731743411193833016146358464424931929:ℚ)/22236137901120000000000000000000000000000000000000000000000000),((113280767:ℚ)/128000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((406043231:ℚ)/500000000),((4598130757:ℚ)/5000000000),((-27226915299:ℚ)/28600000000),((-4254562003:ℚ)/6480000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1345052837372242808149398057477237087960874615363358592553:ℚ)/2608184882160000000000000000000000000000000000000000000000),((113280767:ℚ)/128000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((9075179729:ℚ)/10000000000),((2220156307:ℚ)/2000000000),(-1:ℚ),((-97497336477:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((86667272730060494852698341431296832174455201915336293989:ℚ)/160000000000000000000000000000000000000000000000000000000),((113280767:ℚ)/128000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10981338589:ℚ)/10000000000),((7453039969:ℚ)/5000000000),(-1:ℚ),((-122277401657:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((150552444833468952757268418264257170627:ℚ)/269114572800000000000000000000000000000),((113280767:ℚ)/128000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
private theorem node0_2 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_8
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_8
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7]
theorem packet_count : packets.length = 8 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC03
#check @N11Formalization.C450Source33GroupedC03.bound
#print axioms N11Formalization.C450Source33GroupedC03.valid0
#print axioms N11Formalization.C450Source33GroupedC03.valid1
#print axioms N11Formalization.C450Source33GroupedC03.valid2
#print axioms N11Formalization.C450Source33GroupedC03.valid3
#print axioms N11Formalization.C450Source33GroupedC03.valid4
#print axioms N11Formalization.C450Source33GroupedC03.valid5
#print axioms N11Formalization.C450Source33GroupedC03.valid6
#print axioms N11Formalization.C450Source33GroupedC03.valid7
#print axioms N11Formalization.C450Source33GroupedC03.bound
#print axioms N11Formalization.C450Source33GroupedC03.endpoint_checks
