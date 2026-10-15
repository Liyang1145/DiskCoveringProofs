import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1469493229:ℚ)/2000000000),((7598750003:ℚ)/10000000000),(-1:ℚ),((-3589279687:ℚ)/4044000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((2585103683:ℚ)/10000000000),((58517289977599650564540420150412017835386243161230333:ℚ)/124003719720000000000000000000000000000000000000000000),((18131844001870739607880151:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((1866624837:ℚ)/2500000000),((3858750001:ℚ)/5000000000),(-1:ℚ),((-4575874511:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((938550591:ℚ)/5000000000),((120766267850991638115814866891775152689837726888126429:ℚ)/256107890625000000000000000000000000000000000000000000),((39243:ℚ)/31250)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7585522067:ℚ)/10000000000),((3977500001:ℚ)/5000000000),(-1:ℚ),((-18660566201:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((617348579:ℚ)/10000000000),((728970452601646009936327612267671574179844360197843593:ℚ)/1522733040000000000000000000000000000000000000000000000),((39243:ℚ)/31250)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7823538299:ℚ)/10000000000),((8430000003:ℚ)/10000000000),(-1:ℚ),((-1761328627:ℚ)/2080000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((8270938587891034454463725688752411206143938860651993:ℚ)/16872960000000000000000000000000000000000000000000000),((39243:ℚ)/31250)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((4149733789:ℚ)/5000000000),((4690000001:ℚ)/5000000000),(-1:ℚ),((-10401201367:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((515766399447870171562807962307895168849677528393825693:ℚ)/1020366720000000000000000000000000000000000000000000000),((39243:ℚ)/31250)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((925099839:ℚ)/1000000000),((11280000003:ℚ)/10000000000),(-1:ℚ),((-2365699517:ℚ)/3200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1999726901371449978997511833617841656688281615351887:ℚ)/3840000000000000000000000000000000000000000000000000),((39243:ℚ)/31250)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((2788296493:ℚ)/2500000000),((7540000001:ℚ)/5000000000),(-1:ℚ),((-7340889479:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((18387529711044610835342226126932221:ℚ)/33639321600000000000000000000000000),((39243:ℚ)/31250)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC01
#check @N11Formalization.C450Source33GroupedC01.bound
#print axioms N11Formalization.C450Source33GroupedC01.valid0
#print axioms N11Formalization.C450Source33GroupedC01.valid1
#print axioms N11Formalization.C450Source33GroupedC01.valid2
#print axioms N11Formalization.C450Source33GroupedC01.valid3
#print axioms N11Formalization.C450Source33GroupedC01.valid4
#print axioms N11Formalization.C450Source33GroupedC01.valid5
#print axioms N11Formalization.C450Source33GroupedC01.valid6
#print axioms N11Formalization.C450Source33GroupedC01.bound
#print axioms N11Formalization.C450Source33GroupedC01.endpoint_checks
