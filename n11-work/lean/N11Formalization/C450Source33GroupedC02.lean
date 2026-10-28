import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7255869061:ℚ)/10000000000),((7503031143:ℚ)/10000000000),((-18541093429:ℚ)/19840000000),((-13517027809:ℚ)/16850000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1510402147:ℚ)/5000000000),((1749891001262257388589512566591769136237:ℚ)/3678011563300000000000000000000000000000),((3126366926827518382076211789:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((3687584519:ℚ)/5000000000),((3811035903:ℚ)/5000000000),((-9449107709:ℚ)/10110000000),((-20693091633:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((121922193:ℚ)/500000000),((35959919733873468123207126495112572993517750901215611099801:ℚ)/75744575599975585937500000000000000000000000000000000000000),((217564319:ℚ)/204800000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((7494448589:ℚ)/10000000000),((3930060999:ℚ)/5000000000),((-9806182997:ℚ)/10300000000),((-42221140123:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((16685689:ℚ)/100000000),((1923259757595059803020342184366777586916798160032823766779:ℚ)/3944012407558593750000000000000000000000000000000000000000),((217564319:ℚ)/204800000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((773295081:ℚ)/1000000000),((833611239:ℚ)/1000000000),((-2104033717:ℚ)/2136000000),((-4389065567:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((473154532287477397060149812391225431027726762065004594711:ℚ)/926505745880000000000000000000000000000000000000000000000),((217564319:ℚ)/204800000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((8209754379:ℚ)/10000000000),((1160967977:ℚ)/1250000000),(-1:ℚ),((-47228280653:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((67113901538738185588092530058720840547666442695274802647:ℚ)/127545840000000000000000000000000000000000000000000000000),((217564319:ℚ)/204800000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((2290680999:ℚ)/2500000000),((11190075077:ℚ)/10000000000),(-1:ℚ),((-13474766993:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((500185181636806462501069940602545498847560265675165043:ℚ)/937500000000000000000000000000000000000000000000000000),((217564319:ℚ)/204800000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((1383370623:ℚ)/1250000000),((3748202431:ℚ)/2500000000),(-1:ℚ),((-8403594361:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((36454249644866975754774985550387459:ℚ)/65701800000000000000000000000000000),((217564319:ℚ)/204800000)⟩
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
end N11Formalization.C450Source33GroupedC02
#check @N11Formalization.C450Source33GroupedC02.bound
#print axioms N11Formalization.C450Source33GroupedC02.valid0
#print axioms N11Formalization.C450Source33GroupedC02.valid1
#print axioms N11Formalization.C450Source33GroupedC02.valid2
#print axioms N11Formalization.C450Source33GroupedC02.valid3
#print axioms N11Formalization.C450Source33GroupedC02.valid4
#print axioms N11Formalization.C450Source33GroupedC02.valid5
#print axioms N11Formalization.C450Source33GroupedC02.valid6
#print axioms N11Formalization.C450Source33GroupedC02.bound
#print axioms N11Formalization.C450Source33GroupedC02.endpoint_checks
