import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((452358617:ℚ)/625000000),((7478750003:ℚ)/10000000000),(-1:ℚ),((-1125075851:ℚ)/1263750000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((154999409:ℚ)/500000000),((189947844154023721232033339534174511607248276413827:ℚ)/467196691894531250000000000000000000000000000000000),((3458104348371769097569267:ℚ)/2888000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((7356718761:ℚ)/10000000000),((3798750001:ℚ)/5000000000),(-1:ℚ),((-18358156283:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((2537043283:ℚ)/10000000000),((22207623864567058394140692512093069913383197629442746937:ℚ)/54636350000000000000000000000000000000000000000000000000),((871773037506365039174363:ℚ)/722000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((1868922777:ℚ)/2500000000),((3917500001:ℚ)/5000000000),(-1:ℚ),((-4678768331:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1811144253:ℚ)/10000000000),((10908425816712772846705629031912275200409589622601169:ℚ)/26436337500000000000000000000000000000000000000000000),((603827:ℚ)/500000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((3856806003:ℚ)/5000000000),((8310000003:ℚ)/10000000000),(-1:ℚ),((-9714418009:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((3955003122973102117969862810985181820487713459032946051:ℚ)/9357462400000000000000000000000000000000000000000000000),((603827:ℚ)/500000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((4094684859:ℚ)/5000000000),((4630000001:ℚ)/5000000000),(-1:ℚ),((-10428054577:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((55003097350273015780172534267842244332630096182215441:ℚ)/125971200000000000000000000000000000000000000000000000),((603827:ℚ)/500000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((9140618021:ℚ)/10000000000),((11160000003:ℚ)/10000000000),(-1:ℚ),((-23709854063:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5785565990023432511769879718172589683034185930679479917:ℚ)/12800000000000000000000000000000000000000000000000000000),((603827:ℚ)/500000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((11042402111:ℚ)/10000000000),((14960000003:ℚ)/10000000000),(-1:ℚ),((-29415206333:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1132090039328716818194986343619120509:ℚ)/2392129536000000000000000000000000000),((603827:ℚ)/500000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((1011:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_7
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_7
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6]
theorem packet_count : packets.length = 7 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC01
#check @N11Formalization.C450Source30GroupedC01.bound
#print axioms N11Formalization.C450Source30GroupedC01.valid0
#print axioms N11Formalization.C450Source30GroupedC01.valid1
#print axioms N11Formalization.C450Source30GroupedC01.valid2
#print axioms N11Formalization.C450Source30GroupedC01.valid3
#print axioms N11Formalization.C450Source30GroupedC01.valid4
#print axioms N11Formalization.C450Source30GroupedC01.valid5
#print axioms N11Formalization.C450Source30GroupedC01.valid6
#print axioms N11Formalization.C450Source30GroupedC01.bound
#print axioms N11Formalization.C450Source30GroupedC01.endpoint_checks
