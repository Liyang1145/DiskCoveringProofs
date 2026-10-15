import N11Formalization.C450Source35Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source35GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source35Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((7420460959:ℚ)/10000000000),((7797500003:ℚ)/10000000000),(-1:ℚ),((-17909382877:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((87117687:ℚ)/400000000),((28929337291297655665669478290146322062648369743918746757:ℚ)/54636350000000000000000000000000000000000000000000000000),((640781:ℚ)/500000)⟩
theorem valid0 : Valid source35 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source35 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((7658591221:ℚ)/10000000000),((4017500001:ℚ)/5000000000),(-1:ℚ),((-18623773663:ℚ)/21360000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),(0:ℚ),((892820929957812864923063999391622665617296274412018967:ℚ)/1691925600000000000000000000000000000000000000000000000),((640781:ℚ)/500000)⟩
theorem valid1 : Valid source35 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source35 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7896676467:ℚ)/10000000000),((8510000003:ℚ)/10000000000),(-1:ℚ),((-19338029401:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((40575228478037993227383274224571641372394384424880120401:ℚ)/74859699200000000000000000000000000000000000000000000000),((640781:ℚ)/500000)⟩
theorem valid2 : Valid source35 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source35 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source35 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((4186364967:ℚ)/5000000000),((4730000001:ℚ)/5000000000),(-1:ℚ),((-10383094901:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((636032880437348952298395984733353163909283078638439447:ℚ)/1133740800000000000000000000000000000000000000000000000),((640781:ℚ)/500000)⟩
theorem valid3 : Valid source35 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source35 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((2331116301:ℚ)/2500000000),((11360000003:ℚ)/10000000000),(-1:ℚ),((-5905348903:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((115984747477243914832647554667158266482238436892492263:ℚ)/200000000000000000000000000000000000000000000000000000),((640781:ℚ)/500000)⟩
theorem valid4 : Valid source35 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source35 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((11226944739:ℚ)/10000000000),((7580000001:ℚ)/5000000000),(-1:ℚ),((-29328834217:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1469145852794111739077336014437983339:ℚ)/2392129536000000000000000000000000000),((640781:ℚ)/500000)⟩
theorem valid5 : Valid source35 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source35 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source35 nn0 nn1 packet5 valid5
private theorem node1_3 :
    CellBound source35 nn0 nn1 Qcell ((103:ℚ)/160) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source35 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source35 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source35 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_6
theorem bound : CellBound source35 nn0 nn1 Qcell (31/50) (69/50) := node0_6
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5]
theorem packet_count : packets.length = 6 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source35GroupedC01
#check @N11Formalization.C450Source35GroupedC01.bound
#print axioms N11Formalization.C450Source35GroupedC01.valid0
#print axioms N11Formalization.C450Source35GroupedC01.valid1
#print axioms N11Formalization.C450Source35GroupedC01.valid2
#print axioms N11Formalization.C450Source35GroupedC01.valid3
#print axioms N11Formalization.C450Source35GroupedC01.valid4
#print axioms N11Formalization.C450Source35GroupedC01.valid5
#print axioms N11Formalization.C450Source35GroupedC01.bound
#print axioms N11Formalization.C450Source35GroupedC01.endpoint_checks
