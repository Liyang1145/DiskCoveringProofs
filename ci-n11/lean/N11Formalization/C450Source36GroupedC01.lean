import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((745691111:ℚ)/1000000000),((7837500003:ℚ)/10000000000),(-1:ℚ),((-1789073333:ℚ)/2060000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1943546399:ℚ)/10000000000),((44817576498809790912874987394569436280614466041184559:ℚ)/81954525000000000000000000000000000000000000000000000),((640343:ℚ)/500000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((961885039:ℚ)/1250000000),((4037500001:ℚ)/5000000000),(-1:ℚ),((-2325655117:ℚ)/2670000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),(0:ℚ),((8095566491633860930576847053015412025653811718223357:ℚ)/14870439843750000000000000000000000000000000000000000),((640343:ℚ)/500000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7933201707:ℚ)/10000000000),((8550000003:ℚ)/10000000000),(-1:ℚ),((-19319605121:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((62989712611430697670933583685218854930154046302560442563:ℚ)/112289548800000000000000000000000000000000000000000000000),((640343:ℚ)/500000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((8409320217:ℚ)/10000000000),((4750000001:ℚ)/5000000000),(-1:ℚ),((-20747960651:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((23786853380297160222602284476317776888058792133974822953:ℚ)/40814668800000000000000000000000000000000000000000000000),((640343:ℚ)/500000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((9361162561:ℚ)/10000000000),((11400000003:ℚ)/10000000000),(-1:ℚ),((-23603487683:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11606007963482929136080205814595188622379478029263981849:ℚ)/19200000000000000000000000000000000000000000000000000000),((640343:ℚ)/500000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((1126379497:ℚ)/1000000000),((7600000001:ℚ)/5000000000),(-1:ℚ),((-2931138491:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6956529602888946957438368798649737:ℚ)/10764582912000000000000000000000000),((640343:ℚ)/500000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_3 node3_6
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_6
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5]
theorem packet_count : packets.length = 6 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC01
#check @N11Formalization.C450Source36GroupedC01.bound
#print axioms N11Formalization.C450Source36GroupedC01.valid0
#print axioms N11Formalization.C450Source36GroupedC01.valid1
#print axioms N11Formalization.C450Source36GroupedC01.valid2
#print axioms N11Formalization.C450Source36GroupedC01.valid3
#print axioms N11Formalization.C450Source36GroupedC01.valid4
#print axioms N11Formalization.C450Source36GroupedC01.valid5
#print axioms N11Formalization.C450Source36GroupedC01.bound
#print axioms N11Formalization.C450Source36GroupedC01.endpoint_checks
