import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((3677470599:ℚ)/5000000000),((3865769533:ℚ)/5000000000),((-9421308599:ℚ)/9920000000),((-20142294193:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2546345239:ℚ)/10000000000),((18505625427721877108747045715910735776679:ℚ)/32815957718750000000000000000000000000000),((278503391:ℚ)/256000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((379687079:ℚ)/500000000),((1593939541:ℚ)/2000000000),((-3911418623:ℚ)/4120000000),((-699269851:ℚ)/890000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((202927249:ℚ)/5000000000),((51075686385797179270929215530539517054614519217419251:ℚ)/91296583508300781250000000000000000000000000000000000),((278503391:ℚ)/256000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3916224359:ℚ)/5000000000),((8445883229:ℚ)/10000000000),((-20985649687:ℚ)/21360000000),((-21813570513:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((1027608683560702404482373895466723950689283676517028756508771:ℚ)/1737198273525000000000000000000000000000000000000000000000000),((278503391:ℚ)/256000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((4154810387:ℚ)/5000000000),((234945897:ℚ)/250000000),(-1:ℚ),((-7827890903:ℚ)/10800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1814342539499291510942343504544479076471531242014862181:ℚ)/2952450000000000000000000000000000000000000000000000000),((278503391:ℚ)/256000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((9263196391:ℚ)/10000000000),((2260125153:ℚ)/2000000000),(-1:ℚ),((-53642374737:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((62397494589790463983396672290068887140302007053795971577:ℚ)/100000000000000000000000000000000000000000000000000000000),((278503391:ℚ)/256000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((698018841:ℚ)/625000000),((1510389791:ℚ)/1000000000),(-1:ℚ),((-4186131887:ℚ)/6900000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((27051247409868288974268126465183341:ℚ)/41063625000000000000000000000000000),((278503391:ℚ)/256000000)⟩
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
end N11Formalization.C450Source36GroupedC02
#check @N11Formalization.C450Source36GroupedC02.bound
#print axioms N11Formalization.C450Source36GroupedC02.valid0
#print axioms N11Formalization.C450Source36GroupedC02.valid1
#print axioms N11Formalization.C450Source36GroupedC02.valid2
#print axioms N11Formalization.C450Source36GroupedC02.valid3
#print axioms N11Formalization.C450Source36GroupedC02.valid4
#print axioms N11Formalization.C450Source36GroupedC02.valid5
#print axioms N11Formalization.C450Source36GroupedC02.bound
#print axioms N11Formalization.C450Source36GroupedC02.endpoint_checks
