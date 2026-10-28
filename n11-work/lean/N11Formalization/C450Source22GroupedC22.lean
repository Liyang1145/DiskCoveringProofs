import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5835904403:ℚ)/10000000000),((797700061:ℚ)/1250000000),((2798634801:ℚ)/7120000000),((3233100183:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3476339163:ℚ)/5000000000),((1159997290533932057509289:ℚ)/25347200000000000000000000),((-4961699751723177035205711:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6314423049:ℚ)/10000000000),((1655150217:ℚ)/2500000000),((8874423049:ℚ)/22120000000),((2215150217:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((737714629:ℚ)/1250000000),((1350191712955516770458366456851720897142734698292679399261:ℚ)/36091383636328125000000000000000000000000000000000000000000),((-20550037753438871205073999:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6553499197:ℚ)/10000000000),((428718793:ℚ)/625000000),((828499927:ℚ)/2080000000),((1706156379:ℚ)/3456250000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((132749299:ℚ)/250000000),((140257483121754876934178946727011713029882490563721783:ℚ)/3833811560058593750000000000000000000000000000000000000),((-68521465725604734121811:ℚ)/190000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((339623483:ℚ)/500000000),((1744729001:ℚ)/2500000000),((467623483:ℚ)/1163000000),((6914187003:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2325842343:ℚ)/5000000000),((102949846000299223102804103684625069345986019813934690496491:ℚ)/3089993545142968750000000000000000000000000000000000000000000),((-21177444898862587026798191:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((863989817:ℚ)/1250000000),((7098309757:ℚ)/10000000000),((1183989817:ℚ)/2955000000),((28014929271:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4288057119:ℚ)/10000000000),((592551399125505889992679411999514968998756114156506367623101:ℚ)/17885162672848535156250000000000000000000000000000000000000000),((-341032578887117129633898359:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((439459047:ℚ)/625000000),((7217682981:ℚ)/10000000000),((599459047:ℚ)/1501250000),((9457682981:ℚ)/19700000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3892947941:ℚ)/10000000000),((3410228366483329878062916720416813421289356855145117694888351:ℚ)/103384628067871875000000000000000000000000000000000000000000000),((-343206226812635239130374951:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((1430149879:ℚ)/2000000000),((1834259161:ℚ)/2500000000),((1942149879:ℚ)/4880000000),((7182777483:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1727768067:ℚ)/5000000000),((21206630434244876640090463247334805213842462566133305629:ℚ)/644969114141845703125000000000000000000000000000000000000),((-21585005803504312244188911:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((7270133483:ℚ)/10000000000),((757568887:ℚ)/1000000000),((9830133483:ℚ)/25160000000),((2944706661:ℚ)/6100000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((591412897:ℚ)/2000000000),((2472958595087674155577903919010163972032650001456109747877:ℚ)/70158585797656250000000000000000000000000000000000000000000),((-3462749114843770325064879:ℚ)/9241600000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((3754421881:ℚ)/5000000000),((7814273063:ℚ)/10000000000),((559380209:ℚ)/1440000000),((30162819189:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((38759347:ℚ)/250000000),((2212660174423296159373824000824779315357361986646740160437:ℚ)/62992229090625000000000000000000000000000000000000000000000),((-46406703125988387:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((1936870639:ℚ)/2500000000),((9721083193:ℚ)/10000000000),((2576870639:ℚ)/8000000000),((3987027731:ℚ)/7200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((14287401138134667766307693068783697:ℚ)/240000000000000000000000000000000000),((-24600887:ℚ)/64000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((4827317573:ℚ)/5000000000),((13529060203:ℚ)/10000000000),((6107317573:ℚ)/22080000000),((47307180609:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((21946032937040578507128481:ℚ)/243763200000000000000000000),((-24600887:ℚ)/64000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source22 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC22
#check @N11Formalization.C450Source22GroupedC22.bound
#print axioms N11Formalization.C450Source22GroupedC22.valid0
#print axioms N11Formalization.C450Source22GroupedC22.valid1
#print axioms N11Formalization.C450Source22GroupedC22.valid2
#print axioms N11Formalization.C450Source22GroupedC22.valid3
#print axioms N11Formalization.C450Source22GroupedC22.valid4
#print axioms N11Formalization.C450Source22GroupedC22.valid5
#print axioms N11Formalization.C450Source22GroupedC22.valid6
#print axioms N11Formalization.C450Source22GroupedC22.valid7
#print axioms N11Formalization.C450Source22GroupedC22.valid8
#print axioms N11Formalization.C450Source22GroupedC22.valid9
#print axioms N11Formalization.C450Source22GroupedC22.valid10
#print axioms N11Formalization.C450Source22GroupedC22.bound
#print axioms N11Formalization.C450Source22GroupedC22.endpoint_checks
