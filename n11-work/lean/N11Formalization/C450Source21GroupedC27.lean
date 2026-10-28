import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5622722249:ℚ)/10000000000),((3086791279:ℚ)/5000000000),((2279574083:ℚ)/3560000000),((40354704069:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1844939737:ℚ)/2500000000),((-520885893734588604128347782743889:ℚ)/11279504000000000000000000000000000),((-34522158156509314037915741:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3049835521:ℚ)/5000000000),((200374801:ℚ)/312500000),((3657835521:ℚ)/5530000000),((868040937:ℚ)/1112500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3195873963:ℚ)/5000000000),((-62401651841539714518231105043927747781424239061984321:ℚ)/1056952356250000000000000000000000000000000000000000000),((-134666695107989534088501:ℚ)/361000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6338044441:ℚ)/10000000000),((3325171927:ℚ)/5000000000),((7554044441:ℚ)/11440000000),((42976891197:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5845631841:ℚ)/10000000000),((-556552213212775686796787360725094519995392792432302289:ℚ)/9357462400000000000000000000000000000000000000000000000),((-34377206184054414864796429:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6576359517:ℚ)/10000000000),((6769498023:ℚ)/10000000000),((7792359517:ℚ)/11630000000),((87264478253:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5250268921:ℚ)/10000000000),((-159768686114172742390935382648439205653874079167249813:ℚ)/2457871479687500000000000000000000000000000000000000000),((-412187060066864291096274887:ℚ)/1108992000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6695496983:ℚ)/10000000000),((6888639133:ℚ)/10000000000),((2637165661:ℚ)/3940000000),((88575030463:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4928532723:ℚ)/10000000000),((-6213679590233503080266956587496207983732264115871589:ℚ)/95567162500000000000000000000000000000000000000000000),((-137187821850822525971298789:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6814621933:ℚ)/10000000000),((700776781:ℚ)/1000000000),((8030621933:ℚ)/12010000000),((8988544591:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((143321229:ℚ)/312500000),((-703952927635764080176007330429854013362834238820875517:ℚ)/10827022506250000000000000000000000000000000000000000000),((-1369747908814050254849861:ℚ)/3696640000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((1386746993:ℚ)/2000000000),((7126884637:ℚ)/10000000000),((1629946993:ℚ)/2440000000),((91195731007:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((210924357:ℚ)/500000000),((-5901604647343729887341930287176659252358125581359497:ℚ)/90792400000000000000000000000000000000000000000000000),((-136756594335561129134640869:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7052836639:ℚ)/10000000000),((7245990163:ℚ)/10000000000),((1181262377:ℚ)/1770000000),((92505891793:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((76354983:ℚ)/200000000),((-187638225227976865478428289880480670222827051762451:ℚ)/2888142187500000000000000000000000000000000000000000),((-136533232727947179549505669:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7171927481:ℚ)/10000000000),((7365084903:ℚ)/10000000000),((8387927481:ℚ)/12580000000),((93815933933:ℚ)/123900000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((168615209:ℚ)/500000000),((-788872949562878233880230903001264112041473232579449:ℚ)/12151278759765625000000000000000000000000000000000000),((-408914119630345455723603527:ℚ)/1108992000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((455687999:ℚ)/625000000),((7603243933:ℚ)/10000000000),((177229333:ℚ)/270000000),((96435683263:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((457809:ℚ)/1600000),((-274592162507710712520929777065024275238673978639:ℚ)/4556250000000000000000000000000000000000000000000),((-1395473749682887:ℚ)/3800000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7529139803:ℚ)/10000000000),((9507385739:ℚ)/10000000000),((8745139803:ℚ)/16000000000),((39127081043:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((341654703:ℚ)/2500000000),((-23769075076704665417191940167299198284922057848742843:ℚ)/1600000000000000000000000000000000000000000000000000000),((-22357016183468239:ℚ)/60800000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((1886622147:ℚ)/2000000000),((13312241387:ℚ)/10000000000),((2129822147:ℚ)/4416000000),((159234655257:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((173827014650476432399147:ℚ)/9750528000000000000000000),((-47085843:ℚ)/128000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC27
#check @N11Formalization.C450Source21GroupedC27.bound
#print axioms N11Formalization.C450Source21GroupedC27.valid0
#print axioms N11Formalization.C450Source21GroupedC27.valid1
#print axioms N11Formalization.C450Source21GroupedC27.valid2
#print axioms N11Formalization.C450Source21GroupedC27.valid3
#print axioms N11Formalization.C450Source21GroupedC27.valid4
#print axioms N11Formalization.C450Source21GroupedC27.valid5
#print axioms N11Formalization.C450Source21GroupedC27.valid6
#print axioms N11Formalization.C450Source21GroupedC27.valid7
#print axioms N11Formalization.C450Source21GroupedC27.valid8
#print axioms N11Formalization.C450Source21GroupedC27.valid9
#print axioms N11Formalization.C450Source21GroupedC27.valid10
#print axioms N11Formalization.C450Source21GroupedC27.valid11
#print axioms N11Formalization.C450Source21GroupedC27.bound
#print axioms N11Formalization.C450Source21GroupedC27.endpoint_checks
