import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((5961288081:ℚ)/10000000000),((1626913133:ℚ)/2500000000),((13001288081:ℚ)/53400000000),((8560739399:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6691003631:ℚ)/10000000000),((15259683961030146466172155884688705310903:ℚ)/135921318336000000000000000000000000000000),((-649465173592992849601883:ℚ)/1945600000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1610261321:ℚ)/2500000000),((3373569537:ℚ)/5000000000),((481465903:ℚ)/1975000000),((17480708611:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2797637911:ℚ)/5000000000),((11725853921410990119923045375509876548866302358090906951453:ℚ)/112777415775000000000000000000000000000000000000000000000000),((-52328510071971357869077017:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((1670168839:ℚ)/2500000000),((1373366283:ℚ)/2000000000),((381129871:ℚ)/1562500000),((7064098849:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2484797139:ℚ)/5000000000),((69451755319773735324013713776068112012002491206307531:ℚ)/690254600000000000000000000000000000000000000000000000),((-8609162973266415422912977:ℚ)/23658496000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((850054467:ℚ)/1250000000),((3493246047:ℚ)/5000000000),((1730054467:ℚ)/7150000000),((17839738141:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4628263317:ℚ)/10000000000),((1139601339174168350298668542539511504287118719375181483225879:ℚ)/11373383331298828125000000000000000000000000000000000000000000),((-54464169151059372405090137:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6920162139:ℚ)/10000000000),((1421224537:ℚ)/2000000000),((13960162139:ℚ)/58150000000),((7207673611:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2130947297:ℚ)/5000000000),((3791112604822413240282811939864049830773982700429485407046403:ℚ)/37969840682716800000000000000000000000000000000000000000000000),((-8818894378411548150747017:ℚ)/23658496000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((7039856257:ℚ)/10000000000),((361286233:ℚ)/500000000),((4693285419:ℚ)/19700000000),((1819858699:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1931666503:ℚ)/5000000000),((1780525178527807782570355570957676941852290628859866564883:ℚ)/17885162672848535156250000000000000000000000000000000000000),((-557690423185347455373577:ℚ)/1478656000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((894939959:ℚ)/1250000000),((3732424093:ℚ)/5000000000),((1774939959:ℚ)/7625000000),((18557272279:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((213831507:ℚ)/625000000),((729309419779500622328005099030562896378602605505868713505583:ℚ)/7201009586165625000000000000000000000000000000000000000000000),((-56244584122444971855841057:ℚ)/147865600000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7398760213:ℚ)/10000000000),((7942806967:ℚ)/10000000000),((4812920071:ℚ)/21600000000),((38548420901:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((461273083:ℚ)/2000000000),((108006462574768989893224111202878816070192326380391811061151:ℚ)/1034182181250000000000000000000000000000000000000000000000000),((-379480801366185701:ℚ)/972800000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7876932043:ℚ)/10000000000),((9851812087:ℚ)/10000000000),((14916932043:ℚ)/80000000000),((44275436261:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((153188888141650890690694393020700285590847788635811544333:ℚ)/1275458400000000000000000000000000000000000000000000000000),((-408976603:ℚ)/1024000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((1223323013:ℚ)/1250000000),((13662352743:ℚ)/10000000000),((701107671:ℚ)/4600000000),((55707058229:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((41507107040261248707025750886263009827813:ℚ)/270848000000000000000000000000000000000000),((-408976603:ℚ)/1024000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC19
#check @N11Formalization.C450Source24GroupedC19.bound
#print axioms N11Formalization.C450Source24GroupedC19.valid0
#print axioms N11Formalization.C450Source24GroupedC19.valid1
#print axioms N11Formalization.C450Source24GroupedC19.valid2
#print axioms N11Formalization.C450Source24GroupedC19.valid3
#print axioms N11Formalization.C450Source24GroupedC19.valid4
#print axioms N11Formalization.C450Source24GroupedC19.valid5
#print axioms N11Formalization.C450Source24GroupedC19.valid6
#print axioms N11Formalization.C450Source24GroupedC19.valid7
#print axioms N11Formalization.C450Source24GroupedC19.valid8
#print axioms N11Formalization.C450Source24GroupedC19.valid9
#print axioms N11Formalization.C450Source24GroupedC19.bound
#print axioms N11Formalization.C450Source24GroupedC19.endpoint_checks
