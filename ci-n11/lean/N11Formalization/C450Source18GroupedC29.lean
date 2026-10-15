import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((704351767:ℚ)/1250000000),((6181563257:ℚ)/10000000000),((2433055301:ℚ)/3337500000),((91240322341:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1839019951:ℚ)/2500000000),((-436636612885774415397013347935463857:ℚ)/7435219921875000000000000000000000000),((-3861566370163764961851409:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6110718533:ℚ)/10000000000),((6419525801:ℚ)/10000000000),((2984593657:ℚ)/3950000000),((94333835413:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((79591751:ℚ)/125000000),((-504644840243757070637573982564171334668177272686127:ℚ)/7313671875000000000000000000000000000000000000000000),((-10624447833856218235081:ℚ)/32000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((396789:ℚ)/625000),((6657457533:ℚ)/10000000000),((1350367:ℚ)/1787500),((97426947929:ℚ)/110600000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5820357767:ℚ)/10000000000),((-1235324252417494300110277677250941595155769:ℚ)/17847943115234375000000000000000000000000000),((-3809134470600776325515049:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3293251233:ℚ)/5000000000),((6776412791:ℚ)/10000000000),((11159753699:ℚ)/14537500000),((8997578753:ℚ)/10400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((208943251:ℚ)/400000000),((-531425972440256144144014431675632945601426794402148979:ℚ)/7200795350646972656250000000000000000000000000000000000),((-3795932349641953012493521:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1676358101:ℚ)/2500000000),((3447680717:ℚ)/5000000000),((5669074303:ℚ)/7387500000),((50259849321:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2450415599:ℚ)/5000000000),((-69720546978941053666565075607202840783138137050746823:ℚ)/944938984680175781250000000000000000000000000000000000),((-945673126347324318148049:ℚ)/2888000000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6824356543:ℚ)/10000000000),((7014303777:ℚ)/10000000000),((23033069629:ℚ)/30025000000),((102065949101:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3560361:ℚ)/7812500),((-18717783773508905364131643508512531320482383368541645029:ℚ)/253758339990234375000000000000000000000000000000000000000),((-10441592545828843190649:ℚ)/32000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((3471637581:ℚ)/5000000000),((3566620057:ℚ)/5000000000),((11694912743:ℚ)/15250000000),((51806060741:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((837544711:ℚ)/2000000000),((-817248069126413403632050234278923983546789002045004429:ℚ)/11083056640625000000000000000000000000000000000000000000),((-939024883438712924839609:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((7062188517:ℚ)/10000000000),((1813042681:ℚ)/2500000000),((23746565551:ℚ)/30975000000),((26289554853:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1892292159:ℚ)/5000000000),((-570481037281277320678810946758379862810758374211839679:ℚ)/7739318518066406250000000000000000000000000000000000000),((-647982402004065205541:ℚ)/2000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1795274213:ℚ)/2500000000),((1474219173:ℚ)/2000000000),((6025822639:ℚ)/7862500000),((21340849249:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1667824331:ℚ)/5000000000),((-109294732962186684893594335147308986393467150467937:ℚ)/1483310395479202270507812500000000000000000000000000),((-149174213846693520210489:ℚ)/462080000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((1460000079:ℚ)/2000000000),((7608930711:ℚ)/10000000000),((4892000237:ℚ)/6480000000),((109796099243:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2819081259:ℚ)/10000000000),((-2196260042879430458524637856560701799924015333975237:ℚ)/31492800000000000000000000000000000000000000000000000),((-20517853:ℚ)/64000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7537793951:ℚ)/10000000000),((1902207197:ℚ)/2000000000),((25173381853:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((64016391:ℚ)/500000000),((-1174407583891328881436833413591362176016156114870809253:ℚ)/37500000000000000000000000000000000000000000000000000000),((-20517853:ℚ)/64000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9439639721:ℚ)/10000000000),((13313505721:ℚ)/10000000000),((30878919163:ℚ)/55200000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-167389443651334223351718966530437963:ℚ)/21024576000000000000000000000000000000),((-20517853:ℚ)/64000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC29
#check @N11Formalization.C450Source18GroupedC29.bound
#print axioms N11Formalization.C450Source18GroupedC29.valid0
#print axioms N11Formalization.C450Source18GroupedC29.valid1
#print axioms N11Formalization.C450Source18GroupedC29.valid2
#print axioms N11Formalization.C450Source18GroupedC29.valid3
#print axioms N11Formalization.C450Source18GroupedC29.valid4
#print axioms N11Formalization.C450Source18GroupedC29.valid5
#print axioms N11Formalization.C450Source18GroupedC29.valid6
#print axioms N11Formalization.C450Source18GroupedC29.valid7
#print axioms N11Formalization.C450Source18GroupedC29.valid8
#print axioms N11Formalization.C450Source18GroupedC29.valid9
#print axioms N11Formalization.C450Source18GroupedC29.valid10
#print axioms N11Formalization.C450Source18GroupedC29.valid11
#print axioms N11Formalization.C450Source18GroupedC29.bound
#print axioms N11Formalization.C450Source18GroupedC29.endpoint_checks
