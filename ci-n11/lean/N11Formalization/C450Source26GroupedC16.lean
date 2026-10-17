import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((3059411707:ℚ)/5000000000),((803224967:ℚ)/1250000000),((1116775033:ℚ)/12875000000),((5:ℚ)/31),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((79367277:ℚ)/125000000),((372359326710608113387608161809:ℚ)/2469161867187500000000000000000),((-17041583546584499:ℚ)/60800000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((3179677901:ℚ)/5000000000),((6665878067:ℚ)/10000000000),((8694121933:ℚ)/106800000000),((16:ℚ)/103),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5794620429:ℚ)/10000000000),((579557514396566728461182813342352574428913:ℚ)/3894970755150000000000000000000000000000000),((-17811245936879957:ℚ)/60800000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((131993371:ℚ)/200000000),((3392924289:ℚ)/5000000000),((4287075711:ℚ)/54350000000),((40:ℚ)/267),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5188753627:ℚ)/10000000000),((123268371304159813720504427103270218107322393:ℚ)/843381635315512500000000000000000000000000000),((-743208220673747:ℚ)/2432000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((6719749923:ℚ)/10000000000),((6905776529:ℚ)/10000000000),((8454223471:ℚ)/110600000000),((160:ℚ)/1087),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4860656727:ℚ)/10000000000),((8573647202149659848888102077302978274391540399:ℚ)/58915579516039050000000000000000000000000000000),((-37928890632976411:ℚ)/121600000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((854973101:ℚ)/1250000000),((7025664117:ℚ)/10000000000),((2778111961:ℚ)/37500000000),((80:ℚ)/553),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2255458831:ℚ)/5000000000),((24625027708977907293637667088163147603908109:ℚ)/169867342968750000000000000000000000000000000),((-4837134090626357:ℚ)/15200000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((6959775609:ℚ)/10000000000),((7145513393:ℚ)/10000000000),((8214486607:ℚ)/114400000000),((32:ℚ)/225),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((165360303:ℚ)/400000000),((1378440911993382789316806913416634032247:ℚ)/9540685440000000000000000000000000000000),((-39464972694566113:ℚ)/121600000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((884965571:ℚ)/1250000000),((3632663133:ℚ)/5000000000),((4047336867:ℚ)/58150000000),((20:ℚ)/143),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3721637833:ℚ)/10000000000),((971235512498610260329003077659420240452777:ℚ)/6741804098493750000000000000000000000000000),((-5029075611209147:ℚ)/15200000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((7199633777:ℚ)/10000000000),((1846276131:ℚ)/2500000000),((664574623:ℚ)/9850000000),((160:ℚ)/1163),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3260334407:ℚ)/10000000000),((164493124924909053671708523495158173587397591:ℚ)/1144650411062306250000000000000000000000000000),((-40999982698414489:ℚ)/121600000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((7319505189:ℚ)/10000000000),((762456377:ℚ)/1000000000),((12681043:ℚ)/200000000),((80:ℚ)/591),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2725307211:ℚ)/10000000000),((17863892797729522959294822628084397649649:ℚ)/123855042600000000000000000000000000000000),((-41767118619320173:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((3779570907:ℚ)/5000000000),((202578343:ℚ)/250000000),((181421657:ℚ)/3240000000),((8:ℚ)/61),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1037391063:ℚ)/10000000000),((865005325908902342737284637435156349237:ℚ)/5956889364000000000000000000000000000000),((-21650355411978899:ℚ)/60800000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((8038034583:ℚ)/10000000000),((156468659:ℚ)/156250000),((83531341:ℚ)/2500000000),((10:ℚ)/81),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1880877640940081920649404522833029982143:ℚ)/12455648437500000000000000000000000000000),((-5731867:ℚ)/16000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9949874369:ℚ)/10000000000),((13826698953:ℚ)/10000000000),((511100349:ℚ)/73600000000),((1:ℚ)/10),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((463609154818995494464430391:ℚ)/2708480000000000000000000000),((-5731867:ℚ)/16000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC16
#check @N11Formalization.C450Source26GroupedC16.bound
#print axioms N11Formalization.C450Source26GroupedC16.valid0
#print axioms N11Formalization.C450Source26GroupedC16.valid1
#print axioms N11Formalization.C450Source26GroupedC16.valid2
#print axioms N11Formalization.C450Source26GroupedC16.valid3
#print axioms N11Formalization.C450Source26GroupedC16.valid4
#print axioms N11Formalization.C450Source26GroupedC16.valid5
#print axioms N11Formalization.C450Source26GroupedC16.valid6
#print axioms N11Formalization.C450Source26GroupedC16.valid7
#print axioms N11Formalization.C450Source26GroupedC16.valid8
#print axioms N11Formalization.C450Source26GroupedC16.valid9
#print axioms N11Formalization.C450Source26GroupedC16.valid10
#print axioms N11Formalization.C450Source26GroupedC16.valid11
#print axioms N11Formalization.C450Source26GroupedC16.bound
#print axioms N11Formalization.C450Source26GroupedC16.endpoint_checks
