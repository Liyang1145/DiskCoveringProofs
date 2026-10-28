import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((604804669:ℚ)/1000000000),((3286701033:ℚ)/5000000000),((1084804669:ℚ)/5340000000),((14980103099:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((52038083:ℚ)/80000000),((53007623310173833642249990332192479000231:ℚ)/1087370546688000000000000000000000000000000),((-675686739815466107589673311:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1305066213:ℚ)/2000000000),((1702954847:ℚ)/2500000000),((2265066213:ℚ)/11060000000),((7668864541:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((43061703:ℚ)/80000000),((2487806951088060920093097606059059214256652694548661120233241:ℚ)/54570172058128125000000000000000000000000000000000000000000000),((-177794833682455582226498991:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((27055419:ℚ)/40000000),((3465502341:ℚ)/5000000000),((5139491:ℚ)/25000000),((15516507023:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2367465357:ℚ)/5000000000),((3344804034399101229398914830136420982822283343659111047:ℚ)/75496596875000000000000000000000000000000000000000000000),((-728903713025586683909711319:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((3441545249:ℚ)/5000000000),((7050175439:ℚ)/10000000000),((5841545249:ℚ)/28600000000),((31390526317:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((875678957:ℚ)/2000000000),((364049827332703127734157793682741914909153930322289606388209:ℚ)/8271551513671875000000000000000000000000000000000000000000000),((-2950025128126315103035332879:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((54705547:ℚ)/78125000),((3584666189:ℚ)/5000000000),((92205547:ℚ)/454296875),((15873998567:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((39924027:ℚ)/100000000),((25955456042484017514349133623077803002981871432089360668298363:ℚ)/593278760667450000000000000000000000000000000000000000000000000),((-746099033904977856521991879:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1424302821:ℚ)/2000000000),((7288476169:ℚ)/10000000000),((794767607:ℚ)/3940000000),((32105428507:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((713473889:ℚ)/2000000000),((6225912314240870677100569078535486798718627627209808203130887:ℚ)/143081301382788281250000000000000000000000000000000000000000000),((-3018728119495748487014283039:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((7240703513:ℚ)/10000000000),((92595093:ℚ)/125000000),((12040703513:ℚ)/60050000000),((405785279:ℚ)/1477500000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1543585491:ℚ)/5000000000),((1888659264656105587439066088513713551361307835115778239971:ℚ)/43615389966133447265625000000000000000000000000000000000000),((-477034579445167179302751:ℚ)/2310400000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((1471975789:ℚ)/2000000000),((376336339:ℚ)/500000000),((2431975789:ℚ)/12200000000),((1641009017:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2520423161:ℚ)/10000000000),((108564908553514446031301320210895253502600154417225265919:ℚ)/2517959421609765625000000000000000000000000000000000000000),((-7718189795049399956972679:ℚ)/36966400000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1495808211:ℚ)/2000000000),((3882465921:ℚ)/5000000000),((2455808211:ℚ)/12580000000),((16767397763:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1786507699:ℚ)/10000000000),((3048401682760777563814385446831591466084330628583701609654901:ℚ)/70158585797656250000000000000000000000000000000000000000000000),((-8216689883336001:ℚ)/38912000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7717327747:ℚ)/10000000000),((1000386923:ℚ)/1250000000),((12517327747:ℚ)/64800000000),((4281160769:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3441365048452581048302338134062110470575649455323296080783:ℚ)/79724539942822265625000000000000000000000000000000000000000),((-43757697:ℚ)/204800000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7955568089:ℚ)/10000000000),((9907265527:ℚ)/10000000000),((12755568089:ℚ)/80000000000),((39961796581:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((61553674363595606197142755782067362078594461225124171401:ℚ)/1275458400000000000000000000000000000000000000000000000000),((-43757697:ℚ)/204800000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((2465055109:ℚ)/2500000000),((274243087:ℚ)/200000000),((3665055109:ℚ)/27600000000),((1027529261:ℚ)/3200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1137718248880599512869606258917508561:ℚ)/19501056000000000000000000000000000000),((-43757697:ℚ)/204800000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC19
#check @N11Formalization.C450Source17GroupedC19.bound
#print axioms N11Formalization.C450Source17GroupedC19.valid0
#print axioms N11Formalization.C450Source17GroupedC19.valid1
#print axioms N11Formalization.C450Source17GroupedC19.valid2
#print axioms N11Formalization.C450Source17GroupedC19.valid3
#print axioms N11Formalization.C450Source17GroupedC19.valid4
#print axioms N11Formalization.C450Source17GroupedC19.valid5
#print axioms N11Formalization.C450Source17GroupedC19.valid6
#print axioms N11Formalization.C450Source17GroupedC19.valid7
#print axioms N11Formalization.C450Source17GroupedC19.valid8
#print axioms N11Formalization.C450Source17GroupedC19.valid9
#print axioms N11Formalization.C450Source17GroupedC19.valid10
#print axioms N11Formalization.C450Source17GroupedC19.valid11
#print axioms N11Formalization.C450Source17GroupedC19.bound
#print axioms N11Formalization.C450Source17GroupedC19.endpoint_checks
