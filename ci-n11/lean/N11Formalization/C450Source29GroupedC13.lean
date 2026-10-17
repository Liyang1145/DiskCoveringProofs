import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6311068263:ℚ)/10000000000),((6625502839:ℚ)/10000000000),((-2305502839:ℚ)/24800000000),((-1013204789:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((118192887:ℚ)/200000000),((4330285243040773310414226324291657694793:ℚ)/40454748032000000000000000000000000000000),((-1544562640896282119001192421:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((131039783:ℚ)/200000000),((674594263:ℚ)/1000000000),((-242594263:ℚ)/2575000000),((-34719349:ℚ)/2098000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5313894287:ℚ)/10000000000),((48877631691632180130564853227101494329123897162813983587:ℚ)/458693650637435913085937500000000000000000000000000000000),((-699924939024453658713701:ℚ)/5914624000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3336177367:ℚ)/5000000000),((3433160527:ℚ)/5000000000),((-1273160527:ℚ)/13112500000),((-1048532101:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4992509857:ℚ)/10000000000),((107993829648754851517675434246937835735392486001486529765707:ℚ)/1004521054035168457031250000000000000000000000000000000000000),((-463308584820952650990964101:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6792661699:ℚ)/10000000000),((6986641417:ℚ)/10000000000),((-2666641417:ℚ)/26700000000),((-2457985097:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4651121351:ℚ)/10000000000),((45724243084507121302160733865651434786944371146440796423078439:ℚ)/421690817657756250000000000000000000000000000000000000000000000),((-1957190530922138796618348509:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((6912913197:ℚ)/10000000000),((7046780793:ℚ)/10000000000),((-2726780793:ℚ)/27175000000),((-2818739591:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4284908339:ℚ)/10000000000),((453323968057323072966172052647357752921655777121707550863117:ℚ)/4188933316336566162109375000000000000000000000000000000000000),((-2061682814777189739359829181:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((697301907:ℚ)/1000000000),((7106906787:ℚ)/10000000000),((-928968929:ℚ)/9137500000),((-299905721:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4090413979:ℚ)/10000000000),((3685184895213036470836139813529233548179512325014186655463:ℚ)/33911265281164550781250000000000000000000000000000000000000),((-21141305462845932082855741:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7033112159:ℚ)/10000000000),((3613560011:ℚ)/5000000000),((-1453560011:ℚ)/13825000000),((-3179336477:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3886816047:ℚ)/10000000000),((21060454117256647080643477621361600048159723596431733873:ℚ)/191100760839843750000000000000000000000000000000000000000),((-2166712951109274481649008629:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7153261309:ℚ)/10000000000),((7347283781:ℚ)/10000000000),((-3027283781:ℚ)/28125000000),((-3539783927:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1722882519:ℚ)/5000000000),((315788382451461463551917773075208734779548956923965883887089:ℚ)/2843345832824707031250000000000000000000000000000000000000000),((-2272282575043656965954798429:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7273363187:ℚ)/10000000000),((7587472633:ℚ)/10000000000),((-3267472633:ℚ)/28600000000),((-3900089561:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2942446769:ℚ)/10000000000),((161706790577854379831840786640998965610137490025088425849637:ℚ)/1418569368287500000000000000000000000000000000000000000000000),((-2378393211867253609148010621:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((1502686889:ℚ)/2000000000),((1956872827:ℚ)/2500000000),((-876872827:ℚ)/7387500000),((-924060667:ℚ)/24400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((755377169:ℚ)/5000000000),((3250102401735699995601885157460923038508751845231212868321:ℚ)/28128943695959472656250000000000000000000000000000000000000),((-103689724757012270564985989:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((193833577:ℚ)/250000000),((2076769793:ℚ)/2500000000),((-996769793:ℚ)/7625000000),((-133500731:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((549611592439374668380547092672300962385240831195970608373:ℚ)/4544745913696289062500000000000000000000000000000000000000),((-184897823:ℚ)/1024000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8232730769:ℚ)/10000000000),((5110513053:ℚ)/5000000000),((-983504351:ℚ)/5400000000),((-6778192307:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((26810966492538158774919785701124360005327533942327353:ℚ)/184528125000000000000000000000000000000000000000000000),((-184897823:ℚ)/1024000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((10146071099:ℚ)/10000000000),((3509331331:ℚ)/2500000000),((-2429331331:ℚ)/10000000000),((-12518213297:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((216378880416561087665682473170847110133:ℚ)/1190250000000000000000000000000000000000),((-184897823:ℚ)/1024000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC13
#check @N11Formalization.C450Source29GroupedC13.bound
#print axioms N11Formalization.C450Source29GroupedC13.valid0
#print axioms N11Formalization.C450Source29GroupedC13.valid1
#print axioms N11Formalization.C450Source29GroupedC13.valid2
#print axioms N11Formalization.C450Source29GroupedC13.valid3
#print axioms N11Formalization.C450Source29GroupedC13.valid4
#print axioms N11Formalization.C450Source29GroupedC13.valid5
#print axioms N11Formalization.C450Source29GroupedC13.valid6
#print axioms N11Formalization.C450Source29GroupedC13.valid7
#print axioms N11Formalization.C450Source29GroupedC13.valid8
#print axioms N11Formalization.C450Source29GroupedC13.valid9
#print axioms N11Formalization.C450Source29GroupedC13.valid10
#print axioms N11Formalization.C450Source29GroupedC13.valid11
#print axioms N11Formalization.C450Source29GroupedC13.valid12
#print axioms N11Formalization.C450Source29GroupedC13.bound
#print axioms N11Formalization.C450Source29GroupedC13.endpoint_checks
