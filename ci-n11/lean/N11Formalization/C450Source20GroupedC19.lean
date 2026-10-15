import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((1503098217:ℚ)/2500000000),((1636666301:ℚ)/2500000000),((981032739:ℚ)/4450000000),((7949998903:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((658184039:ℚ)/1000000000),((967319246682149758493519386116140492261:ℚ)/15102368704000000000000000000000000000000),((-224466190347945467370772567:ℚ)/924160000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((649062379:ℚ)/1000000000),((6785489531:ℚ)/10000000000),((1225062379:ℚ)/5530000000),((32516468593:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2735569991:ℚ)/5000000000),((208858451893458080661128209220428066136263530550864083001159331:ℚ)/3492491011720200000000000000000000000000000000000000000000000000),((-3787548324480278901919743687:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((841196399:ℚ)/1250000000),((1726216969:ℚ)/2500000000),((1561196399:ℚ)/7031250000),((8218650907:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2416460523:ℚ)/5000000000),((44395394752276288981838623626789247846632903355311188669:ℚ)/764403043359375000000000000000000000000000000000000000000),((-242836237318409891117292687:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((214031497:ℚ)/312500000),((7024225189:ℚ)/10000000000),((394031497:ℚ)/1787500000),((33232675567:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1120749953:ℚ)/2500000000),((5250059397423257380781250503273051694130035009824426017203127:ℚ)/90987066650390625000000000000000000000000000000000000000000000),((-3931471529852465630860297607:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1393684323:ℚ)/2000000000),((7143562511:ℚ)/10000000000),((2545684323:ℚ)/11630000000),((2583899041:ℚ)/8800000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2052798459:ℚ)/5000000000),((123920703231925085509592478184815231798002740896684144772283:ℚ)/2160323206800000000000000000000000000000000000000000000000000),((-3977459630445361794565457407:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((7087813463:ℚ)/10000000000),((1452576163:ℚ)/2000000000),((12847813463:ℚ)/59100000000),((6789728489:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3692257843:ℚ)/10000000000),((65312832926459387596728574298495438361758885411100597897683:ℚ)/1144650411062306250000000000000000000000000000000000000000000),((-8470199139483492834385517:ℚ)/31129600000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1441436903:ℚ)/2000000000),((3691090507:ℚ)/5000000000),((2593436903:ℚ)/12010000000),((17153271521:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((3229171209:ℚ)/10000000000),((158523875867471142667155114203015754775067948476938675956177467:ℚ)/2791384957832540625000000000000000000000000000000000000000000000),((-1017281718457354359007978983:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((3663267883:ℚ)/5000000000),((7501463959:ℚ)/10000000000),((6543267883:ℚ)/30500000000),((34664391877:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1345362713:ℚ)/5000000000),((1139202786966632792103372795368614909178416982325674600513917:ℚ)/20143675372878125000000000000000000000000000000000000000000000),((-4114806908792793472846718927:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((930733519:ℚ)/1250000000),((1934995311:ℚ)/2500000000),((1650733519:ℚ)/7862500000),((8844985933:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1008697907:ℚ)/5000000000),((500181932107687743120538552910376684802838262030255270276333:ℚ)/8769823224707031250000000000000000000000000000000000000000000),((-34222312373506793:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((7684479779:ℚ)/10000000000),((7978438513:ℚ)/10000000000),((13444479779:ℚ)/64800000000),((36095315539:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2313511126568163559315001123850465877513265212051124857705219:ℚ)/40818964450725000000000000000000000000000000000000000000000000),((-292800597:ℚ)/1024000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((3961512893:ℚ)/5000000000),((617778273:ℚ)/625000000),((6841512893:ℚ)/40000000000),((2613334819:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((19833978012167717434576153709168914814700499135392377:ℚ)/311391210937500000000000000000000000000000000000000000),((-292800597:ℚ)/1024000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9829596379:ℚ)/10000000000),((1369149847:ℚ)/1000000000),((15589596379:ℚ)/110400000000),((5323449541:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((188995422698756259529273612024833385823:ℚ)/2437632000000000000000000000000000000000),((-292800597:ℚ)/1024000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC19
#check @N11Formalization.C450Source20GroupedC19.bound
#print axioms N11Formalization.C450Source20GroupedC19.valid0
#print axioms N11Formalization.C450Source20GroupedC19.valid1
#print axioms N11Formalization.C450Source20GroupedC19.valid2
#print axioms N11Formalization.C450Source20GroupedC19.valid3
#print axioms N11Formalization.C450Source20GroupedC19.valid4
#print axioms N11Formalization.C450Source20GroupedC19.valid5
#print axioms N11Formalization.C450Source20GroupedC19.valid6
#print axioms N11Formalization.C450Source20GroupedC19.valid7
#print axioms N11Formalization.C450Source20GroupedC19.valid8
#print axioms N11Formalization.C450Source20GroupedC19.valid9
#print axioms N11Formalization.C450Source20GroupedC19.valid10
#print axioms N11Formalization.C450Source20GroupedC19.valid11
#print axioms N11Formalization.C450Source20GroupedC19.bound
#print axioms N11Formalization.C450Source20GroupedC19.endpoint_checks
