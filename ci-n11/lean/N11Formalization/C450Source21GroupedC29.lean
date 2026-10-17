import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5532434793:ℚ)/10000000000),((760755531:ℚ)/1250000000),((19637304379:ℚ)/26700000000),((11489821903:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((59020801:ℚ)/78125000),((-5090904282990872231243380329906813991:ℚ)/52872675000000000000000000000000000000),((-1332522132039590549225163:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6008687931:ℚ)/10000000000),((6324197291:ℚ)/10000000000),((21066063793:ℚ)/27650000000),((95014564783:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((658980599:ℚ)/1000000000),((-14926692898802481619380110522819015482685161769184400977:ℚ)/132119044531250000000000000000000000000000000000000000000),((-233836070580596529431443:ℚ)/640000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((1249349937:ℚ)/2000000000),((3281153391:ℚ)/5000000000),((4356049811:ℚ)/5720000000),((49054994083:ℚ)/55300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1514965661:ℚ)/2500000000),((-132392444901008964442360555452735685221125305310239779:ℚ)/1169682800000000000000000000000000000000000000000000000),((-20885068692622343176427523:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1296954799:ℚ)/2000000000),((6681346537:ℚ)/10000000000),((4498864397:ℚ)/5815000000),((99657504981:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2742958891:ℚ)/5000000000),((-37063048927765404236150106628244788903530078884955173:ℚ)/307233934960937500000000000000000000000000000000000000),((-83100015931884366103446227:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6603773261:ℚ)/10000000000),((6800376943:ℚ)/10000000000),((22851319783:ℚ)/29550000000),((101204900259:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2588926063:ℚ)/5000000000),((-4859897617210455382869832190653166732716990143991457303:ℚ)/40317396679687500000000000000000000000000000000000000000),((-82657765050519127532267267:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6722764489:ℚ)/10000000000),((6919398447:ℚ)/10000000000),((23208293467:ℚ)/30025000000),((102752179811:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2426079493:ℚ)/5000000000),((-20376026528864217208308953957324234485126088270088368283:ℚ)/169172226660156250000000000000000000000000000000000000000),((-82213520931686224873455747:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((3420874031:ℚ)/5000000000),((3519205733:ℚ)/5000000000),((11782622093:ℚ)/15250000000),((52149674529:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2252494247:ℚ)/5000000000),((-2667650613665707512204239347803023231911638842028753197:ℚ)/22166113281250000000000000000000000000000000000000000000),((-20441820615736013827692587:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6960724339:ℚ)/10000000000),((894677049:ℚ)/1250000000),((23922173017:ℚ)/30975000000),((13230801637:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4130899059:ℚ)/10000000000),((-1861291157984936704581842614413758605600027994173580611:ℚ)/15478637036132812500000000000000000000000000000000000000),((-1270610134340633239405683:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((7079693657:ℚ)/10000000000),((3638206797:ℚ)/5000000000),((24279080971:ℚ)/31450000000),((53696688361:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1860874841:ℚ)/5000000000),((-22811775115851862663669387580618212333963588070291779:ℚ)/189863730621337890625000000000000000000000000000000000),((-20217204587565371327569947:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((1799664083:ℚ)/2500000000),((1878596547:ℚ)/2500000000),((6158992249:ℚ)/8100000000),((27621755111:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3264347511:ℚ)/10000000000),((-4658108947769009932052393012369234821912386236020001:ℚ)/41006250000000000000000000000000000000000000000000000),((-4997647817153334735061947:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((3718281463:ℚ)/5000000000),((8466027891:ℚ)/10000000000),((12674844389:ℚ)/18100000000),((122858362583:ℚ)/129600000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((2077614013:ℚ)/10000000000),((-189633179298540420270898059977380982048335511902729221:ℚ)/2316305078125000000000000000000000000000000000000000000),((-5514839:ℚ)/16000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((1677595087:ℚ)/2000000000),((941735701:ℚ)/1000000000),((5640785261:ℚ)/8000000000),((13522564113:ℚ)/14480000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-67752096515242987952644066254730011475015049027463669:ℚ)/800000000000000000000000000000000000000000000000000000),((-5514839:ℚ)/16000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((4669559539:ℚ)/5000000000),((6610420583:ℚ)/5000000000),((15528678617:ℚ)/27600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-20774677733208252601149309905936137:ℚ)/1752048000000000000000000000000000000),((-5514839:ℚ)/16000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
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
private theorem node9_11 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source21 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source21 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source21 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC29
#check @N11Formalization.C450Source21GroupedC29.bound
#print axioms N11Formalization.C450Source21GroupedC29.valid0
#print axioms N11Formalization.C450Source21GroupedC29.valid1
#print axioms N11Formalization.C450Source21GroupedC29.valid2
#print axioms N11Formalization.C450Source21GroupedC29.valid3
#print axioms N11Formalization.C450Source21GroupedC29.valid4
#print axioms N11Formalization.C450Source21GroupedC29.valid5
#print axioms N11Formalization.C450Source21GroupedC29.valid6
#print axioms N11Formalization.C450Source21GroupedC29.valid7
#print axioms N11Formalization.C450Source21GroupedC29.valid8
#print axioms N11Formalization.C450Source21GroupedC29.valid9
#print axioms N11Formalization.C450Source21GroupedC29.valid10
#print axioms N11Formalization.C450Source21GroupedC29.valid11
#print axioms N11Formalization.C450Source21GroupedC29.valid12
#print axioms N11Formalization.C450Source21GroupedC29.bound
#print axioms N11Formalization.C450Source21GroupedC29.endpoint_checks
