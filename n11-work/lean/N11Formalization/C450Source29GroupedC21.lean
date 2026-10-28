import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((719754461:ℚ)/1250000000),((304100009:ℚ)/500000000),((1259754461:ℚ)/3218750000),((483300009:ℚ)/992000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7111124497:ℚ)/10000000000),((-94379688583797972440760124855303170410417231056033763:ℚ)/625263404846191406250000000000000000000000000000000000),((-2574702339495018517153593:ℚ)/7393280000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((1199795357:ℚ)/2000000000),((316129053:ℚ)/500000000),((2063795357:ℚ)/5340000000),((495329053:ℚ)/1030000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((132212923:ℚ)/200000000),((-35212782823517923061057106986742716280322198582467953:ℚ)/237927037500000000000000000000000000000000000000000000),((-7783494467714981232915731:ℚ)/22179840000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((6239668047:ℚ)/10000000000),((6442789219:ℚ)/10000000000),((10559668047:ℚ)/27175000000),((3342263073:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6076202913:ℚ)/10000000000),((-18723710049072052980496114137811847623044012617874361083:ℚ)/125426318652343750000000000000000000000000000000000000000),((-1054594071726156140617901233:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((794991049:ℚ)/1250000000),((410184149:ℚ)/625000000),((190713007:ℚ)/493750000),((634184149:ℚ)/1358750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5793244383:ℚ)/10000000000),((-5215529264865667390446883627935989613814377010921:ℚ)/35264897346496582031250000000000000000000000000000),((-4133190956278227107057953:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((3240067943:ℚ)/5000000000),((6683055199:ℚ)/10000000000),((5400067943:ℚ)/14062500000),((10267055199:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5497609261:ℚ)/10000000000),((-29852831890061956131413655939221189662606113861265121:ℚ)/203680247068405151367187500000000000000000000000000000),((-1061420576206731613828674153:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6600293269:ℚ)/10000000000),((6803118127:ℚ)/10000000000),((10920293269:ℚ)/28600000000),((3462372709:ℚ)/7500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((518709581:ℚ)/1000000000),((-21243086387891946051505373461364881705627150234693028889:ℚ)/146210350000000000000000000000000000000000000000000000000),((-1064565452571392033891534537:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((3360201549:ℚ)/5000000000),((3461568733:ℚ)/5000000000),((5520201549:ℚ)/14537500000),((5253568733:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4858816657:ℚ)/10000000000),((-2766353570134884704911583312401282255845054767885042241:ℚ)/19202120935058593750000000000000000000000000000000000000),((-266882950008801625715252017:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((3420233877:ℚ)/5000000000),((7043115361:ℚ)/10000000000),((1860077959:ℚ)/4925000000),((10627115361:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4508855939:ℚ)/10000000000),((-26670231608865741732370096413952611757097528159772979:ℚ)/186654614257812500000000000000000000000000000000000000),((-1070319885173141623287118313:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((1392097893:ℚ)/2000000000),((3641477361:ℚ)/5000000000),((2256097893:ℚ)/6100000000),((5433477361:ℚ)/11820000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((413166883:ℚ)/1000000000),((-196315434098184106338028627542823418452083273384372177:ℚ)/1418631250000000000000000000000000000000000000000000000),((-796719489449300222565830939:ℚ)/2217984000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((3600206119:ℚ)/5000000000),((121284631:ℚ)/156250000),((5760206119:ℚ)/16200000000),((177284631:ℚ)/381250000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1628567431:ℚ)/5000000000),((-1154422125608361237903611160239509012154809155830455153:ℚ)/8857350000000000000000000000000000000000000000000000000),((-10890721467290451:ℚ)/30400000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((7679825649:ℚ)/10000000000),((1209396839:ℚ)/1250000000),((11999825649:ℚ)/40000000000),((552465613:ℚ)/1080000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-40132493294671299065264623914509913410738801554739877069:ℚ)/400000000000000000000000000000000000000000000000000000000),((-381917159:ℚ)/1024000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((1918648787:ℚ)/2000000000),((67451617:ℚ)/50000000),((2782648787:ℚ)/11040000000),((85371617:ℚ)/160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-449906847572538680608135835629347305620849009343704949:ℚ)/6307372800000000000000000000000000000000000000000000000),((-381917159:ℚ)/1024000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC21
#check @N11Formalization.C450Source29GroupedC21.bound
#print axioms N11Formalization.C450Source29GroupedC21.valid0
#print axioms N11Formalization.C450Source29GroupedC21.valid1
#print axioms N11Formalization.C450Source29GroupedC21.valid2
#print axioms N11Formalization.C450Source29GroupedC21.valid3
#print axioms N11Formalization.C450Source29GroupedC21.valid4
#print axioms N11Formalization.C450Source29GroupedC21.valid5
#print axioms N11Formalization.C450Source29GroupedC21.valid6
#print axioms N11Formalization.C450Source29GroupedC21.valid7
#print axioms N11Formalization.C450Source29GroupedC21.valid8
#print axioms N11Formalization.C450Source29GroupedC21.valid9
#print axioms N11Formalization.C450Source29GroupedC21.valid10
#print axioms N11Formalization.C450Source29GroupedC21.valid11
#print axioms N11Formalization.C450Source29GroupedC21.bound
#print axioms N11Formalization.C450Source29GroupedC21.endpoint_checks
