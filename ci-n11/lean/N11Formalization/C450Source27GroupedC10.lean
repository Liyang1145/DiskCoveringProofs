import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC10
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-7:ℚ)/16),((-3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/16),((-3:ℚ)/8),((406581489:ℚ)/625000000),((1706052407:ℚ)/2500000000),((-7942366849:ℚ)/24800000000),((-699744467:ℚ)/3218750000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2716948123:ℚ)/5000000000),((1377274375511216283045459167590847753010550852033088171:ℚ)/6461055183410644531250000000000000000000000000000000000),((372184151463437916344939:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((52698459:ℚ)/78125000),((1388841887:ℚ)/2000000000),((-6521893209:ℚ)/20600000000),((-93095377:ℚ)/409765625),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4787900707:ℚ)/10000000000),((9210426266252644492795864071690731919969854687849233:ℚ)/44291849004849791526794433593750000000000000000000000),((4438727820804008383979:ℚ)/112812500000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((13730761:ℚ)/20000000),((3502096127:ℚ)/5000000000),((-16514672889:ℚ)/52450000000),((-24552283:ℚ)/105850000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2216518649:ℚ)/5000000000),((1597918192933438611403220285919248812746111835743941:ℚ)/7775495826591406250000000000000000000000000000000000),((245384609347869682939:ℚ)/7393280000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/16),((-3:ℚ)/8),((3462676297:ℚ)/5000000000),((1412832819:ℚ)/2000000000),((-6689829733:ℚ)/21170000000),((-6228028891:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((849068831:ℚ)/2000000000),((1438023815423645657632262741060842654623490327263919646041:ℚ)/6995715810937500000000000000000000000000000000000000000000),((13907996278705018895329531:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-7:ℚ)/16),((-3:ℚ)/8),((1746328477:ℚ)/2500000000),((890515657:ℚ)/1250000000),((-4233609599:ℚ)/13350000000),((-3158985431:ℚ)/13468750000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((506193357:ℚ)/1250000000),((1091585978980062211009212720976290058982119440228908233:ℚ)/5308990328758955001831054687500000000000000000000000000),((3118812639117023387877411:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-7:ℚ)/16),((-3:ℚ)/8),((7045264733:ℚ)/10000000000),((7184076021:ℚ)/10000000000),((-34288532147:ℚ)/107750000000),((-12815794199:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1922201107:ℚ)/5000000000),((88944324066779399762737178497849266241631074987666603390223:ℚ)/432469946713281250000000000000000000000000000000000000000000),((122307992658351586952491:ℚ)/5120000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/16),((-3:ℚ)/8),((1776301337:ℚ)/2500000000),((7244016667:ℚ)/10000000000),((-34708116669:ℚ)/108700000000),((-3248904011:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3543281:ℚ)/9765625),((33321469747783190081797090595688372394148786143046969697:ℚ)/161972674376296997070312500000000000000000000000000000000),((2399282310853038595063771:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/16),((-3:ℚ)/8),((286605441:ℚ)/400000000),((3651973729:ℚ)/5000000000),((-17563816103:ℚ)/54825000000),((-527016323:ℚ)/2212000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3399208567:ℚ)/10000000000),((158993253917209253023419244468610971254086082444288871:ℚ)/772632172418750000000000000000000000000000000000000000),((52171167884931279207179:ℚ)/2957312000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/16),((-3:ℚ)/8),((7225057023:ℚ)/10000000000),((463986281:ℚ)/625000000),((-2247903967:ℚ)/6912500000),((-13355171069:ℚ)/56250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((630844993:ℚ)/2000000000),((166716142027790441004719954946653833664968296955966888993:ℚ)/800961256027221679687500000000000000000000000000000000000),((26808557978076718676774411:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/16),((-3:ℚ)/8),((918108873:ℚ)/1250000000),((7543577081:ℚ)/10000000000),((-36805039567:ℚ)/112500000000),((-1714326619:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1299213741:ℚ)/5000000000),((1427035085430724340901916106070315746330027973250920359:ℚ)/6853610156250000000000000000000000000000000000000000000),((236890565521043632402811:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-7:ℚ)/16),((-3:ℚ)/8),((7464649143:ℚ)/10000000000),((8022433517:ℚ)/10000000000),((-3089002663:ℚ)/8800000000),((-14073947429:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((7383213:ℚ)/39062500),((3449741078383737909915236006032482282850783924985618854713:ℚ)/15604943750000000000000000000000000000000000000000000000000),((3445711310639849152573691:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/16),((-3:ℚ)/8),((7943437749:ℚ)/10000000000),((340033311:ℚ)/400000000),((-1740233177:ℚ)/4880000000),((-15510313247:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((846787952484180256435193893931490282123394107390619624303:ℚ)/3842121600000000000000000000000000000000000000000000000000),((-684099:ℚ)/128000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/16),((-3:ℚ)/8),((8421777303:ℚ)/10000000000),((5205587611:ℚ)/5000000000),((-28439113277:ℚ)/64800000000),((-16945331909:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((22433433661771355102642284039020911474507545335671958111521:ℚ)/86400000000000000000000000000000000000000000000000000000000),((-684099:ℚ)/128000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/16),((-3:ℚ)/8),((10331938533:ℚ)/10000000000),((7111638019:ℚ)/5000000000),((-41781466133:ℚ)/80000000000),((-22675815599:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((212028641010944405703253799817116907641058491029107965651:ℚ)/700819200000000000000000000000000000000000000000000000000),((-684099:ℚ)/128000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source27 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source27 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC10
#check @N11Formalization.C450Source27GroupedC10.bound
#print axioms N11Formalization.C450Source27GroupedC10.valid0
#print axioms N11Formalization.C450Source27GroupedC10.valid1
#print axioms N11Formalization.C450Source27GroupedC10.valid2
#print axioms N11Formalization.C450Source27GroupedC10.valid3
#print axioms N11Formalization.C450Source27GroupedC10.valid4
#print axioms N11Formalization.C450Source27GroupedC10.valid5
#print axioms N11Formalization.C450Source27GroupedC10.valid6
#print axioms N11Formalization.C450Source27GroupedC10.valid7
#print axioms N11Formalization.C450Source27GroupedC10.valid8
#print axioms N11Formalization.C450Source27GroupedC10.valid9
#print axioms N11Formalization.C450Source27GroupedC10.valid10
#print axioms N11Formalization.C450Source27GroupedC10.valid11
#print axioms N11Formalization.C450Source27GroupedC10.valid12
#print axioms N11Formalization.C450Source27GroupedC10.valid13
#print axioms N11Formalization.C450Source27GroupedC10.bound
#print axioms N11Formalization.C450Source27GroupedC10.endpoint_checks
