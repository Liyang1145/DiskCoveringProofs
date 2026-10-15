import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC16
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-1:ℚ)/16),(0:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/16),(0:ℚ),((6105210887:ℚ)/10000000000),((3209134669:ℚ)/5000000000),((5110865331:ℚ)/51500000000),((27:ℚ)/155),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3189759239:ℚ)/5000000000),((267065843570568879761839996527:ℚ)/2469161867187500000000000000000),((-34109786440008537:ℚ)/121600000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/16),(0:ℚ),((634625923:ℚ)/1000000000),((832350489:ℚ)/1250000000),((1247649511:ℚ)/13350000000),((432:ℚ)/2575),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5826015503:ℚ)/10000000000),((1820265562424338127708893432369350599:ℚ)/16905255013671875000000000000000000000),((-3566839321447773:ℚ)/12160000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((102922653:ℚ)/156250000),((6778990177:ℚ)/10000000000),((9861009823:ℚ)/108700000000),((72:ℚ)/445),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5222137659:ℚ)/10000000000),((276271298277487613896824422129186706635159:ℚ)/2603029738628125000000000000000000000000000),((-581645831088003:ℚ)/1900000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((3353678541:ℚ)/5000000000),((6899126227:ℚ)/10000000000),((9740873773:ℚ)/110600000000),((864:ℚ)/5435),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((19581793:ℚ)/40000000),((130261387534422818502027633648082124324108819:ℚ)/1227407906584146875000000000000000000000000000),((-19001617115857491:ℚ)/60800000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/16),(0:ℚ),((3413804923:ℚ)/5000000000),((877401833:ℚ)/1250000000),((1202598167:ℚ)/14062500000),((432:ℚ)/2765),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1136881541:ℚ)/2500000000),((52832634796894624921247627545359789775319:ℚ)/497658231353759765625000000000000000000000),((-19390391355676773:ℚ)/60800000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/16),(0:ℚ),((1736952729:ℚ)/2500000000),((3569628957:ℚ)/5000000000),((431851913:ℚ)/5200000000),((96:ℚ)/625),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((521627829:ℚ)/1250000000),((14026651874201193846547154270192854253:ℚ)/132031250000000000000000000000000000000),((-9889499235030279:ℚ)/30400000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/16),(0:ℚ),((7067962929:ℚ)/10000000000),((3629629119:ℚ)/5000000000),((4690370881:ℚ)/58150000000),((108:ℚ)/715),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((376396753:ℚ)/1000000000),((164309097638521346284928305258314070049047:ℚ)/1544996772571484375000000000000000000000000),((-40334893968730479:ℚ)/121600000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/16),(0:ℚ),((1437613669:ℚ)/2000000000),((7379217749:ℚ)/10000000000),((3086927417:ℚ)/39400000000),((864:ℚ)/5815),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((25839983:ℚ)/78125000),((40633327274346808710968444116163968933715219:ℚ)/381550137020768750000000000000000000000000000),((-8222297940684219:ℚ)/24320000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/16),(0:ℚ),((7308129461:ℚ)/10000000000),((761902211:ℚ)/1000000000),((902097789:ℚ)/12200000000),((144:ℚ)/985),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2780373309:ℚ)/10000000000),((38300648412090530067910856047084210253727:ℚ)/355605411662500000000000000000000000000000),((-41887798996482411:ℚ)/121600000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/16),(0:ℚ),((7548127249:ℚ)/10000000000),((2024555023:ℚ)/2500000000),((2135444977:ℚ)/32400000000),((216:ℚ)/1525),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1169028693:ℚ)/10000000000),((272831736664560707124427456680179154773:ℚ)/2482037235000000000000000000000000000000),((-43439612933798799:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/16),(0:ℚ),((8027677121:ℚ)/10000000000),((10010985373:ℚ)/10000000000),((6629014627:ℚ)/160000000000),((2:ℚ)/15),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((19247968335003659420270655859896423883:ℚ)/162000000000000000000000000000000000000),((-5759871:ℚ)/16000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/16),(0:ℚ),((9941508937:ℚ)/10000000000),((13825909311:ℚ)/10000000000),((2814090689:ℚ)/220800000000),((27:ℚ)/250),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((23762297587226885915989913:ℚ)/169280000000000000000000000),((-5759871:ℚ)/16000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC16
#check @N11Formalization.C450Source28GroupedC16.bound
#print axioms N11Formalization.C450Source28GroupedC16.valid0
#print axioms N11Formalization.C450Source28GroupedC16.valid1
#print axioms N11Formalization.C450Source28GroupedC16.valid2
#print axioms N11Formalization.C450Source28GroupedC16.valid3
#print axioms N11Formalization.C450Source28GroupedC16.valid4
#print axioms N11Formalization.C450Source28GroupedC16.valid5
#print axioms N11Formalization.C450Source28GroupedC16.valid6
#print axioms N11Formalization.C450Source28GroupedC16.valid7
#print axioms N11Formalization.C450Source28GroupedC16.valid8
#print axioms N11Formalization.C450Source28GroupedC16.valid9
#print axioms N11Formalization.C450Source28GroupedC16.valid10
#print axioms N11Formalization.C450Source28GroupedC16.valid11
#print axioms N11Formalization.C450Source28GroupedC16.bound
#print axioms N11Formalization.C450Source28GroupedC16.endpoint_checks
