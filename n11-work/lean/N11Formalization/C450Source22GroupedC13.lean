import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((3149999999:ℚ)/5000000000),((6595914679:ℚ)/10000000000),((-3395914679:ℚ)/24800000000),((-2729999997:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((185491637:ℚ)/312500000),((1944653894256713046833102432741124920292956912894788284621:ℚ)/13232241015625000000000000000000000000000000000000000000000),((-172649994276403745703189873:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6539358827:ℚ)/10000000000),((1708816037:ℚ)/2500000000),((-908816037:ℚ)/6437500000),((-2059358827:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((334162469:ℚ)/625000000),((528900141364273688082911778922756834274891026005547333123:ℚ)/3630590350000000000000000000000000000000000000000000000000),((-765508766657837491035887017:ℚ)/7393280000000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3389291967:ℚ)/5000000000),((6954889851:ℚ)/10000000000),((-3754889851:ℚ)/26700000000),((-3447875901:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7331643:ℚ)/15625000),((19207225644606554259904335073346945123756277237966650234809:ℚ)/133955308320703125000000000000000000000000000000000000000000),((-210185228352228859111315697:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3449075393:ℚ)/5000000000),((7074485143:ℚ)/10000000000),((-3874485143:ℚ)/27175000000),((-3627226179:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((541427613:ℚ)/1250000000),((1282939515553005049830537230956652759881012247135358037459:ℚ)/8975837587841796875000000000000000000000000000000000000000),((-219619864702773874433044977:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1754422323:ℚ)/2500000000),((7194051589:ℚ)/10000000000),((-3994051589:ℚ)/27650000000),((-634422323:ℚ)/9375000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((788003861:ℚ)/2000000000),((339742976296258913044707732034750766024132975273036473:ℚ)/2383813261985778808593750000000000000000000000000000000),((-158639236728578298389297:ℚ)/1280000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((1784300227:ℚ)/2500000000),((1828397661:ℚ)/2500000000),((-1028397661:ℚ)/7031250000),((-1992900681:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1753893951:ℚ)/5000000000),((93525358036480472362499927229529500309764241409684861063:ℚ)/657946575000000000000000000000000000000000000000000000000),((-59637726780329547601565817:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7256686989:ℚ)/10000000000),((1858275917:ℚ)/2500000000),((-1058275917:ℚ)/7150000000),((-8330060967:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((377148091:ℚ)/1250000000),((99685327705440976047308606587703361199840131710866041143247:ℚ)/702951243190625000000000000000000000000000000000000000000000),((-992190020017942067046452633:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7376148803:ℚ)/10000000000),((1888147983:ℚ)/2500000000),((-1088147983:ℚ)/7268750000),((-2896148803:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1216549263:ℚ)/5000000000),((7863798022197527312881250121028433098077976940306681180087:ℚ)/55572304993750000000000000000000000000000000000000000000000),((-1030259752112606620272443257:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((3747793767:ℚ)/5000000000),((1558299773:ℚ)/2000000000),((-918299773:ℚ)/5910000000),((-4523381301:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((829760683:ℚ)/5000000000),((59665596899572015699165527604307131638354788901195073137437:ℚ)/419205534375000000000000000000000000000000000000000000000000),((-267103286987985009787523297:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((3867200053:ℚ)/5000000000),((8269063223:ℚ)/10000000000),((-5069063223:ℚ)/30500000000),((-1627200053:ℚ)/21600000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((92158961935056091655966785273442891926545842238917925613:ℚ)/640353600000000000000000000000000000000000000000000000000),((-76304787:ℚ)/512000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((4105896301:ℚ)/5000000000),((10176870123:ℚ)/10000000000),((-6976870123:ℚ)/32400000000),((-5597688903:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((19977810866682467287759794558047271637701155199651846819889:ℚ)/129600000000000000000000000000000000000000000000000000000000),((-76304787:ℚ)/512000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5059538593:ℚ)/5000000000),((6993005881:ℚ)/5000000000),((-5393005881:ℚ)/20000000000),((-2819538593:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((20205471882879921789359278209769796082743713757349830797:ℚ)/116803200000000000000000000000000000000000000000000000000),((-76304787:ℚ)/512000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC13
#check @N11Formalization.C450Source22GroupedC13.bound
#print axioms N11Formalization.C450Source22GroupedC13.valid0
#print axioms N11Formalization.C450Source22GroupedC13.valid1
#print axioms N11Formalization.C450Source22GroupedC13.valid2
#print axioms N11Formalization.C450Source22GroupedC13.valid3
#print axioms N11Formalization.C450Source22GroupedC13.valid4
#print axioms N11Formalization.C450Source22GroupedC13.valid5
#print axioms N11Formalization.C450Source22GroupedC13.valid6
#print axioms N11Formalization.C450Source22GroupedC13.valid7
#print axioms N11Formalization.C450Source22GroupedC13.valid8
#print axioms N11Formalization.C450Source22GroupedC13.valid9
#print axioms N11Formalization.C450Source22GroupedC13.valid10
#print axioms N11Formalization.C450Source22GroupedC13.valid11
#print axioms N11Formalization.C450Source22GroupedC13.bound
#print axioms N11Formalization.C450Source22GroupedC13.endpoint_checks
