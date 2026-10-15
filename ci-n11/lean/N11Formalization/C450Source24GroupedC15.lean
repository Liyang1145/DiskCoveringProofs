import N11Formalization.C450Source24Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source24GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source24Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((1547282903:ℚ)/2500000000),((3244008713:ℚ)/5000000000),((275991287:ℚ)/25750000000),((2132717097:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3095858727:ℚ)/5000000000),((3503721024620827744399129252682946031761:ℚ)/20227374016000000000000000000000000000000),((-8383963101667430218896117:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source24 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source24 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((3214590253:ℚ)/5000000000),((1681913133:ℚ)/2500000000),((78086867:ℚ)/13350000000),((4145409747:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2812309633:ℚ)/5000000000),((20358858645617432401234707747017114786031637083326102314297:ℚ)/118865074314880371093750000000000000000000000000000000000000),((-35347752373391915707871917:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source24 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source24 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6669045297:ℚ)/10000000000),((6847413383:ℚ)/10000000000),((192586617:ℚ)/54350000000),((8050954703:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5001597551:ℚ)/10000000000),((2280149447668658117090804003925668030908542601903773005636839111:ℚ)/13494106165048200000000000000000000000000000000000000000000000000),((-445945962670362939934689551:ℚ)/1774387200000000000000000000)⟩
theorem valid2 : Valid source24 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source24 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1357782961:ℚ)/2000000000),((3483569537:ℚ)/5000000000),((36430463:ℚ)/27650000000),((1586217039:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4662101249:ℚ)/10000000000),((1307584790474423866506141412460380584779381669559942847099:ℚ)/7768404472051562500000000000000000000000000000000000000000),((-6091256748145669907603973:ℚ)/23658496000000000000000000)⟩
theorem valid3 : Valid source24 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((3454372661:ℚ)/5000000000),((7086833871:ℚ)/10000000000),((-6690553:ℚ)/7900000000),((3905627339:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2149044021:ℚ)/5000000000),((1809132030393974264099367606422957212145968834731703761:ℚ)/10785228125000000000000000000000000000000000000000000000),((-38979223717852754091698173:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source24 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source24 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7028538859:ℚ)/10000000000),((7206522621:ℚ)/10000000000),((-166522621:ℚ)/56250000000),((7691461141:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3902664009:ℚ)/10000000000),((744108873802479593500452121016342842016625459178505465071:ℚ)/4449462890625000000000000000000000000000000000000000000000),((-159555140035535036072222653:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source24 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source24 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source24 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((714829729:ℚ)/1000000000),((7326211371:ℚ)/10000000000),((-286211371:ℚ)/57200000000),((5294897:ℚ)/80000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((433131133:ℚ)/1250000000),((2201651795654576867004671127031632750435696650531:ℚ)/13200000000000000000000000000000000000000000000000),((-1631962075996760471544933:ℚ)/5914624000000000000000000)⟩
theorem valid6 : Valid source24 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source24 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((1453604473:ℚ)/2000000000),((7445892257:ℚ)/10000000000),((-405892257:ℚ)/58150000000),((1490395527:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2966581663:ℚ)/10000000000),((1636018559957399478354691379109989121480990062944823493:ℚ)/9831485918750000000000000000000000000000000000000000000),((-6673605897433371412704277:ℚ)/23658496000000000000000000)⟩
theorem valid7 : Valid source24 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source24 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((7387715717:ℚ)/10000000000),((7685168429:ℚ)/10000000000),((-215056143:ℚ)/19700000000),((2444094761:ℚ)/39400000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1184549577:ℚ)/5000000000),((95596901091471775835779894332164596021077381480208811017:ℚ)/573402975000000000000000000000000000000000000000000000000),((-472263174729774514639637:ℚ)/1638400000000000000000000)⟩
theorem valid8 : Valid source24 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source24 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source24 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((3813506637:ℚ)/5000000000),((2040851281:ℚ)/2500000000),((-280851281:ℚ)/15250000000),((3546493363:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((29690507916832488163513789763316736714248867899145002593:ℚ)/177328906250000000000000000000000000000000000000000000000),((-306378999:ℚ)/1024000000)⟩
theorem valid9 : Valid source24 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source24 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((4052644451:ℚ)/5000000000),((10073254117:ℚ)/10000000000),((-3033254117:ℚ)/64800000000),((3307355549:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((27716525501774864033110712133601335648429672307723925557:ℚ)/159432300000000000000000000000000000000000000000000000000),((-306378999:ℚ)/1024000000)⟩
theorem valid10 : Valid source24 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source24 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10015256083:ℚ)/10000000000),((3471194853:ℚ)/2500000000),((-1711194853:ℚ)/20000000000),((4704743917:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((99877995035380835401119035045564340349:ℚ)/512000000000000000000000000000000000000),((-306378999:ℚ)/1024000000)⟩
theorem valid11 : Valid source24 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source24 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source24 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source24 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source24 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source24 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source24 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source24 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source24 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source24 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source24 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source24 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source24GroupedC15
#check @N11Formalization.C450Source24GroupedC15.bound
#print axioms N11Formalization.C450Source24GroupedC15.valid0
#print axioms N11Formalization.C450Source24GroupedC15.valid1
#print axioms N11Formalization.C450Source24GroupedC15.valid2
#print axioms N11Formalization.C450Source24GroupedC15.valid3
#print axioms N11Formalization.C450Source24GroupedC15.valid4
#print axioms N11Formalization.C450Source24GroupedC15.valid5
#print axioms N11Formalization.C450Source24GroupedC15.valid6
#print axioms N11Formalization.C450Source24GroupedC15.valid7
#print axioms N11Formalization.C450Source24GroupedC15.valid8
#print axioms N11Formalization.C450Source24GroupedC15.valid9
#print axioms N11Formalization.C450Source24GroupedC15.valid10
#print axioms N11Formalization.C450Source24GroupedC15.valid11
#print axioms N11Formalization.C450Source24GroupedC15.bound
#print axioms N11Formalization.C450Source24GroupedC15.endpoint_checks
