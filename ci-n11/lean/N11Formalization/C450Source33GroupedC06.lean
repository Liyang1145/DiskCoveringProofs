import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((344948567:ℚ)/500000000),((7130008127:ℚ)/10000000000),((-58590089397:ℚ)/99200000000),((-242548567:ℚ)/505500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((865769569:ℚ)/2000000000),((4368088178786096447361166401286445831:ℚ)/12300800000000000000000000000000000000),((17251948245203146646918749:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7019167401:ℚ)/10000000000),((1797507499:ℚ)/2500000000),((-14812582489:ℚ)/25275000000),((-4971167401:ℚ)/10205000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((491868741:ℚ)/1250000000),((779426601972274120273909836554463:ℚ)/2218144531250000000000000000000000),((6841505518218611739643138141:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((3539622439:ℚ)/5000000000),((7250039739:ℚ)/10000000000),((-59910437129:ℚ)/102050000000),((-2515622439:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((3723373189:ℚ)/10000000000),((1055051511507611116200925575337945957:ℚ)/3004096875000000000000000000000000000),((1702880371099989184860204861:ℚ)/3696640000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7139309171:ℚ)/10000000000),((3655018849:ℚ)/5000000000),((-30285207339:ℚ)/51500000000),((-565701019:ℚ)/1155000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((699941247:ℚ)/2000000000),((581899958305591476198911265811859057:ℚ)/1657656250000000000000000000000000000),((6781305976809962338351820181:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((899920081:ℚ)/1250000000),((3685012099:ℚ)/5000000000),((-10205044363:ℚ)/17325000000),((-643920081:ℚ)/1311250000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1630728137:ℚ)/5000000000),((3134543162902396686151466697817121:ℚ)/8933203125000000000000000000000000),((105482171326217042282048301:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3629699833:ℚ)/5000000000),((1485999911:ℚ)/2000000000),((-12377999021:ℚ)/20980000000),((-2605699833:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1502575051:ℚ)/5000000000),((192983255375071813836716575949978453:ℚ)/550200500000000000000000000000000000),((1680045104452569537127489149:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((914928321:ℚ)/1250000000),((936245509:ℚ)/1250000000),((-7818700599:ℚ)/13231250000),((-7403689:ℚ)/15000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((272569151:ℚ)/1000000000),((230187129831646220060706040728237607:ℚ)/656497412109375000000000000000000000),((104519848536915289463203981:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((1475888337:ℚ)/2000000000),((475616359:ℚ)/625000000),((-3991779949:ℚ)/6675000000),((-1066288337:ℚ)/2174000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((301881059:ℚ)/1250000000),((6564183551340281091937681990298801:ℚ)/18564843750000000000000000000000000),((266325144083099019489578029:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((7499437823:ℚ)/10000000000),((7729719431:ℚ)/10000000000),((-65186913741:ℚ)/108700000000),((-5451437823:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((814283403:ℚ)/5000000000),((1957068417639174612889163087478750473:ℚ)/5538604687500000000000000000000000000),((6595150309187121302571570189:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((7619390493:ℚ)/10000000000),((99616537:ℚ)/125000000),((-121111701:ℚ)/197500000),((-5571390493:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((1094230881249712580787389509617:ℚ)/3047363281250000000000000000000),((453022159:ℚ)/1024000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7859174261:ℚ)/10000000000),((27895281:ℚ)/31250000),((-244848091:ℚ)/357500000),((-645686029:ℚ)/1440000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((188303161326527833395114974243089:ℚ)/479273437500000000000000000000000),((453022159:ℚ)/1024000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((8816954051:ℚ)/10000000000),((2167341257:ℚ)/2000000000),((-19872753827:ℚ)/25920000000),((-6768954051:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3337155511270237875998361612684929:ℚ)/7776000000000000000000000000000000),((453022159:ℚ)/1024000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((1072804099:ℚ)/1000000000),((3662165017:ℚ)/2500000000),((-35323815187:ℚ)/40000000000),((-868004099:ℚ)/2208000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((100290191032610800521692553:ℚ)/200000000000000000000000000),((453022159:ℚ)/1024000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source33 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC06
#check @N11Formalization.C450Source33GroupedC06.bound
#print axioms N11Formalization.C450Source33GroupedC06.valid0
#print axioms N11Formalization.C450Source33GroupedC06.valid1
#print axioms N11Formalization.C450Source33GroupedC06.valid2
#print axioms N11Formalization.C450Source33GroupedC06.valid3
#print axioms N11Formalization.C450Source33GroupedC06.valid4
#print axioms N11Formalization.C450Source33GroupedC06.valid5
#print axioms N11Formalization.C450Source33GroupedC06.valid6
#print axioms N11Formalization.C450Source33GroupedC06.valid7
#print axioms N11Formalization.C450Source33GroupedC06.valid8
#print axioms N11Formalization.C450Source33GroupedC06.valid9
#print axioms N11Formalization.C450Source33GroupedC06.valid10
#print axioms N11Formalization.C450Source33GroupedC06.valid11
#print axioms N11Formalization.C450Source33GroupedC06.valid12
#print axioms N11Formalization.C450Source33GroupedC06.bound
#print axioms N11Formalization.C450Source33GroupedC06.endpoint_checks
