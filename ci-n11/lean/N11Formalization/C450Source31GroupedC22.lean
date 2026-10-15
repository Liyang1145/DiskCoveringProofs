import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((1412346303:ℚ)/2500000000),((1494998153:ℚ)/2500000000),((2340346303:ℚ)/5150000000),((6884994459:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7327463167:ℚ)/10000000000),((-30771658798276743620175684153258504859402802734999681402097:ℚ)/126421087600000000000000000000000000000000000000000000000000),((-42202701356120509373894273:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5890655031:ℚ)/10000000000),((6220920941:ℚ)/10000000000),((9602655031:ℚ)/21360000000),((28262762823:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((106866381:ℚ)/156250000),((-405660981789071115481956591206654145359266224090037013:ℚ)/1691925600000000000000000000000000000000000000000000000),((-675522438024979274802380057:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3065825313:ℚ)/5000000000),((1268258671:ℚ)/2000000000),((4921825313:ℚ)/10870000000),((1908258671:ℚ)/3560000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6320871177:ℚ)/10000000000),((-1933192813485591325229970052563382690963477488676667939:ℚ)/8027284393750000000000000000000000000000000000000000000),((-27297697916432848663037777:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((1563013709:ℚ)/2500000000),((6461608919:ℚ)/10000000000),((2491013709:ℚ)/5530000000),((28984826757:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6047596179:ℚ)/10000000000),((-563895234321166643744244974105029902018202075631841:ℚ)/2359268652343750000000000000000000000000000000000000),((-682239365267610001384730817:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((6372401059:ℚ)/10000000000),((6581870587:ℚ)/10000000000),((10084401059:ℚ)/22500000000),((29345611761:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5763197911:ℚ)/10000000000),((-814658190308553416701675684637461751545924853584873:ℚ)/3433227539062500000000000000000000000000000000000000),((-681901213228731327225294793:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((6492692311:ℚ)/10000000000),((837760139:ℚ)/1250000000),((927699301:ℚ)/2080000000),((412586713:ℚ)/781250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5465905881:ℚ)/10000000000),((-13253361340119811165553510898592995324231310600766287:ℚ)/56243200000000000000000000000000000000000000000000000),((-10647315248757285518368537:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((33064657:ℚ)/50000000),((6822243061:ℚ)/10000000000),((51624657:ℚ)/116300000),((30066729183:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2576726963:ℚ)/5000000000),((-2301357592320573935522677586641558795403849321739:ℚ)/9831485918750000000000000000000000000000000000000),((-680820424822940812938167337:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((3366560473:ℚ)/5000000000),((6942358831:ℚ)/10000000000),((1740853491:ℚ)/3940000000),((30427076493:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1205715067:ℚ)/2500000000),((-22228134769189117965129933402861240373925299124845137:ℚ)/95567162500000000000000000000000000000000000000000000),((-680078119948297707831716817:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((1370652679:ℚ)/2000000000),((1436492131:ℚ)/2000000000),((2113052679:ℚ)/4880000000),((2076492131:ℚ)/3940000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((894012777:ℚ)/2000000000),((-165051669530047452855374840396298311500952265076699413:ℚ)/726339200000000000000000000000000000000000000000000000),((-1413110920177925676363843:ℚ)/3891200000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7093416001:ℚ)/10000000000),((7662199763:ℚ)/10000000000),((10805416001:ℚ)/25920000000),((32586599289:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((57371519:ℚ)/156250000),((-97511184701289047989025142070573402954954338786721729:ℚ)/447897600000000000000000000000000000000000000000000000),((-86363995307620387:ℚ)/243200000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((757324747:ℚ)/1000000000),((1197075613:ℚ)/1250000000),((1128524747:ℚ)/3200000000),((1597075613:ℚ)/2700000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((167860343:ℚ)/2000000000),((-37389311598367841049992782120913487398829372615391361:ℚ)/204800000000000000000000000000000000000000000000000000),((-9002433544793089:ℚ)/24320000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((4743966189:ℚ)/5000000000),((1339343713:ℚ)/1000000000),((6599966189:ℚ)/22080000000),((4978031139:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-284306131582850144319896507588037058451400577752719047:ℚ)/1868851200000000000000000000000000000000000000000000000),((-47488639:ℚ)/128000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC22
#check @N11Formalization.C450Source31GroupedC22.bound
#print axioms N11Formalization.C450Source31GroupedC22.valid0
#print axioms N11Formalization.C450Source31GroupedC22.valid1
#print axioms N11Formalization.C450Source31GroupedC22.valid2
#print axioms N11Formalization.C450Source31GroupedC22.valid3
#print axioms N11Formalization.C450Source31GroupedC22.valid4
#print axioms N11Formalization.C450Source31GroupedC22.valid5
#print axioms N11Formalization.C450Source31GroupedC22.valid6
#print axioms N11Formalization.C450Source31GroupedC22.valid7
#print axioms N11Formalization.C450Source31GroupedC22.valid8
#print axioms N11Formalization.C450Source31GroupedC22.valid9
#print axioms N11Formalization.C450Source31GroupedC22.valid10
#print axioms N11Formalization.C450Source31GroupedC22.valid11
#print axioms N11Formalization.C450Source31GroupedC22.bound
#print axioms N11Formalization.C450Source31GroupedC22.endpoint_checks
