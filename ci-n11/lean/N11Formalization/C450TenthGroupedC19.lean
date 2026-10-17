import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((612240761:ℚ)/1000000000),((1325489033:ℚ)/2000000000),((289413587:ℚ)/1780000000),((5128467099:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1268285343:ℚ)/2000000000),((258551500943001906934727660108567867133:ℚ)/15464825552896000000000000000000000000000),((-1336045872357882236282611:ℚ)/18483200000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6598126843:ℚ)/10000000000),((3432602507:ℚ)/5000000000),((9158126843:ℚ)/55300000000),((4392602507:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5192842799:ℚ)/10000000000),((507643691467815214769572045795832334569258578594597130134861:ℚ)/32337879738150000000000000000000000000000000000000000000000000),((-139338584438766650447804459:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((1708987329:ℚ)/2500000000),((1396815669:ℚ)/2000000000),((2348987329:ℚ)/14062500000),((5342447007:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1130620059:ℚ)/2500000000),((1708527707040850962573158088111497366826811952517703123:ℚ)/111821245200000000000000000000000000000000000000000000000),((-8888146467836628947210531:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((434678273:ℚ)/625000000),((7043513459:ℚ)/10000000000),((594678273:ℚ)/3545312500),((8963513459:ℚ)/37500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4150103347:ℚ)/10000000000),((25604143505267627757814296098834157537316760801334797222966231:ℚ)/1696847497558593750000000000000000000000000000000000000000000000),((-561122757659923364027539:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((7014301967:ℚ)/10000000000),((7102947573:ℚ)/10000000000),((9574301967:ℚ)/57200000000),((27068842719:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((493951669:ℚ)/1250000000),((112279376203379700565238089391590296981299270437270197081379:ℚ)/7464927329623156250000000000000000000000000000000000000000000),((-144366269325144387880410499:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((3536875163:ℚ)/5000000000),((895297589:ℚ)/1250000000),((4816875163:ℚ)/28837500000),((3405892767:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3743195907:ℚ)/10000000000),((121547043737793580793338567472457532431672452207795080777889:ℚ)/8105915511220312500000000000000000000000000000000000000000000),((-36271328657138101324179179:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((7133197473:ℚ)/10000000000),((72218129:ℚ)/100000000),((9693197473:ℚ)/58150000000),((91418129:ℚ)/384500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((880771367:ℚ)/2500000000),((287381257210334263472612652027389881364795964545464461:ℚ)/19221552871203781250000000000000000000000000000000000000),((-145804562196411387659608739:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((89908043:ℚ)/125000000),((1422118:ℚ)/1953125),((121908043:ℚ)/732812500),((21565416:ℚ)/90859375),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((205558177:ℚ)/625000000),((1921768524704890031470674797889170664902655858681737:ℚ)/128897635589490458369255065917968750000000000000000000),((-22894376937936704805659:ℚ)/288800000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1450417651:ℚ)/2000000000),((3670337257:ℚ)/5000000000),((654139217:ℚ)/3940000000),((1984430253:ℚ)/8375000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((303748111:ℚ)/1000000000),((529671414201289679239608773979778296771230750867143181897:ℚ)/35621067098999023437500000000000000000000000000000000000000),((-5889746622952464653270491:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((3655765973:ℚ)/5000000000),((1480020797:ℚ)/2000000000),((4935765973:ℚ)/29787500000),((1864020797:ℚ)/7880000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2764015091:ℚ)/10000000000),((772729109335939606970595326080928409145735809977969654815171:ℚ)/52098834667196400000000000000000000000000000000000000000000000),((-36990880508994766195849739:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((368548727:ℚ)/500000000),((466220787:ℚ)/625000000),((496548727:ℚ)/3002500000),((1758662361:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2461199281:ℚ)/10000000000),((3442882418650341415485968711331850548000065557920027620181:ℚ)/232684921833571040630340576171875000000000000000000000000000),((-371708955260270885355539:ℚ)/4620800000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((3715208031:ℚ)/5000000000),((7578387299:ℚ)/10000000000),((4995208031:ℚ)/30500000000),((28495161897:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((529116679:ℚ)/2500000000),((9800627521839971794874712735671700997433434572316019280033:ℚ)/660448372881250000000000000000000000000000000000000000000000),((-37350961517291711924630051:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3774647997:ℚ)/5000000000),((8053775389:ℚ)/10000000000),((5054647997:ℚ)/32400000000),((29921326167:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((577884561:ℚ)/5000000000),((283051442544108668945507737748678855359630832344554921274883:ℚ)/18615279262500000000000000000000000000000000000000000000000000),((-37711246726067876883668219:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((4012388783:ℚ)/5000000000),((2488739683:ℚ)/2500000000),((5292388783:ℚ)/40000000000),((2968739683:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((24090387695692847287938558130402507774628255606287709:ℚ)/1476225000000000000000000000000000000000000000000000000),((-5244457:ℚ)/64000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4963122927:ℚ)/5000000000),((2751269469:ℚ)/2000000000),((6243122927:ℚ)/55200000000),((9405808407:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((755502837664250058231339949781109491521:ℚ)/39002112000000000000000000000000000000000),((-5244457:ℚ)/64000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC19
#check @N11Formalization.C450TenthGroupedC19.bound
#print axioms N11Formalization.C450TenthGroupedC19.valid0
#print axioms N11Formalization.C450TenthGroupedC19.valid1
#print axioms N11Formalization.C450TenthGroupedC19.valid2
#print axioms N11Formalization.C450TenthGroupedC19.valid3
#print axioms N11Formalization.C450TenthGroupedC19.valid4
#print axioms N11Formalization.C450TenthGroupedC19.valid5
#print axioms N11Formalization.C450TenthGroupedC19.valid6
#print axioms N11Formalization.C450TenthGroupedC19.valid7
#print axioms N11Formalization.C450TenthGroupedC19.valid8
#print axioms N11Formalization.C450TenthGroupedC19.valid9
#print axioms N11Formalization.C450TenthGroupedC19.valid10
#print axioms N11Formalization.C450TenthGroupedC19.valid11
#print axioms N11Formalization.C450TenthGroupedC19.valid12
#print axioms N11Formalization.C450TenthGroupedC19.valid13
#print axioms N11Formalization.C450TenthGroupedC19.valid14
#print axioms N11Formalization.C450TenthGroupedC19.bound
#print axioms N11Formalization.C450TenthGroupedC19.endpoint_checks
