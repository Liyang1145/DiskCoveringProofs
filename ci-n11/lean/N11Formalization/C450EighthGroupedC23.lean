import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((6072385489:ℚ)/10000000000),((6581291107:ℚ)/10000000000),((6712385489:ℚ)/17800000000),((50549037749:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6451691039:ℚ)/10000000000),((685898054777779034337099:ℚ)/158420000000000000000000000),((-173282530573935836008142611:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((409234357:ℚ)/625000000),((1363783721:ℚ)/2000000000),((1347703071:ℚ)/3456250000),((10442486047:ℚ)/21360000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5324892209:ℚ)/10000000000),((186752449103265649563013470944533862731932376540936750678837:ℚ)/55879856187523200000000000000000000000000000000000000000000000),((-687379326698281900503259:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((6785413033:ℚ)/10000000000),((6937729121:ℚ)/10000000000),((7425413033:ℚ)/18750000000),((7577729121:ℚ)/15800000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4672341227:ℚ)/10000000000),((644889642685419764505630955524156342751317173156581657:ℚ)/221867550000000000000000000000000000000000000000000000000),((-177325963905168993852150499:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((6904240551:ℚ)/10000000000),((3498566809:ℚ)/5000000000),((22632721653:ℚ)/56725000000),((2969996407:ℚ)/6250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2156145301:ℚ)/5000000000),((21224526436757309302166036585999386942648867553910088022719:ℚ)/7855775451660156250000000000000000000000000000000000000000000),((-178007786535330825781548291:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((870456667:ℚ)/1250000000),((3528268813:ℚ)/5000000000),((2851370001:ℚ)/7150000000),((26937881691:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4121288253:ℚ)/10000000000),((191739238318571150045267532648028969975854187345100281519:ℚ)/71778147400222656250000000000000000000000000000000000000000),((-2786711668115972062602299:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((7023065493:ℚ)/10000000000),((1423188231:ℚ)/2000000000),((7663065493:ℚ)/19225000000),((10858317617:ℚ)/22880000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((39215511:ℚ)/100000000),((87725773264455502162964998767458074244986759186352289059483:ℚ)/33201829933958400000000000000000000000000000000000000000000000),((-178691873020972785471056859:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((7082477037:ℚ)/10000000000),((3587672109:ℚ)/5000000000),((23167431111:ℚ)/58150000000),((27353704763:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((185583269:ℚ)/500000000),((56536556847505896784507993895114147459191539581562979211297:ℚ)/21624246980104253906250000000000000000000000000000000000000000),((-179034765388562721468383979:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/8),((7:ℚ)/16),((446367999:ℚ)/625000000),((289389873:ℚ)/400000000),((1459103997:ℚ)/3664062500),((2204929111:ℚ)/4652000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3489796397:ℚ)/10000000000),((268654664285796154414022239773906726931295144820668062549:ℚ)/103802086760360100000000000000000000000000000000000000000000),((-700696187254427798504691:ℚ)/7220000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7201298347:ℚ)/10000000000),((7294148989:ℚ)/10000000000),((7841298347:ℚ)/19700000000),((7934148989:ℚ)/16750000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3253489181:ℚ)/10000000000),((730401763860355647734618585342000598396430685425540817773:ℚ)/284968536791992187500000000000000000000000000000000000000000),((-179722248724854125101014619:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((3630354071:ℚ)/5000000000),((7353550719:ℚ)/10000000000),((11851062213:ℚ)/29787500000),((55954855033:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((299932839:ℚ)/1000000000),((446498226608725698446408667776058650517158338983367966417203403:ℚ)/175833567001787850000000000000000000000000000000000000000000000000),((-45016709956951834197951331:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((7320117381:ℚ)/10000000000),((3706476013:ℚ)/5000000000),((23880352143:ℚ)/60050000000),((28185332091:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2722313011:ℚ)/10000000000),((299837073334160939965676684549156214058548399902885309773187:ℚ)/119134679978788372802734375000000000000000000000000000000000000),((-180411997299431222977600251:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((3689763039:ℚ)/5000000000),((753175341:ℚ)/1000000000),((12029289117:ℚ)/30500000000),((5720227387:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((241458413:ℚ)/1000000000),((105645432920268862336732682240997797865106912376671130171:ℚ)/40287350745756250000000000000000000000000000000000000000000),((-45189430301318157467905011:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7498341897:ℚ)/10000000000),((3884675759:ℚ)/5000000000),((24415025691:ℚ)/62900000000),((29432730313:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1637436589:ℚ)/10000000000),((395994111518614403709999342061731398589842746547035979940089:ℚ)/140317171595312500000000000000000000000000000000000000000000000),((-181450868555263679429718819:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1933991891:ℚ)/2500000000),((800694387:ℚ)/1000000000),((697997297:ℚ)/1800000000),((6052860709:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2766652170987894349310379325534300865336480581215595037:ℚ)/1007875665450000000000000000000000000000000000000000000000),((-2521409:ℚ)/25600000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7973585857:ℚ)/10000000000),((1238440587:ℚ)/1250000000),((25840757571:ℚ)/80000000000),((9229084109:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((123069380138132024480231455898874427:ℚ)/24000000000000000000000000000000000000),((-2521409:ℚ)/25600000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((9874329807:ℚ)/10000000000),((1713525801:ℚ)/1250000000),((10514329807:ℚ)/36800000000),((12554680607:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((5271143051151011386049931:ℚ)/677120000000000000000000000),((-2521409:ℚ)/25600000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC23
#check @N11Formalization.C450EighthGroupedC23.bound
#print axioms N11Formalization.C450EighthGroupedC23.valid0
#print axioms N11Formalization.C450EighthGroupedC23.valid1
#print axioms N11Formalization.C450EighthGroupedC23.valid2
#print axioms N11Formalization.C450EighthGroupedC23.valid3
#print axioms N11Formalization.C450EighthGroupedC23.valid4
#print axioms N11Formalization.C450EighthGroupedC23.valid5
#print axioms N11Formalization.C450EighthGroupedC23.valid6
#print axioms N11Formalization.C450EighthGroupedC23.valid7
#print axioms N11Formalization.C450EighthGroupedC23.valid8
#print axioms N11Formalization.C450EighthGroupedC23.valid9
#print axioms N11Formalization.C450EighthGroupedC23.valid10
#print axioms N11Formalization.C450EighthGroupedC23.valid11
#print axioms N11Formalization.C450EighthGroupedC23.valid12
#print axioms N11Formalization.C450EighthGroupedC23.valid13
#print axioms N11Formalization.C450EighthGroupedC23.valid14
#print axioms N11Formalization.C450EighthGroupedC23.valid15
#print axioms N11Formalization.C450EighthGroupedC23.bound
#print axioms N11Formalization.C450EighthGroupedC23.endpoint_checks
