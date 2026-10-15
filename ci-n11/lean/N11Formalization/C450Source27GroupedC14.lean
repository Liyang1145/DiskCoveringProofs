import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((1560883541:ℚ)/2500000000),((6550928829:ℚ)/10000000000),((-3652786487:ℚ)/99200000000),((519116459:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((121345739:ℚ)/200000000),((77440214586121618438666630959372161:ℚ)/476656000000000000000000000000000000),((-22376859427557039024389111:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6484266773:ℚ)/10000000000),((6671174727:ℚ)/10000000000),((-4013524181:ℚ)/103000000000),((1835733227:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((5487197447:ℚ)/10000000000),((533232916720138461786934073933127506251157231747346539:ℚ)/3334738159179687500000000000000000000000000000000000000),((-383226696551289693137409399:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((3302271769:ℚ)/5000000000),((6791366427:ℚ)/10000000000),((-4374099281:ℚ)/104900000000),((857728231:ℚ)/26225000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((5175804059:ℚ)/10000000000),((17974790025141692388122807773639376836292188816190606023:ℚ)/112726625878906250000000000000000000000000000000000000000),((-98964768788861303429200191:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((6724764967:ℚ)/10000000000),((6911506837:ℚ)/10000000000),((-4734520511:ℚ)/106800000000),((531745011:ℚ)/17800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1211628071:ℚ)/2500000000),((5607093412852524071975915187783423220825989182419762627:ℚ)/35248450000000000000000000000000000000000000000000000000),((-408514459509022846491213759:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((684493403:ℚ)/1000000000),((7031598663:ℚ)/10000000000),((-5094795989:ℚ)/108700000000),((147506597:ℚ)/5435000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2247675571:ℚ)/5000000000),((9955923992346217527793833076138378152273676416645309:ℚ)/62713159326171875000000000000000000000000000000000000),((-4211931235395747207102679:ℚ)/18483200000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((696505349:ℚ)/1000000000),((7151644421:ℚ)/10000000000),((-5454933263:ℚ)/110600000000),((135494651:ℚ)/5530000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4116686509:ℚ)/10000000000),((23930818243412523579901524509557010886575700948835189:ℚ)/150993193750000000000000000000000000000000000000000000),((-4338953221231932982295831:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((7085125917:ℚ)/10000000000),((3635823227:ℚ)/5000000000),((-2907469681:ℚ)/56250000000),((1234874083:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((925511013:ℚ)/2500000000),((19562449607659836187444769561350103146550540570506589219:ℚ)/123596191406250000000000000000000000000000000000000000000),((-1339863876957736480051562677:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3602576853:ℚ)/5000000000),((147832139:ℚ)/200000000),((-11226947:ℚ)/208000000),((557423147:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((647516231:ℚ)/2000000000),((5779421973457887554537099579985532801084568703103379931:ℚ)/36552587500000000000000000000000000000000000000000000000),((-344528441288274300729585637:ℚ)/1386240000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((732513909:ℚ)/1000000000),((7511527953:ℚ)/10000000000),((-6534583859:ℚ)/116300000000),((99486091:ℚ)/5815000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((674407443:ℚ)/2500000000),((48540482589389846976122592235487198693250081270037803:ℚ)/307233934960937500000000000000000000000000000000000000),((-14164362488392641336996133:ℚ)/55449600000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((1861271039:ℚ)/2500000000),((3875629499:ℚ)/5000000000),((-3626888497:ℚ)/59100000000),((218728961:ℚ)/14775000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1011268797:ℚ)/5000000000),((1069206477817543938141144755899725371173042061664433979:ℚ)/6719566113281250000000000000000000000000000000000000000),((-30308998032371057780255151:ℚ)/115520000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((1536972203:ℚ)/2000000000),((411516179:ℚ)/500000000),((-434548537:ℚ)/6100000000),((127027797:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((457837294983442005345216818199396609894702102977312021:ℚ)/2837262500000000000000000000000000000000000000000000000),((-34731057:ℚ)/128000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((4082003233:ℚ)/5000000000),((5071342203:ℚ)/5000000000),((-7214026609:ℚ)/64800000000),((77996767:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((773209258485392892615607304912424152052188609355763333:ℚ)/4428675000000000000000000000000000000000000000000000000),((-34731057:ℚ)/128000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10075659523:ℚ)/10000000000),((13957137373:ℚ)/10000000000),((-25871412119:ℚ)/160000000000),((-585219841:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((15633554238683300321699235895246045171632788835277949687:ℚ)/77868800000000000000000000000000000000000000000000000000),((-34731057:ℚ)/128000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC14
#check @N11Formalization.C450Source27GroupedC14.bound
#print axioms N11Formalization.C450Source27GroupedC14.valid0
#print axioms N11Formalization.C450Source27GroupedC14.valid1
#print axioms N11Formalization.C450Source27GroupedC14.valid2
#print axioms N11Formalization.C450Source27GroupedC14.valid3
#print axioms N11Formalization.C450Source27GroupedC14.valid4
#print axioms N11Formalization.C450Source27GroupedC14.valid5
#print axioms N11Formalization.C450Source27GroupedC14.valid6
#print axioms N11Formalization.C450Source27GroupedC14.valid7
#print axioms N11Formalization.C450Source27GroupedC14.valid8
#print axioms N11Formalization.C450Source27GroupedC14.valid9
#print axioms N11Formalization.C450Source27GroupedC14.valid10
#print axioms N11Formalization.C450Source27GroupedC14.valid11
#print axioms N11Formalization.C450Source27GroupedC14.valid12
#print axioms N11Formalization.C450Source27GroupedC14.bound
#print axioms N11Formalization.C450Source27GroupedC14.endpoint_checks
