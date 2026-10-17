import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((738567729:ℚ)/1250000000),((6239921351:ℚ)/10000000000),((3218567729:ℚ)/12875000000),((16479921351:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6802114953:ℚ)/10000000000),((-682595179953573304198391422886136673075920017461790139911:ℚ)/3845620045166015625000000000000000000000000000000000000000),((-489732494491515569476023167:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((3075495453:ℚ)/5000000000),((6360886471:ℚ)/10000000000),((12995495453:ℚ)/52450000000),((16600886471:ℚ)/51500000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((6277672459:ℚ)/10000000000),((-41926090616235531185959285331177525187850642690552823713181:ℚ)/239183354789863281250000000000000000000000000000000000000000),((-504960359703441889281330047:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6272076961:ℚ)/10000000000),((1620442659:ℚ)/2500000000),((26112076961:ℚ)/106800000000),((4180442659:ℚ)/13112500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((93767247:ℚ)/156250000),((-36109649628176689510153084633278167211496642943153038158549233:ℚ)/209452119993630000000000000000000000000000000000000000000000000),((-31937177972302770988479527:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((6393077519:ℚ)/10000000000),((1650644561:ℚ)/2500000000),((26233077519:ℚ)/108700000000),((1403548187:ℚ)/4450000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1142616023:ℚ)/2000000000),((-1078756334967030511078835523871709583610160251166328627110727:ℚ)/6358411968289375000000000000000000000000000000000000000000000),((-32310430313398598354141007:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((651399723:ℚ)/1000000000),((6723313373:ℚ)/10000000000),((2635399723:ℚ)/11060000000),((16963313373:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2705866081:ℚ)/5000000000),((-1117633422993394785624147920618842198783425722114427358639:ℚ)/6690332885474765625000000000000000000000000000000000000000),((-522876823475946561670483943:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((6634840411:ℚ)/10000000000),((855497477:ℚ)/1250000000),((26474840411:ℚ)/112500000000),((2135497477:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((509465493:ℚ)/1000000000),((-6643572545622870582822067117832175779816636031234864655799:ℚ)/40368447303771972656250000000000000000000000000000000000000),((-434806734481933811027197:ℚ)/1520000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((3377805537:ℚ)/5000000000),((1392916221:ℚ)/2000000000),((13297805537:ℚ)/57200000000),((3440916221:ℚ)/11250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((7435411:ℚ)/15625000),((-512296376871156270995957373647180525782044891106489644283:ℚ)/3158143560000000000000000000000000000000000000000000000000),((-21380467403675650664059047:ℚ)/73932800000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((859539119:ℚ)/1250000000),((7085120529:ℚ)/10000000000),((3339539119:ℚ)/14537500000),((17325120529:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((439938117:ℚ)/1000000000),((-6281357811730492810618683171234457736695796464461251611127:ℚ)/39266417100101318359375000000000000000000000000000000000000),((-540237193489359570378732047:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6996949527:ℚ)/10000000000),((3602800581:ℚ)/5000000000),((26836949527:ℚ)/118200000000),((8722800581:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2005254401:ℚ)/5000000000),((-6120251363890255167129845523537676982752159187202024730827599:ℚ)/38778354424638750000000000000000000000000000000000000000000000),((-136475444339996739673963287:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((1779381011:ℚ)/2500000000),((7446397347:ℚ)/10000000000),((6739381011:ℚ)/30500000000),((17686397347:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((447796631:ℚ)/1250000000),((-105404232092252204299257610477473877971142961947677544755627:ℚ)/688195752265625000000000000000000000000000000000000000000000),((-547975583580804756545385703:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((147169977:ℚ)/200000000),((7927398893:ℚ)/10000000000),((543969977:ℚ)/2592000000),((18167398893:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1263847273:ℚ)/5000000000),((-1957152623262685302293630181600193356231361982720739923:ℚ)/13499678453760000000000000000000000000000000000000000000),((-295542239740031:ℚ)/972800000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((1959956249:ℚ)/2500000000),((393824993:ℚ)/400000000),((6919956249:ℚ)/40000000000),((267808331:ℚ)/864000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-390172957142379057571578413741644789486544291669959340537:ℚ)/3240000000000000000000000000000000000000000000000000000000),((-40146313:ℚ)/128000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((609939513:ℚ)/625000000),((13666895451:ℚ)/10000000000),((1849939513:ℚ)/13800000000),((23906895451:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-117828177591636457181419387803942306866766497023362883:ℚ)/1231908750000000000000000000000000000000000000000000000),((-40146313:ℚ)/128000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC18
#check @N11Formalization.C450Source33GroupedC18.bound
#print axioms N11Formalization.C450Source33GroupedC18.valid0
#print axioms N11Formalization.C450Source33GroupedC18.valid1
#print axioms N11Formalization.C450Source33GroupedC18.valid2
#print axioms N11Formalization.C450Source33GroupedC18.valid3
#print axioms N11Formalization.C450Source33GroupedC18.valid4
#print axioms N11Formalization.C450Source33GroupedC18.valid5
#print axioms N11Formalization.C450Source33GroupedC18.valid6
#print axioms N11Formalization.C450Source33GroupedC18.valid7
#print axioms N11Formalization.C450Source33GroupedC18.valid8
#print axioms N11Formalization.C450Source33GroupedC18.valid9
#print axioms N11Formalization.C450Source33GroupedC18.valid10
#print axioms N11Formalization.C450Source33GroupedC18.valid11
#print axioms N11Formalization.C450Source33GroupedC18.valid12
#print axioms N11Formalization.C450Source33GroupedC18.bound
#print axioms N11Formalization.C450Source33GroupedC18.endpoint_checks
