import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((91526239:ℚ)/156250000),((6174619343:ℚ)/10000000000),((524578717:ℚ)/1609375000),((10334619343:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6907831481:ℚ)/10000000000),((1850317388821993416430748298085524182117:ℚ)/40454748032000000000000000000000000000000),((-87953615302494313749421653:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((3049127483:ℚ)/5000000000),((400926969:ℚ)/625000000),((17147382449:ℚ)/53400000000),((660926969:ℚ)/1609375000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3197435373:ℚ)/5000000000),((20571747928998858778632719199577876766082753787374471937:ℚ)/464316696542501449584960937500000000000000000000000000000),((-1052947778942086970199551:ℚ)/2707500000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((1267721561:ℚ)/2000000000),((6534865309:ℚ)/10000000000),((7003164683:ℚ)/21740000000),((3564955103:ℚ)/8900000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2922144213:ℚ)/5000000000),((207023094545296106523504523625904273665562588548425344917271:ℚ)/5206059477256250000000000000000000000000000000000000000000000),((-92089906206987235850468957:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6458708137:ℚ)/10000000000),((831856789:ℚ)/1250000000),((35376124411:ℚ)/110600000000),((1351856789:ℚ)/3396875000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((173479259:ℚ)/312500000),((421990725017425063295566670566102382085608540525708871759:ℚ)/10702147622978401184082031250000000000000000000000000000000),((-1453443497439252084129837:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((6578761307:ℚ)/10000000000),((677480083:ℚ)/1000000000),((35736283921:ℚ)/112500000000),((1093480083:ℚ)/2765000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((209758423:ℚ)/400000000),((59872881251213606983258545831928712859481376083214333:ℚ)/1528806086718750000000000000000000000000000000000000000),((-939437684539063426631933:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6698769757:ℚ)/10000000000),((6894707021:ℚ)/10000000000),((3281482661:ℚ)/10400000000),((11054707021:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((491942353:ℚ)/1000000000),((101723428808188488322633772662031157840316111893619006733:ℚ)/2610969543457031250000000000000000000000000000000000000000),((-94860086677076300796646077:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((85234197:ℚ)/125000000),((7014574899:ℚ)/10000000000),((455702591:ℚ)/1453750000),((11174574899:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((71469337:ℚ)/156250000),((1919132258066036785842855333824377086921192160771639461137307:ℚ)/49439896722287500000000000000000000000000000000000000000000000),((-287308089838556370903598391:ℚ)/693120000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((21683317:ℚ)/31250000),((3567203173:ℚ)/5000000000),((115049951:ℚ)/369375000),((5647203173:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((840525507:ℚ)/2000000000),((7215961502199848223142311949147712178445196135231240272029:ℚ)/186303777842172241210937500000000000000000000000000000000000),((-24167905352363755850624813:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((3529274389:ℚ)/5000000000),((3686983437:ℚ)/5000000000),((18587823167:ℚ)/61000000000),((5766983437:ℚ)/14775000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3797524781:ℚ)/10000000000),((1042140768560643596226192741228099021882195267141640375567:ℚ)/25003505507519531250000000000000000000000000000000000000000),((-72868658856078428977297079:ℚ)/173280000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((3649107863:ℚ)/5000000000),((7852721159:ℚ)/10000000000),((18947323589:ℚ)/64800000000),((12012721159:ℚ)/30500000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1413755097:ℚ)/5000000000),((13685372562583893832839396220355391983243616746108345836463:ℚ)/290863738476562500000000000000000000000000000000000000000000),((-651067231288981:ℚ)/1520000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((1944290919:ℚ)/2500000000),((1952828177:ℚ)/2000000000),((9832872757:ℚ)/40000000000),((309425353:ℚ)/720000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3473576893366056928135275139153659992755315815907:ℚ)/48600000000000000000000000000000000000000000000000),((-3539749:ℚ)/8000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9689170817:ℚ)/10000000000),((2715499501:ℚ)/2000000000),((45067512451:ℚ)/220800000000),((3547499501:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((69152396091749907269367649442283934399:ℚ)/609408000000000000000000000000000000000),((-3539749:ℚ)/8000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC20
#check @N11Formalization.C450Source27GroupedC20.bound
#print axioms N11Formalization.C450Source27GroupedC20.valid0
#print axioms N11Formalization.C450Source27GroupedC20.valid1
#print axioms N11Formalization.C450Source27GroupedC20.valid2
#print axioms N11Formalization.C450Source27GroupedC20.valid3
#print axioms N11Formalization.C450Source27GroupedC20.valid4
#print axioms N11Formalization.C450Source27GroupedC20.valid5
#print axioms N11Formalization.C450Source27GroupedC20.valid6
#print axioms N11Formalization.C450Source27GroupedC20.valid7
#print axioms N11Formalization.C450Source27GroupedC20.valid8
#print axioms N11Formalization.C450Source27GroupedC20.valid9
#print axioms N11Formalization.C450Source27GroupedC20.valid10
#print axioms N11Formalization.C450Source27GroupedC20.valid11
#print axioms N11Formalization.C450Source27GroupedC20.bound
#print axioms N11Formalization.C450Source27GroupedC20.endpoint_checks
