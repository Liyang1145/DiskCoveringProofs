import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/16),((1:ℚ)/4),((2912212311:ℚ)/5000000000),((1229397831:ℚ)/2000000000),((17376636933:ℚ)/51500000000),((2125397831:ℚ)/4960000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3488112431:ℚ)/5000000000),((-103459707709329590081240819630242576049948758739428468217:ℚ)/853692968750000000000000000000000000000000000000000000000),((-481024748268386723657093:ℚ)/1459200000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((3032751417:ℚ)/5000000000),((798457713:ℚ)/1250000000),((5912751417:ℚ)/17800000000),((1358457713:ℚ)/3218750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1616684019:ℚ)/2500000000),((-1041541574759216031003456474908084283620282954927952773:ℚ)/8812112500000000000000000000000000000000000000000000000),((-3617475898970533580128943:ℚ)/10830000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6306321049:ℚ)/10000000000),((3253956601:ℚ)/5000000000),((36198963147:ℚ)/108700000000),((1831318867:ℚ)/4450000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5920845983:ℚ)/10000000000),((-954211874121749950973347064122306824568665896785279272783:ℚ)/8027284393750000000000000000000000000000000000000000000000),((-19693504326050306174168949:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1606660353:ℚ)/2500000000),((1657028041:ℚ)/2500000000),((9139981059:ℚ)/27650000000),((2777028041:ℚ)/6793750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5630881107:ℚ)/10000000000),((-242499295742834424195775328313915539390915877638899071:ℚ)/2064360070800781250000000000000000000000000000000000000),((-4953045789197855522776469:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((3273453391:ℚ)/5000000000),((3374130657:ℚ)/5000000000),((6153453391:ℚ)/18750000000),((5614130657:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2663538243:ℚ)/5000000000),((-56064099697363256622007993620293965778294525017819513:ℚ)/482797622680664062500000000000000000000000000000000000),((-59783641676611352439601103:ℚ)/173280000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6667120017:ℚ)/10000000000),((858545399:ℚ)/1250000000),((2867796927:ℚ)/8800000000),((1418545399:ℚ)/3515625000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1251719353:ℚ)/2500000000),((-489081304052832453111677119442073714771704870286695843:ℚ)/4259200000000000000000000000000000000000000000000000000),((-1252537702942865612972949:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((106051309:ℚ)/156250000),((6988420167:ℚ)/10000000000),((588153927:ℚ)/1817187500),((11468420167:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2333436669:ℚ)/5000000000),((-4259880289975237773404598109663247328422740153642647:ℚ)/37504142451286315917968750000000000000000000000000000),((-241804289632232248564380383:ℚ)/693120000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((345370027:ℚ)/500000000),((142168689:ℚ)/200000000),((633370027:ℚ)/1970000000),((231768689:ℚ)/581500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((134447889:ℚ)/312500000),((-1342540745077712338196929436906931750260901061637983:ℚ)/11945895312500000000000000000000000000000000000000000),((-97234315476408705594287:ℚ)/277248000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((1756868157:ℚ)/2500000000),((1469668617:ℚ)/2000000000),((9590604471:ℚ)/30500000000),((2365668617:ℚ)/5910000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1953175037:ℚ)/5000000000),((-19216066935310241700530290340592519597165180963232143171:ℚ)/177328906250000000000000000000000000000000000000000000000),((-9688407703255466791185983:ℚ)/27724800000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7267491303:ℚ)/10000000000),((3913865387:ℚ)/5000000000),((4342497101:ℚ)/14400000000),((6153865387:ℚ)/15250000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1484485547:ℚ)/5000000000),((-629437114992001719112283198401532023725732182466133667:ℚ)/6220800000000000000000000000000000000000000000000000000),((-1339409281307903:ℚ)/3800000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((7747079167:ℚ)/10000000000),((38051059:ℚ)/39062500),((40521237501:ℚ)/160000000000),((55551059:ℚ)/126562500),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-1928099239136864741379404261842130963560063575403571860881:ℚ)/25600000000000000000000000000000000000000000000000000000000),((-1170541:ℚ)/3200000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((9661026101:ℚ)/10000000000),((105911441:ℚ)/78125000),((15421026101:ℚ)/73600000000),((140911441:ℚ)/312500000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-90740477214237508855416009822473958500132762117519210483:ℚ)/1868851200000000000000000000000000000000000000000000000000),((-1170541:ℚ)/3200000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC20
#check @N11Formalization.C450Source29GroupedC20.bound
#print axioms N11Formalization.C450Source29GroupedC20.valid0
#print axioms N11Formalization.C450Source29GroupedC20.valid1
#print axioms N11Formalization.C450Source29GroupedC20.valid2
#print axioms N11Formalization.C450Source29GroupedC20.valid3
#print axioms N11Formalization.C450Source29GroupedC20.valid4
#print axioms N11Formalization.C450Source29GroupedC20.valid5
#print axioms N11Formalization.C450Source29GroupedC20.valid6
#print axioms N11Formalization.C450Source29GroupedC20.valid7
#print axioms N11Formalization.C450Source29GroupedC20.valid8
#print axioms N11Formalization.C450Source29GroupedC20.valid9
#print axioms N11Formalization.C450Source29GroupedC20.valid10
#print axioms N11Formalization.C450Source29GroupedC20.valid11
#print axioms N11Formalization.C450Source29GroupedC20.bound
#print axioms N11Formalization.C450Source29GroupedC20.endpoint_checks
