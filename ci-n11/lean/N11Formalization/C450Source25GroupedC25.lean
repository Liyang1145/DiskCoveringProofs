import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((5608983653:ℚ)/10000000000),((770909857:ℚ)/1250000000),((2482994551:ℚ)/4450000000),((285748023:ℚ)/400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((231455881:ℚ)/312500000),((-1820211708241180650626832142351343:ℚ)/22030281250000000000000000000000000),((-29570007015280861954231:ℚ)/76000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6087640981:ℚ)/10000000000),((6406429661:ℚ)/10000000000),((7927640981:ℚ)/13825000000),((24339288983:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1283647157:ℚ)/2000000000),((-1645620247381745693634121504626632245873050972704964119:ℚ)/16514880566406250000000000000000000000000000000000000000),((-1137760280259777105784033:ℚ)/2888000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6326779173:ℚ)/10000000000),((261038513:ℚ)/400000000),((8166779173:ℚ)/14062500000),((2963746617:ℚ)/4424000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5872438353:ℚ)/10000000000),((-207216267062069832285475134769935348189252842234469223:ℚ)/1931190490722656250000000000000000000000000000000000000),((-1831405783316581494537:ℚ)/4620800000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((3223153179:ℚ)/5000000000),((6645469727:ℚ)/10000000000),((376650289:ℚ)/650000000),((25056409181:ℚ)/37500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((5582220293:ℚ)/10000000000),((-183906708289078973130089829971806243594113061390379:ℚ)/1716406250000000000000000000000000000000000000000000),((-1144820890012810961557067:ℚ)/2888000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3282903741:ℚ)/5000000000),((1691237917:ℚ)/2500000000),((4202903741:ℚ)/7268750000),((1732831023:ℚ)/2600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((659737883:ℚ)/1250000000),((-64185604765986720049761107624479092771313495930561199:ℚ)/600066279220581054687500000000000000000000000000000000),((-286224399720054850881513:ℚ)/722000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6685283837:ℚ)/10000000000),((3442204933:ℚ)/5000000000),((2841761279:ℚ)/4925000000),((38659844397:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4956860443:ℚ)/10000000000),((-19926197598630478190045981222401119402585668859534029:ℚ)/186654614257812500000000000000000000000000000000000000),((-572429408299774933987419:ℚ)/1444000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6804736633:ℚ)/10000000000),((7003845463:ℚ)/10000000000),((8644736633:ℚ)/15012500000),((26131536389:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((184622891:ℚ)/400000000),((-2252486832181595313733137645488456816724001312334333123:ℚ)/21146528332519531250000000000000000000000000000000000000),((-1144704613680541439671137:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((6924167001:ℚ)/10000000000),((3561629763:ℚ)/5000000000),((8764167001:ℚ)/15250000000),((39734667867:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2124564953:ℚ)/5000000000),((-2355287504631075669042590131940393112256313557615970899:ℚ)/22166113281250000000000000000000000000000000000000000000),((-1716652584291668094214597:ℚ)/4332000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7043576001:ℚ)/10000000000),((3681013497:ℚ)/5000000000),((8883576001:ℚ)/15725000000),((40809121473:ℚ)/61000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1925161311:ℚ)/5000000000),((-604016439255195041228100281039560074575515759958762579:ℚ)/6075639379882812500000000000000000000000000000000000000),((-1705500606159828089925517:ℚ)/4332000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((455145863:ℚ)/625000000),((7600719573:ℚ)/10000000000),((190048621:ℚ)/337500000),((83766476157:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2901470469:ℚ)/10000000000),((-881270353509765807568867266640466670329489463973:ℚ)/8898925781250000000000000000000000000000000000000),((-23909495993907297:ℚ)/60800000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7521017303:ℚ)/10000000000),((9508209471:ℚ)/10000000000),((9361017303:ℚ)/20000000000),((33644628413:ℚ)/43200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((360737279:ℚ)/2500000000),((-1069174653143152474483234114235689:ℚ)/31250000000000000000000000000000000),((-386962644346656657:ℚ)/972800000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((2357112557:ℚ)/2500000000),((3329245201:ℚ)/2500000000),((939037519:ℚ)/2300000000),((33803206809:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3351354198389818427189:ℚ)/165312500000000000000000),((-51108183:ℚ)/128000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC25
#check @N11Formalization.C450Source25GroupedC25.bound
#print axioms N11Formalization.C450Source25GroupedC25.valid0
#print axioms N11Formalization.C450Source25GroupedC25.valid1
#print axioms N11Formalization.C450Source25GroupedC25.valid2
#print axioms N11Formalization.C450Source25GroupedC25.valid3
#print axioms N11Formalization.C450Source25GroupedC25.valid4
#print axioms N11Formalization.C450Source25GroupedC25.valid5
#print axioms N11Formalization.C450Source25GroupedC25.valid6
#print axioms N11Formalization.C450Source25GroupedC25.valid7
#print axioms N11Formalization.C450Source25GroupedC25.valid8
#print axioms N11Formalization.C450Source25GroupedC25.valid9
#print axioms N11Formalization.C450Source25GroupedC25.valid10
#print axioms N11Formalization.C450Source25GroupedC25.valid11
#print axioms N11Formalization.C450Source25GroupedC25.bound
#print axioms N11Formalization.C450Source25GroupedC25.endpoint_checks
