import N11Formalization.C450Source17Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source17GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source17Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((2908689041:ℚ)/5000000000),((6354744551:ℚ)/10000000000),((3508689041:ℚ)/6675000000),((67432700959:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3495322763:ℚ)/5000000000),((-61016727439192161621040576964059:ℚ)/37176099609375000000000000000000000),((-4102928351702382034788551:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source17 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source17 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((157349829:ℚ)/250000000),((3296471249:ℚ)/5000000000),((187349829:ℚ)/345625000),((34788241241:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2974924213:ℚ)/5000000000),((-918009685822709420646059310186209757132734659653:ℚ)/129022504425048828125000000000000000000000000000000),((-1038067869432667717096951:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source17 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((261288683:ℚ)/400000000),((53367921:ℚ)/78125000),((28117153:ℚ)/52000000),((560311289:ℚ)/864062500),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1341253197:ℚ)/2500000000),((-3337556674473389354551819748168559832691400001:ℚ)/439400000000000000000000000000000000000000000000),((-6259899727393382640379141:ℚ)/21660000000000000000000000)⟩
theorem valid2 : Valid source17 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source17 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source17 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3385196347:ℚ)/5000000000),((6950153557:ℚ)/10000000000),((3985196347:ℚ)/7268750000),((72791382013:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((943206099:ℚ)/2000000000),((-8877724741035245042800281436404365894442530053334833:ℚ)/900099418830871582031250000000000000000000000000000000),((-4197703736331374244037799:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source17 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6889463879:ℚ)/10000000000),((7069203233:ℚ)/10000000000),((8089463879:ℚ)/14775000000),((73862829097:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((871714737:ℚ)/2000000000),((-75481097250172800105703560125849373678968554406111261:ℚ)/7559511877441406250000000000000000000000000000000000000),((-4208040177864373991172089:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source17 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7008524697:ℚ)/10000000000),((112316303:ℚ)/156250000),((8208524697:ℚ)/15012500000),((1170846727:ℚ)/1846875000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1985656821:ℚ)/5000000000),((-106672118810093585997955022111182706065008099847521801:ℚ)/10573264166259765625000000000000000000000000000000000000),((-2109156448060964492508357:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source17 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source17 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((1781893911:ℚ)/2500000000),((3653637241:ℚ)/5000000000),((2081893911:ℚ)/3812500000),((38002735169:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((141778411:ℚ)/400000000),((-1762162537674513539408759354476505467228616344553207:ℚ)/173172760009765625000000000000000000000000000000000000),((-1057130487529878159906281:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid source17 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source17 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7246617183:ℚ)/10000000000),((185657423:ℚ)/250000000),((2815539061:ℚ)/5162500000),((1926916807:ℚ)/3050000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((153072883:ℚ)/500000000),((-1101393962014955138446621181765064918036840242494597:ℚ)/107490534973144531250000000000000000000000000000000000),((-84773347901136917596203:ℚ)/288800000000000000000000)⟩
theorem valid7 : Valid source17 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source17 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1841412437:ℚ)/2500000000),((3772655551:ℚ)/5000000000),((2141412437:ℚ)/3931250000),((39073899959:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2489793069:ℚ)/10000000000),((-1910069498887269144030830498131577420205768361269:ℚ)/185413799434900283813476562500000000000000000000000),((-1062187320634230677579301:ℚ)/3610000000000000000000000)⟩
theorem valid8 : Valid source17 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source17 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source17 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((1871168437:ℚ)/2500000000),((3891658077:ℚ)/5000000000),((2171168437:ℚ)/4050000000),((40144922693:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((109019209:ℚ)/625000000),((-66703342517213323764658249664376561451441041137687:ℚ)/7688671875000000000000000000000000000000000000000000),((-14352649824936271:ℚ)/48640000000000000)⟩
theorem valid9 : Valid source17 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source17 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7722697567:ℚ)/10000000000),((4843245439:ℚ)/5000000000),((8922697567:ℚ)/20000000000),((48709208951:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3084407683325899350760241011397731:ℚ)/375000000000000000000000000000000000),((-37890623:ℚ)/128000000)⟩
theorem valid10 : Valid source17 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source17 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((1203248773:ℚ)/1250000000),((3372553481:ℚ)/2500000000),((1353248773:ℚ)/3450000000),((32912981329:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((35368357513772969658707:ℚ)/1487812500000000000000000),((-37890623:ℚ)/128000000)⟩
theorem valid11 : Valid source17 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source17 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source17 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source17 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source17 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source17 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source17 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source17 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source17 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source17 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source17 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source17 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source17GroupedC25
#check @N11Formalization.C450Source17GroupedC25.bound
#print axioms N11Formalization.C450Source17GroupedC25.valid0
#print axioms N11Formalization.C450Source17GroupedC25.valid1
#print axioms N11Formalization.C450Source17GroupedC25.valid2
#print axioms N11Formalization.C450Source17GroupedC25.valid3
#print axioms N11Formalization.C450Source17GroupedC25.valid4
#print axioms N11Formalization.C450Source17GroupedC25.valid5
#print axioms N11Formalization.C450Source17GroupedC25.valid6
#print axioms N11Formalization.C450Source17GroupedC25.valid7
#print axioms N11Formalization.C450Source17GroupedC25.valid8
#print axioms N11Formalization.C450Source17GroupedC25.valid9
#print axioms N11Formalization.C450Source17GroupedC25.valid10
#print axioms N11Formalization.C450Source17GroupedC25.valid11
#print axioms N11Formalization.C450Source17GroupedC25.bound
#print axioms N11Formalization.C450Source17GroupedC25.endpoint_checks
