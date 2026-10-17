import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((234957139:ℚ)/400000000),((401753599:ℚ)/625000000),((439757139:ℚ)/1424000000),((651753599:ℚ)/1550000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1374841219:ℚ)/2000000000),((138247523436939948066562070539262673:ℚ)/1843550867187500000000000000000000000),((-6730873831332676935647:ℚ)/18050000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((6354401939:ℚ)/10000000000),((6667879693:ℚ)/10000000000),((4917600831:ℚ)/15800000000),((10667879693:ℚ)/26700000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5806513481:ℚ)/10000000000),((144192813533972438281027557606925956790081983083866213309289:ℚ)/2227353961556250000000000000000000000000000000000000000000000),((-1812685940988102912310703:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((329717607:ℚ)/500000000),((3393865547:ℚ)/5000000000),((585717607:ℚ)/1875000000),((770552221:ℚ)/1975000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5202842367:ℚ)/10000000000),((26207683193329974667908445952068691929039407091337219:ℚ)/433335058593750000000000000000000000000000000000000000),((-464308546612034726393823:ℚ)/1155200000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6714264249:ℚ)/10000000000),((6907545417:ℚ)/10000000000),((35502792747:ℚ)/114400000000),((10907545417:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4876085301:ℚ)/10000000000),((171018791133796457333565393669471574277545660003722732785087:ℚ)/2843345832824707031250000000000000000000000000000000000000000),((-5627752877357777957691349:ℚ)/13862400000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((6834137207:ℚ)/10000000000),((702732451:ℚ)/1000000000),((35862411621:ℚ)/116300000000),((1102732451:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((70748961:ℚ)/156250000),((807433498006956309456038576635062114394441884234735715933:ℚ)/13483608196987500000000000000000000000000000000000000000000),((-18944717263266864616847:ℚ)/46208000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((869246621:ℚ)/1250000000),((3573535051:ℚ)/5000000000),((1509246621:ℚ)/4925000000),((5573535051:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2076486111:ℚ)/5000000000),((11118998699773182497166997830186457055107874927632996323789:ℚ)/186303777842172241210937500000000000000000000000000000000000),((-478224227430915852641247:ℚ)/1155200000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((7073773359:ℚ)/10000000000),((923308393:ℚ)/1250000000),((36581320077:ℚ)/122000000000),((474436131:ℚ)/1231250000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3743113019:ℚ)/10000000000),((5421719782821979432431423547654506444883988023470532443:ℚ)/86817727456665039062500000000000000000000000000000000000),((-30057443960400780616103:ℚ)/72200000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7313274751:ℚ)/10000000000),((1966230967:ℚ)/2500000000),((4144424917:ℚ)/14400000000),((2966230967:ℚ)/7625000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((2755599521:ℚ)/10000000000),((1893387421026750969247902873640126996307279779210515641:ℚ)/28053987121582031250000000000000000000000000000000000000),((-3225862095843487:ℚ)/7600000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((779192141:ℚ)/1000000000),((4887720363:ℚ)/5000000000),((3873576423:ℚ)/16000000000),((6887720363:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((453209296159531867630760101686969883976368640238121271:ℚ)/4982259375000000000000000000000000000000000000000000000),((-1751053:ℚ)/4000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((1212876827:ℚ)/1250000000),((3396936229:ℚ)/2500000000),((1852876827:ℚ)/9200000000),((4396936229:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((17591400717953483130905406399546733313:ℚ)/132250000000000000000000000000000000000),((-1751053:ℚ)/4000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_10
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_10
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9]
theorem packet_count : packets.length = 10 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC20
#check @N11Formalization.C450Source26GroupedC20.bound
#print axioms N11Formalization.C450Source26GroupedC20.valid0
#print axioms N11Formalization.C450Source26GroupedC20.valid1
#print axioms N11Formalization.C450Source26GroupedC20.valid2
#print axioms N11Formalization.C450Source26GroupedC20.valid3
#print axioms N11Formalization.C450Source26GroupedC20.valid4
#print axioms N11Formalization.C450Source26GroupedC20.valid5
#print axioms N11Formalization.C450Source26GroupedC20.valid6
#print axioms N11Formalization.C450Source26GroupedC20.valid7
#print axioms N11Formalization.C450Source26GroupedC20.valid8
#print axioms N11Formalization.C450Source26GroupedC20.valid9
#print axioms N11Formalization.C450Source26GroupedC20.bound
#print axioms N11Formalization.C450Source26GroupedC20.endpoint_checks
