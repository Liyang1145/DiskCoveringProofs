import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((246485353:ℚ)/400000000),((1666321267:ℚ)/2500000000),((24:ℚ)/445),((3266321267:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((625266637:ℚ)/1000000000),((821041687501867961974492274084154704871:ℚ)/30204737408000000000000000000000000000000),((-1055026573224193:ℚ)/19456000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((66380511:ℚ)/100000000),((6784205119:ℚ)/10000000000),((288:ℚ)/5435),((13184205119:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((127149653:ℚ)/250000000),((706358439716522262883480116855634657899870908826278189406922363:ℚ)/26988212330096400000000000000000000000000000000000000000000000000),((-284127240003591:ℚ)/4864000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((1689252581:ℚ)/2500000000),((1725779829:ℚ)/2500000000),((144:ℚ)/2765),((3325779829:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1188660629:ℚ)/2500000000),((187122920247219075275544557313758038229157903623665386689897:ℚ)/7191843202641485595703125000000000000000000000000000000000000),((-7230475726655261:ℚ)/121600000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((343798117:ℚ)/500000000),((1404405591:ℚ)/2000000000),((32:ℚ)/625),((383486513:ℚ)/3160000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((110011607:ℚ)/250000000),((5103476571929811264413771051070521932594130887113343:ℚ)/197215600000000000000000000000000000000000000000000000),((-1471552548030877:ℚ)/24320000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((1748726879:ℚ)/2500000000),((3540740139:ℚ)/5000000000),((576:ℚ)/11345),((6740740139:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((4017385789:ℚ)/10000000000),((147268227333479258002697826757834128261976911606866673120343541:ℚ)/5726860304260253906250000000000000000000000000000000000000000000),((-7485042434372999:ℚ)/121600000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((3527188823:ℚ)/5000000000),((3570465657:ℚ)/5000000000),((36:ℚ)/715),((6770465657:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3812303121:ℚ)/10000000000),((23939839283018418560274980869263039242600477547560552856983:ℚ)/933115916202894531250000000000000000000000000000000000000000),((-794597858026277:ℚ)/12800000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),(0:ℚ),((1:ℚ)/16),((7113846193:ℚ)/10000000000),((900047637:ℚ)/1250000000),((192:ℚ)/3845),((1700047637:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3596149607:ℚ)/10000000000),((207503648429069273040085254662317837607127437394987418508209:ℚ)/8105915511220312500000000000000000000000000000000000000000000),((-30449260696820233:ℚ)/486400000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((1434662639:ℚ)/2000000000),((3629914827:ℚ)/5000000000),((288:ℚ)/5815),((6829914827:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1683394637:ℚ)/5000000000),((552390928361573577432409059536151517680525749277187912565839:ℚ)/21624246980104253906250000000000000000000000000000000000000000),((-6140759235121559:ℚ)/97280000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),(0:ℚ),((1:ℚ)/16),((7232778691:ℚ)/10000000000),((7319277017:ℚ)/10000000000),((576:ℚ)/11725),((13719277017:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1560653721:ℚ)/5000000000),((13782726490384846465124039086457841826814788224938648665438647:ℚ)/540635868543542187500000000000000000000000000000000000000000000),((-30958325208292171:ℚ)/486400000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((7292242717:ℚ)/10000000000),((1475744643:ℚ)/2000000000),((48:ℚ)/985),((2755744643:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2855544387:ℚ)/10000000000),((19896556967562029839411437435861390157918272222909907216877:ℚ)/781953664957226562500000000000000000000000000000000000000000),((-31212847948963477:ℚ)/486400000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((7351705309:ℚ)/10000000000),((7497612227:ℚ)/10000000000),((288:ℚ)/6005),((4632537409:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1281596903:ℚ)/5000000000),((42062876905080352358201596885324121111275420833577960476978797:ℚ)/1654154049085950000000000000000000000000000000000000000000000000),((-31467364551711829:ℚ)/486400000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((3735313163:ℚ)/5000000000),((7616496901:ℚ)/10000000000),((72:ℚ)/1525),((14016496901:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((923887671:ℚ)/5000000000),((1020968320346506670277412239723389017436820708682453652334331:ℚ)/40287350745756250000000000000000000000000000000000000000000000),((-15988189960638803:ℚ)/243200000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((3794771003:ℚ)/5000000000),((505749753:ℚ)/625000000),((2:ℚ)/45),((905749753:ℚ)/7625000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((262332571:ℚ)/5000000000),((1426834416046362215719460206067544649264632360186956447:ℚ)/56107974243164062500000000000000000000000000000000000000),((-16242686223491843:ℚ)/243200000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((8065156053:ℚ)/10000000000),((4996758951:ℚ)/5000000000),((9:ℚ)/250),((8196758951:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((8197413670628156536807264227466977891449914645358840107:ℚ)/318864600000000000000000000000000000000000000000000000000),((-4280281:ℚ)/64000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((996702807:ℚ)/1000000000),((13795303551:ℚ)/10000000000),((3:ℚ)/115),((20195303551:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((15449188051755899573564123036577056411883:ℚ)/541696000000000000000000000000000000000000),((-4280281:ℚ)/64000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source11 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((2307:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC17
#check @N11Formalization.C450Source11GroupedC17.bound
#print axioms N11Formalization.C450Source11GroupedC17.valid0
#print axioms N11Formalization.C450Source11GroupedC17.valid1
#print axioms N11Formalization.C450Source11GroupedC17.valid2
#print axioms N11Formalization.C450Source11GroupedC17.valid3
#print axioms N11Formalization.C450Source11GroupedC17.valid4
#print axioms N11Formalization.C450Source11GroupedC17.valid5
#print axioms N11Formalization.C450Source11GroupedC17.valid6
#print axioms N11Formalization.C450Source11GroupedC17.valid7
#print axioms N11Formalization.C450Source11GroupedC17.valid8
#print axioms N11Formalization.C450Source11GroupedC17.valid9
#print axioms N11Formalization.C450Source11GroupedC17.valid10
#print axioms N11Formalization.C450Source11GroupedC17.valid11
#print axioms N11Formalization.C450Source11GroupedC17.valid12
#print axioms N11Formalization.C450Source11GroupedC17.valid13
#print axioms N11Formalization.C450Source11GroupedC17.valid14
#print axioms N11Formalization.C450Source11GroupedC17.bound
#print axioms N11Formalization.C450Source11GroupedC17.endpoint_checks
