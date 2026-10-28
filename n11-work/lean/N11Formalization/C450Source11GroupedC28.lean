import N11Formalization.C450Source11Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source11GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source11Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((736794033:ℚ)/1250000000),((200699333:ℚ)/312500000),((2941578121:ℚ)/4450000000),((652097999:ℚ)/775000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6831745547:ℚ)/10000000000),((-479696474440220051600906209152003:ℚ)/22030281250000000000000000000000000),((-346783027397113358619647:ℚ)/1805000000000000000000000)⟩
theorem valid0 : Valid source11 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source11 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6369754491:ℚ)/10000000000),((832506843:ℚ)/1250000000),((10832471343:ℚ)/15800000000),((2697520529:ℚ)/3337500000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1442396261:ℚ)/2500000000),((-632992729489907451381558067349597270073600828767090343:ℚ)/24651950000000000000000000000000000000000000000000000000),((-22183631647358707412264263:ℚ)/115520000000000000000000000)⟩
theorem valid1 : Valid source11 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source11 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((6607434851:ℚ)/10000000000),((3389444161:ℚ)/5000000000),((78441783361:ℚ)/112500000000),((10968332483:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5168109851:ℚ)/10000000000),((-81538792909067968433373229134097527102512484424723292987:ℚ)/2966308593750000000000000000000000000000000000000000000000),((-1167314233931823997342317:ℚ)/6080000000000000000000000)⟩
theorem valid2 : Valid source11 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source11 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((840783807:ℚ)/1250000000),((6897719121:ℚ)/10000000000),((9968621877:ℚ)/14300000000),((22293157363:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4842258779:ℚ)/10000000000),((-45755966198735817558007878316552859801155339737904103:ℚ)/1661481250000000000000000000000000000000000000000000000),((-346393366034923847926327:ℚ)/1805000000000000000000000)⟩
theorem valid3 : Valid source11 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source11 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source11 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((427818951:ℚ)/625000000),((6957133521:ℚ)/10000000000),((1688669487:ℚ)/2403125000),((22471400563:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2247419413:ℚ)/5000000000),((-615673518097348917122320067794585826696862349641927:ℚ)/21684484910964965820312500000000000000000000000000000),((-86590181618678224986373:ℚ)/451250000000000000000000)⟩
theorem valid4 : Valid source11 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1726129643:ℚ)/2500000000),((7016547277:ℚ)/10000000000),((20427426073:ℚ)/29075000000),((22649641831:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1077853833:ℚ)/2500000000),((-174540948794989171684451408946198682609096934567550193:ℚ)/6144678699218750000000000000000000000000000000000000000),((-1385142104534405828897927:ℚ)/7220000000000000000000000)⟩
theorem valid5 : Valid source11 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source11 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((1740983317:ℚ)/2500000000),((1415192081:ℚ)/2000000000),((20590816487:ℚ)/29312500000),((4565576243:ℚ)/5815000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((4120368617:ℚ)/10000000000),((-479272075890055356556857374221025987344970650726199627:ℚ)/16865600967407226562500000000000000000000000000000000000),((-1384842816707870247379847:ℚ)/7220000000000000000000000)⟩
theorem valid6 : Valid source11 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source11 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7023347321:ℚ)/10000000000),((7135372919:ℚ)/10000000000),((83016820531:ℚ)/118200000000),((23006118757:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((490072587:ℚ)/1250000000),((-8150385789079738188781335016464062350535471434154725379:ℚ)/286701487500000000000000000000000000000000000000000000000),((-1165932667206680964900597:ℚ)/6080000000000000000000000)⟩
theorem valid7 : Valid source11 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source11 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((1416552149:ℚ)/2000000000),((3597392417:ℚ)/5000000000),((16734073639:ℚ)/23830000000),((11592177251:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3710636027:ℚ)/10000000000),((-7215653675642539777250373853733869824520701017384809333:ℚ)/253730922881250000000000000000000000000000000000000000000),((-885919219973067497802023:ℚ)/4620800000000000000000000)⟩
theorem valid8 : Valid source11 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1428434711:ℚ)/2000000000),((1450839233:ℚ)/2000000000),((16864781821:ℚ)/24020000000),((4672517699:ℚ)/5957500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((872174337:ℚ)/2500000000),((-154000419014956041043352021795511107455369178078685189:ℚ)/5413511253125000000000000000000000000000000000000000000),((-885730581302800144002383:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source11 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source11 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7201585767:ℚ)/10000000000),((292544277:ℚ)/400000000),((28325814479:ℚ)/40350000000),((941632831:ℚ)/1201000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((650461163:ℚ)/2000000000),((-3894571530686483378063446545673594406396795948146124357:ℚ)/136864047656250000000000000000000000000000000000000000000),((-22138572775031576236683247:ℚ)/115520000000000000000000000)⟩
theorem valid10 : Valid source11 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source11 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((1452199479:ℚ)/2000000000),((7373017127:ℚ)/10000000000),((17126194269:ℚ)/24400000000),((23719051381:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2998039957:ℚ)/10000000000),((-2584249589582731567636035610982588112954741574735597301:ℚ)/90792400000000000000000000000000000000000000000000000000),((-885356209000508631942543:ℚ)/4620800000000000000000000)⟩
theorem valid11 : Valid source11 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source11 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source11 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((7320408451:ℚ)/10000000000),((936479489:ℚ)/1250000000),((86284492961:ℚ)/123900000000),((3009438467:ℚ)/3812500000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((680222069:ℚ)/2500000000),((-27464234921756858083196002278567160898274689820142626563:ℚ)/990632770312500000000000000000000000000000000000000000000),((-22121653270541546607009623:ℚ)/115520000000000000000000000)⟩
theorem valid12 : Valid source11 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source11 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((929903613:ℚ)/1250000000),((951331577:ℚ)/1250000000),((644055279:ℚ)/925000000),((3053994731:ℚ)/3871875000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((103026933:ℚ)/500000000),((-134043325642463576880934216075995269472263532439:ℚ)/4830646514892578125000000000000000000000000000000),((-345528181556977363251287:ℚ)/1805000000000000000000000)⟩
theorem valid13 : Valid source11 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source11 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source11 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((3779023613:ℚ)/5000000000),((7848280153:ℚ)/10000000000),((44449259743:ℚ)/64800000000),((25144840459:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1051207681:ℚ)/10000000000),((-1661493376898200842602380781761367977337657646383176061:ℚ)/62985600000000000000000000000000000000000000000000000000),((-5529975809637634417011287:ℚ)/28880000000000000000000000)⟩
theorem valid14 : Valid source11 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source11 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7795677857:ℚ)/10000000000),((9749082231:ℚ)/10000000000),((91512456427:ℚ)/160000000000),((30847246693:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-59662729495392824152236297911592863141809448386255416169:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-383:ℚ)/2000)⟩
theorem valid15 : Valid source11 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source11 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((1939299877:ℚ)/2000000000),((13550023557:ℚ)/10000000000),((22484298647:ℚ)/44160000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-75952904350735362570369917900364829:ℚ)/21529165824000000000000000000000000000),((-383:ℚ)/2000)⟩
theorem valid16 : Valid source11 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source11 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source11 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source11 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source11 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source11 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source11 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source11 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source11 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source11 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source11 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source11 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source11 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source11GroupedC28
#check @N11Formalization.C450Source11GroupedC28.bound
#print axioms N11Formalization.C450Source11GroupedC28.valid0
#print axioms N11Formalization.C450Source11GroupedC28.valid1
#print axioms N11Formalization.C450Source11GroupedC28.valid2
#print axioms N11Formalization.C450Source11GroupedC28.valid3
#print axioms N11Formalization.C450Source11GroupedC28.valid4
#print axioms N11Formalization.C450Source11GroupedC28.valid5
#print axioms N11Formalization.C450Source11GroupedC28.valid6
#print axioms N11Formalization.C450Source11GroupedC28.valid7
#print axioms N11Formalization.C450Source11GroupedC28.valid8
#print axioms N11Formalization.C450Source11GroupedC28.valid9
#print axioms N11Formalization.C450Source11GroupedC28.valid10
#print axioms N11Formalization.C450Source11GroupedC28.valid11
#print axioms N11Formalization.C450Source11GroupedC28.valid12
#print axioms N11Formalization.C450Source11GroupedC28.valid13
#print axioms N11Formalization.C450Source11GroupedC28.valid14
#print axioms N11Formalization.C450Source11GroupedC28.valid15
#print axioms N11Formalization.C450Source11GroupedC28.valid16
#print axioms N11Formalization.C450Source11GroupedC28.bound
#print axioms N11Formalization.C450Source11GroupedC28.endpoint_checks
