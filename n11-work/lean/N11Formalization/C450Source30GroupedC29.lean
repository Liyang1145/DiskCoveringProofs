import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((1305127783:ℚ)/2500000000),((2777366349:ℚ)/5000000000),((5035383349:ℚ)/6437500000),((45385762537:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8135685967:ℚ)/10000000000),((-2180397851820025714326574320489240854754887:ℚ)/6524959360000000000000000000000000000000000),((-5346994708444748449754133:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((5459383509:ℚ)/10000000000),((5793764017:ℚ)/10000000000),((20858150527:ℚ)/26700000000),((93878932221:ℚ)/103000000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7693831627:ℚ)/10000000000),((-70801349971730677983766694423183031098365637093644813831111:ℚ)/211315687670898437500000000000000000000000000000000000000000),((-21043184374745396999389837:ℚ)/46208000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((5698157439:ℚ)/10000000000),((1478309789:ℚ)/2500000000),((21574472317:ℚ)/27175000000),((23858027257:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7231007101:ℚ)/10000000000),((-1807361349031320481181294405850841279990506542899537384058649:ℚ)/5206059477256250000000000000000000000000000000000000000000000),((-1304242419270988708353893:ℚ)/2888000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1163502149:ℚ)/2000000000),((150817229:ℚ)/250000000),((4386506447:ℚ)/5530000000),((2424623977:ℚ)/2717500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6990374261:ℚ)/10000000000),((-16985767260697766668530994194702569003553304249871010043:ℚ)/48924103419329833984375000000000000000000000000000000000),((-12931645668345074032253:ℚ)/28880000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((5936843171:ℚ)/10000000000),((1538028829:ℚ)/2500000000),((22290529513:ℚ)/28125000000),((24634374777:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6742689479:ℚ)/10000000000),((-6552979623952158815627351497423578550294075046950294509:ℚ)/18874149218750000000000000000000000000000000000000000000),((-1281965422745881960919653:ℚ)/2888000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((757019473:ℚ)/1250000000),((6211819831:ℚ)/10000000000),((2831058419:ℚ)/3545312500),((11034850867:ℚ)/12500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((25948481:ℚ)/40000000),((-22154828645301745387391294160702071540571504624626595345147833:ℚ)/62846203613281250000000000000000000000000000000000000000000000),((-20421125654780736024385213:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((3057902487:ℚ)/5000000000),((1567879707:ℚ)/2500000000),((877977497:ℚ)/1100000000),((25022436191:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6356075201:ℚ)/10000000000),((-243256352403643292990084458573468131418546617615269859301:ℚ)/690174494232910156250000000000000000000000000000000000000),((-1270644946212328672807317:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6175449579:ℚ)/10000000000),((1266242489:ℚ)/2000000000),((23006348737:ℚ)/28837500000),((20173152357:ℚ)/22880000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6222670081:ℚ)/10000000000),((-11699905265424720460044543886679665679638911690709451126349101:ℚ)/33201829933958400000000000000000000000000000000000000000000000),((-809561085722840445313693:ℚ)/1848320000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3117544857:ℚ)/5000000000),((1278180163:ℚ)/2000000000),((11592634571:ℚ)/14537500000),((20328342119:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6086746613:ℚ)/10000000000),((-54176765333329269165980806852187617215166691662642659670927:ℚ)/153772422969630250000000000000000000000000000000000000000000),((-805889983768840079085077:ℚ)/1848320000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((6294725489:ℚ)/10000000000),((1612646017:ℚ)/2500000000),((23364176467:ℚ)/29312500000),((25604398221:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5948129033:ℚ)/10000000000),((-2975590556560855086236822777953381951339035322442637639828271:ℚ)/8447435445992846679687500000000000000000000000000000000000000),((-1253436651344100487843837:ℚ)/2888000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((635435701:ℚ)/1000000000),((813782791:ℚ)/1250000000),((2354307103:ℚ)/2955000000),((1842739469:ℚ)/2093750000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2903310623:ℚ)/5000000000),((-588043815611885112179940122179988565105712372776125963093:ℚ)/1669737520265579223632812500000000000000000000000000000000),((-311909961853474769721173:ℚ)/722000000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((3206992191:ℚ)/5000000000),((1313987143:ℚ)/2000000000),((11860976573:ℚ)/14893750000),((20793832859:ℚ)/23640000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5662003359:ℚ)/10000000000),((-6114783147878722293756931924615607931251243087298227318736267:ℚ)/17366278222398800000000000000000000000000000000000000000000000),((-794760117656955490265117:ℚ)/1848320000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((809200963:ℚ)/1250000000),((6629604347:ℚ)/10000000000),((2987602889:ℚ)/3753125000),((104744856511:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5514027439:ℚ)/10000000000),((-335517413738697991303842239340676556839135090262631509469250189:ℚ)/953077439830306982421875000000000000000000000000000000000000000),((-19775282504934202916637797:ℚ)/46208000000000000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6533227073:ℚ)/10000000000),((421807987:ℚ)/625000000),((24079681219:ℚ)/30500000000),((6643503831:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((670301527:ℚ)/1250000000),((-3413823227612397319350046413460842271519894198376870373349:ℚ)/9835778990663146972656250000000000000000000000000000000000),((-76509312249990345617377:ℚ)/180500000000000000000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3326227163:ℚ)/5000000000),((6868233527:ℚ)/10000000000),((1745525927:ℚ)/2212500000),((107847035851:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1261732627:ℚ)/2500000000),((-10282622644454910492868594519546308937900860150083463535444027:ℚ)/29629532287500000000000000000000000000000000000000000000000000),((-19395541383714397582151357:ℚ)/46208000000000000000000000)⟩
theorem valid14 : Valid source30 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1354333371:ℚ)/2000000000),((174688059:ℚ)/250000000),((291705889:ℚ)/370000000),((2734944767:ℚ)/3097500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2356169463:ℚ)/5000000000),((-6382696646600239371140259633778783513808510673059807:ℚ)/18394317797279357910156250000000000000000000000000000),((-12001721508561284628573:ℚ)/28880000000000000000000)⟩
theorem valid15 : Valid source30 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source30 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((3445432667:ℚ)/5000000000),((7226052321:ℚ)/10000000000),((12576298001:ℚ)/16200000000),((112498680173:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4354203863:ℚ)/10000000000),((-540763764552272408057010081320136324386004828559936464300037:ℚ)/1600743703950000000000000000000000000000000000000000000000000),((-18811345598140525226131053:ℚ)/46208000000000000000000000)⟩
theorem valid16 : Valid source30 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((712922263:ℚ)/1000000000),((9132522251:ℚ)/10000000000),((2586766789:ℚ)/4000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3538211067:ℚ)/10000000000),((-4798041842182221439752220810043869:ℚ)/20000000000000000000000000000000000),((-5036527:ℚ)/12800000)⟩
theorem valid17 : Valid source30 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((903460911:ℚ)/1000000000),((12940101599:ℚ)/10000000000),((3158382733:ℚ)/5520000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-980659534285989506438117:ℚ)/5078400000000000000000000),((-5036527:ℚ)/12800000)⟩
theorem valid18 : Valid source30 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source30 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC29
#check @N11Formalization.C450Source30GroupedC29.bound
#print axioms N11Formalization.C450Source30GroupedC29.valid0
#print axioms N11Formalization.C450Source30GroupedC29.valid1
#print axioms N11Formalization.C450Source30GroupedC29.valid2
#print axioms N11Formalization.C450Source30GroupedC29.valid3
#print axioms N11Formalization.C450Source30GroupedC29.valid4
#print axioms N11Formalization.C450Source30GroupedC29.valid5
#print axioms N11Formalization.C450Source30GroupedC29.valid6
#print axioms N11Formalization.C450Source30GroupedC29.valid7
#print axioms N11Formalization.C450Source30GroupedC29.valid8
#print axioms N11Formalization.C450Source30GroupedC29.valid9
#print axioms N11Formalization.C450Source30GroupedC29.valid10
#print axioms N11Formalization.C450Source30GroupedC29.valid11
#print axioms N11Formalization.C450Source30GroupedC29.valid12
#print axioms N11Formalization.C450Source30GroupedC29.valid13
#print axioms N11Formalization.C450Source30GroupedC29.valid14
#print axioms N11Formalization.C450Source30GroupedC29.valid15
#print axioms N11Formalization.C450Source30GroupedC29.valid16
#print axioms N11Formalization.C450Source30GroupedC29.valid17
#print axioms N11Formalization.C450Source30GroupedC29.valid18
#print axioms N11Formalization.C450Source30GroupedC29.bound
#print axioms N11Formalization.C450Source30GroupedC29.endpoint_checks
