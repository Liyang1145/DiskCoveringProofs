import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((746293867:ℚ)/1250000000),((1298622419:ℚ)/2000000000),((786293867:ℚ)/1112500000),((17778091447:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6671755331:ℚ)/10000000000),((-4344231186375694603202394067503:ℚ)/344223144531250000000000000000000),((-33950946445899986591413253:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6445503913:ℚ)/10000000000),((6730676977:ℚ)/10000000000),((2899501677:ℚ)/3950000000),((91978800701:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5584213349:ℚ)/10000000000),((-5633004751175631104935496931641423425113160224856899:ℚ)/385186718750000000000000000000000000000000000000000000),((-2169507075234534672461414013:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((3341536257:ℚ)/5000000000),((3424728887:ℚ)/5000000000),((3501536257:ℚ)/4687500000),((46761475531:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((992594871:ℚ)/2000000000),((-3340730060367089679031760030206585566841223958979717:ℚ)/214576721191406250000000000000000000000000000000000000),((-1625898940202461255044982919:ℚ)/11089920000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((272074203:ℚ)/400000000),((1742059387:ℚ)/2500000000),((854622609:ℚ)/1144000000),((23766772031:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4624078719:ℚ)/10000000000),((-13263648634697024846233666405734039725785420991533:ℚ)/850678400000000000000000000000000000000000000000000),((-10396370865126735167888879:ℚ)/70975488000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1384127311:ℚ)/2000000000),((3513813533:ℚ)/5000000000),((1448127311:ℚ)/1922500000),((47919575929:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1065096091:ℚ)/2500000000),((-534275276161467576209621586105982743008910098912539:ℚ)/33307368823242187500000000000000000000000000000000000),((-86604169709137244222274317:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3490013453:ℚ)/5000000000),((1771754087:ℚ)/2500000000),((10950040359:ℚ)/14537500000),((8050934377:ℚ)/9612500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((406716797:ℚ)/1000000000),((-12324931408960021816048989174576335574592493767750577:ℚ)/768084837402343750000000000000000000000000000000000000),((-541033003727123697454522293:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((3519708503:ℚ)/5000000000),((3573202699:ℚ)/5000000000),((11039125509:ℚ)/14656250000),((48691635087:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((241554163:ℚ)/625000000),((-11279990075481852003318303177244845300235071185576589:ℚ)/702733373641967773437500000000000000000000000000000000),((-540790311379672013043232893:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((3549403431:ℚ)/5000000000),((3602897111:ℚ)/5000000000),((3709403431:ℚ)/4925000000),((49077662443:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((365196691:ℚ)/1000000000),((-2997037510139919775584100002147363843132923171560217:ℚ)/186654614257812500000000000000000000000000000000000000),((-1621643950834229527523079191:ℚ)/11089920000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((3579098239:ℚ)/5000000000),((7235488551:ℚ)/10000000000),((11217294717:ℚ)/14834375000),((98541351163:ℚ)/118200000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((171324491:ℚ)/500000000),((-331969330999465711880536730640444465439808106917673659:ℚ)/20402706284141540527343750000000000000000000000000000000),((-540448827120764698077795117:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((3593945599:ℚ)/5000000000),((290607313:ℚ)/400000000),((11261836797:ℚ)/14893750000),((3957095069:ℚ)/4747000000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((1654117743:ℚ)/5000000000),((-83999153428191052532720209445206258433496059006130339:ℚ)/5162168841171264648437500000000000000000000000000000000),((-540327981954838265438610477:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((7217585861:ℚ)/10000000000),((3662285607:ℚ)/5000000000),((22612757583:ℚ)/30025000000),((49849712891:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((159288077:ℚ)/500000000),((-169867980482556214830717394978515231742168040123482161:ℚ)/10573264166259765625000000000000000000000000000000000000),((-2160257686811443295994540517:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7276975017:ℚ)/10000000000),((230748731:ℚ)/312500000),((7596975017:ℚ)/10087500000),((3139733503:ℚ)/3753125000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2926015567:ℚ)/10000000000),((-3818417814808738267804951253041122973111640341960677:ℚ)/237611193847656250000000000000000000000000000000000000),((-6477878250186042395875434359:ℚ)/44359680000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((146727279:ℚ)/200000000),((1860836841:ℚ)/2500000000),((459381837:ℚ)/610000000),((25310878933:ℚ)/30262500000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((105665713:ℚ)/400000000),((-22803080966259574691104539935779221378451685040699:ℚ)/1418631250000000000000000000000000000000000000000000),((-2589995125485592841421671:ℚ)/17743872000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3697876333:ℚ)/5000000000),((7562122713:ℚ)/10000000000),((3857876333:ℚ)/5162500000),((102787595269:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((290451663:ℚ)/1250000000),((-3371449686127272924867312631041447087218919385628291:ℚ)/214981069946289062500000000000000000000000000000000000),((-539056203778228045980289653:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((7514529467:ℚ)/10000000000),((1536179459:ℚ)/2000000000),((23503588401:ℚ)/31450000000),((20866332967:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1501150589:ℚ)/10000000000),((-2980203927853602067355891511648282256216016656733847:ℚ)/189863730621337890625000000000000000000000000000000000),((-2155861369702282285153294053:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((7633305459:ℚ)/10000000000),((3959222149:ℚ)/5000000000),((7953305459:ℚ)/10800000000),((53709887937:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-4366578488032856207317676117965613673290310056631199:ℚ)/291600000000000000000000000000000000000000000000000000),((-149316327:ℚ)/1024000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((1574171031:ℚ)/2000000000),((9818739923:ℚ)/10000000000),((4914513093:ℚ)/8000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-1530621580234744399429606905331921042343463735418899:ℚ)/200000000000000000000000000000000000000000000000000000),((-149316327:ℚ)/1024000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((9771167721:ℚ)/10000000000),((13619086929:ℚ)/10000000000),((10091167721:ℚ)/18400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-5138665417335674493309520768390941:ℚ)/1557376000000000000000000000000000000),((-149316327:ℚ)/1024000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((4747:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((4747:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4747:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC29
#check @N11Formalization.C450EighthGroupedC29.bound
#print axioms N11Formalization.C450EighthGroupedC29.valid0
#print axioms N11Formalization.C450EighthGroupedC29.valid1
#print axioms N11Formalization.C450EighthGroupedC29.valid2
#print axioms N11Formalization.C450EighthGroupedC29.valid3
#print axioms N11Formalization.C450EighthGroupedC29.valid4
#print axioms N11Formalization.C450EighthGroupedC29.valid5
#print axioms N11Formalization.C450EighthGroupedC29.valid6
#print axioms N11Formalization.C450EighthGroupedC29.valid7
#print axioms N11Formalization.C450EighthGroupedC29.valid8
#print axioms N11Formalization.C450EighthGroupedC29.valid9
#print axioms N11Formalization.C450EighthGroupedC29.valid10
#print axioms N11Formalization.C450EighthGroupedC29.valid11
#print axioms N11Formalization.C450EighthGroupedC29.valid12
#print axioms N11Formalization.C450EighthGroupedC29.valid13
#print axioms N11Formalization.C450EighthGroupedC29.valid14
#print axioms N11Formalization.C450EighthGroupedC29.valid15
#print axioms N11Formalization.C450EighthGroupedC29.valid16
#print axioms N11Formalization.C450EighthGroupedC29.valid17
#print axioms N11Formalization.C450EighthGroupedC29.bound
#print axioms N11Formalization.C450EighthGroupedC29.endpoint_checks
