import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((1056468203:ℚ)/2000000000),((5615914679:ℚ)/10000000000),((15205150233:ℚ)/20600000000),((21487744037:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1604628037:ℚ)/2000000000),((-10560340977230977858946020928153009454891:ℚ)/32624796800000000000000000000000000000000),((-1340527276307524511019703377:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5521612177:ℚ)/10000000000),((1463816037:ℚ)/2500000000),((26219244649:ℚ)/35600000000),((5551448111:ℚ)/6437500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7575409383:ℚ)/10000000000),((-1068976554650040830861007228485198031554727349689811272031:ℚ)/3301807619857788085937500000000000000000000000000000000000),((-247518744677883384308039179:ℚ)/554496000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1440188997:ℚ)/2500000000),((5974889851:ℚ)/10000000000),((20322078967:ℚ)/27175000000),((22564669553:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((27756401:ℚ)/39062500),((-1737432422825597253023092825038722935439948580602428812355489:ℚ)/5206059477256250000000000000000000000000000000000000000000000),((-1309632382582833020808415897:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((5880284367:ℚ)/10000000000),((6094485143:ℚ)/10000000000),((82603128037:ℚ)/110600000000),((22923455429:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6861015963:ℚ)/10000000000),((-28550417278590466496237342438793400451438718768227317846177:ℚ)/85617180983827209472656250000000000000000000000000000000000),((-1298995486346432620309611153:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((5999785747:ℚ)/10000000000),((6214051589:ℚ)/10000000000),((27972547739:ℚ)/37500000000),((23282154767:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((826114031:ℚ)/1250000000),((-515886518363721694832156500903186855396564472950375879:ℚ)/1548270053100585937500000000000000000000000000000000000),((-1288189271508278513123747737:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((1223852303:ℚ)/2000000000),((1583397661:ℚ)/2500000000),((1311259641:ℚ)/1760000000),((5910192983:ℚ)/7031250000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((6348410217:ℚ)/10000000000),((-8644417636580867609329013599734632002700426754088803191:ℚ)/25963783264160156250000000000000000000000000000000000000),((-221124260356655725867617:ℚ)/512000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6238712961:ℚ)/10000000000),((799168791:ℚ)/1250000000),((86545842571:ℚ)/115350000000),((2977506373:ℚ)/3575000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6078403753:ℚ)/10000000000),((-6675029013822718911135269551973531307333367323965511149:ℚ)/19789832791065216064453125000000000000000000000000000000),((-59609177561100948831752371:ℚ)/138624000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6298429943:ℚ)/10000000000),((1613275917:ℚ)/2500000000),((87202729373:ℚ)/116300000000),((5999827751:ℚ)/7209375000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2969712427:ℚ)/5000000000),((-19775154962895826696935142471117573754900801661427085558489:ℚ)/58659524143077945709228515625000000000000000000000000000000),((-237387908544168897724389499:ℚ)/554496000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((6358141291:ℚ)/10000000000),((6512850819:ℚ)/10000000000),((87859554201:ℚ)/117250000000),((24178552457:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((5797538181:ℚ)/10000000000),((-11385176580453389811597632856298042928854424983498738474098627:ℚ)/33789741783971386718750000000000000000000000000000000000000000),((-3781298698832492453651530651:ℚ)/8871936000000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6417847143:ℚ)/10000000000),((1643147983:ℚ)/2500000000),((88516318573:ℚ)/118200000000),((6089443949:ℚ)/7328125000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5652521447:ℚ)/10000000000),((-192874140006053360217690258896501075555895083296347192469499:ℚ)/572719969451093673706054687500000000000000000000000000000000),((-78422163480753669905297633:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6477547633:ℚ)/10000000000),((6692056627:ℚ)/10000000000),((89173023963:ℚ)/120100000000),((24716169881:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5504123893:ℚ)/10000000000),((-715482212234763554877261253989278184092868187454699015369953:ℚ)/2153846418080664062500000000000000000000000000000000000000000),((-1243271029548408849523251113:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((82461663:ℚ)/125000000),((1362299773:ℚ)/2000000000),((1131078293:ℚ)/1525000000),((5014899319:ℚ)/6005000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5196007193:ℚ)/10000000000),((-1671664523109852500602974619796591747469719911296730949669:ℚ)/5035918843219531250000000000000000000000000000000000000000),((-49264723175931673305547913:ℚ)/118292480000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3358149251:ℚ)/5000000000),((7050320089:ℚ)/10000000000),((45899641761:ℚ)/62900000000),((25790960267:ℚ)/30500000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((974073833:ℚ)/2000000000),((-5671817402212005362457667019251652293706773841621248714849257:ℚ)/17539646449414062500000000000000000000000000000000000000000000),((-1207804057373083816930618737:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((173874331:ℚ)/250000000),((7289063223:ℚ)/10000000000),((87430283:ℚ)/120000000),((26507189669:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4149708879:ℚ)/10000000000),((-99913328602874406058774980923635850225242211690426131:ℚ)/309094531250000000000000000000000000000000000000000000),((-3549937485913251431836477939:ℚ)/8871936000000000000000000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((449598663:ℚ)/625000000),((9196870123:ℚ)/10000000000),((6065585293:ℚ)/10000000000),((32230610369:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((3285119103:ℚ)/10000000000),((-108587885488516110243639852173827909802494840941714937:ℚ)/492075000000000000000000000000000000000000000000000000),((-398333647:ℚ)/1024000000)⟩
theorem valid14 : Valid source30 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9100521549:ℚ)/10000000000),((6503005881:ℚ)/5000000000),((118025737039:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1411375943122504330301594813:ℚ)/8125440000000000000000000000),((-398333647:ℚ)/1024000000)⟩
theorem valid15 : Valid source30 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet15 valid15
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
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC28
#check @N11Formalization.C450Source30GroupedC28.bound
#print axioms N11Formalization.C450Source30GroupedC28.valid0
#print axioms N11Formalization.C450Source30GroupedC28.valid1
#print axioms N11Formalization.C450Source30GroupedC28.valid2
#print axioms N11Formalization.C450Source30GroupedC28.valid3
#print axioms N11Formalization.C450Source30GroupedC28.valid4
#print axioms N11Formalization.C450Source30GroupedC28.valid5
#print axioms N11Formalization.C450Source30GroupedC28.valid6
#print axioms N11Formalization.C450Source30GroupedC28.valid7
#print axioms N11Formalization.C450Source30GroupedC28.valid8
#print axioms N11Formalization.C450Source30GroupedC28.valid9
#print axioms N11Formalization.C450Source30GroupedC28.valid10
#print axioms N11Formalization.C450Source30GroupedC28.valid11
#print axioms N11Formalization.C450Source30GroupedC28.valid12
#print axioms N11Formalization.C450Source30GroupedC28.valid13
#print axioms N11Formalization.C450Source30GroupedC28.valid14
#print axioms N11Formalization.C450Source30GroupedC28.valid15
#print axioms N11Formalization.C450Source30GroupedC28.bound
#print axioms N11Formalization.C450Source30GroupedC28.endpoint_checks
