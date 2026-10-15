import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/4),((13:ℚ)/16),((1033291:ℚ)/1953125),((1405160271:ℚ)/2500000000),((31298984:ℚ)/40234375),((22587083523:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8008289309:ℚ)/10000000000),((-36260665747236126940423520573373:ℚ)/104210567474365234375000000000000),((-5990308660941267409096959:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((1382284539:ℚ)/2500000000),((2929729847:ℚ)/5000000000),((5186853617:ℚ)/6675000000),((46726488011:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7560986983:ℚ)/10000000000),((-2523069405519447308044251123003398784719102670934067:ℚ)/7260956954956054687500000000000000000000000000000000),((-23556099951751420926106191:ℚ)/57760000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((2883870623:ℚ)/5000000000),((747354269:ℚ)/1250000000),((10731611869:ℚ)/13587500000),((11875605497:ℚ)/13350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7091535919:ℚ)/10000000000),((-16980462963746881491942384666224368507867395725186130157:ℚ)/47034869494628906250000000000000000000000000000000000000),((-1459435393810541836914039:ℚ)/3610000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1471753419:ℚ)/2500000000),((6098186991:ℚ)/10000000000),((5455260257:ℚ)/6912500000),((96556430883:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6847027697:ℚ)/10000000000),((-139523317266733121723400054140963607905347182290647361:ℚ)/387067513275146484375000000000000000000000000000000000),((-92576481346104905768072319:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((6006268043:ℚ)/10000000000),((1539463913:ℚ)/2500000000),((22178804129:ℚ)/27887500000),((3476147267:ℚ)/3950000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((6595004319:ℚ)/10000000000),((-49731786228065855077657651120538498448161908173372598331:ℚ)/135552885632324218750000000000000000000000000000000000000),((-5760013731112000198382031:ℚ)/14440000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((6065888743:ℚ)/10000000000),((6217519317:ℚ)/10000000000),((22357666229:ℚ)/28125000000),((98107751121:ℚ)/111550000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3232946649:ℚ)/5000000000),((-50965535127842833785418217894924009539506865960099506839:ℚ)/139045715332031250000000000000000000000000000000000000000),((-91742244271706290054155111:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1531376317:ℚ)/2500000000),((3138589057:ℚ)/5000000000),((5634128951:ℚ)/7090625000),((49441657741:ℚ)/56250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3167272123:ℚ)/5000000000),((-815930634240355135827874457383478396610681431250599709:ℚ)/2228094312477111816406250000000000000000000000000000000),((-22830638651191415674296351:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((6185117723:ℚ)/10000000000),((6336832163:ℚ)/10000000000),((22715353169:ℚ)/28600000000),((99658818119:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6200811909:ℚ)/10000000000),((-14963362626056790845496433827374091176183903209555477:ℚ)/40898000000000000000000000000000000000000000000000000),((-90901150275478860764195031:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1561181553:ℚ)/2500000000),((399780099:ℚ)/625000000),((5723544659:ℚ)/7209375000),((6277141287:ℚ)/7150000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6064535561:ℚ)/10000000000),((-642059485440307189494299229208035079821889973670945347:ℚ)/1756443277788162231445312500000000000000000000000000000),((-353429808000999166174599:ℚ)/902500000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((394020677:ℚ)/625000000),((6456126491:ℚ)/10000000000),((1442062031:ℚ)/1817187500),((101209644383:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1481384149:ℚ)/2500000000),((-547899247808489605192917464775613068382913192678801:ℚ)/1500165698051452636718750000000000000000000000000000),((-90053195916234577919333319:ℚ)/231040000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((39774573:ℚ)/62500000),((1303153399:ℚ)/2000000000),((145323719:ℚ)/183203125),((20396994187:ℚ)/23260000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2891807797:ℚ)/5000000000),((-6010212066896322136119222690175563556267717954241:ℚ)/16470313444733619689941406250000000000000000000000),((-9930930202843559635959:ℚ)/25600000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6423528847:ℚ)/10000000000),((1643850801:ℚ)/2500000000),((23430586541:ℚ)/29550000000),((25690060413:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2819274381:ℚ)/5000000000),((-4899948778131459242777811176437506573344894479312587773:ℚ)/13439132226562500000000000000000000000000000000000000000),((-5574898621958810679452799:ℚ)/14440000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((810390303:ℚ)/1250000000),((6635035219:ℚ)/10000000000),((2951170909:ℚ)/3723437500),((103535457847:ℚ)/118200000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5490083529:ℚ)/10000000000),((-352607790210050267154351772727472303061365907707361177:ℚ)/967906657719612121582031250000000000000000000000000000),((-88768394175962106502400439:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((408919531:ℚ)/625000000),((6694663143:ℚ)/10000000000),((1486758593:ℚ)/1876562500),((104310620859:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5337933097:ℚ)/10000000000),((-939617767203348886609468153457785631643448366736487:ℚ)/2581363321840763092041015625000000000000000000000000),((-88336693375851363654287151:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((6602299147:ℚ)/10000000000),((68139071:ℚ)/100000000),((23966897441:ℚ)/30500000000),((1058607923:ℚ)/1201000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((323860597:ℚ)/625000000),((-63390167346758600096072588950499586161271765785242916171:ℚ)/177328906250000000000000000000000000000000000000000000000),((-8746813934566795387359:ℚ)/23104000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((6721462509:ℚ)/10000000000),((1386627163:ℚ)/2000000000),((24324387527:ℚ)/30975000000),((21482153119:ℚ)/24400000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((606978851:ℚ)/1250000000),((-5526215668859581613613811280337860299369600596913044631:ℚ)/15478637036132812500000000000000000000000000000000000000),((-9594760466933294055471:ℚ)/25600000000000000000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((6840613129:ℚ)/10000000000),((1410469997:ℚ)/2000000000),((24681839387:ℚ)/31450000000),((21792109961:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2254208479:ℚ)/5000000000),((-67702261823854524265975373923264145007472697377169977:ℚ)/189863730621337890625000000000000000000000000000000000),((-9496998612758143414431:ℚ)/25600000000000000000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((1739937897:ℚ)/2500000000),((7290737267:ℚ)/10000000000),((6259813691:ℚ)/8100000000),((6591740263:ℚ)/7400000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4134086251:ℚ)/10000000000),((-42416395396251362661275474677658952235103213240321347:ℚ)/123018750000000000000000000000000000000000000000000000),((-83925177976204044923992311:ℚ)/231040000000000000000000000)⟩
theorem valid17 : Valid source28 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((7197994177:ℚ)/10000000000),((4598155973:ℚ)/5000000000),((25753982531:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1633531713:ℚ)/5000000000),((-17170155311256699747517155605846727115766322181855131467:ℚ)/75000000000000000000000000000000000000000000000000000000),((-1412181:ℚ)/4000000)⟩
theorem valid18 : Valid source28 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((910266063:ℚ)/1000000000),((13002844411:ℚ)/10000000000),((3146798189:ℚ)/5520000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-6728710651119445857741986945199133:ℚ)/42049152000000000000000000000000000),((-1412181:ℚ)/4000000)⟩
theorem valid19 : Valid source28 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source28 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC29
#check @N11Formalization.C450Source28GroupedC29.bound
#print axioms N11Formalization.C450Source28GroupedC29.valid0
#print axioms N11Formalization.C450Source28GroupedC29.valid1
#print axioms N11Formalization.C450Source28GroupedC29.valid2
#print axioms N11Formalization.C450Source28GroupedC29.valid3
#print axioms N11Formalization.C450Source28GroupedC29.valid4
#print axioms N11Formalization.C450Source28GroupedC29.valid5
#print axioms N11Formalization.C450Source28GroupedC29.valid6
#print axioms N11Formalization.C450Source28GroupedC29.valid7
#print axioms N11Formalization.C450Source28GroupedC29.valid8
#print axioms N11Formalization.C450Source28GroupedC29.valid9
#print axioms N11Formalization.C450Source28GroupedC29.valid10
#print axioms N11Formalization.C450Source28GroupedC29.valid11
#print axioms N11Formalization.C450Source28GroupedC29.valid12
#print axioms N11Formalization.C450Source28GroupedC29.valid13
#print axioms N11Formalization.C450Source28GroupedC29.valid14
#print axioms N11Formalization.C450Source28GroupedC29.valid15
#print axioms N11Formalization.C450Source28GroupedC29.valid16
#print axioms N11Formalization.C450Source28GroupedC29.valid17
#print axioms N11Formalization.C450Source28GroupedC29.valid18
#print axioms N11Formalization.C450Source28GroupedC29.valid19
#print axioms N11Formalization.C450Source28GroupedC29.bound
#print axioms N11Formalization.C450Source28GroupedC29.endpoint_checks
