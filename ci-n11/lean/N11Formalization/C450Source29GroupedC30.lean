import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((13:ℚ)/16),((7:ℚ)/8),((5196244811:ℚ)/10000000000),((5529138161:ℚ)/10000000000),((84831182543:ℚ)/103000000000),((47663967127:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8179530139:ℚ)/10000000000),((-71368635114832542438400484140104631162558297:ℚ)/202273740160000000000000000000000000000000000),((-6628085747653277058535121861:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2717312201:ℚ)/5000000000),((5767741251:ℚ)/10000000000),((43965058613:ℚ)/53400000000),((49334188757:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7740546977:ℚ)/10000000000),((-84097395424301497935558531048419846122662135798287444179817:ℚ)/237730148629760742187500000000000000000000000000000000000000),((-54121757138450327745628943:ℚ)/122880000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1418235269:ℚ)/2500000000),((5887013681:ℚ)/10000000000),((22757058497:ℚ)/27175000000),((50169095767:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((364050371:ℚ)/500000000),((-1237199087230244397500949428581897037951404997540810003851695289:ℚ)/3373526541262050000000000000000000000000000000000000000000000000),((-6454479034746022543209567301:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((724009737:ℚ)/1250000000),((375391753:ℚ)/625000000),((11572126581:ℚ)/13825000000),((3187742271:ℚ)/3396875000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((7042219677:ℚ)/10000000000),((-245338386957905550901329124267480173021605861968023257997:ℚ)/668884226436150074005126953125000000000000000000000000000),((-24984385411216586702273269:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((2955600681:ℚ)/5000000000),((6125505273:ℚ)/10000000000),((15687602951:ℚ)/18750000000),((7405505273:ℚ)/7900000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6796549257:ℚ)/10000000000),((-1130371374946052358649696946234822763000836332351288517:ℚ)/3081493750000000000000000000000000000000000000000000000),((-19011666062341203831792192767:ℚ)/44359680000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((1507578039:ℚ)/2500000000),((193284929:ℚ)/312500000),((23918514507:ℚ)/28362500000),((544331501:ℚ)/585937500),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1635799373:ℚ)/2500000000),((-2412037779946181863741291439679246809896386118240410833581:ℚ)/6472959509119391441345214843750000000000000000000000000000),((-17063380538440126152221:ℚ)/40000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6089863001:ℚ)/10000000000),((6244726217:ℚ)/10000000000),((96448219013:ℚ)/114400000000),((52673083519:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3206675203:ℚ)/5000000000),((-347659653574951978528826549900688826928343427394556247924891:ℚ)/933115916202894531250000000000000000000000000000000000000000),((-6278136808284363082141202549:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6149410913:ℚ)/10000000000),((6304330837:ℚ)/10000000000),((97222341869:ℚ)/115350000000),((53090315859:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6281211183:ℚ)/10000000000),((-193258078904406623649149420194210512881534836910139805349659973:ℚ)/518778592718100000000000000000000000000000000000000000000000000),((-6248479902817289016222799229:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1552238991:ℚ)/2500000000),((1272786337:ℚ)/2000000000),((24499106883:ℚ)/29075000000),((10701504359:ℚ)/11535000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3073314529:ℚ)/5000000000),((-64435177887093105283376269071086703729294114091002192596153:ℚ)/172993975840834031250000000000000000000000000000000000000000),((-248749870148828684420536229:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((3134249113:ℚ)/5000000000),((1605882213:ℚ)/2500000000),((7055034067:ℚ)/8375000000),((13481175491:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((751179617:ℚ)/1250000000),((-24076212640131395591969620836148504357311103480083880429037:ℚ)/64648740658108520507812500000000000000000000000000000000000),((-1160425749421908403724624087:ℚ)/2772480000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1265607553:ℚ)/2000000000),((6483122429:ℚ)/10000000000),((19908898189:ℚ)/23640000000),((7763122429:ℚ)/8375000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2934724403:ℚ)/5000000000),((-119374968910750730671368880838094534594658920395979567265169:ℚ)/320589603890991210937500000000000000000000000000000000000000),((-6159051601183234110545776781:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6387574649:ℚ)/10000000000),((6542712501:ℚ)/10000000000),((100318470437:ℚ)/119150000000),((54758987507:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2863228291:ℚ)/5000000000),((-8182973238286966484683973265880939340169160360156498436942483069:ℚ)/21979195875223481250000000000000000000000000000000000000000000000),((-18387268613520899580070538423:ℚ)/44359680000000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6447108941:ℚ)/10000000000),((412643697:ℚ)/625000000),((101092416233:ℚ)/120100000000),((3448505879:ℚ)/3723437500),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5580226257:ℚ)/10000000000),((-692935612395662646946735069014793063723336063138009420888809:ℚ)/1861479374668568325042724609375000000000000000000000000000000),((-71473255214064640293680207:ℚ)/173280000000000000000000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((101666261:ℚ)/156250000),((3360731257:ℚ)/5000000000),((1591661393:ℚ)/1906250000),((28005118799:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((543049313:ℚ)/1000000000),((-230951452954845103713145855235204486472664959016881556685851:ℚ)/629489855402441406250000000000000000000000000000000000000000),((-1509686265083599300656685909:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((2120223:ℚ)/3200000),((3420306567:ℚ)/5000000000),((11030833:ℚ)/13216000),((28422145969:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5119268979:ℚ)/10000000000),((-2774235867050818961536410260385022656938770736230898377041229:ℚ)/7561703552539062500000000000000000000000000000000000000000000),((-4483599927546544871081038847:ℚ)/11089920000000000000000000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3372371811:ℚ)/5000000000),((6959751593:ℚ)/10000000000),((52480833543:ℚ)/62900000000),((8239751593:ℚ)/8850000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4789782861:ℚ)/10000000000),((-614074806528551323731046391758366900733320392910664770477:ℚ)/1673829291803741455078125000000000000000000000000000000000),((-5917215443107133096468787509:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid source29 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source29 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((1715945343:ℚ)/2500000000),((3598997091:ℚ)/5000000000),((8875763153:ℚ)/10800000000),((29672979637:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((443794031:ℚ)/1000000000),((-50594150013527581781609318107136414417751351907079749863217:ℚ)/141732515453906250000000000000000000000000000000000000000000),((-4345845909492485979730197863:ℚ)/11089920000000000000000000000)⟩
theorem valid16 : Valid source29 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7101831473:ℚ)/10000000000),((1820532127:ℚ)/2000000000),((109603809149:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((364080701:ℚ)/1000000000),((-25424309931288209588502596402284794773:ℚ)/96000000000000000000000000000000000000),((-77347619:ℚ)/204800000)⟩
theorem valid17 : Valid source29 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((9005289177:ℚ)/10000000000),((12908130429:ℚ)/10000000000),((44782919767:ℚ)/73600000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-583072043571835757869644469:ℚ)/2708480000000000000000000000),((-77347619:ℚ)/204800000)⟩
theorem valid18 : Valid source29 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source29 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source29 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC30
#check @N11Formalization.C450Source29GroupedC30.bound
#print axioms N11Formalization.C450Source29GroupedC30.valid0
#print axioms N11Formalization.C450Source29GroupedC30.valid1
#print axioms N11Formalization.C450Source29GroupedC30.valid2
#print axioms N11Formalization.C450Source29GroupedC30.valid3
#print axioms N11Formalization.C450Source29GroupedC30.valid4
#print axioms N11Formalization.C450Source29GroupedC30.valid5
#print axioms N11Formalization.C450Source29GroupedC30.valid6
#print axioms N11Formalization.C450Source29GroupedC30.valid7
#print axioms N11Formalization.C450Source29GroupedC30.valid8
#print axioms N11Formalization.C450Source29GroupedC30.valid9
#print axioms N11Formalization.C450Source29GroupedC30.valid10
#print axioms N11Formalization.C450Source29GroupedC30.valid11
#print axioms N11Formalization.C450Source29GroupedC30.valid12
#print axioms N11Formalization.C450Source29GroupedC30.valid13
#print axioms N11Formalization.C450Source29GroupedC30.valid14
#print axioms N11Formalization.C450Source29GroupedC30.valid15
#print axioms N11Formalization.C450Source29GroupedC30.valid16
#print axioms N11Formalization.C450Source29GroupedC30.valid17
#print axioms N11Formalization.C450Source29GroupedC30.valid18
#print axioms N11Formalization.C450Source29GroupedC30.bound
#print axioms N11Formalization.C450Source29GroupedC30.endpoint_checks
