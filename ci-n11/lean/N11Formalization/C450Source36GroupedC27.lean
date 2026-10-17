import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/8),((11:ℚ)/16),((5153577683:ℚ)/10000000000),((5499354793:ℚ)/10000000000),((7329577683:ℚ)/10300000000),((82892902723:ℚ)/99200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((4128093803:ℚ)/5000000000),((-326127549202399026770188481424489540340444678284164412842207:ℚ)/942634905600000000000000000000000000000000000000000000000000),((-46426046972251439154591637:ℚ)/92416000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((337138373:ℚ)/625000000),((717504031:ℚ)/1250000000),((157712791:ℚ)/222500000),((10692544341:ℚ)/12875000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1954079447:ℚ)/2500000000),((-51685063617023834085192018221561307624894960533771558541:ℚ)/148395848083496093750000000000000000000000000000000000000),((-715375891409288094515893:ℚ)/1444000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((112692459:ℚ)/200000000),((5860286067:ℚ)/10000000000),((156212459:ℚ)/217400000),((86863146737:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7356454679:ℚ)/10000000000),((-504520311194717235203522266668461491607177522728723573687493:ℚ)/1379342345400000000000000000000000000000000000000000000000000),((-45475553509895791182970957:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((575474983:ℚ)/1000000000),((1196097453:ℚ)/2000000000),((793074983:ℚ)/1106000000),((17637071983:ℚ)/21740000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3558873103:ℚ)/5000000000),((-304775896068692078512797662350411835314877904651655551053:ℚ)/832329050576953125000000000000000000000000000000000000000),((-1805460461985120188722317:ℚ)/3696640000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((2937414303:ℚ)/5000000000),((6040568993:ℚ)/10000000000),((4025414303:ℚ)/5577500000),((88846258923:ℚ)/110600000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((6872339377:ℚ)/10000000000),((-31487392239535128610842546365090877904524933099945264147011:ℚ)/84216453814062500000000000000000000000000000000000000000000),((-44975933205154402650567237:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((296742537:ℚ)/500000000),((244025543:ℚ)/400000000),((405542537:ℚ)/562500000),((3580280973:ℚ)/4462000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3373443747:ℚ)/5000000000),((-3649708544128196275301102098462092426133550497495877:ℚ)/9759807765527343750000000000000000000000000000000000),((-71683045105933634267637:ℚ)/147865600000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((749357721:ℚ)/1250000000),((3080348161:ℚ)/5000000000),((1021357721:ℚ)/1418125000),((5009314419:ℚ)/6250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1323892033:ℚ)/2000000000),((-1618652515862156718362960211201844079866155026785091271:ℚ)/4327774047851562500000000000000000000000000000000000000),((-11156517716772467501978373:ℚ)/23104000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((756857747:ℚ)/1250000000),((3110371269:ℚ)/5000000000),((1028857747:ℚ)/1430000000),((45414083959:ℚ)/56725000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1297987497:ℚ)/2000000000),((-30511692179216153279149721713391087745255141927606766594033:ℚ)/81566076591162109375000000000000000000000000000000000000000),((-584847847514733920252847:ℚ)/1216000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((3057425819:ℚ)/5000000000),((785097189:ℚ)/1250000000),((4145425819:ℚ)/5767500000),((11436069079:ℚ)/14300000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1589546963:ℚ)/2500000000),((-308096141401162804488397731736231273595617831449014533:ℚ)/823504095336914062500000000000000000000000000000000000),((-691703125154327415487023:ℚ)/1444000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6174831021:ℚ)/10000000000),((6340801527:ℚ)/10000000000),((8350831021:ℚ)/11630000000),((92148816797:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6224066277:ℚ)/10000000000),((-695732305717680866758445988065164474039171270242703273731173:ℚ)/1859350557188671875000000000000000000000000000000000000000000),((-44087761832420194228709077:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((6234800381:ℚ)/10000000000),((3200407427:ℚ)/5000000000),((8410800381:ℚ)/11725000000),((46404481697:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3043706199:ℚ)/5000000000),((-323542749095935146450043726093861652888689880514687955399591:ℚ)/864556292980078125000000000000000000000000000000000000000000),((-10976180512500042111870877:ℚ)/23104000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6294759967:ℚ)/10000000000),((3230408879:ℚ)/5000000000),((8470759967:ℚ)/11820000000),((46734497669:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5948048073:ℚ)/10000000000),((-34819260198005137260337337178826290827151617166426620017571:ℚ)/93030654936218261718750000000000000000000000000000000000000),((-10929970204736518168927733:ℚ)/23104000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((6354710019:ℚ)/10000000000),((1630202623:ℚ)/2500000000),((8530710019:ℚ)/11915000000),((23532228853:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5805774483:ℚ)/10000000000),((-215781540965763852721760229289081520906871822106066265070713:ℚ)/576458137726171875000000000000000000000000000000000000000000),((-2720827393820621234760777:ℚ)/5776000000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((641465077:ℚ)/1000000000),((3290396651:ℚ)/5000000000),((859065077:ℚ)/1201000000),((47394363161:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1415092147:ℚ)/2500000000),((-222814989293061943212270200490872970649548653018443592710147:ℚ)/595177418711682128906250000000000000000000000000000000000000),((-10836198662361798870770813:ℚ)/23104000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((1618645611:ℚ)/2500000000),((67007301:ℚ)/100000000),((2162645611:ℚ)/3050000000),((961080311:ℚ)/1201000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5511578783:ℚ)/10000000000),((-364554320834035329484786062307250216754558977676224977:ℚ)/990672559321875000000000000000000000000000000000000000),((-4295087910118686259213:ℚ)/9241600000000000000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3297209713:ℚ)/5000000000),((426289373:ℚ)/625000000),((1461736571:ℚ)/2065000000),((6089183103:ℚ)/7625000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5202664273:ℚ)/10000000000),((-210686524476894532282904333684921442841579967668291019691:ℚ)/572162799072265625000000000000000000000000000000000000000),((-332510854984464253571429:ℚ)/722000000000000000000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3357111313:ℚ)/5000000000),((6940494611:ℚ)/10000000000),((4445111313:ℚ)/6290000000),((32915146907:ℚ)/41300000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2438101097:ℚ)/5000000000),((-648562491136446882952933938013167769133314423307534068999:ℚ)/1760192125781250000000000000000000000000000000000000000000),((-42164697829138904950210573:ℚ)/92416000000000000000000000)⟩
theorem valid16 : Valid source36 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source36 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((2135623:ℚ)/3125000),((1436024907:ℚ)/2000000000),((312847:ℚ)/450000),((20276273977:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4528365407:ℚ)/10000000000),((-4318924303629768942345020444913603419277587946084887629:ℚ)/12106614600000000000000000000000000000000000000000000000),((-1653059292348586744627037:ℚ)/3696640000000000000000000)⟩
theorem valid17 : Valid source36 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source36 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((7073444637:ℚ)/10000000000),((8137513563:ℚ)/10000000000),((9249444637:ℚ)/14480000000),((111912649193:ℚ)/129600000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((748859161:ℚ)/2000000000),((-354913859280076884640238132378621301584141634492594835802453:ℚ)/1231242508800000000000000000000000000000000000000000000000000),((-418873877654676201:ℚ)/972800000000000000)⟩
theorem valid18 : Valid source36 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((4015107031:ℚ)/5000000000),((9093485307:ℚ)/10000000000),((5103107031:ℚ)/8000000000),((122428338377:ℚ)/144800000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-8574634116386314062529451721654179974476165722917229121571:ℚ)/28462756800000000000000000000000000000000000000000000000000),((-55256473:ℚ)/128000000)⟩
theorem valid19 : Valid source36 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source36 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((2246421519:ℚ)/2500000000),((3227275611:ℚ)/2500000000),((2790421519:ℚ)/5520000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-39278566143659:ℚ)/552000000000000),((-55256473:ℚ)/128000000)⟩
theorem valid20 : Valid source36 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source36 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source36 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source36 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC27
#check @N11Formalization.C450Source36GroupedC27.bound
#print axioms N11Formalization.C450Source36GroupedC27.valid0
#print axioms N11Formalization.C450Source36GroupedC27.valid1
#print axioms N11Formalization.C450Source36GroupedC27.valid2
#print axioms N11Formalization.C450Source36GroupedC27.valid3
#print axioms N11Formalization.C450Source36GroupedC27.valid4
#print axioms N11Formalization.C450Source36GroupedC27.valid5
#print axioms N11Formalization.C450Source36GroupedC27.valid6
#print axioms N11Formalization.C450Source36GroupedC27.valid7
#print axioms N11Formalization.C450Source36GroupedC27.valid8
#print axioms N11Formalization.C450Source36GroupedC27.valid9
#print axioms N11Formalization.C450Source36GroupedC27.valid10
#print axioms N11Formalization.C450Source36GroupedC27.valid11
#print axioms N11Formalization.C450Source36GroupedC27.valid12
#print axioms N11Formalization.C450Source36GroupedC27.valid13
#print axioms N11Formalization.C450Source36GroupedC27.valid14
#print axioms N11Formalization.C450Source36GroupedC27.valid15
#print axioms N11Formalization.C450Source36GroupedC27.valid16
#print axioms N11Formalization.C450Source36GroupedC27.valid17
#print axioms N11Formalization.C450Source36GroupedC27.valid18
#print axioms N11Formalization.C450Source36GroupedC27.valid19
#print axioms N11Formalization.C450Source36GroupedC27.valid20
#print axioms N11Formalization.C450Source36GroupedC27.bound
#print axioms N11Formalization.C450Source36GroupedC27.endpoint_checks
