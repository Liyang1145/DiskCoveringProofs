import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((672715067:ℚ)/1250000000),((5708910129:ℚ)/10000000000),((9399865737:ℚ)/12875000000),((21286730387:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3919813183:ℚ)/5000000000),((-21818652153895207194784235631331704993:ℚ)/85369296875000000000000000000000000000),((-18587298933411162323623548601:ℚ)/44359680000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5620641079:ℚ)/10000000000),((297394051:ℚ)/500000000),((25942350623:ℚ)/35600000000),((1100182153:ℚ)/1287500000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1476765643:ℚ)/2000000000),((-281581148229611378221636850715379192954076878077035689:ℚ)/1101514062500000000000000000000000000000000000000000000),((-15314966964810122295013387:ℚ)/36966400000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((5859459689:ℚ)/10000000000),((6067327559:ℚ)/10000000000),((80454056579:ℚ)/108700000000),((22361982677:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6904153891:ℚ)/10000000000),((-2155372842013944058023435714360534889198865002405274621837:ℚ)/8027284393750000000000000000000000000000000000000000000000),((-6090399330022848603292866947:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((5978834147:ℚ)/10000000000),((3093374981:ℚ)/5000000000),((81767175617:ℚ)/110600000000),((11360124943:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((33268477:ℚ)/50000000),((-141705113768836880996163943321558066163776805331147112671:ℚ)/528476178125000000000000000000000000000000000000000000000),((-1513586652076455994956648507:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((3049093493:ℚ)/5000000000),((3153074733:ℚ)/5000000000),((13846676141:ℚ)/18750000000),((11539224199:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6395020627:ℚ)/10000000000),((-1225753526436813416931891179878877897088637928686464163:ℚ)/4577636718750000000000000000000000000000000000000000000),((-4513371394817499759588400129:ℚ)/11089920000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((388594957:ℚ)/625000000),((3182920497:ℚ)/5000000000),((5274544527:ℚ)/7090625000),((11628761491:ℚ)/14062500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6127063361:ℚ)/10000000000),((-609748696868624678333200965045027729617258670508860961:ℚ)/2228094312477111816406250000000000000000000000000000000),((-4499546210873040586053669049:ℚ)/11089920000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6277178109:ℚ)/10000000000),((803190903:ℚ)/1250000000),((85048959199:ℚ)/114400000000),((2929572709:ℚ)/3545312500),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((119784163:ℚ)/200000000),((-715624940726421999562557886202598441098578845442084111:ℚ)/2617472000000000000000000000000000000000000000000000000),((-280352109215237426950001449:ℚ)/693120000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((3168416079:ℚ)/5000000000),((6485208287:ℚ)/10000000000),((42852576869:ℚ)/57675000000),((23615624861:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1462130441:ℚ)/2500000000),((-27293086206140966485377363707117624820234126574967220409:ℚ)/99922106469726562500000000000000000000000000000000000000),((-5962178663027714357982206003:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6396481579:ℚ)/10000000000),((6544884313:ℚ)/10000000000),((86361297369:ℚ)/116300000000),((23794652939:ℚ)/28837500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((5704791517:ℚ)/10000000000),((-107314706791125251207069883777885532837913408411389923887:ℚ)/393259436750000000000000000000000000000000000000000000000),((-5943395936737159795303227203:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((3228063243:ℚ)/5000000000),((206392357:ℚ)/312500000),((43508695673:ℚ)/58625000000),((749177071:ℚ)/908593750),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1111555599:ℚ)/2000000000),((-12261423948520882951471982912564006484058710795068499417:ℚ)/44974935913085937500000000000000000000000000000000000000),((-5785641414872827534067963:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((651576699:ℚ)/1000000000),((333211087:ℚ)/500000000),((8767343689:ℚ)/11820000000),((1207633261:ℚ)/1465625000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5407210091:ℚ)/10000000000),((-234267977612328757276887918798284296368237923934753661:ℚ)/860104462500000000000000000000000000000000000000000000),((-14763703175219093181632403:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6575403199:ℚ)/10000000000),((420242711:ℚ)/625000000),((88329435189:ℚ)/119150000000),((1520728133:ℚ)/1846875000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1313194699:ℚ)/2500000000),((-2876843493600591678449400678278972770026343703594110982787:ℚ)/10572121786718750000000000000000000000000000000000000000000),((-22993551999805220790411427:ℚ)/57760000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3317517607:ℚ)/5000000000),((3391770223:ℚ)/5000000000),((44492693677:ℚ)/60050000000),((12255310669:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1273532337:ℚ)/2500000000),((-22995685328595973903693866456212639443056836829140638539:ℚ)/84586113330078125000000000000000000000000000000000000000),((-1466775231317253869235898323:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((3347331569:ℚ)/5000000000),((1725710329:ℚ)/2500000000),((44820647259:ℚ)/61000000000),((6217130987:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1232712779:ℚ)/2500000000),((-377186196851556126252024525657419701253133219132902693277:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-364265927146221550822712067:ℚ)/924160000000000000000000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1362781419:ℚ)/2000000000),((877765647:ℚ)/1250000000),((18190595609:ℚ)/24780000000),((3153296941:ℚ)/3812500000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((4588403419:ℚ)/10000000000),((-2104043568603034006785384669982282018440956460162785189:ℚ)/7925062162500000000000000000000000000000000000000000000),((-271356700073274534321966649:ℚ)/693120000000000000000000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((693313581:ℚ)/1000000000),((1785348201:ℚ)/2500000000),((9226449391:ℚ)/12580000000),((6396044603:ℚ)/7743750000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2110206077:ℚ)/5000000000),((-3221312506155145910756946656944867251417911233894857:ℚ)/12151278759765625000000000000000000000000000000000000),((-1077968468916829908661833961:ℚ)/2772480000000000000000000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((352617499:ℚ)/500000000),((1475976449:ℚ)/2000000000),((4678792489:ℚ)/6480000000),((5259929347:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3819467503:ℚ)/10000000000),((-5339329190415550649725268177566228563072316286254343:ℚ)/20995200000000000000000000000000000000000000000000000),((-628056710179627703750267:ℚ)/1638400000000000000000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((3645368631:ℚ)/5000000000),((4643048981:ℚ)/5000000000),((48099054941:ℚ)/80000000000),((16009146943:ℚ)/16200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1431284031:ℚ)/5000000000),((-29976871528056493998908666286094082566817435092384279467:ℚ)/200000000000000000000000000000000000000000000000000000000),((-387245337:ℚ)/1024000000)⟩
theorem valid17 : Valid source27 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((9196311941:ℚ)/10000000000),((130933801:ℚ)/100000000),((117159431351:ℚ)/220800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-73564331662181796331561537943436470497:ℚ)/897048576000000000000000000000000000000),((-387245337:ℚ)/1024000000)⟩
theorem valid18 : Valid source27 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source27 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC28
#check @N11Formalization.C450Source27GroupedC28.bound
#print axioms N11Formalization.C450Source27GroupedC28.valid0
#print axioms N11Formalization.C450Source27GroupedC28.valid1
#print axioms N11Formalization.C450Source27GroupedC28.valid2
#print axioms N11Formalization.C450Source27GroupedC28.valid3
#print axioms N11Formalization.C450Source27GroupedC28.valid4
#print axioms N11Formalization.C450Source27GroupedC28.valid5
#print axioms N11Formalization.C450Source27GroupedC28.valid6
#print axioms N11Formalization.C450Source27GroupedC28.valid7
#print axioms N11Formalization.C450Source27GroupedC28.valid8
#print axioms N11Formalization.C450Source27GroupedC28.valid9
#print axioms N11Formalization.C450Source27GroupedC28.valid10
#print axioms N11Formalization.C450Source27GroupedC28.valid11
#print axioms N11Formalization.C450Source27GroupedC28.valid12
#print axioms N11Formalization.C450Source27GroupedC28.valid13
#print axioms N11Formalization.C450Source27GroupedC28.valid14
#print axioms N11Formalization.C450Source27GroupedC28.valid15
#print axioms N11Formalization.C450Source27GroupedC28.valid16
#print axioms N11Formalization.C450Source27GroupedC28.valid17
#print axioms N11Formalization.C450Source27GroupedC28.valid18
#print axioms N11Formalization.C450Source27GroupedC28.bound
#print axioms N11Formalization.C450Source27GroupedC28.endpoint_checks
