import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((6234386817:ℚ)/10000000000),((841369229:ℚ)/1250000000),((-741369229:ℚ)/3100000000),((-4954386817:ℚ)/35600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3044181971:ℚ)/5000000000),((12427211422594483066144596380382722393321238205663300103:ℚ)/1092701950000000000000000000000000000000000000000000000000),((86680356581056942763:ℚ)/2968750000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((3354804227:ℚ)/5000000000),((3424887299:ℚ)/5000000000),((-3024887299:ℚ)/13350000000),((-8144412681:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4889144693:ℚ)/10000000000),((1451124090401801378880480847761075496400139042261107890147:ℚ)/133955308320703125000000000000000000000000000000000000000000),((202325522408454334953661:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6828409017:ℚ)/10000000000),((6968592931:ℚ)/10000000000),((-6168592931:ℚ)/27175000000),((-16645227051:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4545131577:ℚ)/10000000000),((775643842999922433846189943740631841910637958434515212053:ℚ)/71806700702734375000000000000000000000000000000000000000000),((42208959030217006828559:ℚ)/1520000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((3473603921:ℚ)/5000000000),((7028001223:ℚ)/10000000000),((-6228001223:ℚ)/27650000000),((-8500811763:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((166999203:ℚ)/400000000),((200804643384295581595151538466331030755754955950015726419:ℚ)/18740186438668823242187500000000000000000000000000000000000),((793886737575615038871269:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((7006606631:ℚ)/10000000000),((7087408953:ℚ)/10000000000),((-64818649:ℚ)/287500000),((-1908868877:ℚ)/12500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((994458437:ℚ)/2500000000),((17606285479528432295127705573782867646849407427315937:ℚ)/1645088195800781250000000000000000000000000000000000000),((2370711799701348834929647:ℚ)/86640000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((7066005017:ℚ)/10000000000),((1429363227:ℚ)/2000000000),((-1269363227:ℚ)/5625000000),((-17358015051:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((150838801:ℚ)/400000000),((1097546348891217444390903751223103488163346149730203331:ℚ)/102670585918945312500000000000000000000000000000000000000),((94391323958200181371207:ℚ)/3465600000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-1:ℚ)/4),((-3:ℚ)/16),((1781350753:ℚ)/2500000000),((1794129881:ℚ)/2500000000),((-1594129881:ℚ)/7090625000),((-1461350753:ℚ)/9493750000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((888171963:ℚ)/2500000000),((64617398444359647936881595214570922804610921545715863677:ℚ)/6067333834511566162109375000000000000000000000000000000000),((48910107716046187880021:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((1431020373:ℚ)/2000000000),((7206222781:ℚ)/10000000000),((-915174683:ℚ)/4068750000),((-3525061119:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1719294269:ℚ)/5000000000),((259372045436518299114639167659712833467254082984313711309:ℚ)/24366832089600000000000000000000000000000000000000000000000),((780744386614964071577821:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-1:ℚ)/4),((-3:ℚ)/16),((449050039:ℚ)/625000000),((1808981477:ℚ)/2500000000),((-1608981477:ℚ)/7150000000),((-1107150117:ℚ)/7179687500),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((664146411:ℚ)/2000000000),((1759559033215678982015196190434933964105782769481735871:ℚ)/165387500728666782379150390625000000000000000000000000000),((48683043247769288185069:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((721449929:ℚ)/1000000000),((3632814453:ℚ)/5000000000),((-3232814453:ℚ)/14359375000),((-593449929:ℚ)/3845000000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3198702589:ℚ)/10000000000),((67810556543262090491137162638770417375292571351599:ℚ)/6376973322616577148437500000000000000000000000000000),((582835979566667755568647:ℚ)/21660000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((905524733:ℚ)/1250000000),((3662517261:ℚ)/5000000000),((-3262517261:ℚ)/14418750000),((-2236574199:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((384000291:ℚ)/1250000000),((236021361282734078521092454431582045369614381264747653997:ℚ)/22149646498590087890625000000000000000000000000000000000000),((581778811572026197922743:ℚ)/21660000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/4),((-3:ℚ)/16),((365179737:ℚ)/500000000),((7384439641:ℚ)/10000000000),((-6584439641:ℚ)/29075000000),((-903539211:ℚ)/5862500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2802030379:ℚ)/10000000000),((7795336674392504693019596673904471202916358912022942137:ℚ)/732281906536865234375000000000000000000000000000000000000),((772088457252989985771941:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3681495631:ℚ)/5000000000),((1860961069:ℚ)/2500000000),((-1660961069:ℚ)/7328125000),((-3041495631:ℚ)/19700000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2503949269:ℚ)/10000000000),((29792542967951269633059629080049832173523258579589510299:ℚ)/2801312450781250000000000000000000000000000000000000000000),((48029899970231706339621:ℚ)/1805000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7422387437:ℚ)/10000000000),((3781326069:ℚ)/5000000000),((-3381326069:ℚ)/14775000000),((-18427162311:ℚ)/120100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2166179699:ℚ)/10000000000),((8540571604866387201843857061794596921171362806147295380081:ℚ)/799846287649218750000000000000000000000000000000000000000000),((574278856827768178103863:ℚ)/21660000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((7541178783:ℚ)/10000000000),((1920364549:ℚ)/2500000000),((-1720364549:ℚ)/7506250000),((-18783536349:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((9726257:ℚ)/78125000),((72638648540769052654891495733540104864228433395251779697909:ℚ)/6815104525000000000000000000000000000000000000000000000000000),((1594476166550423:ℚ)/60800000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((191499221:ℚ)/250000000),((8156665983:ℚ)/10000000000),((-7356665983:ℚ)/30500000000),((-53166407:ℚ)/360000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((32398151733031907669831118250268849978752129745321:ℚ)/2964600000000000000000000000000000000000000000000000),((41717:ℚ)/1600000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8135117317:ℚ)/10000000000),((5028649819:ℚ)/5000000000),((-1542883273:ℚ)/5400000000),((-20565351951:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4076052719159428399402459423091990740886411081513893660397:ℚ)/345600000000000000000000000000000000000000000000000000000000),((41717:ℚ)/1600000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((2508892531:ℚ)/2500000000),((6929021671:ℚ)/5000000000),((-6529021671:ℚ)/20000000000),((-2188892531:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((191639507473637946555153092057628313705047566349154193:ℚ)/14600400000000000000000000000000000000000000000000000000),((41717:ℚ)/1600000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((919:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((919:ℚ)/1280) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((591:ℚ)/800) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC13
#check @N11Formalization.C450SeventhGroupedC13.bound
#print axioms N11Formalization.C450SeventhGroupedC13.valid0
#print axioms N11Formalization.C450SeventhGroupedC13.valid1
#print axioms N11Formalization.C450SeventhGroupedC13.valid2
#print axioms N11Formalization.C450SeventhGroupedC13.valid3
#print axioms N11Formalization.C450SeventhGroupedC13.valid4
#print axioms N11Formalization.C450SeventhGroupedC13.valid5
#print axioms N11Formalization.C450SeventhGroupedC13.valid6
#print axioms N11Formalization.C450SeventhGroupedC13.valid7
#print axioms N11Formalization.C450SeventhGroupedC13.valid8
#print axioms N11Formalization.C450SeventhGroupedC13.valid9
#print axioms N11Formalization.C450SeventhGroupedC13.valid10
#print axioms N11Formalization.C450SeventhGroupedC13.valid11
#print axioms N11Formalization.C450SeventhGroupedC13.valid12
#print axioms N11Formalization.C450SeventhGroupedC13.valid13
#print axioms N11Formalization.C450SeventhGroupedC13.valid14
#print axioms N11Formalization.C450SeventhGroupedC13.valid15
#print axioms N11Formalization.C450SeventhGroupedC13.valid16
#print axioms N11Formalization.C450SeventhGroupedC13.valid17
#print axioms N11Formalization.C450SeventhGroupedC13.bound
#print axioms N11Formalization.C450SeventhGroupedC13.endpoint_checks
