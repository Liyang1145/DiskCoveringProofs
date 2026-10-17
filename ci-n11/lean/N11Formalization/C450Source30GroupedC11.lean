import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((807254461:ℚ)/1250000000),((3391024511:ℚ)/5000000000),((-5693073533:ℚ)/24800000000),((-343254461:ℚ)/2575000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5553014819:ℚ)/10000000000),((212031792281666868168090708085872414859:ℚ)/1304991872000000000000000000000000000000),((167155549379490827298459:ℚ)/9241600000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1339795357:ℚ)/2000000000),((6902460019:ℚ)/10000000000),((-11747380057:ℚ)/51500000000),((-597395357:ℚ)/4196000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4918846783:ℚ)/10000000000),((587339442597140471157609149251167630743372546212860726307283:ℚ)/3669549205099487304687500000000000000000000000000000000000000),((83243995147194585342171:ℚ)/23658496000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3409675951:ℚ)/5000000000),((6962642697:ℚ)/10000000000),((-11927928091:ℚ)/52450000000),((-1553675951:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((285762591:ℚ)/625000000),((8800281877189039450082681801197155459813456554336045376882713:ℚ)/55365005940669531250000000000000000000000000000000000000000000),((-1578820255930119239061:ℚ)/409600000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((3439758571:ℚ)/5000000000),((1755702679:ℚ)/2500000000),((-3027108037:ℚ)/13231250000),((-1583758571:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2194735611:ℚ)/5000000000),((1141986779809630740710607669061152437223986461062726897263:ℚ)/7167086962754535675048828125000000000000000000000000000000),((-1118356796560510715765461:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/8),((-5:ℚ)/16),((6939668047:ℚ)/10000000000),((1770741119:ℚ)/2500000000),((-3072223357:ℚ)/13350000000),((-3227668047:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1049845019:ℚ)/2500000000),((49022885406840375339764518172818933176072126917289753824543:ℚ)/306927530646093750000000000000000000000000000000000000000000),((-6675817059650812576365789:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1399961001:ℚ)/2000000000),((7143104359:ℚ)/10000000000),((-12469313077:ℚ)/53875000000),((-657561001:ℚ)/4348000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2000436757:ℚ)/5000000000),((184882870461726544425695099721185676821780012956757143485430967:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((-1066439245994251256741863:ℚ)/70975488000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((882491049:ℚ)/1250000000),((450201921:ℚ)/625000000),((-790605763:ℚ)/3396875000),((-418491049:ℚ)/2741250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((3792624747:ℚ)/10000000000),((1312957175339275251097511164072598964864963685862206799177:ℚ)/8181510383469855785369873046875000000000000000000000000000),((-520638965691168452761063:ℚ)/27724800000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((7120038569:ℚ)/10000000000),((1815835991:ℚ)/2500000000),((-3207507973:ℚ)/13706250000),((-3408038569:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3572924847:ℚ)/10000000000),((120324475769604323326597496493720381847068321569804830543:ℚ)/748042616496276855468750000000000000000000000000000000000),((-13335736834856998117877581:ℚ)/591462400000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((3590067943:ℚ)/5000000000),((3691766167:ℚ)/5000000000),((-6595298501:ℚ)/27650000000),((-1734067943:ℚ)/11250000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((667901677:ℚ)/2000000000),((83045477839421250406928840922596903879297728638883122571:ℚ)/509602028906250000000000000000000000000000000000000000000),((-3893329337967094277907629:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((7300293269:ℚ)/10000000000),((1875918021:ℚ)/2500000000),((-3387754063:ℚ)/14062500000),((-326208479:ℚ)/2080000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((8805299:ℚ)/31250000),((989149533895091997836760977965496227812794817875939653:ℚ)/6043910980224609375000000000000000000000000000000000000),((-20074929393085196597748181:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((3710201549:ℚ)/5000000000),((124746739:ℚ)/156250000),((-234240217:ℚ)/893750000),((-1854201549:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1706816001:ℚ)/5000000000),((2178294489:ℚ)/10000000000),((361754256575334376689856928742481246445555107007478421:ℚ)/2075381135368347167968750000000000000000000000000000000),((-6152962817935234149446021:ℚ)/147865600000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((3950206119:ℚ)/5000000000),((66119543:ℚ)/78125000),((-128358629:ℚ)/476562500),((-2094206119:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((66769623484294574896417546842355577053094916842826737773:ℚ)/378728826141357421875000000000000000000000000000000000000),((-54475359:ℚ)/1024000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((8379825649:ℚ)/10000000000),((10377013129:ℚ)/10000000000),((-22171039387:ℚ)/64800000000),((-4667825649:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((834691396037205621017321738969796690352493975262634379:ℚ)/3936600000000000000000000000000000000000000000000000000),((-54475359:ℚ)/1024000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((2058648787:ℚ)/2000000000),((7096519281:ℚ)/5000000000),((-16809557843:ℚ)/40000000000),((-1316248787:ℚ)/8832000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((6570721306484229381806534258502884799217:ℚ)/25392000000000000000000000000000000000000),((-54475359:ℚ)/1024000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((2117:ℚ)/3200) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source30 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC11
#check @N11Formalization.C450Source30GroupedC11.bound
#print axioms N11Formalization.C450Source30GroupedC11.valid0
#print axioms N11Formalization.C450Source30GroupedC11.valid1
#print axioms N11Formalization.C450Source30GroupedC11.valid2
#print axioms N11Formalization.C450Source30GroupedC11.valid3
#print axioms N11Formalization.C450Source30GroupedC11.valid4
#print axioms N11Formalization.C450Source30GroupedC11.valid5
#print axioms N11Formalization.C450Source30GroupedC11.valid6
#print axioms N11Formalization.C450Source30GroupedC11.valid7
#print axioms N11Formalization.C450Source30GroupedC11.valid8
#print axioms N11Formalization.C450Source30GroupedC11.valid9
#print axioms N11Formalization.C450Source30GroupedC11.valid10
#print axioms N11Formalization.C450Source30GroupedC11.valid11
#print axioms N11Formalization.C450Source30GroupedC11.valid12
#print axioms N11Formalization.C450Source30GroupedC11.valid13
#print axioms N11Formalization.C450Source30GroupedC11.bound
#print axioms N11Formalization.C450Source30GroupedC11.endpoint_checks
