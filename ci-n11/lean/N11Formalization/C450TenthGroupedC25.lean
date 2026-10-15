import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((5990351219:ℚ)/10000000000),((813655589:ℚ)/1250000000),((2210117073:ℚ)/4450000000),((8042900301:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((414319371:ℚ)/625000000),((-7129938121966830849833:ℚ)/4950625000000000000000000),((-2202489979915330069497300467:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6465860459:ℚ)/10000000000),((1349388523:ℚ)/2000000000),((7105860459:ℚ)/13825000000),((4432165569:ℚ)/7120000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5533454837:ℚ)/10000000000),((-7862329869658618478038818252641264388868367543730903:ℚ)/2359268652343750000000000000000000000000000000000000000),((-2223876800905264130236678307:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6703588797:ℚ)/10000000000),((6865786547:ℚ)/10000000000),((7343588797:ℚ)/14062500000),((9650296989:ℚ)/15800000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2452991159:ℚ)/5000000000),((-24242764420978015087100535050562268590782509898940821:ℚ)/5793571472167968750000000000000000000000000000000000000),((-6190248307985702511014043:ℚ)/40960000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((6822447173:ℚ)/10000000000),((1396925471:ℚ)/2000000000),((7462447173:ℚ)/14300000000),((1524925471:ℚ)/2500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4562967113:ℚ)/10000000000),((-7085887330158428646192577774488129969313715707576997:ℚ)/1661481250000000000000000000000000000000000000000000000),((-6205286547663722623553483:ℚ)/40960000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((867662743:ℚ)/1250000000),((1761011659:ℚ)/2500000000),((315887581:ℚ)/600781250),((17289104931:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((838820771:ℚ)/2000000000),((-2366324870766970387652119098499387820218483963991:ℚ)/508230115100741386413574218750000000000000000000000),((-35086804914941106728513003:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3500364017:ℚ)/5000000000),((887933149:ℚ)/1250000000),((3820364017:ℚ)/7268750000),((2903799447:ℚ)/4806250000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((249859639:ℚ)/625000000),((-449959712062052331063719550500904090234517691554027:ℚ)/96010604675292968750000000000000000000000000000000000),((-562071475480385743947000283:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/2),((9:ℚ)/16),((882519161:ℚ)/1250000000),((3581441521:ℚ)/5000000000),((962519161:ℚ)/1832031250),((35112973689:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3791825403:ℚ)/10000000000),((-9708129303151163696667512351731714511324653044977:ℚ)/2058789180591702461242675781250000000000000000000000),((-35172200910214451390432587:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3559788863:ℚ)/5000000000),((7222300203:ℚ)/10000000000),((3879788863:ℚ)/7387500000),((70760701827:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((357465823:ℚ)/1000000000),((-331969931458937904362067678885190575217555358683493:ℚ)/69995480346679687500000000000000000000000000000000000),((-563440096070280548940358843:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((7179001369:ℚ)/10000000000),((7281716691:ℚ)/10000000000),((7819001369:ℚ)/14893750000),((23765150073:ℚ)/39400000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((668811931:ℚ)/2000000000),((-295385838830066703636214266396880731943184285576214113:ℚ)/61946026094055175781250000000000000000000000000000000000),((-2256504480784502922797305867:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((1447684847:ℚ)/2000000000),((7341132521:ℚ)/10000000000),((1575684847:ℚ)/3002500000),((71830192689:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((774256589:ℚ)/2500000000),((-50673547169718469810412320171792461018919396492877:ℚ)/10573264166259765625000000000000000000000000000000000),((-90370125936490625417120923:ℚ)/591462400000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((912230793:ℚ)/1250000000),((740054771:ℚ)/1000000000),((992230793:ℚ)/1891406250),((7236492939:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2829251721:ℚ)/10000000000),((-3771058127791614444449223995564748594385959350387:ℚ)/783142362534999847412109375000000000000000000000000),((-97905401138813108782323:ℚ)/640000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((28739327:ℚ)/39062500),((7459962273:ℚ)/10000000000),((62478654:ℚ)/119140625),((8099962273:ℚ)/13450000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2534163881:ℚ)/10000000000),((-102240296258113607261734853938951499965932751817:ℚ)/21139252930879592895507812500000000000000000000000),((-34557559201786085931863:ℚ)/225625000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7416688357:ℚ)/10000000000),((947348697:ℚ)/1250000000),((8056688357:ℚ)/15487500000),((9246138273:ℚ)/15250000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1100398647:ℚ)/5000000000),((-60039976671347889509274550920422182503282024821287:ℚ)/13162106323242187500000000000000000000000000000000000),((-2267526584888761634958476803:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((941940943:ℚ)/1250000000),((3848807271:ℚ)/5000000000),((1021940943:ℚ)/1965625000),((12506421813:ℚ)/20650000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1303475301:ℚ)/10000000000),((-213335237481179416785682188236068704124692043957:ℚ)/46353449858725070953369140625000000000000000000000),((-35516641823256109776397403:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((1530872807:ℚ)/2000000000),((3967628937:ℚ)/5000000000),((1658872807:ℚ)/3240000000),((38588660433:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-32179747326871424760245020462946667872384930796239:ℚ)/7873200000000000000000000000000000000000000000000000),((-157623097:ℚ)/1024000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((39460147:ℚ)/50000000),((1967231853:ℚ)/2000000000),((42660147:ℚ)/100000000),((2095231853:ℚ)/2880000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((30214995490328866040983555591:ℚ)/18750000000000000000000000000000),((-157623097:ℚ)/1024000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((612066833:ℚ)/625000000),((13637217113:ℚ)/10000000000),((217355611:ℚ)/575000000),((128494954017:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((545581897619972084783:ℚ)/82656250000000000000000),((-157623097:ℚ)/1024000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC25
#check @N11Formalization.C450TenthGroupedC25.bound
#print axioms N11Formalization.C450TenthGroupedC25.valid0
#print axioms N11Formalization.C450TenthGroupedC25.valid1
#print axioms N11Formalization.C450TenthGroupedC25.valid2
#print axioms N11Formalization.C450TenthGroupedC25.valid3
#print axioms N11Formalization.C450TenthGroupedC25.valid4
#print axioms N11Formalization.C450TenthGroupedC25.valid5
#print axioms N11Formalization.C450TenthGroupedC25.valid6
#print axioms N11Formalization.C450TenthGroupedC25.valid7
#print axioms N11Formalization.C450TenthGroupedC25.valid8
#print axioms N11Formalization.C450TenthGroupedC25.valid9
#print axioms N11Formalization.C450TenthGroupedC25.valid10
#print axioms N11Formalization.C450TenthGroupedC25.valid11
#print axioms N11Formalization.C450TenthGroupedC25.valid12
#print axioms N11Formalization.C450TenthGroupedC25.valid13
#print axioms N11Formalization.C450TenthGroupedC25.valid14
#print axioms N11Formalization.C450TenthGroupedC25.valid15
#print axioms N11Formalization.C450TenthGroupedC25.valid16
#print axioms N11Formalization.C450TenthGroupedC25.bound
#print axioms N11Formalization.C450TenthGroupedC25.endpoint_checks
