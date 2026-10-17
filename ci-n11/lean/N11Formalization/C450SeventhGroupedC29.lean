import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC29
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((3:ℚ)/4),((13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/4),((13:ℚ)/16),((6003421167:ℚ)/10000000000),((1630922253:ℚ)/2500000000),((18810263501:ℚ)/26700000000),((22161989289:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6601115431:ℚ)/10000000000),((-20962665163548596299377366419183023:ℚ)/2379270375000000000000000000000000000),((-704324370638427762557977183:ℚ)/5544960000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((809816693:ℚ)/1250000000),((422577129:ℚ)/625000000),((2529450079:ℚ)/3456250000),((1911167559:ℚ)/2225000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5501643171:ℚ)/10000000000),((-3997253547778396072478417268293678793524170050546733:ℚ)/387067513275146484375000000000000000000000000000000000),((-3664211035500373118622701:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/4),((13:ℚ)/16),((6716083939:ℚ)/10000000000),((860000681:ℚ)/1250000000),((20948251817:ℚ)/28125000000),((11660008853:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2435486183:ℚ)/5000000000),((-255863728580182729119671320423700357173551099857612251:ℚ)/23174285888671875000000000000000000000000000000000000000),((-234381133316438402113008829:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/4),((13:ℚ)/16),((341742893:ℚ)/500000000),((3499388061:ℚ)/5000000000),((1065228679:ℚ)/1430000000),((5268004977:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((226288277:ℚ)/500000000),((-9189463907267766773894695288926738116442297857549:ℚ)/830740625000000000000000000000000000000000000000000),((-585535776326435077429501:ℚ)/4620800000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((1390726197:ℚ)/2000000000),((7058161203:ℚ)/10000000000),((4332178591:ℚ)/5767500000),((8690554149:ℚ)/10400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4154087373:ℚ)/10000000000),((-5126304779606415090637649908017131337584135986270717:ℚ)/449649479113769531250000000000000000000000000000000000),((-28098228364969193950252423:ℚ)/221798400000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((3506508631:ℚ)/5000000000),((7117546119:ℚ)/10000000000),((10919525893:ℚ)/14537500000),((32122699849:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((791200437:ℚ)/2000000000),((-4380589945654215033835814356525068202107974386763853:ℚ)/384042418701171875000000000000000000000000000000000000),((-58517278663947426941932389:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/4),((13:ℚ)/16),((1414480671:ℚ)/2000000000),((57415447:ℚ)/80000000),((4403442013:ℚ)/5862500000),((777120811:ℚ)/930400000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3748040129:ℚ)/10000000000),((-769888949924263751951157090535222544807004916879273:ℚ)/67462403869628906250000000000000000000000000000000000),((-28078380520996619566900927:ℚ)/221798400000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((1782947317:ℚ)/2500000000),((3603311597:ℚ)/5000000000),((5548841951:ℚ)/7357812500),((48763050761:ℚ)/58625000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((1764225631:ℚ)/5000000000),((-3602298199067516987899354536298891124108074265193971:ℚ)/311197557535767555236816406250000000000000000000000000),((-14622245203493633335232461:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((7161482159:ℚ)/10000000000),((3618157737:ℚ)/5000000000),((22284446477:ℚ)/29550000000),((48956050581:ℚ)/58862500000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((136543961:ℚ)/400000000),((-233384671079986454596042677399434141503781597420352157:ℚ)/20158698339843750000000000000000000000000000000000000000),((-233914773838043206972001269:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((3:ℚ)/4),((13:ℚ)/16),((3595587503:ℚ)/5000000000),((1816501929:ℚ)/2500000000),((11186762509:ℚ)/14834375000),((8191508359:ℚ)/9850000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((205931723:ℚ)/625000000),((-354367016897718659381811862743467743491847576756376503:ℚ)/30604059426212310791015625000000000000000000000000000000),((-58468417233567879396701941:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((722086781:ℚ)/1000000000),((91196249:ℚ)/125000000),((2246260343:ℚ)/2978750000),((26245771:ℚ)/31562500),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((634389079:ℚ)/2000000000),((-239127183953632879232140520216750398342093094674983:ℚ)/20648675364685058593750000000000000000000000000000000),((-2338326085447495598174589:ℚ)/18483200000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((1812640143:ℚ)/2500000000),((7355084217:ℚ)/10000000000),((5637920429:ℚ)/7506250000),((99456094821:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3044194473:ℚ)/10000000000),((-943943201402517061170010350479857340053251178776861:ℚ)/82603626298904418945312500000000000000000000000000000),((-43826201581397057821535503:ℚ)/346560000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((3:ℚ)/4),((13:ℚ)/16),((7309945971:ℚ)/10000000000),((7414468367:ℚ)/10000000000),((22729837913:ℚ)/30262500000),((100228088771:ℚ)/120100000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2771651729:ℚ)/10000000000),((-110012936854352253735003111189697487283384987338931337:ℚ)/9623253350830078125000000000000000000000000000000000000),((-700973531036638234282023127:ℚ)/5544960000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((3:ℚ)/4),((13:ℚ)/16),((7369331207:ℚ)/10000000000),((59790819:ℚ)/80000000),((22907993621:ℚ)/30500000000),((269333549:ℚ)/322800000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2470058463:ℚ)/10000000000),((-1013999456820538282106525606409274255665619421828885029:ℚ)/88664453125000000000000000000000000000000000000000000000),((-233576123630133951507132101:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/4),((13:ℚ)/16),((7428716283:ℚ)/10000000000),((7592619977:ℚ)/10000000000),((23086148849:ℚ)/30975000000),((102544059701:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2127087161:ℚ)/10000000000),((-86257138684039938437661642641926673524256805768282827:ℚ)/7739318518066406250000000000000000000000000000000000000),((-700172642205065628047124583:ℚ)/5544960000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/4),((13:ℚ)/16),((1886871493:ℚ)/2500000000),((3855693523:ℚ)/5000000000),((5860614479:ℚ)/7862500000),((52044015799:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1176240849:ℚ)/10000000000),((-16551325764553339910024028037730874612195034535239:ℚ)/1483310395479202270507812500000000000000000000000000),((-14588927793700107607469901:ℚ)/115520000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/4),((13:ℚ)/16),((3833127533:ℚ)/5000000000),((1987229921:ℚ)/2500000000),((11899382599:ℚ)/16200000000),((26793988973:ℚ)/31450000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-5226677623849239056997816361914464753582771116552877:ℚ)/492075000000000000000000000000000000000000000000000000),((-8083203:ℚ)/64000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/4),((13:ℚ)/16),((3951895787:ℚ)/5000000000),((2462281241:ℚ)/2500000000),((12255687361:ℚ)/20000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-24282427530433098849004242486560865832466029204739083:ℚ)/4687500000000000000000000000000000000000000000000000000),((-8083203:ℚ)/64000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/4),((13:ℚ)/16),((24510053:ℚ)/25000000),((1364936593:ℚ)/1000000000),((75530159:ℚ)/138000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-632284600133788632193141117:ℚ)/328509000000000000000000000000),((-8083203:ℚ)/64000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC29
#check @N11Formalization.C450SeventhGroupedC29.bound
#print axioms N11Formalization.C450SeventhGroupedC29.valid0
#print axioms N11Formalization.C450SeventhGroupedC29.valid1
#print axioms N11Formalization.C450SeventhGroupedC29.valid2
#print axioms N11Formalization.C450SeventhGroupedC29.valid3
#print axioms N11Formalization.C450SeventhGroupedC29.valid4
#print axioms N11Formalization.C450SeventhGroupedC29.valid5
#print axioms N11Formalization.C450SeventhGroupedC29.valid6
#print axioms N11Formalization.C450SeventhGroupedC29.valid7
#print axioms N11Formalization.C450SeventhGroupedC29.valid8
#print axioms N11Formalization.C450SeventhGroupedC29.valid9
#print axioms N11Formalization.C450SeventhGroupedC29.valid10
#print axioms N11Formalization.C450SeventhGroupedC29.valid11
#print axioms N11Formalization.C450SeventhGroupedC29.valid12
#print axioms N11Formalization.C450SeventhGroupedC29.valid13
#print axioms N11Formalization.C450SeventhGroupedC29.valid14
#print axioms N11Formalization.C450SeventhGroupedC29.valid15
#print axioms N11Formalization.C450SeventhGroupedC29.valid16
#print axioms N11Formalization.C450SeventhGroupedC29.valid17
#print axioms N11Formalization.C450SeventhGroupedC29.valid18
#print axioms N11Formalization.C450SeventhGroupedC29.bound
#print axioms N11Formalization.C450SeventhGroupedC29.endpoint_checks
