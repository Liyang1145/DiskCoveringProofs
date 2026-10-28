import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((3008983703:ℚ)/5000000000),((6535919759:ℚ)/10000000000),((34698820733:ℚ)/53400000000),((20567759277:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1642459917:ℚ)/2500000000),((-117657931112204692132045476147030751:ℚ)/19034163000000000000000000000000000000),((-866240249593060489236631:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((649311209:ℚ)/1000000000),((3386737033:ℚ)/5000000000),((7462423299:ℚ)/11060000000),((3546737033:ℚ)/4450000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((273242157:ℚ)/500000000),((-31835195863981690614639393654533598021675818456535051:ℚ)/4227809425000000000000000000000000000000000000000000000),((-34669434331361749135879:ℚ)/288800000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((1682669243:ℚ)/2500000000),((3446124921:ℚ)/5000000000),((6436453891:ℚ)/9375000000),((1545482109:ℚ)/1975000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2414894547:ℚ)/5000000000),((-2333123354484464739687406911368339099780336302235339:ℚ)/286102294921875000000000000000000000000000000000000000),((-216753944015763554149191:ℚ)/1805000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((6849457769:ℚ)/10000000000),((7011024763:ℚ)/10000000000),((78544035459:ℚ)/114400000000),((2443674921:ℚ)/3125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4481633949:ℚ)/10000000000),((-3481442678175851205002948068457340058868922672126072889:ℚ)/425339200000000000000000000000000000000000000000000000000),((-3468022691939268448136999:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6968237543:ℚ)/10000000000),((1414082383:ℚ)/2000000000),((26616870991:ℚ)/38450000000),((4434247149:ℚ)/5720000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4106203707:ℚ)/10000000000),((-1129644942090058170511641681111721748713051175310307117:ℚ)/133229475292968750000000000000000000000000000000000000000),((-3468636051500043454728391:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((7027627061:ℚ)/10000000000),((7129798869:ℚ)/10000000000),((80503897671:ℚ)/116300000000),((7449798869:ℚ)/9612500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((976454097:ℚ)/2500000000),((-1669251294084116933624805878299589451769758823171446919:ℚ)/196629718375000000000000000000000000000000000000000000000),((-3468634581368323943770239:ℚ)/28880000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((7087016343:ℚ)/10000000000),((7189185629:ℚ)/10000000000),((81157179773:ℚ)/117250000000),((22527556887:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3695162989:ℚ)/10000000000),((-655287274352148026919448918153181118646145229018205679:ℚ)/77099890136718750000000000000000000000000000000000000000),((-3468638464923761187079591:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((11:ℚ)/16),((3:ℚ)/4),((7146405393:ℚ)/10000000000),((7218878937:ℚ)/10000000000),((81810459323:ℚ)/117725000000),((22616636811:ℚ)/29312500000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((434046447:ℚ)/1250000000),((-11013318188040549347759799923246888342194426183115115307:ℚ)/1274665195666503906250000000000000000000000000000000000000),((-3468963878184098233696791:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((7176099833:ℚ)/10000000000),((36242861:ℚ)/50000000),((27379032721:ℚ)/39400000000),((113528583:ℚ)/147156250),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3355672537:ℚ)/10000000000),((-413043568018532141378165184785720341576557905730802969:ℚ)/47783581250000000000000000000000000000000000000000000000),((-3468970503860690614567751:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7205794217:ℚ)/10000000000),((3653979293:ℚ)/5000000000),((82463736387:ℚ)/119150000000),((3813979293:ℚ)/4925000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3234930961:ℚ)/10000000000),((-45024357865325994592381971645739582888820332003499133507:ℚ)/5286060893359375000000000000000000000000000000000000000000),((-3468662292835370788104551:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((363259141:ℚ)/500000000),((920918099:ℚ)/1250000000),((4155850551:ℚ)/6005000000),((2882754297:ℚ)/3723437500),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1489668071:ℚ)/5000000000),((-360593492610577721497501628234099330536734765922399:ℚ)/42293056665039062500000000000000000000000000000000000),((-8671705592731535431679:ℚ)/72200000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((7324571209:ℚ)/10000000000),((3713365411:ℚ)/5000000000),((83770283299:ℚ)/121050000000),((11620096233:ℚ)/15012500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2700432117:ℚ)/10000000000),((-5256075221624113318672785372599605689284756136720149179:ℚ)/615888214453125000000000000000000000000000000000000000000),((-3468707534839877546755879:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((7383959387:ℚ)/10000000000),((187152917:ℚ)/250000000),((84423553257:ℚ)/122000000000),((195152917:ℚ)/252187500),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2390067091:ℚ)/10000000000),((-48470571068071917499942701621579720838495922281142898577:ℚ)/5674525000000000000000000000000000000000000000000000000000),((-3468738186010317850568671:ℚ)/28880000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((7443347359:ℚ)/10000000000),((7604887897:ℚ)/10000000000),((85076820949:ℚ)/123900000000),((23774663691:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1016941293:ℚ)/5000000000),((-1370832615978724616330211683951635261365858722433925909:ℚ)/165105461718750000000000000000000000000000000000000000000),((-3468193895709209796634679:ℚ)/28880000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1890530677:ℚ)/2500000000),((7723658473:ℚ)/10000000000),((21595837447:ℚ)/31450000000),((8043658473:ℚ)/10325000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((499399617:ℚ)/5000000000),((-789874315894386435838927008052768732524204901565623:ℚ)/94931865310668945312500000000000000000000000000000000),((-216846665386674661451711:ℚ)/1805000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((768089729:ℚ)/1000000000),((3980598907:ℚ)/5000000000),((108259099:ℚ)/160000000),((12421796721:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-100829993796169527898434023616393734184337947179:ℚ)/12800000000000000000000000000000000000000000000000),((-480607:ℚ)/4000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((7918444293:ℚ)/10000000000),((9861445259:ℚ)/10000000000),((90302887223:ℚ)/160000000000),((10181445259:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-7941068468223531521124878234687609774978405331960580781:ℚ)/2400000000000000000000000000000000000000000000000000000000),((-480607:ℚ)/4000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((4909369959:ℚ)/5000000000),((2732347143:ℚ)/2000000000),((2417524763:ℚ)/4800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-4968982869752629431845722268281:ℚ)/13824000000000000000000000000000000),((-480607:ℚ)/4000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
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
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC28
#check @N11Formalization.C450SeventhGroupedC28.bound
#print axioms N11Formalization.C450SeventhGroupedC28.valid0
#print axioms N11Formalization.C450SeventhGroupedC28.valid1
#print axioms N11Formalization.C450SeventhGroupedC28.valid2
#print axioms N11Formalization.C450SeventhGroupedC28.valid3
#print axioms N11Formalization.C450SeventhGroupedC28.valid4
#print axioms N11Formalization.C450SeventhGroupedC28.valid5
#print axioms N11Formalization.C450SeventhGroupedC28.valid6
#print axioms N11Formalization.C450SeventhGroupedC28.valid7
#print axioms N11Formalization.C450SeventhGroupedC28.valid8
#print axioms N11Formalization.C450SeventhGroupedC28.valid9
#print axioms N11Formalization.C450SeventhGroupedC28.valid10
#print axioms N11Formalization.C450SeventhGroupedC28.valid11
#print axioms N11Formalization.C450SeventhGroupedC28.valid12
#print axioms N11Formalization.C450SeventhGroupedC28.valid13
#print axioms N11Formalization.C450SeventhGroupedC28.valid14
#print axioms N11Formalization.C450SeventhGroupedC28.valid15
#print axioms N11Formalization.C450SeventhGroupedC28.valid16
#print axioms N11Formalization.C450SeventhGroupedC28.valid17
#print axioms N11Formalization.C450SeventhGroupedC28.bound
#print axioms N11Formalization.C450SeventhGroupedC28.endpoint_checks
