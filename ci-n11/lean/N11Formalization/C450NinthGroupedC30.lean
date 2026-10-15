import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((5918064211:ℚ)/10000000000),((3222751959:ℚ)/5000000000),((81414834743:ℚ)/106800000000),((23839263713:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3391084689:ℚ)/5000000000),((-176042286497184611092266398467360972931:ℚ)/7613665200000000000000000000000000000000),((-235788269021076320813367617:ℚ)/1386240000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6393202003:ℚ)/10000000000),((6683072519:ℚ)/10000000000),((87591626039:ℚ)/110600000000),((16447169211:ℚ)/17800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1142555439:ℚ)/2000000000),((-673734496356885668413032716829670509874146020789084781301:ℚ)/25366856550000000000000000000000000000000000000000000000000),((-313033590571381459803856459:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((3315381897:ℚ)/5000000000),((170046377:ℚ)/250000000),((45339964661:ℚ)/56250000000),((1254324639:ℚ)/1382500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5105642389:ℚ)/10000000000),((-10451621736510243432982730251960202344050522269155325159:ℚ)/370788574218750000000000000000000000000000000000000000000),((-195223672347539388255851:ℚ)/1155200000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((1687385781:ℚ)/2500000000),((86507957:ℚ)/125000000),((23056015153:ℚ)/28600000000),((637555699:ℚ)/703125000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2388031087:ℚ)/5000000000),((-34076353594574106301634907785476184064164037895854609:ℚ)/1208350000000000000000000000000000000000000000000000000),((-48700303124915946914531:ℚ)/288800000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6868321479:ℚ)/10000000000),((6980026911:ℚ)/10000000000),((93768179227:ℚ)/115350000000),((51420188377:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((553000857:ℚ)/1250000000),((-208472143903607734672435078824842474907511188481652041337:ℚ)/7194391665820312500000000000000000000000000000000000000000),((-934031667530710700513021297:ℚ)/5544960000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3463855153:ℚ)/5000000000),((7039417011:ℚ)/10000000000),((47270116989:ℚ)/58150000000),((51835919077:ℚ)/57675000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4237806239:ℚ)/10000000000),((-1424330374706494029679444600297854540116224149306755557:ℚ)/49157429593750000000000000000000000000000000000000000000),((-933017349035157737688196697:ℚ)/5544960000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((6987098907:ℚ)/10000000000),((7098806867:ℚ)/10000000000),((95312285791:ℚ)/117250000000),((52251648069:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((2021790617:ℚ)/5000000000),((-31273181382962701909218189129555057842983390262594640923:ℚ)/1079398461914062500000000000000000000000000000000000000000),((-310667621464768053091533491:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((880810911:ℚ)/1250000000),((7158196483:ℚ)/10000000000),((12010541843:ℚ)/14775000000),((52667375381:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((960027683:ℚ)/2500000000),((-16222584248556662589070026021519622271892623856330731:ℚ)/559963842773437500000000000000000000000000000000000000),((-310329404513968260645551891:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7105875453:ℚ)/10000000000),((3608792933:ℚ)/5000000000),((96856380889:ℚ)/119150000000),((26541550531:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3625834683:ℚ)/10000000000),((-918785926611460065304545657971387644038351530600316694931:ℚ)/31716365360156250000000000000000000000000000000000000000000),((-77497783030033472821362691:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((7165263409:ℚ)/10000000000),((3638487511:ℚ)/5000000000),((97628424317:ℚ)/120100000000),((26749412577:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3398705819:ℚ)/10000000000),((-19601618494555328728646288359162344090157031323875782909:ℚ)/676688906640625000000000000000000000000000000000000000000),((-77413201062437368357217899:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7224651159:ℚ)/10000000000),((1467272791:ℚ)/2000000000),((98400465067:ℚ)/121050000000),((10782909537:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1577972991:ℚ)/5000000000),((-35678599516912181792739541715164437465498233635706869411:ℚ)/1231776428906250000000000000000000000000000000000000000000),((-12372576835226922003570539:ℚ)/73932800000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((728403871:ℚ)/1000000000),((7395752671:ℚ)/10000000000),((9917250323:ℚ)/12200000000),((54330268697:ℚ)/60525000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2893619019:ℚ)/10000000000),((-328707437448474743544303473657869708575539872511656291:ℚ)/11349050000000000000000000000000000000000000000000000000),((-308975981979348997486173179:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1468685213:ℚ)/2000000000),((117414523:ℚ)/156250000),((19988907769:ℚ)/24780000000),((861901661:ℚ)/953125000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((260581697:ℚ)/1000000000),((-74649712515269008237029827468712846636413705241289633:ℚ)/2641687387500000000000000000000000000000000000000000000),((-75268295280377241132451:ℚ)/451250000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3731100103:ℚ)/5000000000),((954163183:ℚ)/1250000000),((50744301339:ℚ)/62900000000),((2333047427:ℚ)/2581250000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1907176477:ℚ)/10000000000),((-42937413577370539160083921863276520503531024167329683:ℚ)/1518909844970703125000000000000000000000000000000000000),((-21316593:ℚ)/128000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7580973617:ℚ)/10000000000),((196771379:ℚ)/250000000),((34344219007:ℚ)/43200000000),((1441399653:ℚ)/1572500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((353872627:ℚ)/5000000000),((-503399898066038582791137625625642627835032876215708373:ℚ)/18662400000000000000000000000000000000000000000000000000),((-21316593:ℚ)/128000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7818518381:ℚ)/10000000000),((4885583863:ℚ)/5000000000),((106120738953:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-22632606221046945756621092821248907773298394515918699809:ℚ)/1600000000000000000000000000000000000000000000000000000000),((-21316593:ℚ)/128000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((388751997:ℚ)/400000000),((2714306923:ℚ)/2000000000),((5232975961:ℚ)/8832000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1198638827155278817560095301537691:ℚ)/172233326592000000000000000000000000),((-21316593:ℚ)/128000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound ninth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC30
#check @N11Formalization.C450NinthGroupedC30.bound
#print axioms N11Formalization.C450NinthGroupedC30.valid0
#print axioms N11Formalization.C450NinthGroupedC30.valid1
#print axioms N11Formalization.C450NinthGroupedC30.valid2
#print axioms N11Formalization.C450NinthGroupedC30.valid3
#print axioms N11Formalization.C450NinthGroupedC30.valid4
#print axioms N11Formalization.C450NinthGroupedC30.valid5
#print axioms N11Formalization.C450NinthGroupedC30.valid6
#print axioms N11Formalization.C450NinthGroupedC30.valid7
#print axioms N11Formalization.C450NinthGroupedC30.valid8
#print axioms N11Formalization.C450NinthGroupedC30.valid9
#print axioms N11Formalization.C450NinthGroupedC30.valid10
#print axioms N11Formalization.C450NinthGroupedC30.valid11
#print axioms N11Formalization.C450NinthGroupedC30.valid12
#print axioms N11Formalization.C450NinthGroupedC30.valid13
#print axioms N11Formalization.C450NinthGroupedC30.valid14
#print axioms N11Formalization.C450NinthGroupedC30.valid15
#print axioms N11Formalization.C450NinthGroupedC30.valid16
#print axioms N11Formalization.C450NinthGroupedC30.bound
#print axioms N11Formalization.C450NinthGroupedC30.endpoint_checks
